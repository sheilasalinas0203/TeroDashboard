# =====================================================================
# HMI DE ALTO DESEMPEÑO (ISA-101 / High Performance HMI)
# Monitoreo del motor con ESP32 (corriente, velocidad, vibración) por USB
# ---------------------------------------------------------------------
# NO requiere cambios en el ESP32: lee la línea que ya imprime el código
#   "Corriente: x A | Velocidad: y RPM | Pulsos/ventana: n | Vibracion: z mm/s RMS | Zona: W"
# (también acepta líneas "DATA,..." si más adelante se usan).
#
# Instalar (una sola vez):   pip install -r requirements.txt
# Ejecutar con el ESP32:     streamlit run app.py
# Ejecutar sin ESP32 (demo): streamlit run app.py -- --sim
#
# IMPORTANTE: cerrar el Monitor Serie del Arduino IDE antes de ejecutar.
# =====================================================================

import sys
import re
import io
import html
import csv
import time
import math
import random
import threading
import datetime as dt
from pathlib import Path
from collections import deque

import numpy as np          # >>> NUEVO (Curvas P-F): tendencia lineal para estimar tiempo a F
import pandas as pd
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import serial
import serial.tools.list_ports
import streamlit as st

# =====================================================================
# 1. CONFIGURACIÓN GENERAL
# =====================================================================
EQUIPO = "M-101 · Motor del molino de cacao"
PUERTO_DEF = "COM8"
BAUDIOS = 115200
REFRESCO_S = 0.5            # refresco de pantalla (el ESP32 envía ~cada 0.4 s)
TIMEOUT_COM_S = 3.0         # sin datos por más de esto -> alarma de comunicación
MAX_PUNTOS = 30000          # historial en memoria (~3 h a 2.5 muestras/s)
CARPETA_REG = Path(__file__).parent / "registros"

# Límites por defecto. El motor no tiene placa: ajusta corriente y velocidad
# con "Aprender línea base" (barra lateral) cuando el motor trabaje normal.
LIMITES_DEF = {
    # Corriente (A)
    "i_esc": 10.0, "i_nlo": 1.0, "i_nhi": 4.0, "i_h": 4.5, "i_hh": 5.5,
    # Velocidad (RPM)
    "r_esc": 2000.0, "r_nlo": 1650.0, "r_nhi": 1780.0, "r_l": 1600.0,
    # Vibración (mm/s RMS) - zonas ISO 10816 iguales a las del ESP32
    "v_esc": 7.1, "v_a": 0.71, "v_h": 1.8, "v_hh": 4.5,
}

# =====================================================================
# 2. PALETA HP-HMI (gris neutro; el color SOLO indica alarmas)
# =====================================================================
C = {
    "fondo": "#DADADA", "panel": "#E6E6E6", "borde": "#B3B3B3",
    "texto": "#1E1E1E", "tenue": "#5F5F5F", "barra": "#F2F2F2",
    "normal": "#BEBEBE", "pv": "#262626", "tend": "#333333", "lim": "#7A7A7A",
}
# Prioridad -> nombre, color y forma (codificación redundante: color + forma + número)
PRIO = {
    1: {"nombre": "CRÍTICA", "color": "#D62728", "txt": "#FFFFFF", "forma": "■"},
    2: {"nombre": "ALTA", "color": "#F28C28", "txt": "#1E1E1E", "forma": "▲"},
    3: {"nombre": "MEDIA", "color": "#F2D21B", "txt": "#1E1E1E", "forma": "◆"},
    4: {"nombre": "DIAGNÓSTICO", "color": "#A24FB0", "txt": "#FFFFFF", "forma": "●"},
}

RE_MEDICION = re.compile(
    r"Corriente:\s*(-?[\d.]+)\s*A\s*\|\s*Velocidad:\s*(-?[\d.]+)\s*RPM\s*\|\s*"
    r"Pulsos/ventana:\s*(\d+)\s*\|\s*Vibracion:\s*(-?[\d.]+)\s*mm/s RMS\s*\|\s*Zona:\s*(.+)$"
)
RE_DATA = re.compile(r"^DATA,(\d+),(-?[\d.]+),(-?[\d.]+),(-?[\d.]+),(-?\d+),([01])$")
ZONA_TXT = {0: "BUENA", 1: "ACEPTABLE", 2: "ALERTA", 3: "PELIGRO"}


# =====================================================================
# 3. ADQUISICIÓN, ALARMAS Y REGISTRO (hilo en segundo plano)
# =====================================================================
class Planta:
    """Lee el ESP32 en segundo plano, evalúa alarmas y guarda los registros."""

    def __init__(self):
        self.lock = threading.RLock()
        self.hist = deque(maxlen=MAX_PUNTOS)
        self.msgs = deque(maxlen=40)
        self.alarmas = {}
        self.eventos = deque(maxlen=1000)
        self.lim = dict(LIMITES_DEF)
        self.fuente, self.puerto = None, None
        self.estado_com, self.conectado = "Sin iniciar", False
        self.t_inicio, self.ultimo_dato = time.time(), None
        self.n_lineas = self.n_muestras = self.n_err = 0
        self.offset, self.mpu_id = None, None
        self.marcha, self.t_marcha, self.arranques = False, None, 0
        self._stop, self._hilo = threading.Event(), None
        CARPETA_REG.mkdir(exist_ok=True)

    # ---------- arranque / parada de la adquisición ----------
    def iniciar(self, fuente, puerto=None):
        self.detener()
        self._stop = threading.Event()
        self.fuente, self.puerto = fuente, puerto
        self.t_inicio, self.ultimo_dato = time.time(), None
        destino = self._hilo_sim if fuente == "sim" else self._hilo_serial
        self._hilo = threading.Thread(target=destino, args=(self._stop,), daemon=True)
        self._hilo.start()

    def detener(self):
        if self._hilo is not None and self._hilo.is_alive():
            self._stop.set()
            self._hilo.join(timeout=2)
        self.conectado = False

    def _hilo_serial(self, stop):
        while not stop.is_set():
            ser = None
            try:
                ser = serial.Serial()
                ser.port, ser.baudrate, ser.timeout = self.puerto, BAUDIOS, 0.1
                ser.dtr = False   # no reinicia el ESP32 al conectar
                ser.rts = False   # (evita recalibrar con el motor encendido)
                ser.open()
                self.conectado, self.estado_com = True, f"Conectado a {self.puerto}"
                self._msg(f"[HMI] Puerto {self.puerto} abierto")
                pend = b""
                while not stop.is_set():
                    bloque = ser.read(ser.in_waiting or 1)
                    if bloque:
                        pend += bloque
                        *lineas, pend = pend.split(b"\n")
                        for ln in lineas:
                            self._procesar(ln.decode("utf-8", "ignore").strip())
                    self._vigilar_com()
            except (serial.SerialException, OSError, ValueError) as e:
                self.conectado = False
                self.estado_com = f"Sin conexión con {self.puerto}"
                self._msg(f"[HMI] {e}")
                self._vigilar_com()
                stop.wait(1.5)
            finally:
                if ser is not None and ser.is_open:
                    ser.close()
        self.conectado = False

    def _hilo_sim(self, stop):
        """ESP32 simulado: genera las mismas líneas que imprime el código real."""
        self.conectado, self.estado_com = True, "Simulación (sin ESP32)"
        self._procesar("Offset calibrado: 1.652 V")
        self._procesar("MPU6050 WHO_AM_I = 0x68")
        t0 = time.time()
        while not stop.is_set():
            t = time.time() - t0
            ciclo = t % 300
            if ciclo < 270:                                   # en marcha
                carga = 1 + 0.12 * math.sin(2 * math.pi * t / 40)
                i = 3.1 * carga + random.gauss(0, 0.05)
                if 150 < ciclo < 170:
                    i += 1.7                                  # sobrecarga temporal
                rpm = 1748 - 20 * (i - 3.1) + random.gauss(0, 1.5)
                v = 1.0 + 0.95 * max(0.0, math.sin(2 * math.pi * t / 75)) + random.gauss(0, 0.04)
            else:                                             # detenido
                i, rpm, v = 0.0, 0.0, 0.0
            i = 0.0 if i < 0.30 else i
            v = 0.0 if v < 0.30 else v
            zona = ("BUENA" if v < 0.71 else "ACEPTABLE" if v < 1.8
                    else "ALERTA" if v < 4.5 else "PELIGRO")
            self._procesar(f"Corriente: {i:.2f} A | Velocidad: {rpm:.1f} RPM | "
                           f"Pulsos/ventana: {round(rpm / 6)} | Vibracion: {v:.2f} mm/s RMS | Zona: {zona}")
            self._vigilar_com()
            stop.wait(0.38)
        self.conectado = False

    # ---------- interpretación de cada línea del ESP32 ----------
    def _procesar(self, linea):
        if not linea:
            return
        self.n_lineas += 1
        m = RE_MEDICION.search(linea)
        if m:
            med = {"i": float(m[1]), "rpm": float(m[2]), "pulsos": int(m[3]),
                   "vib": float(m[4]), "zona": m[5].strip()}
        else:
            d = RE_DATA.match(linea)
            if d:
                ok = d[6] == "1"
                med = {"i": float(d[2]), "rpm": float(d[3]), "pulsos": None, "vib": float(d[4]),
                       "zona": ZONA_TXT.get(int(d[5]), "?") if ok else "SIN SENSOR"}
            else:
                if linea.startswith(("Corriente:", "DATA,")):
                    self.n_err += 1                           # línea cortada o con ruido
                    return
                if linea.startswith("Offset calibrado"):
                    try:
                        self.offset = float(linea.split(":")[1].split()[0])
                    except (IndexError, ValueError):
                        pass
                elif "WHO_AM_I" in linea:
                    self.mpu_id = linea.split("=")[-1].strip()
                self._msg(linea)
                return

        med["t"] = time.time()
        med["mpu_ok"] = med["zona"] != "SIN SENSOR"
        with self.lock:
            marcha = med["i"] > 0 or med["rpm"] > 100
            if marcha and not self.marcha:
                self.arranques += 1
                self.t_marcha = med["t"]
                self._evento("M-101", "ARRANQUE", 0, "Motor en marcha", None, "")
            elif not marcha and self.marcha:
                self.t_marcha = None
                self._evento("M-101", "PARADA", 0, "Motor detenido", None, "")
            self.marcha = med["marcha"] = marcha
            self.hist.append(med)
            self.ultimo_dato = med["t"]
            self.n_muestras += 1
            self._evaluar(med)
        self._guardar_medicion(med)

    # ---------- alarmas (ISA-18.2 simplificado) ----------
    def _evaluar(self, m):
        L = self.lim
        # Corriente: HH (crítica) y H (alta), H solo si HH no está activa
        hh = self._limite("II-101.HH", m["i"], L["i_hh"], True, 1, "Corriente muy alta", "A")
        self._limite("II-101.H", m["i"], L["i_h"], True, 2, "Corriente alta", "A", habil=not hh)
        # Velocidad baja con el motor en marcha (sobrecarga / deslizamiento)
        self._limite("SI-101.L", m["rpm"], L["r_l"], False, 2, "Velocidad baja con motor en marcha",
                     "RPM", habil=m["marcha"] and m["rpm"] > 100)
        # Sensor de velocidad: corriente sin pulsos
        self._set("SI-101.BAD", m["i"] > 0 and m["rpm"] < 1, 4,
                  "Sin pulsos de velocidad con motor energizado", m["rpm"], "RPM")
        # Vibración: zona D (crítica) y zona C (alta), ISO 10816
        ok = m["mpu_ok"]
        hh = self._limite("VI-101.HH", m["vib"], L["v_hh"], True, 1,
                          "Vibración zona D (peligro, ISO 10816)", "mm/s", habil=ok)
        self._limite("VI-101.H", m["vib"], L["v_h"], True, 2,
                     "Vibración zona C (alerta, ISO 10816)", "mm/s", habil=ok and not hh)
        self._set("VI-101.BAD", not ok, 4, "Sensor de vibración MPU6050 sin respuesta", None, "")

    def _limite(self, tag, valor, limite, alto, prio, desc, unidad, habil=True, banda=0.03):
        """Alarma de límite con banda muerta del 3 % para evitar alarmas repetitivas."""
        a = self.alarmas.get(tag)
        activa_antes = a is not None and a["activa"]
        if not habil:
            activa = False
        elif alto:
            activa = valor > limite * (1 - banda) if activa_antes else valor >= limite
        else:
            activa = valor < limite * (1 + banda) if activa_antes else valor <= limite
        self._set(tag, activa, prio, desc, valor, unidad, limite)
        return activa

    def _set(self, tag, activa, prio, desc, valor, unidad, limite=None):
        ahora = time.time()
        a = self.alarmas.get(tag)
        if activa:
            if a is None or not a["activa"]:
                if a is None:
                    a = {"tag": tag, "prio": prio, "desc": desc, "unidad": unidad}
                    self.alarmas[tag] = a
                a.update(activa=True, reconocida=False, t_on=ahora, pico=valor)
                self._evento(tag, "ACTIVA", prio, desc, valor, unidad)
            a["valor"], a["limite"] = valor, limite
            if valor is not None and a.get("pico") is not None:
                a["pico"] = max(a["pico"], valor) if tag.endswith(("H", "HH")) else min(a["pico"], valor)
        elif a is not None and a["activa"]:
            a["activa"] = False
            self._evento(tag, "NORMALIZADA", prio, desc, valor, unidad)
            if a["reconocida"]:
                del self.alarmas[tag]

    def reconocer(self, tag):
        with self.lock:
            a = self.alarmas.get(tag)
            if a is None or a["reconocida"]:
                return
            a["reconocida"] = True
            self._evento(tag, "RECONOCIDA", a["prio"], a["desc"], a.get("valor"), a["unidad"])
            if not a["activa"]:
                del self.alarmas[tag]

    def reconocer_todas(self):
        for tag in list(self.alarmas):
            self.reconocer(tag)

    def _vigilar_com(self):
        ref = self.ultimo_dato or self.t_inicio
        edad = time.time() - ref
        with self.lock:
            self._set("COM-101", edad > TIMEOUT_COM_S, 4,
                      "Sin datos del ESP32 (USB)", round(edad, 1), "s")

    # ---------- registros ----------
    def _evento(self, tag, estado, prio, desc, valor, unidad):
        ahora = dt.datetime.now()
        ev = {"fecha_hora": ahora.strftime("%Y-%m-%d %H:%M:%S"), "tag": tag, "estado": estado,
              "prioridad": PRIO[prio]["nombre"] if prio in PRIO else "EVENTO",
              "descripcion": desc, "valor": "" if valor is None else f"{valor:.2f}", "unidad": unidad}
        self.eventos.appendleft(ev)
        self._escribir_csv(f"alarmas_{ahora:%Y-%m-%d}.csv", ev)

    def _guardar_medicion(self, m):
        ahora = dt.datetime.fromtimestamp(m["t"])
        fila = {"fecha_hora": ahora.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3], "corriente_A": m["i"],
                "velocidad_rpm": m["rpm"], "pulsos_ventana": m["pulsos"], "vibracion_mm_s_rms": m["vib"],
                "zona_iso": m["zona"], "motor_en_marcha": int(m["marcha"])}
        self._escribir_csv(f"mediciones_{ahora:%Y-%m-%d}.csv", fila)

    @staticmethod
    def _escribir_csv(nombre, fila):
        ruta = CARPETA_REG / nombre
        nuevo = not ruta.exists()
        try:
            with open(ruta, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(fila))
                if nuevo:
                    w.writeheader()
                w.writerow(fila)
        except OSError:
            pass   # p. ej. el archivo está abierto en Excel; se reintenta con la siguiente fila

    def _msg(self, texto):
        if not self.msgs or self.msgs[-1][1] != texto:
            self.msgs.append((dt.datetime.now().strftime("%H:%M:%S"), texto))

    # ---------- lectura para la interfaz ----------
    def datos(self, segundos):
        lim_t = time.time() - segundos
        with self.lock:
            out = []
            for m in reversed(self.hist):
                if m["t"] < lim_t:
                    break
                out.append(m)
        return out[::-1]

    def estado(self):
        with self.lock:
            ult = self.hist[-1] if self.hist else None
            recientes = list(self.hist)[-11:]
            alarmas = [dict(a) for a in self.alarmas.values()]
        hz = 0.0
        if len(recientes) > 2 and recientes[-1]["t"] > recientes[0]["t"]:
            hz = (len(recientes) - 1) / (recientes[-1]["t"] - recientes[0]["t"])
        alarmas.sort(key=lambda a: (a["reconocida"], not a["activa"], a["prio"], -a["t_on"]))
        return {"ult": ult, "alarmas": alarmas, "hz": hz,
                "edad": None if self.ultimo_dato is None else time.time() - self.ultimo_dato}


@st.cache_resource
def obtener_planta():
    p = Planta()
    if "--sim" in sys.argv:
        p.iniciar("sim")
    else:
        p.iniciar("serial", PUERTO_DEF)
    return p


# =====================================================================
# 4. ELEMENTOS GRÁFICOS HP-HMI
# =====================================================================
CSS = f"""
<style>
.stApp, header[data-testid="stHeader"] {{ background:{C['fondo']}; }}
.block-container {{ padding-top:2.6rem; padding-bottom:1rem; max-width:100%; }}
div[data-testid="stVerticalBlock"] {{ gap:.55rem; }}
.hp-head {{ display:flex; align-items:center; gap:22px; background:{C['panel']};
  border:1px solid {C['borde']}; padding:8px 14px; }}
.hp-title {{ font-size:19px; font-weight:700; color:{C['texto']}; }}
.hp-sub {{ font-size:12px; color:{C['tenue']}; }}
.hp-kv {{ font-size:13px; color:{C['tenue']}; }}
.hp-kv b {{ color:{C['texto']}; }}
.hp-clock {{ margin-left:auto; font-size:15px; font-variant-numeric:tabular-nums; color:{C['texto']}; }}
.hp-cnt {{ display:inline-block; min-width:44px; text-align:center; padding:2px 6px; margin-left:4px;
  border:1px solid {C['borde']}; font-size:13px; font-weight:700; color:{C['tenue']}; }}
.hp-banner {{ padding:7px 14px; font-size:14px; border:1px solid {C['borde']}; }}
.hp-card {{ background:{C['panel']}; border:1px solid {C['borde']}; padding:10px 14px 8px; }}
.hp-row {{ display:flex; align-items:center; gap:8px; }}
.hp-tag {{ font-size:12px; font-weight:700; color:{C['texto']}; letter-spacing:.03em; }}
.hp-desc {{ font-size:12px; color:{C['tenue']}; }}
.hp-ind {{ margin-left:auto; padding:1px 8px; font-size:12px; font-weight:700; border:1px solid #333; }}
.hp-val {{ font-size:36px; font-weight:600; color:{C['texto']}; font-variant-numeric:tabular-nums; line-height:1.15; }}
.hp-unit {{ font-size:15px; color:{C['tenue']}; margin-left:6px; font-weight:400; }}
.hp-bar {{ position:relative; height:16px; background:{C['barra']}; border:1px solid {C['lim']}; margin:16px 0 2px; }}
.hp-bar-n {{ position:absolute; top:0; bottom:0; background:{C['normal']}; }}
.hp-bar-l {{ position:absolute; top:-5px; bottom:-5px; width:0; border-left:2px solid {C['lim']}; }}
.hp-bar-lt {{ position:absolute; top:-17px; font-size:10px; color:{C['tenue']}; transform:translateX(-50%); }}
.hp-bar-p {{ position:absolute; top:-3px; bottom:-3px; width:4px; margin-left:-2px; }}
.hp-scale {{ display:flex; justify-content:space-between; font-size:10px; color:{C['tenue']}; }}
.hp-foot {{ font-size:11px; color:{C['tenue']}; margin-top:2px; }}
.hp-panel {{ background:{C['panel']}; border:1px solid {C['borde']}; padding:10px 14px; height:100%; }}
.hp-panel h4 {{ font-size:13px; margin:0 0 6px; padding:0 !important; color:{C['texto']}; font-weight:700; }}
.hp-t {{ width:100%; font-size:13px; border-collapse:collapse; }}
.hp-t td {{ padding:3px 4px; border-bottom:1px solid #D0D0D0; color:{C['texto']}; }}
.hp-t td:first-child {{ color:{C['tenue']}; }}
.hp-big {{ font-size:22px; font-weight:700; color:{C['texto']}; }}
div.hp-log {{ font-family:Consolas,monospace; background:#EFEFEF; border:1px solid {C['borde']}; font-size:12px; padding:8px; max-height:260px; overflow:auto; }}
.hp-sw {{ display:inline-block; width:14px; height:11px; border:1px solid #888; margin:0 4px 0 12px; vertical-align:-1px; }}
.hp-pfz {{ display:inline-block; padding:1px 8px; font-size:12px; font-weight:700; border:1px solid #333; }}
</style>
"""
# >>> NUEVO (Curvas P-F): las dos últimas clases CSS (.hp-sw y .hp-pfz) son para la pantalla P-F


def caja_alarma(a):
    """Indicador de alarma: forma + número de prioridad + tipo (redundante al color)."""
    p = PRIO[a["prio"]]
    tipo = a["tag"].split(".")[-1]
    estilo = f"background:{p['color']};color:{p['txt']};"
    if not a["activa"]:                      # normalizada sin reconocer: solo contorno
        estilo = f"background:{C['panel']};color:{C['texto']};border:2px solid {p['color']};"
    elif a["reconocida"]:
        estilo = f"background:{C['panel']};color:{C['texto']};border-color:{p['color']};"
    return f"<span class='hp-ind' style='{estilo}'>{p['forma']} {a['prio']} {tipo}</span>"


def pct(v, lo, hi):
    return max(0.0, min(100.0, (v - lo) / (hi - lo) * 100.0)) if hi > lo else 0.0


def svg_tendencia(med, clave, ymin, ymax, normal, lims, ventana=300, ancho=300, alto=58):
    """Mini tendencia en SVG (liviana): línea gris, banda normal y límites."""
    ahora = time.time()

    def y(v):
        return alto - (min(max(v, ymin), ymax) - ymin) / (ymax - ymin) * alto

    partes = [f"<svg viewBox='0 0 {ancho} {alto}' preserveAspectRatio='none' "
              f"style='width:100%;height:{alto}px;background:{C['barra']};border:1px solid #CCC;margin-top:8px'>"]
    if normal:
        y1, y2 = y(normal[1]), y(normal[0])
        partes.append(f"<rect x='0' y='{y1:.1f}' width='{ancho}' height='{max(y2 - y1, 0):.1f}' fill='#DCDCDC'/>")
    for lv in lims:
        partes.append(f"<line x1='0' x2='{ancho}' y1='{y(lv):.1f}' y2='{y(lv):.1f}' "
                      f"stroke='{C['lim']}' stroke-width='1' stroke-dasharray='4 3'/>")
    pts = " ".join(f"{(1 - (ahora - m['t']) / ventana) * ancho:.1f},{y(m[clave]):.1f}" for m in med)
    if pts:
        partes.append(f"<polyline points='{pts}' fill='none' stroke='{C['tend']}' stroke-width='1.6' "
                      f"vector-effect='non-scaling-stroke'/>")
    partes.append("</svg>")
    return "".join(partes)


def tarjeta(tag, desc, valor, unidad, dec, esc, normal, lims, alarmas, spark, pie, calidad=True):
    """Indicador analógico HP: valor, barra con rango normal, límites y puntero."""
    act = [a for a in alarmas if a["tag"].startswith(tag)]
    ind = "".join(caja_alarma(a) for a in act[:2])
    col_ptr = PRIO[min(a["prio"] for a in act if a["activa"])]["color"] if any(a["activa"] for a in act) else C["pv"]
    if valor is None or not calidad:
        txt_val = "----"
        ptr = ""
    else:
        txt_val = f"{valor:.{dec}f}"
        ptr = f"<div class='hp-bar-p' style='left:{pct(valor, esc[0], esc[1]):.1f}%;background:{col_ptr}'></div>"
    banda = (f"<div class='hp-bar-n' style='left:{pct(normal[0], *esc):.1f}%;"
             f"width:{pct(normal[1], *esc) - pct(normal[0], *esc):.1f}%'></div>")
    marcas = "".join(
        f"<div class='hp-bar-l' style='left:{pct(v, *esc):.1f}%'></div>"
        f"<div class='hp-bar-lt' style='left:{pct(v, *esc):.1f}%'>{et}</div>" for v, et in lims)
    return (f"<div class='hp-card'>"
            f"<div class='hp-row'><span class='hp-tag'>{tag}</span><span class='hp-desc'>{desc}</span>{ind}</div>"
            f"<div class='hp-val'>{txt_val}<span class='hp-unit'>{unidad}</span></div>"
            f"<div class='hp-bar'>{banda}{marcas}{ptr}</div>"
            f"<div class='hp-scale'><span>{esc[0]:g}</span><span>{esc[1]:g} {unidad}</span></div>"
            f"{spark}<div class='hp-foot'>{pie}</div></div>")


def fmt_dur(seg):
    seg = int(seg)
    return f"{seg // 3600:02d}:{seg % 3600 // 60:02d}:{seg % 60:02d}"


# =====================================================================
# >>> NUEVO (Curvas P-F) ---------------------------------------------
# 4b. CURVAS P-F CON RANGOS OPERACIONALES (solo visualización)
#     P = falla potencial (detectable), F = falla funcional.
#     Usa los MISMOS límites de la barra lateral (P.lim); no cambia alarmas.
# =====================================================================
PF_ZONAS = {   # colores tenues (HP-HMI): el color fuerte queda solo para el punto en alarma
    "normal": {"txt": "Normal", "fondo": "#D2D2D2", "punto": C["pv"], "simb": "circle"},
    "vigil": {"txt": "Vigilancia", "fondo": "#E9E4C9", "punto": PRIO[3]["color"], "simb": "diamond"},
    "p": {"txt": "Falla potencial (P)", "fondo": "#F2D7BC", "punto": PRIO[2]["color"], "simb": "triangle-up"},
    "f": {"txt": "Falla funcional (F)", "fondo": "#EFC3C3", "punto": PRIO[1]["color"], "simb": "square"},
}
PF_K = 4.0     # forma de la curva (degradación lenta al inicio y acelerada cerca de F)


def pf_config(L):
    """Rangos operacionales por variable: base (sano), N (fin de rango normal), P y F."""
    rmin, rmax = max(0.0, L["r_l"] - 150), L["r_nhi"] + 80
    return [
        {"tag": "VI-101", "nombre": "Vibración (velocidad RMS)", "clave": "vib", "unidad": "mm/s", "dec": 2,
         "sube": True, "base": L["v_a"] / 2, "N": L["v_a"], "P": L["v_h"], "F": L["v_hh"],
         "esc": (0.0, max(L["v_esc"], L["v_hh"] * 1.2)),
         "etq": ("A|B (ISO 10816)", "H · zona C", "HH · zona D"),
         "modo": "Desbalance, desalineación, holgura o rodamientos"},
        {"tag": "II-101", "nombre": "Corriente RMS", "clave": "i", "unidad": "A", "dec": 2,
         "sube": True, "base": (L["i_nlo"] + L["i_nhi"]) / 2, "N": L["i_nhi"], "P": L["i_h"], "F": L["i_hh"],
         "esc": (0.0, max(L["i_esc"], L["i_hh"] * 1.2)),
         "etq": ("Normal máx", "H", "HH"),
         "modo": "Sobrecarga mecánica, rodamientos o atascamiento del molino"},
        {"tag": "SI-101", "nombre": "Velocidad del eje", "clave": "rpm", "unidad": "RPM", "dec": 0,
         "sube": False, "base": (L["r_nlo"] + L["r_nhi"]) / 2, "N": L["r_nlo"], "P": L["r_nlo"], "F": L["r_l"],
         "esc": (rmin, rmax),
         "etq": ("Normal mín", "Normal mín", "L"),
         "modo": "Deslizamiento por sobrecarga o falla de transmisión"},
    ]


def pf_zona(c, v):
    s = 1 if c["sube"] else -1          # +1: la falla sube el valor · −1: la falla lo baja
    if s * v >= s * c["F"]:
        return "f"
    if s * v > s * c["N"] and s * v >= s * c["P"]:
        return "p"
    if s * v > s * c["N"]:
        return "vigil"
    return "normal"


def pf_s(c, v):
    """Posición horizontal (tiempo relativo) de un valor sobre la curva P-F."""
    d = c["F"] - c["base"]
    frac = (v - c["base"]) / d if d else 0.0
    frac = max(0.0, min(frac, 1.15))
    return math.log(1 + frac * (math.exp(PF_K) - 1)) / PF_K


def pf_y(c, s):
    return c["base"] + (c["F"] - c["base"]) * (math.exp(PF_K * s) - 1) / (math.exp(PF_K) - 1)


def pf_tendencia(P, c, segundos=600):
    """Pendiente (unidad/min) de los últimos 10 min con el motor en marcha."""
    med = [m for m in P.datos(segundos) if m["marcha"] and (c["clave"] != "vib" or m["mpu_ok"])]
    if len(med) < 30 or med[-1]["t"] - med[0]["t"] < 60:
        return None
    t = np.array([m["t"] for m in med])
    v = np.array([m[c["clave"]] for m in med])
    return float(np.polyfit(t - t[0], v, 1)[0]) * 60.0


def pf_figura(c, valor, zona):
    ymin, ymax = c["esc"]
    xs = [i / 300 * 1.12 for i in range(301)]
    fig = go.Figure()
    # Bandas de rangos operacionales
    if c["sube"]:
        bandas = [(ymin, c["N"], "normal"), (c["N"], c["P"], "vigil"), (c["P"], c["F"], "p"), (c["F"], ymax, "f")]
    else:
        bandas = [(c["N"], ymax, "normal"), (c["P"], c["N"], "vigil"), (c["F"], c["P"], "p"), (ymin, c["F"], "f")]
    for y0, y1, z in bandas:
        y0, y1 = max(y0, ymin), min(y1, ymax)
        if y1 <= y0:
            continue
        fig.add_hrect(y0=y0, y1=y1, fillcolor=PF_ZONAS[z]["fondo"], line_width=0, layer="below")
        fig.add_annotation(x=1.01, xref="paper", y=(y0 + y1) / 2, text=PF_ZONAS[z]["txt"].replace(" (", "<br>("),
                           showarrow=False, xanchor="left", align="left", font={"size": 10, "color": C["tenue"]})
    # Límites (mismos de la barra lateral)
    for v, et in zip((c["N"], c["P"], c["F"]), c["etq"]):
        fig.add_hline(y=v, line={"color": C["lim"], "width": 1, "dash": "dash"},
                      annotation_text=f"{et} = {v:g}", annotation_position="top left",
                      annotation_font={"size": 9, "color": C["tenue"]})
    # Curva P-F
    fig.add_trace(go.Scatter(x=xs, y=[pf_y(c, x) for x in xs], mode="lines",
                             line={"color": C["tend"], "width": 2.2}, hoverinfo="skip"))
    sP, sF = pf_s(c, c["P"]), 1.0
    fig.add_trace(go.Scatter(x=[sP, sF], y=[c["P"], c["F"]], mode="markers+text", text=["P", "F"],
                             textposition="top left" if c["sube"] else "bottom left",
                             textfont={"size": 14, "color": C["texto"]},
                             marker={"size": 9, "color": C["panel"], "line": {"color": C["pv"], "width": 2}},
                             hoverinfo="skip"))
    for sx in (sP, sF):
        fig.add_vline(x=sx, line={"color": C["lim"], "width": 1, "dash": "dot"})
    # Intervalo P-F (flecha doble)
    y_int = ymin + 0.08 * (ymax - ymin) if c["sube"] else ymax - 0.08 * (ymax - ymin)
    fig.add_annotation(x=sF, y=y_int, ax=sP, ay=y_int, xref="x", yref="y", axref="x", ayref="y",
                       showarrow=True, arrowhead=2, arrowside="end+start", arrowwidth=1.3,
                       arrowcolor=C["pv"], text="")
    fig.add_annotation(x=(sP + sF) / 2, y=y_int, text="Intervalo P-F", showarrow=False,
                       yshift=10 if c["sube"] else -10, font={"size": 11, "color": C["texto"]})
    # Punto de operación actual
    if valor is not None:
        z = PF_ZONAS[zona]
        fig.add_trace(go.Scatter(x=[pf_s(c, valor)], y=[min(max(valor, ymin), ymax)], mode="markers+text",
                                 text=[f"{valor:.{c['dec']}f} {c['unidad']}"], textposition="middle right",
                                 textfont={"size": 12, "color": C["texto"]},
                                 marker={"size": 15, "color": z["punto"], "symbol": z["simb"],
                                         "line": {"color": "#1E1E1E", "width": 1.5}},
                                 hovertemplate="Actual: %{y:.2f}<extra></extra>"))
    fig.update_layout(height=340, showlegend=False, margin={"l": 50, "r": 78, "t": 10, "b": 35},
                      paper_bgcolor=C["panel"], plot_bgcolor=C["barra"],
                      font={"color": C["texto"], "size": 11}, uirevision=f"pf_{c['tag']}")
    fig.update_xaxes(range=[-0.04, 1.12], showticklabels=False, showgrid=False, zeroline=False,
                     showline=True, linecolor=C["borde"], title_text="Tiempo de operación / degradación →",
                     title_font={"size": 11, "color": C["tenue"]})
    fig.update_yaxes(range=[ymin, ymax], gridcolor="#DDDDDD", showline=True, linecolor=C["borde"],
                     zeroline=False, title_text=f"{c['tag']} [{c['unidad']}]", title_font={"size": 11})
    return fig


@st.fragment(run_every=REFRESCO_S)
def pantalla_pf():
    P = obtener_planta()
    s = P.estado()
    u = s["ult"]
    leyenda = "".join(f"<span class='hp-sw' style='background:{z['fondo']}'></span>{z['txt']}"
                      for z in PF_ZONAS.values())
    st.markdown(
        f"<div class='hp-panel'><h4>Curvas P-F · Rangos operacionales del M-101</h4>"
        f"<div class='hp-desc'>La curva muestra cómo avanza la degradación: <b>P</b> = falla potencial "
        f"(ya es detectable por monitoreo de condición) y <b>F</b> = falla funcional (el equipo deja de cumplir "
        f"su función). El punto marca la condición actual; el eje horizontal es relativo (conceptual). "
        f"Los rangos usan los mismos límites de alarma de la barra lateral.</div>"
        f"<div class='hp-desc' style='margin-top:6px'>{leyenda}</div></div>", unsafe_allow_html=True)

    cols = st.columns(3)
    for col, c in zip(cols, pf_config(P.lim)):
        valido = u is not None and u["marcha"] and (c["clave"] != "vib" or u["mpu_ok"])
        valor = u[c["clave"]] if valido else None
        zona = pf_zona(c, valor) if valor is not None else None
        col.markdown(f"<div class='hp-panel' style='padding-bottom:4px'><div class='hp-row'>"
                     f"<span class='hp-tag'>{c['tag']}</span><span class='hp-desc'>{c['nombre']}</span></div></div>",
                     unsafe_allow_html=True)
        col.plotly_chart(pf_figura(c, valor, zona), width="stretch", config={"displayModeBar": False},
                         key=f"pf_{c['tag']}")

        # ---- estado de la variable en la curva ----
        if valor is None:
            txt_zona = "<span class='hp-pfz' style='background:#EFEFEF'>SIN EVALUAR</span>"
            motivo = "Motor detenido" if u is None or not u["marcha"] else "Sensor sin respuesta"
            consumido = eta = "—"
        else:
            z = PF_ZONAS[zona]
            estilo = {"normal": f"background:{C['panel']};color:{C['texto']}",
                      "vigil": f"background:{z['punto']};color:#1E1E1E",
                      "p": f"background:{z['punto']};color:#1E1E1E",
                      "f": f"background:{z['punto']};color:#FFFFFF"}[zona]
            txt_zona = f"<span class='hp-pfz' style='{estilo}'>{z['txt'].upper()}</span>"
            motivo = c["modo"] if zona != "normal" else "Condición dentro del rango operacional"
            sg = 1 if c["sube"] else -1
            rango = sg * (c["F"] - c["P"])
            if zona in ("p", "f") and rango > 0:
                consumido = f"{min(100.0, max(0.0, sg * (valor - c['P']) / rango * 100)):.0f} %"
            else:
                consumido = "0 % (antes de P)"
            pend = pf_tendencia(P, c)
            restante = sg * (c["F"] - valor)
            if pend is None:
                eta = "Faltan datos (≥1 min en marcha)"
            elif restante <= 0:
                eta = "En falla funcional"
            elif sg * pend * 60 < 0.02 * abs(c["F"] - c["base"]):
                eta = f"Estable ({pend:+.3f} {c['unidad']}/min)"
            else:
                seg = restante / (sg * pend) * 60
                eta = ("> 24 h" if seg > 86400 else fmt_dur(seg)) + f" ({pend:+.3f} {c['unidad']}/min)"
        txt_valor = "—" if valor is None else f"{valor:.{c['dec']}f} {c['unidad']}"
        col.markdown(
            f"<div class='hp-panel'><table class='hp-t'>"
            f"<tr><td>Zona actual</td><td>{txt_zona}</td></tr>"
            f"<tr><td>Valor actual</td><td>{txt_valor}</td></tr>"
            f"<tr><td>Límite normal · P · F</td><td>{c['N']:g} · {c['P']:g} · {c['F']:g} {c['unidad']}</td></tr>"
            f"<tr><td>Intervalo P-F consumido</td><td>{consumido}</td></tr>"
            f"<tr><td>Tiempo estimado a F</td><td>{eta}</td></tr>"
            f"<tr><td>Diagnóstico</td><td>{motivo}</td></tr>"
            f"</table></div>", unsafe_allow_html=True)
# <<< FIN NUEVO (Curvas P-F) -------------------------------------------


# =====================================================================
# 5. PANTALLAS
# =====================================================================
@st.fragment(run_every=REFRESCO_S)
def cabecera():
    P = obtener_planta()
    s = P.estado()
    marcha = "EN MARCHA" if P.marcha else "DETENIDO"
    cuenta = ""
    for k, p in PRIO.items():
        n = sum(1 for a in s["alarmas"] if a["prio"] == k and a["activa"])
        est = f"background:{p['color']};color:{p['txt']};border-color:#333" if n else ""
        cuenta += f"<span class='hp-cnt' style='{est}' title='{p['nombre']}'>{p['forma']} {n}</span>"
    st.markdown(
        f"<div class='hp-head'>"
        f"<div><div class='hp-title'>{EQUIPO}</div><div class='hp-sub'>HMI de alto desempeño · ISA-101</div></div>"
        f"<div class='hp-kv'>Motor<br><b>{marcha}</b></div>"
        f"<div class='hp-kv'>Comunicación<br><b>{P.estado_com}</b></div>"
        f"<div class='hp-kv'>Alarmas activas<br>{cuenta}</div>"
        f"<div class='hp-clock'>{dt.datetime.now():%Y-%m-%d %H:%M:%S}</div></div>",
        unsafe_allow_html=True)

    pend = [a for a in s["alarmas"] if not a["reconocida"]]
    if pend:
        a = pend[0]
        p = PRIO[a["prio"]]
        val = "" if a.get("valor") is None else f" · {a['valor']} {a['unidad']}"
        estado = "ACTIVA" if a["activa"] else "NORMALIZADA"
        extra = f" &nbsp;(+{len(pend) - 1} sin reconocer)" if len(pend) > 1 else ""
        st.markdown(
            f"<div class='hp-banner' style='background:{p['color']};color:{p['txt']};border-color:#333'>"
            f"<b>{p['forma']} {a['prio']} · {a['tag']}</b> · {a['desc']}{val} · "
            f"{dt.datetime.fromtimestamp(a['t_on']):%H:%M:%S} · {estado} – NO RECONOCIDA{extra}"
            f" &nbsp;→ ir a la pantalla <b>Alarmas</b></div>", unsafe_allow_html=True)
    else:
        st.markdown(f"<div class='hp-banner' style='background:{C['panel']};color:{C['tenue']}'>"
                    f"Sin alarmas pendientes de reconocer</div>", unsafe_allow_html=True)


@st.fragment(run_every=REFRESCO_S)
def nivel_1():
    P = obtener_planta()
    s, L = P.estado(), P.lim
    u = s["ult"]
    med = P.datos(300)
    al = s["alarmas"]

    c1, c2, c3 = st.columns(3)
    c1.markdown(tarjeta(
        "II-101", "Corriente RMS", u and u["i"], "A", 2, (0, L["i_esc"]), (L["i_nlo"], L["i_nhi"]),
        [(L["i_h"], "H"), (L["i_hh"], "HH")], al,
        svg_tendencia(med, "i", 0, L["i_esc"], (L["i_nlo"], L["i_nhi"]), [L["i_h"], L["i_hh"]]),
        f"Normal {L['i_nlo']:g}–{L['i_nhi']:g} A · H {L['i_h']:g} · HH {L['i_hh']:g} · tendencia 5 min"),
        unsafe_allow_html=True)
    rmin, rmax = max(0.0, L["r_l"] - 150), L["r_nhi"] + 80   # escala operativa de velocidad
    c2.markdown(tarjeta(
        "SI-101", "Velocidad del eje", u and u["rpm"], "RPM", 0, (rmin, rmax), (L["r_nlo"], L["r_nhi"]),
        [(L["r_l"], "L")], al,
        svg_tendencia(med, "rpm", rmin, rmax, (L["r_nlo"], L["r_nhi"]), [L["r_l"]]),
        f"Normal {L['r_nlo']:g}–{L['r_nhi']:g} RPM · L {L['r_l']:g} · tendencia 5 min"),
        unsafe_allow_html=True)
    c3.markdown(tarjeta(
        "VI-101", "Vibración (velocidad RMS)", u and u["vib"], "mm/s", 2, (0, L["v_esc"]), (0, L["v_h"]),
        [(L["v_a"], "A|B"), (L["v_h"], "H"), (L["v_hh"], "HH")], al,
        svg_tendencia(med, "vib", 0, L["v_esc"], (0, L["v_h"]), [L["v_a"], L["v_h"], L["v_hh"]]),
        f"ISO 10816 · Zona {u['zona'] if u else '—'} · H {L['v_h']:g} (C) · HH {L['v_hh']:g} (D)",
        calidad=bool(u and u["mpu_ok"])),
        unsafe_allow_html=True)

    # ---- fila inferior: estado, condición y comunicación ----
    d1, d2, d3 = st.columns(3)
    t_m = fmt_dur(time.time() - P.t_marcha) if P.t_marcha else "--:--:--"
    d1.markdown(
        f"<div class='hp-panel'><h4>Estado del equipo</h4>"
        f"<div class='hp-big'>{'EN MARCHA' if P.marcha else 'DETENIDO'}</div>"
        f"<table class='hp-t'><tr><td>Tiempo en marcha actual</td><td>{t_m}</td></tr>"
        f"<tr><td>Arranques en la sesión</td><td>{P.arranques}</td></tr>"
        f"<tr><td>Pulsos por ventana (0.5 s)</td><td>{u['pulsos'] if u and u['pulsos'] is not None else '—'}</td></tr>"
        f"</table></div>", unsafe_allow_html=True)

    def condicion(prefijo):
        act = [a for a in al if a["tag"].startswith(prefijo) and a["activa"]]
        if not act:
            return "Normal"
        a = min(act, key=lambda x: x["prio"])
        return f"{PRIO[a['prio']]['forma']} {a['desc']}"

    d2.markdown(
        f"<div class='hp-panel'><h4>Condición por variable</h4><table class='hp-t'>"
        f"<tr><td>Corriente</td><td>{condicion('II-101')}</td></tr>"
        f"<tr><td>Velocidad</td><td>{condicion('SI-101')}</td></tr>"
        f"<tr><td>Vibración</td><td>{condicion('VI-101')}</td></tr>"
        f"<tr><td>Comunicación</td><td>{condicion('COM-101')}</td></tr>"
        f"</table></div>", unsafe_allow_html=True)

    edad = "—" if s["edad"] is None else f"{s['edad']:.1f} s"
    d3.markdown(
        f"<div class='hp-panel'><h4>Adquisición</h4><table class='hp-t'>"
        f"<tr><td>Fuente</td><td>{'Simulación' if P.fuente == 'sim' else 'USB ' + str(P.puerto)}</td></tr>"
        f"<tr><td>Frecuencia de datos</td><td>{s['hz']:.2f} muestras/s</td></tr>"
        f"<tr><td>Antigüedad del último dato</td><td>{edad}</td></tr>"
        f"<tr><td>Registro</td><td>carpeta <i>registros/</i></td></tr>"
        f"</table></div>", unsafe_allow_html=True)


@st.fragment(run_every=REFRESCO_S)
def nivel_2():
    P = obtener_planta()
    L = P.lim
    ventanas = {"2 min": 120, "10 min": 600, "30 min": 1800, "2 h": 7200}
    sel = st.radio("Ventana de tiempo", list(ventanas), horizontal=True, key="ventana", index=1)
    med = P.datos(ventanas[sel])
    if not med:
        st.info("Esperando datos del ESP32…")
        return
    df = pd.DataFrame(med)
    df["hora"] = pd.to_datetime(df["t"], unit="s", utc=True).dt.tz_convert(
        dt.datetime.now().astimezone().tzinfo).dt.tz_localize(None)

    fig = make_subplots(rows=3, cols=1, shared_xaxes=True, vertical_spacing=0.07,
                        subplot_titles=("II-101 · Corriente RMS [A]", "SI-101 · Velocidad [RPM]",
                                        "VI-101 · Vibración RMS [mm/s] (ISO 10816)"))
    config = [
        ("i", 1, (L["i_nlo"], L["i_nhi"]), [(L["i_h"], "H", 2), (L["i_hh"], "HH", 1)], True),
        ("rpm", 2, (L["r_nlo"], L["r_nhi"]), [(L["r_l"], "L", 2)], False),
        ("vib", 3, (0, L["v_h"]), [(L["v_h"], "H", 2), (L["v_hh"], "HH", 1)], True),
    ]
    for col, fila, normal, lims, alto in config:
        fig.add_hrect(y0=normal[0], y1=normal[1], fillcolor="#D2D2D2", line_width=0, layer="below",
                      row=fila, col=1)
        fig.add_trace(go.Scattergl(x=df["hora"], y=df[col], mode="lines",
                                   line={"color": C["tend"], "width": 1.6}, name=col,
                                   hovertemplate="%{x|%H:%M:%S}  %{y:.2f}<extra></extra>"), row=fila, col=1)
        for v, et, prio in lims:
            fig.add_hline(y=v, line={"color": C["lim"], "width": 1, "dash": "dash"}, row=fila, col=1,
                          annotation_text=et, annotation_position="right",
                          annotation_font={"size": 10, "color": C["tenue"]})
            fuera = df[df[col] >= v] if alto else df[(df[col] <= v) & (df["rpm"] > 100)]
            if not fuera.empty:
                fig.add_trace(go.Scattergl(x=fuera["hora"], y=fuera[col], mode="markers",
                                           marker={"color": PRIO[prio]["color"], "size": 5},
                                           hoverinfo="skip"), row=fila, col=1)
    fig.update_layout(height=680, showlegend=False, margin={"l": 50, "r": 40, "t": 30, "b": 30},
                      paper_bgcolor=C["panel"], plot_bgcolor=C["barra"], font={"color": C["texto"], "size": 12},
                      uirevision="tendencias")
    fig.update_annotations(font_size=12)
    fig.update_xaxes(gridcolor="#DDDDDD", showline=True, linecolor=C["borde"])
    fig.update_yaxes(gridcolor="#DDDDDD", showline=True, linecolor=C["borde"], zeroline=False)
    fig.update_yaxes(range=[0, max(L["i_esc"], df["i"].max() * 1.1)], row=1, col=1)
    fig.update_yaxes(range=[0, max(L["v_esc"], df["vib"].max() * 1.1)], row=3, col=1)
    st.plotly_chart(fig, width="stretch", config={"displayModeBar": False}, key="graf_tend")

    resumen = df[df["marcha"]] if df["marcha"].any() else df
    st.markdown(
        f"<div class='hp-panel'><h4>Estadística de la ventana ({sel}, solo con motor en marcha)</h4>"
        f"<table class='hp-t'><tr><td></td><td><b>Mín</b></td><td><b>Promedio</b></td><td><b>Máx</b></td></tr>"
        + "".join(f"<tr><td>{n}</td><td>{resumen[c].min():.2f}</td><td>{resumen[c].mean():.2f}</td>"
                  f"<td>{resumen[c].max():.2f}</td></tr>"
                  for n, c in (("Corriente [A]", "i"), ("Velocidad [RPM]", "rpm"), ("Vibración [mm/s]", "vib")))
        + "</table></div>", unsafe_allow_html=True)


@st.fragment(run_every=REFRESCO_S)
def nivel_3():
    P = obtener_planta()
    s = P.estado()
    u = s["ult"]
    c1, c2 = st.columns(2)
    edad = "—" if s["edad"] is None else f"{s['edad']:.1f} s"
    c1.markdown(
        f"<div class='hp-panel'><h4>Comunicación ESP32</h4><table class='hp-t'>"
        f"<tr><td>Estado</td><td>{P.estado_com}</td></tr>"
        f"<tr><td>Puerto / velocidad</td><td>{P.puerto or '—'} / {BAUDIOS} baudios</td></tr>"
        f"<tr><td>Líneas recibidas</td><td>{P.n_lineas}</td></tr>"
        f"<tr><td>Mediciones válidas</td><td>{P.n_muestras}</td></tr>"
        f"<tr><td>Líneas con error</td><td>{P.n_err}</td></tr>"
        f"<tr><td>Frecuencia de datos</td><td>{s['hz']:.2f} muestras/s</td></tr>"
        f"<tr><td>Antigüedad del último dato</td><td>{edad}</td></tr>"
        f"</table></div>", unsafe_allow_html=True)
    c2.markdown(
        f"<div class='hp-panel'><h4>Instrumentos</h4><table class='hp-t'>"
        f"<tr><td>II-101 Offset calibrado (GPIO34)</td><td>{'—' if P.offset is None else f'{P.offset:.3f} V'}</td></tr>"
        f"<tr><td>II-101 Corriente cruda</td><td>{'—' if not u else u['i']} A</td></tr>"
        f"<tr><td>SI-101 Pulsos / ventana (GPIO35)</td><td>{'—' if not u or u['pulsos'] is None else u['pulsos']}</td></tr>"
        f"<tr><td>SI-101 Velocidad cruda</td><td>{'—' if not u else u['rpm']} RPM</td></tr>"
        f"<tr><td>VI-101 MPU6050 WHO_AM_I</td><td>{P.mpu_id or '—'}</td></tr>"
        f"<tr><td>VI-101 Estado del sensor</td><td>{'OK' if u and u['mpu_ok'] else 'SIN SENSOR'}</td></tr>"
        f"<tr><td>VI-101 Zona reportada por el ESP32</td><td>{u['zona'] if u else '—'}</td></tr>"
        f"</table></div>", unsafe_allow_html=True)
    log = "<br>".join(f"{h}&nbsp;&nbsp;{html.escape(t)}" for h, t in list(P.msgs)[-25:]) or "(sin mensajes)"
    st.markdown(f"<div class='hp-panel'><h4>Mensajes del ESP32 y del HMI (últimos 25)</h4>"
                f"<div class='hp-log'>{log}</div></div>", unsafe_allow_html=True)


def descargas():
    """Fuera del refresco automático: descarga de registros en Excel / CSV."""
    archivos = sorted(CARPETA_REG.glob("*.csv"), reverse=True)
    st.markdown(f"<div class='hp-panel'><h4>Registros guardados</h4>"
                f"<div class='hp-desc'>Se guardan solos en <b>{CARPETA_REG}</b>, un archivo por día. "
                f"La descarga incluye los datos hasta el momento en que abriste esta pantalla.</div></div>",
                unsafe_allow_html=True)
    if not archivos:
        st.caption("Todavía no hay registros.")
        return
    sel = st.selectbox("Archivo", [a.name for a in archivos])
    ruta = CARPETA_REG / sel
    c1, c2 = st.columns(2)
    try:
        df = pd.read_csv(ruta)
        buf = io.BytesIO()
        df.to_excel(buf, index=False, sheet_name=sel[:31].replace(".csv", ""))
        c1.download_button("Descargar en Excel (.xlsx)", buf.getvalue(), sel.replace(".csv", ".xlsx"),
                           width="stretch")
    except Exception as e:  # noqa: BLE001
        c1.caption(f"No se pudo convertir a Excel: {e}")
    c2.download_button("Descargar CSV", ruta.read_bytes(), sel, width="stretch")


@st.fragment(run_every=REFRESCO_S)
def pantalla_alarmas():
    P = obtener_planta()
    s = P.estado()
    act = s["alarmas"]
    cab = st.columns([5, 1.4])
    cab[0].markdown(f"<div class='hp-panel'><h4>Alarmas activas y sin reconocer ({len(act)})</h4>"
                    f"<div class='hp-desc'>Orden: sin reconocer → activas → prioridad. "
                    f"■1 crítica · ▲2 alta · ◆3 media · ●4 diagnóstico de instrumento</div></div>",
                    unsafe_allow_html=True)
    if cab[1].button("Reconocer todas", width="stretch", disabled=not act):
        P.reconocer_todas()
        st.rerun(scope="fragment")
    if not act:
        st.markdown(f"<div class='hp-banner' style='background:{C['panel']};color:{C['tenue']}'>"
                    f"No hay alarmas.</div>", unsafe_allow_html=True)
    for a in act:
        p = PRIO[a["prio"]]
        estado = ("ACTIVA" if a["activa"] else "NORMALIZADA") + (" · reconocida" if a["reconocida"] else " · SIN RECONOCER")
        val = "" if a.get("valor") is None else f"{a['valor']} {a['unidad']}"
        lim = "" if a.get("limite") is None else f"(límite {a['limite']:g})"
        fondo = (f"background:{p['color']};color:{p['txt']}" if not a["reconocida"]
                 else f"background:{C['panel']};color:{C['texto']};border-left:8px solid {p['color']}")
        fila = st.columns([5, 1.4])
        fila[0].markdown(
            f"<div class='hp-banner' style='{fondo};border-color:#555'>"
            f"<b>{p['forma']} {a['prio']} {p['nombre']}</b> · {dt.datetime.fromtimestamp(a['t_on']):%H:%M:%S} · "
            f"<b>{a['tag']}</b> · {a['desc']} · {val} {lim} · {estado}</div>", unsafe_allow_html=True)
        if fila[1].button("Reconocer", key=f"ack_{a['tag']}", disabled=a["reconocida"],
                          width="stretch"):
            P.reconocer(a["tag"])
            st.rerun(scope="fragment")

    st.markdown("<div class='hp-panel'><h4>Historial de eventos (últimos 200)</h4></div>",
                unsafe_allow_html=True)
    ev = pd.DataFrame(list(P.eventos)[:200])
    if not ev.empty:
        st.dataframe(ev, hide_index=True, width="stretch", height=330)


# =====================================================================
# 6. BARRA LATERAL (fuente de datos y límites)
# =====================================================================
def aprender_linea_base():
    P = obtener_planta()
    med = [m for m in P.datos(120) if m["marcha"]]
    if len(med) < 20:
        st.session_state["aviso"] = "Se necesitan al menos ~10 s de datos con el motor en marcha."
        return
    i = sum(m["i"] for m in med) / len(med)
    r = sum(m["rpm"] for m in med) / len(med)
    nuevos = {"i_nlo": round(i * 0.70, 2), "i_nhi": round(i * 1.10, 2), "i_h": round(i * 1.20, 2),
              "i_hh": round(i * 1.35, 2), "i_esc": max(5.0, math.ceil(i * 2)),
              "r_nlo": round(r * 0.98), "r_nhi": round(r * 1.01), "r_l": round(r * 0.95)}
    for k, v in nuevos.items():
        st.session_state[f"lim_{k}"] = float(v)
    st.session_state["aviso"] = f"Línea base: {i:.2f} A y {r:.0f} RPM (últimos 2 min en marcha)."


def restablecer_limites():
    for k, v in LIMITES_DEF.items():
        st.session_state[f"lim_{k}"] = float(v)


def barra_lateral():
    P = obtener_planta()
    sb = st.sidebar
    sb.markdown("### Fuente de datos")
    fuente = sb.radio("Fuente", ["ESP32 por USB", "Simulación (sin ESP32)"],
                      index=1 if P.fuente == "sim" else 0, label_visibility="collapsed")
    puertos = [p.device for p in serial.tools.list_ports.comports()]
    opciones = sorted(set(puertos + [P.puerto or PUERTO_DEF]))
    puerto = sb.selectbox("Puerto", opciones, index=opciones.index(P.puerto or PUERTO_DEF),
                          disabled=fuente != "ESP32 por USB")
    if sb.button("Conectar / reiniciar", width="stretch"):
        P.iniciar("sim" if fuente.startswith("Sim") else "serial", None if fuente.startswith("Sim") else puerto)
        st.rerun()

    sb.markdown("### Límites de alarma")
    sb.button("Aprender línea base (2 min)", on_click=aprender_linea_base, width="stretch",
              help="Usa los últimos 2 min con el motor en marcha normal para fijar corriente y velocidad.")
    if "aviso" in st.session_state:
        sb.caption(st.session_state.pop("aviso"))
    grupos = {
        "Corriente II-101 [A]": [("i_nlo", "Normal mín"), ("i_nhi", "Normal máx"), ("i_h", "Alarma H"),
                                 ("i_hh", "Alarma HH"), ("i_esc", "Escala máx")],
        "Velocidad SI-101 [RPM]": [("r_nlo", "Normal mín"), ("r_nhi", "Normal máx"), ("r_l", "Alarma L")],
        "Vibración VI-101 [mm/s]": [("v_a", "Límite zona A/B"), ("v_h", "Alarma H (zona C)"),
                                    ("v_hh", "Alarma HH (zona D)"), ("v_esc", "Escala máx")],
    }
    for titulo, campos in grupos.items():
        with sb.expander(titulo):
            for k, et in campos:
                clave = f"lim_{k}"
                if clave not in st.session_state:
                    st.session_state[clave] = float(P.lim[k])
                P.lim[k] = st.number_input(et, key=clave, step=0.1 if not k.startswith("r_") else 10.0,
                                           format="%.2f" if not k.startswith("r_") else "%.0f")
    sb.button("Restablecer límites", on_click=restablecer_limites, width="stretch")
    sb.caption("Los límites de vibración siguen ISO 10816 (máquinas ≤15 kW). "
               "Corriente y velocidad: ajustar con la línea base del motor (no tiene placa).")


# =====================================================================
# 7. APLICACIÓN
# =====================================================================
st.set_page_config(page_title="HMI · M-101", layout="wide", initial_sidebar_state="collapsed")
st.markdown(CSS, unsafe_allow_html=True)
obtener_planta()
barra_lateral()
cabecera()
pantalla = st.radio("Pantalla", ["Nivel 1 · Vista general", "Nivel 2 · Tendencias",
                                 "Curvas P-F · Rangos operacionales",      # >>> NUEVO (Curvas P-F)
                                 "Nivel 3 · Diagnóstico", "Alarmas"],
                    horizontal=True, label_visibility="collapsed", key="pantalla")
if pantalla.startswith("Nivel 1"):
    nivel_1()
elif pantalla.startswith("Nivel 2"):
    nivel_2()
elif pantalla.startswith("Curvas P-F"):     # >>> NUEVO (Curvas P-F)
    pantalla_pf()
elif pantalla.startswith("Nivel 3"):
    nivel_3()
    descargas()
else:
    pantalla_alarmas()
