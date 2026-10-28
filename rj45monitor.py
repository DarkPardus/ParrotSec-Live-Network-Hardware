#!/usr/bin/env python3
"""
Parrot Sec. Linux Network World v1.0 - KDE Plasma masaüstü widget'ı (Python3 + PyQt6)

  * Cihazdaki tüm Ethernet ve Wi-Fi arayüzleri bir "switch" gövdesinde yan yana
  * Her port: RJ45 / Wi-Fi çizimi, cihaz (donanım) adı, MAC adresi, link durumu (UP/DOWN)
  * Yeşil LED = download, kırmızı LED = upload (paket geldikçe/gittikçe yanıp söner)
  * Her portta mini piksel çubuk ölçer, altta seçili port için piksel up/down grafiği
  * Seçili port: anlık hız, toplam download/upload, çalışma süresi, IP, bağlantı hızı/SSID

Kullanım:
  python3 rj45monitor.py            # normal başlat
  python3 rj45monitor.py --native   # Wayland'de XWayland yerine yerel Wayland kullan

Sol tık (port üstünde) = portu seç, sol tuşla sürükle = taşı, fare tekerleği = boyut,
sağ tık = menü (MAC kopyala, sanal arayüzler, boyut, çıkış...). Port üstünde durunca ayrıntı balonu çıkar.
"""
import os
import re
import sys
import json
import time
import math
import fcntl
import shutil
import socket
import struct
import random
import threading
import subprocess
from collections import deque

# Wayland'de pencere konumu/"en altta tut" ancak XWayland (xcb) ile güvenilir çalışır.
if "--native" not in sys.argv and os.environ.get("XDG_SESSION_TYPE") == "wayland":
    os.environ.setdefault("QT_QPA_PLATFORM", "xcb")

from PyQt6.QtCore import Qt, QTimer, QRectF, QPointF, QEvent
from PyQt6.QtGui import (QPainter, QColor, QFont, QLinearGradient, QPen, QBrush,
                         QAction, QActionGroup, QFontMetrics, QPolygonF, QPixmap, QIcon)
from PyQt6.QtWidgets import QApplication, QWidget, QMenu, QToolTip

CFG_PATH = os.path.expanduser("~/.config/rj45monitor.json")
AUTOSTART = os.path.expanduser("~/.config/autostart/rj45monitor.desktop")
APP_NAME = "Parrot Sec. Linux Network World"
APP_VERSION = "v1.0"
MIN_SCALE, MAX_SCALE = 0.5, 3.0

# ---- yerleşim sabitleri (tasarım pikseli, ölçek 1.0)
M = 14               # kart kenar boşluğu
HEADER_H = 40        # logo + başlık alanı
CHASSIS_Y = 54
PAD = 9              # switch gövdesi iç boşluğu
TILE_W, TILE_H = 130, 166
GAP = 8
MIN_COLS, MAX_COLS = 2, 4
DETAIL_H = 226       # seçili port ayrıntı + grafik bloğu
GRAPH_H = 74
HIST_LEN = 240       # 500 ms * 240 = 2 dk geçmiş

GREEN = QColor("#2cff5a")
RED = QColor("#ff2a2a")
ACCENT = QColor("#15E0ED")      # Parrot cyan: link UP / seçili port
PARROT = QColor("#15E0ED")

SANS = ["Arial", "Liberation Sans", "Arimo", "Helvetica", "Nimbus Sans", "DejaVu Sans"]
MONO = ["DejaVu Sans Mono", "Liberation Mono", "Noto Sans Mono", "monospace"]


# ---- Parrot logosu (parrotsec-logo.svg'den birebir; QtSvg gerekmez, 175x175 tasarım alanı)
_LOGO_CIRCLE = (87.5, 87.5, 87.5, "#15E0ED")
_LOGO_GRAD = (61.3272, 97.5719, 167.614, 91.5736)
_LOGO_STOPS = [
    (0, "#000000", 0.9),
    (0.0856376, "#000909", 0.8229),
    (0.2278, "#002023", 0.695),
    (0.4089, "#00464C", 0.532),
    (0.6218, "#007A85", 0.3404),
    (0.8587, "#00BCCD", 0.1271),
    (1, "#00E7FC", 0),
]
_LOGO_SHADOW = [
    (60.6, 31.7), (141.9, 19), (146.8, 23.2), (149.4, 25.6), (153.4, 30),
    (156.3, 33.5), (159.3, 37.5), (162, 41.6), (164.4, 45.8), (166.2, 49.3),
    (168.2, 53.7), (169.9, 58.1), (171.5, 62.8), (172.9, 68.6), (174, 73.9),
    (174.5, 78.4), (175, 83.7), (175, 89.9), (174.7, 94.3), (174.1, 100),
    (173.4, 104.4), (171.9, 110.6), (170, 116.7), (168.5, 120.8), (166.7, 124.7),
    (164.9, 128.3), (162.7, 132.2), (160.3, 136.1), (156.8, 141), (154.4, 143.9),
    (150.4, 148.3), (146.2, 152.4), (141.1, 156.7), (135.8, 160.4), (132.8, 162.4),
    (128.3, 164.9), (121.7, 168.2), (116.6, 162.4), (80.6, 122.1), (54.6, 61.3),
]
_LOGO_BIRD = [
    (80.6, 122.1), (116.6, 162.4), (104.6, 137.2), (115.8, 148.9), (79.3, 83),
    (95, 63.4), (153.7, 39.1), (95, 40.4), (133.2, 20.3), (60.6, 31.7),
    (54.6, 61.3), (25.3, 63.2), (20.2, 88.3), (34.9, 76.3),
]


def paint_logo(p, x, y, size):
    """Parrot logosunu (x, y) konumuna size x size piksel olarak çizer."""
    p.save()
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.translate(x, y)
    p.scale(size / 175.0, size / 175.0)
    p.setPen(Qt.PenStyle.NoPen)
    cx, cy, r, col = _LOGO_CIRCLE
    p.setBrush(QColor(col))
    p.drawEllipse(QPointF(cx, cy), r, r)
    gx1, gy1, gx2, gy2 = _LOGO_GRAD
    g = QLinearGradient(gx1, gy1, gx2, gy2)
    for off, hexcol, alpha in _LOGO_STOPS:
        c = QColor(hexcol)
        c.setAlphaF(alpha)
        g.setColorAt(off, c)
    p.setBrush(QBrush(g))
    p.drawPolygon(QPolygonF([QPointF(a, b) for a, b in _LOGO_SHADOW]))
    p.setBrush(QColor("#000000"))
    p.drawPolygon(QPolygonF([QPointF(a, b) for a, b in _LOGO_BIRD]))
    p.restore()


def logo_icon(size=128):
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    pp = QPainter(pm)
    paint_logo(pp, 0, 0, size)
    pp.end()
    return QIcon(pm)



# ----------------------------------------------------------------- sistem
def rd(path, default=""):
    try:
        with open(path) as f:
            return f.read().strip()
    except OSError:
        return default


def classify(name):
    """'eth' | 'wifi' | 'virt'"""
    base = f"/sys/class/net/{name}"
    if os.path.isdir(base + "/wireless") or os.path.isdir(base + "/phy80211"):
        return "wifi"
    if "/virtual/" in os.path.realpath(base):
        return "virt"
    try:
        typ = int(rd(base + "/type", "1"))
    except ValueError:
        typ = 1
    if typ == 1 and os.path.exists(base + "/device"):
        return "eth"
    return "virt"


def detect_ports(show_virtual=False):
    """[(ad, tür)] - önce Ethernet, sonra Wi-Fi, (isteğe bağlı) sanal."""
    try:
        names = [n for n in os.listdir("/sys/class/net") if n != "lo"]
    except OSError:
        return []
    out = []
    order = {"eth": 0, "wifi": 1, "virt": 2}
    for n in names:
        k = classify(n)
        if k == "virt" and not show_virtual:
            continue
        out.append((n, k))
    out.sort(key=lambda t: (order[t[1]], t[0]))
    return out


def default_iface(candidates):
    try:
        with open("/proc/net/route") as f:
            next(f)
            for line in f:
                p = line.split()
                if p[1] == "00000000" and p[0] in candidates:
                    return p[0]
    except Exception:
        pass
    return candidates[0] if candidates else ""


def read_mac(iface):
    m = rd(f"/sys/class/net/{iface}/address")
    return m.upper() if m else "—"


def read_stats(iface):
    """(rx_bytes, rx_packets, tx_bytes, tx_packets) veya None"""
    try:
        with open("/proc/net/dev") as f:
            for line in f:
                if ":" not in line:
                    continue
                name, data = line.split(":", 1)
                if name.strip() == iface:
                    v = data.split()
                    return int(v[0]), int(v[1]), int(v[8]), int(v[9])
    except Exception:
        pass
    return None


def read_uptime():
    try:
        with open("/proc/uptime") as f:
            return float(f.read().split()[0])
    except Exception:
        return 0.0


def read_link(iface):
    st = rd(f"/sys/class/net/{iface}/operstate")
    if st == "up":
        return True
    if st == "unknown":
        return rd(f"/sys/class/net/{iface}/carrier") == "1"
    return False


def read_speed(iface):
    try:
        v = int(rd(f"/sys/class/net/{iface}/speed", "-1"))
        return v if v > 0 else 0
    except ValueError:
        return 0


def read_ip(iface):
    s = None
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        r = fcntl.ioctl(s.fileno(), 0x8915,                       # SIOCGIFADDR
                        struct.pack("256s", iface[:15].encode()))
        return socket.inet_ntoa(r[20:24])
    except OSError:
        return ""
    finally:
        if s:
            s.close()


def is_monitor(iface):
    return rd(f"/sys/class/net/{iface}/type") == "803"       # radiotap = monitor modu


# ---- cihaz (donanım) adı
_PCI_PATHS = ["/usr/share/hwdata/pci.ids", "/usr/share/misc/pci.ids", "/usr/share/pci.ids"]
_pci_cache = {}


def pci_lookup(vid, did):
    """('Vendor', 'Device' | None) - pci.ids dosyasından."""
    key = (vid, did)
    if key in _pci_cache:
        return _pci_cache[key]
    v = vid[2:].lower() if vid.lower().startswith("0x") else vid.lower()
    d = did[2:].lower() if did.lower().startswith("0x") else did.lower()
    res = (None, None)
    for path in _PCI_PATHS:
        if not os.path.exists(path):
            continue
        vendor = None
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                for line in f:
                    if not line.strip() or line.startswith("#"):
                        continue
                    if line[0] != "\t":
                        if vendor is not None:
                            break                                 # vendor bölümü bitti
                        if line.startswith(v + "  "):
                            vendor = line[len(v) + 2:].strip()
                    elif vendor is not None and not line.startswith("\t\t"):
                        if line[1:].startswith(d + "  "):
                            res = (vendor, line[1 + len(d) + 2:].strip())
                            break
            if vendor and res == (None, None):
                res = (vendor, None)
        except OSError:
            continue
        if res != (None, None):
            break
    _pci_cache[key] = res
    return res


_VENDOR_NOISE = re.compile(
    r"\b(Corporation|Corp\.?|Inc\.?|Co\.?|Ltd\.?|Limited|Technologies|Technology|GmbH|plc)\b[,.]?"
    r"|\band subsidiaries\b", re.I)


def short_vendor(v):
    s = _VENDOR_NOISE.sub("", v or "")
    s = re.sub(r"\s{2,}", " ", s).strip(" ,.")
    return s or (v or "")


def device_info(iface):
    """(görünen_ad, sürücü)"""
    base = f"/sys/class/net/{iface}"
    kind = classify(iface)
    dev = os.path.realpath(base + "/device") if os.path.exists(base + "/device") else None
    drv = ""
    if dev and os.path.exists(dev + "/driver"):
        drv = os.path.basename(os.path.realpath(dev + "/driver"))
    if not drv:
        for line in rd(base + "/device/uevent").splitlines():
            if line.startswith("DRIVER="):
                drv = line.split("=", 1)[1]
    if kind == "virt" or not dev:
        devtype = ""
        for line in rd(base + "/uevent").splitlines():
            if line.startswith("DEVTYPE="):
                devtype = line.split("=", 1)[1]
        return ("Sanal arayüz" + (f" ({devtype})" if devtype else "")), drv

    # PCI
    vid, did = rd(dev + "/vendor"), rd(dev + "/device")
    if vid and did:
        vendor, name = pci_lookup(vid, did)
        if vendor and name:
            return f"{short_vendor(vendor)} {name}", drv
        if vendor:
            return f"{short_vendor(vendor)} {did}", drv
        ids = f"PCI {vid[2:]}:{did[2:]}"
        return (f"{drv} ({ids})" if drv else ids), drv
    # USB (üst dizinlerde 'product' ara)
    d = dev
    for _ in range(4):
        prod = rd(d + "/product")
        if prod:
            manu = rd(d + "/manufacturer")
            if manu and not prod.lower().startswith(manu.lower().split()[0]):
                prod = f"{manu} {prod}"
            return prod, drv
        d = os.path.dirname(d)
    return (drv or iface), drv


# ---- biçimlendirme
def fmt_rate(bps):
    kb = bps / 1024
    if kb >= 10240:
        return f"{kb / 1024:.2f} MB/s"
    return f"{kb:.1f} KB/s"


def fmt_bytes(b):
    units = ["B", "KB", "MB", "GB", "TB"]
    i = 0
    b = float(b)
    while b >= 1024 and i < len(units) - 1:
        b /= 1024
        i += 1
    return f"{b:.0f} {units[i]}" if i == 0 else f"{b:.2f} {units[i]}"


def fmt_uptime(sec):
    m = int(sec // 60)
    d, rem = divmod(m, 1440)
    h, mm = divmod(rem, 60)
    human = (f"{d} g " if d else "") + (f"{h} sa " if (h or d) else "") + f"{mm} dk"
    return f"{m} dk  ({human})"


def fmt_speed(mbps):
    if mbps >= 1000:
        return f"{mbps / 1000:g} Gb/s"
    return f"{mbps} Mb/s"


def signal_level(dbm):
    """0..3 çubuk; bilinmiyorsa 3."""
    if dbm is None:
        return 3
    if dbm >= -55:
        return 3
    if dbm >= -67:
        return 2
    if dbm >= -80:
        return 1
    return 0


# ---- yerleşim (GUI'den bağımsız, test edilebilir)
def compute_layout(n_ports):
    """(W, H, [slot_rect_tuple...], chassis_rect, detail_y)"""
    cols = min(MAX_COLS, max(MIN_COLS, n_ports))
    rows = max(1, math.ceil(n_ports / cols))
    cw = 2 * PAD + cols * TILE_W + (cols - 1) * GAP
    ch = 2 * PAD + rows * TILE_H + (rows - 1) * GAP
    W = cw + 2 * M
    slots = []
    for i in range(rows * cols):
        r, c = divmod(i, cols)
        slots.append((M + PAD + c * (TILE_W + GAP), CHASSIS_Y + PAD + r * (TILE_H + GAP),
                      TILE_W, TILE_H))
    detail_y = CHASSIS_Y + ch + 12
    H = detail_y + (DETAIL_H if n_ports else 34) + M
    return W, H, slots, (M, CHASSIS_Y, cw, ch), detail_y


# ---- Wi-Fi bilgisi (SSID / sinyal) - arka plan iş parçacığı, arayüzü bloklamaz
class WifiProbe(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self.targets = []
        self.info = {}
        self.iw = shutil.which("iw")
        self.iwgetid = shutil.which("iwgetid")

    def run(self):
        while True:
            for n in list(self.targets):
                self.info[n] = self.probe(n)
            time.sleep(6)

    def probe(self, n):
        ssid, sig = "", None
        try:
            if self.iw:
                out = subprocess.run([self.iw, "dev", n, "link"], capture_output=True,
                                     text=True, timeout=2).stdout
                m = re.search(r"SSID:\s*(.+)", out)
                if m:
                    ssid = m.group(1).strip()
                m = re.search(r"signal:\s*(-?\d+)", out)
                if m:
                    sig = int(m.group(1))
            elif self.iwgetid:
                ssid = subprocess.run([self.iwgetid, "-r", n], capture_output=True,
                                      text=True, timeout=2).stdout.strip()
        except Exception:
            pass
        return {"ssid": ssid, "signal": sig}


# ------------------------------------------------------------------ model
class Led:
    def __init__(self):
        self.pps = 0.0
        self.lit = False
        self._next = 0.0

    def tick(self, now):
        """Durum değiştiyse True döner."""
        old = self.lit
        if self.pps > 0.5:
            if now >= self._next:
                self.lit = not self.lit
                interval = max(0.04, 0.28 - self.pps / 3000.0)
                self._next = now + interval * random.uniform(0.7, 1.3)
        else:
            self.lit = False
        return old != self.lit


class Port:
    def __init__(self, name, kind):
        self.name, self.kind = name, kind
        self.mac = read_mac(name)
        self.dev_name, self.driver = device_info(name)
        self.rx_b = self.tx_b = 0
        self.rx_rate = self.tx_rate = 0.0
        self.ema_rx = self.ema_tx = 0.0
        self.prev, self.prev_t = None, 0.0
        self.led_rx, self.led_tx = Led(), Led()
        self.hist = deque(maxlen=HIST_LEN)
        self.link, self.speed, self.ip = False, 0, ""
        self.ssid, self.signal = "", None
        self.monitor = False

    @property
    def tag(self):
        if self.kind == "wifi":
            return "WI-FI · MON" if self.monitor else "WI-FI"
        return "ETHERNET" if self.kind == "eth" else "SANAL"

    def poll(self, now, wifi_info):
        self.mac = read_mac(self.name)          # macchanger ile değişirse hemen yansısın
        self.link = read_link(self.name)
        self.ip = read_ip(self.name)
        self.speed = read_speed(self.name) if (self.kind == "eth" and self.link) else 0
        if self.kind == "wifi":
            self.monitor = is_monitor(self.name)
            wi = wifi_info.get(self.name, {})
            self.ssid, self.signal = wi.get("ssid", ""), wi.get("signal")
        st = read_stats(self.name)
        if st:
            rxb, rxp, txb, txp = st
            if self.prev and now - self.prev_t > 0.05:
                dt = now - self.prev_t
                self.rx_rate = max(0, (rxb - self.prev[0]) / dt)
                self.tx_rate = max(0, (txb - self.prev[2]) / dt)
                self.led_rx.pps = max(0, (rxp - self.prev[1]) / dt)
                self.led_tx.pps = max(0, (txp - self.prev[3]) / dt)
                self.ema_rx = self.ema_rx * 0.6 + self.rx_rate * 0.4
                self.ema_tx = self.ema_tx * 0.6 + self.tx_rate * 0.4
                self.hist.append((self.rx_rate, self.tx_rate))
            self.rx_b, self.tx_b = rxb, txb
            self.prev, self.prev_t = st, now
        else:
            self.rx_rate = self.tx_rate = self.ema_rx = self.ema_tx = 0
            self.led_rx.pps = self.led_tx.pps = 0

    def tooltip(self):
        lines = [f"{self.name}  ({self.tag})", self.dev_name]
        if self.driver:
            lines.append(f"Sürücü: {self.driver}")
        lines.append(f"MAC: {self.mac}")
        if self.ip:
            lines.append(f"IP: {self.ip}")
        if self.kind == "wifi" and self.ssid:
            lines.append(f"SSID: {self.ssid}" + (f"  ({self.signal} dBm)" if self.signal else ""))
        if self.speed:
            lines.append(f"Hız: {fmt_speed(self.speed)}")
        lines.append("Link: " + ("UP" if self.link else "DOWN"))
        return "\n".join(lines)


# ------------------------------------------------------------------ çizim yardımcıları
def font_(px, bold=False, mono=False, spacing=0.0):
    f = QFont()
    f.setFamilies(MONO if mono else SANS)
    f.setStyleHint(QFont.StyleHint.Monospace if mono else QFont.StyleHint.SansSerif)
    f.setPixelSize(px)
    f.setBold(bold)
    if spacing:
        f.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing, spacing)
    return f


def wrap_lines(text, fm, width, max_lines):
    lines, cur = [], ""
    for w in text.split():
        t = (cur + " " + w).strip()
        if fm.horizontalAdvance(t) <= width:
            cur = t
        else:
            if cur:
                lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    if len(lines) > max_lines:
        tail = " ".join(lines[max_lines - 1:])
        lines = lines[:max_lines - 1] + [tail]
    return [fm.elidedText(l, Qt.TextElideMode.ElideRight, int(width)) for l in lines]


def meter_frac(bps):
    """Log ölçek: 1 KB/s ~ %6, 100 KB/s ~ %40, 10 MB/s ~ %80, 100 MB/s = %100."""
    if bps <= 0:
        return 0.0
    return min(1.0, math.log10(1 + bps / 1024) / math.log10(1 + 102400))


AL = Qt.AlignmentFlag


class RJ45Widget(QWidget):
    def __init__(self):
        super().__init__()
        self.cfg = self.load_cfg()
        self.show_virtual = bool(self.cfg.get("show_virtual", False))
        self.ports = []
        self.sel = self.cfg.get("iface", "")
        self.uptime = read_uptime()
        self.wifi = WifiProbe()
        self.W, self.H, self.slots, self.chassis, self.detail_y = compute_layout(0)

        self.s = min(MAX_SCALE, max(MIN_SCALE, float(self.cfg.get("scale", 1.0))))

        self.apply_flags(self.cfg.get("keep_below", True))
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setWindowTitle(f"{APP_NAME} {APP_VERSION}")
        self.setWindowIcon(logo_icon())

        self.rescan(initial=True)
        if "pos" in self.cfg:
            self.move(*self.cfg["pos"])
        self.wifi.start()

        self.poll_timer = QTimer(self, interval=500, timeout=self.poll)
        self.poll_timer.start()
        self.blink_timer = QTimer(self, interval=30, timeout=self.blink)
        self.blink_timer.start()
        self.scan_timer = QTimer(self, interval=3000, timeout=self.rescan)   # tak-çıkar algıla
        self.scan_timer.start()
        self.poll()

    # ---- ayarlar
    def load_cfg(self):
        try:
            with open(CFG_PATH) as f:
                return json.load(f)
        except Exception:
            return {}

    def save_cfg(self):
        self.cfg["pos"] = [self.x(), self.y()]
        self.cfg["iface"] = self.sel
        self.cfg["scale"] = round(self.s, 3)
        self.cfg["show_virtual"] = self.show_virtual
        os.makedirs(os.path.dirname(CFG_PATH), exist_ok=True)
        with open(CFG_PATH, "w") as f:
            json.dump(self.cfg, f)

    def apply_flags(self, keep_below):
        flags = (Qt.WindowType.FramelessWindowHint | Qt.WindowType.Tool)
        flags |= (Qt.WindowType.WindowStaysOnBottomHint if keep_below
                  else Qt.WindowType.WindowStaysOnTopHint)
        self.cfg["keep_below"] = keep_below
        was_visible = self.isVisible()
        self.setWindowFlags(flags)
        if was_visible:
            self.show()

    # ---- port listesi / yerleşim
    def rescan(self, initial=False):
        found = detect_ports(self.show_virtual)
        if not initial and [(p.name, p.kind) for p in self.ports] == found:
            return
        old = {p.name: p for p in self.ports}
        self.ports = [old.get(n) or Port(n, k) for n, k in found]
        names = [p.name for p in self.ports]
        if self.sel not in names:
            self.sel = default_iface(names)
        self.wifi.targets = [p.name for p in self.ports if p.kind == "wifi"]
        self.W, self.H, self.slots, self.chassis, self.detail_y = compute_layout(len(self.ports))
        self.setFixedSize(int(self.W * self.s), int(self.H * self.s))
        if not initial:
            self.poll()
            self.update()

    @property
    def cur(self):
        for p in self.ports:
            if p.name == self.sel:
                return p
        return None

    def select(self, name):
        if name != self.sel:
            self.sel = name
            self.save_cfg()
            self.update()

    def port_at(self, pos):
        """pos: widget pikseli -> Port | None"""
        x, y = pos.x() / self.s, pos.y() / self.s
        for i, (sx, sy, sw, sh) in enumerate(self.slots):
            if sx <= x <= sx + sw and sy <= y <= sy + sh:
                return self.ports[i] if i < len(self.ports) else None
        return None

    # ---- veri
    def poll(self):
        now = time.time()
        self.uptime = read_uptime()
        for p in self.ports:
            p.poll(now, self.wifi.info)
        self.update()

    def blink(self):
        now = time.time()
        changed = False
        for p in self.ports:
            a = p.led_rx.tick(now)
            b = p.led_tx.tick(now)
            changed = changed or a or b
        if changed:
            self.update()

    # ---- çizim
    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        p.scale(self.s, self.s)
        W, H = self.W, self.H

        card = QRectF(1, 1, W - 2, H - 2)
        g = QLinearGradient(0, 0, 0, H)
        g.setColorAt(0, QColor(29, 35, 48, 235))
        g.setColorAt(1, QColor(15, 18, 24, 235))
        p.setBrush(QBrush(g))
        p.setPen(QPen(QColor(255, 255, 255, 64), 1))
        p.drawRoundedRect(card, 18, 18)

        self.draw_header(p)
        self.draw_chassis(p)
        if self.cur:
            self.draw_detail(p, self.cur)
        else:
            p.setFont(font_(11))
            p.setPen(QColor("#8f9bb0"))
            p.drawText(QRectF(M, self.detail_y, W - 2 * M, 22), AL.AlignCenter,
                       "Ağ donanımı bulunamadı")
        p.end()

    # -- başlık + logo
    def draw_header(self, p):
        paint_logo(p, M, 8, 36)
        tx = M + 44
        right_w = 84
        avail = int(self.W - M - right_w - 6 - tx)
        f1 = font_(15, bold=True)
        p.setFont(f1)
        p.setPen(QColor("#e8eef7"))
        p.drawText(QRectF(tx, 7, avail, 20), AL.AlignVCenter | AL.AlignLeft,
                   QFontMetrics(f1).elidedText("Parrot Sec. Linux", Qt.TextElideMode.ElideRight, avail))
        f2 = font_(10, spacing=1.4)
        p.setFont(f2)
        p.setPen(QColor("#7d8aa0"))
        sub = "NETWORK WORLD"
        sw = QFontMetrics(f2).horizontalAdvance(sub)
        p.drawText(QRectF(tx, 27, avail, 14), AL.AlignVCenter | AL.AlignLeft, sub)
        p.setFont(font_(10, bold=True))
        p.setPen(PARROT)
        p.drawText(QRectF(tx + sw + 6, 27, max(0, avail - sw - 6), 14),
                   AL.AlignVCenter | AL.AlignLeft, APP_VERSION)
        n = len(self.ports)
        p.setFont(font_(10, bold=True, spacing=1.2))
        p.setPen(PARROT)
        p.drawText(QRectF(self.W - M - right_w, 10, right_w, 16), AL.AlignVCenter | AL.AlignRight,
                   f"{n} ARAYÜZ")
        up = sum(1 for q in self.ports if q.link)
        p.setFont(font_(10))
        p.setPen(QColor("#7d8aa0"))
        p.drawText(QRectF(self.W - M - right_w, 26, right_w, 14), AL.AlignVCenter | AL.AlignRight,
                   f"{up} link UP")

    # -- switch gövdesi
    def draw_chassis(self, p):
        x, y, w, h = self.chassis
        g = QLinearGradient(0, y, 0, y + h)
        g.setColorAt(0, QColor(42, 49, 62, 255))
        g.setColorAt(1, QColor(22, 26, 33, 255))
        p.setBrush(QBrush(g))
        p.setPen(QPen(QColor(255, 255, 255, 55), 1))
        p.drawRoundedRect(QRectF(x, y, w, h), 10, 10)
        # vidalar
        p.setPen(QPen(QColor(10, 12, 16, 200), 1))
        p.setBrush(QColor("#4a5365"))
        for sx, sy in ((x + 5, y + 5), (x + w - 5, y + 5), (x + 5, y + h - 5), (x + w - 5, y + h - 5)):
            p.drawEllipse(QPointF(sx, sy), 2.2, 2.2)
            p.drawLine(QPointF(sx - 1.3, sy + 0.9), QPointF(sx + 1.3, sy - 0.9))
        for i, (sx, sy, sw, sh) in enumerate(self.slots):
            r = QRectF(sx, sy, sw, sh)
            if i < len(self.ports):
                self.draw_tile(p, r, self.ports[i], self.ports[i].name == self.sel)
            else:
                self.draw_empty(p, r)

    def draw_empty(self, p, r):
        pen = QPen(QColor(255, 255, 255, 34), 1, Qt.PenStyle.DashLine)
        p.setPen(pen)
        p.setBrush(QColor(0, 0, 0, 50))
        p.drawRoundedRect(r, 7, 7)
        p.setFont(font_(10, spacing=1.2))
        p.setPen(QColor(255, 255, 255, 70))
        p.drawText(r, AL.AlignCenter, "BOŞ PORT")

    def draw_tile(self, p, r, pt, selected):
        x, y = r.x(), r.y()
        g = QLinearGradient(0, y, 0, y + r.height())
        g.setColorAt(0, QColor("#1d2430"))
        g.setColorAt(1, QColor("#10141b"))
        p.setBrush(QBrush(g))
        if selected:
            p.setPen(QPen(ACCENT, 1.6))
        else:
            p.setPen(QPen(QColor(255, 255, 255, 40), 1))
        p.drawRoundedRect(r, 7, 7)

        inner = r.width() - 16
        # ad
        f = font_(12, bold=True)
        p.setFont(f)
        p.setPen(QColor("#e8eef7"))
        p.drawText(QRectF(x + 8, y + 6, inner, 16), AL.AlignVCenter | AL.AlignLeft,
                   QFontMetrics(f).elidedText(pt.name, Qt.TextElideMode.ElideRight, int(inner)))
        # tür
        p.setFont(font_(10, spacing=1.2))
        p.setPen(ACCENT if selected else QColor("#7d8aa0"))
        p.drawText(QRectF(x + 8, y + 22, inner, 14), AL.AlignVCenter | AL.AlignLeft, pt.tag)

        # simge
        ix, iy = x + (r.width() - 64) / 2, y + 40
        if pt.kind == "wifi":
            self.draw_wifi_icon(p, ix, iy, pt)
        else:
            self.draw_mini_jack(p, ix, iy, pt)

        # cihaz adı (2 satır)
        f = font_(11)
        p.setFont(f)
        p.setPen(QColor("#b9c4d6"))
        fm = QFontMetrics(f)
        for i, line in enumerate(wrap_lines(pt.dev_name, fm, inner, 2)):
            p.drawText(QRectF(x + 8, y + 90 + i * 13, inner, 13), AL.AlignVCenter | AL.AlignLeft, line)

        # MAC (sığmazsa küçült)
        px = 11
        while px > 8:
            mf = font_(px, mono=True)
            if QFontMetrics(mf).horizontalAdvance(pt.mac) <= inner:
                break
            px -= 1
        p.setFont(mf)
        p.setPen(QColor("#a9b6cc"))
        p.drawText(QRectF(x + 8, y + 118, inner, 14), AL.AlignVCenter | AL.AlignLeft, pt.mac)

        # link durumu
        self.draw_link_row(p, x + 8, y + 134, inner, pt)

        # mini piksel ölçerler
        self.draw_meter(p, x + 8, y + 150, inner, pt.ema_rx, GREEN, "↓")
        self.draw_meter(p, x + 8, y + 158, inner, pt.ema_tx, RED, "↑")

    def draw_link_row(self, p, x, y, w, pt):
        col = ACCENT if pt.link else QColor("#6b7686")
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        p.drawEllipse(QPointF(x + 3.5, y + 6.5), 3.2, 3.2)
        f = font_(11, bold=True)
        p.setFont(f)
        p.setPen(col)
        label = "UP" if pt.link else "DOWN"
        lw = QFontMetrics(f).horizontalAdvance(label)
        p.drawText(QRectF(x + 11, y, lw + 4, 14), AL.AlignVCenter | AL.AlignLeft, label)
        extra = ""
        if pt.link:
            extra = pt.ssid if pt.kind == "wifi" else (fmt_speed(pt.speed) if pt.speed else "")
        if extra:
            f2 = font_(11)
            p.setFont(f2)
            p.setPen(QColor("#8f9bb0"))
            avail = int(w - 11 - lw - 10)
            p.drawText(QRectF(x + 11 + lw + 8, y, avail, 14), AL.AlignVCenter | AL.AlignLeft,
                       QFontMetrics(f2).elidedText(extra, Qt.TextElideMode.ElideRight, avail))

    def draw_meter(self, p, x, y, w, bps, color, arrow):
        p.setFont(font_(9, bold=True))
        p.setPen(color)
        p.drawText(QRectF(x, y - 3, 10, 10), AL.AlignCenter, arrow)
        seg, step = 4, 5
        x0 = x + 13
        n = int((w - 13) // step)
        lit = int(round(meter_frac(bps) * n))
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(n):
            if i < lit:
                c = QColor(color)
                c.setAlpha(255 if i >= lit - 2 else 190)
                p.setBrush(c)
            else:
                p.setBrush(QColor(255, 255, 255, 18))
            p.drawRect(QRectF(x0 + i * step, y, seg, 4))

    def draw_mini_jack(self, p, x, y, pt):
        JW, JH = 64, 46
        g = QLinearGradient(0, y, 0, y + JH)
        g.setColorAt(0.0, QColor("#d9dde3"))
        g.setColorAt(0.5, QColor("#9aa1ab"))
        g.setColorAt(1.0, QColor("#6f7681"))
        p.setBrush(QBrush(g))
        p.setPen(QPen(QColor("#3a3f47"), 1))
        p.drawRoundedRect(QRectF(x, y, JW, JH), 4, 4)
        ox, oy, ow, oh = x + 9, y + 8, 46, 24
        dark = QColor("#0b0d10")
        p.setBrush(dark)
        p.setPen(QPen(QColor("#22262c"), 1.2))
        p.drawRoundedRect(QRectF(ox, oy, ow, oh), 2, 2)
        p.drawRect(QRectF(ox + (ow - 16) / 2, oy - 5, 16, 7))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRect(QRectF(ox + (ow - 14) / 2, oy - 1, 14, 3))
        px0 = ox + (ow - 38) / 2
        for i in range(8):
            r = QRectF(px0 + i * 5, oy + oh - 3 - 14, 3, 14)
            pg = QLinearGradient(0, r.top(), 0, r.bottom())
            pg.setColorAt(0, QColor("#f7e08a"))
            pg.setColorAt(1, QColor("#b8891f"))
            p.setBrush(QBrush(pg))
            p.drawRoundedRect(r, 0.8, 0.8)
        if not pt.link:                                   # link yok: soluk
            p.setBrush(QColor(8, 10, 14, 125))
            p.drawRoundedRect(QRectF(x, y, JW, JH), 4, 4)
        self.draw_led_pair(p, x, y + JH - 9, JW, pt)

    def draw_wifi_icon(self, p, x, y, pt):
        JW, JH = 64, 46
        g = QLinearGradient(0, y, 0, y + JH)
        g.setColorAt(0, QColor("#26344a"))
        g.setColorAt(1, QColor("#141b28"))
        p.setBrush(QBrush(g))
        p.setPen(QPen(QColor("#3a4a62"), 1))
        p.drawRoundedRect(QRectF(x, y, JW, JH), 6, 6)
        cx, cy = x + JW / 2, y + 34
        lvl = max(1, signal_level(pt.signal)) if pt.link else 0
        for i, rad in enumerate((8, 15, 22), start=1):
            on = i <= lvl
            pen = QPen(ACCENT if on else QColor("#34415a"), 3)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawArc(QRectF(cx - rad, cy - rad, 2 * rad, 2 * rad), 45 * 16, 90 * 16)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(ACCENT if pt.link else QColor("#34415a"))
        p.drawEllipse(QPointF(cx, cy), 2.8, 2.8)
        self.draw_led_pair(p, x, y + JH - 9, JW, pt)

    def draw_led_pair(self, p, x, y, jw, pt):
        LW, LH = 11, 5
        self.draw_led(p, QRectF(x + 5, y, LW, LH), GREEN, pt.led_rx.lit, 0.45)
        self.draw_led(p, QRectF(x + jw - 5 - LW, y, LW, LH), RED, pt.led_tx.lit, 0.45)

    def draw_led(self, p, r, color, lit, k=1.0):
        fr = 3 * k
        p.setPen(QPen(QColor("#1a1d22"), 1))
        p.setBrush(QColor("#0b0d10"))
        p.drawRoundedRect(r.adjusted(-fr, -fr, fr, fr), 3 * k + 1, 3 * k + 1)
        if lit:
            p.setPen(Qt.PenStyle.NoPen)
            for i, a in enumerate((18, 30, 46, 64)):
                glow = QColor(color)
                glow.setAlpha(a)
                p.setBrush(glow)
                m = (9 - i * 2) * k
                p.drawRoundedRect(r.adjusted(-m, -m, m, m), 3 + m / 2, 3 + m / 2)
            lg = QLinearGradient(0, r.top(), 0, r.bottom())
            lg.setColorAt(0, color.lighter(150))
            lg.setColorAt(1, color)
            p.setBrush(QBrush(lg))
        else:
            p.setBrush(color.darker(500))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRoundedRect(r, 2, 2)
        p.setBrush(QColor(255, 255, 255, 120 if lit else 28))
        p.drawRoundedRect(QRectF(r.left() + 1.5, r.top() + 0.8, r.width() - 3, max(1.2, r.height() * 0.3)), 1, 1)

    # -- seçili port: ayrıntı + piksel grafik
    def draw_detail(self, p, pt):
        W = self.W
        y0 = self.detail_y
        # başlık satırı
        p.setFont(font_(16, bold=True))
        p.setPen(QColor("#e8eef7"))
        p.drawText(QRectF(M, y0, 140, 24), AL.AlignVCenter | AL.AlignLeft,
                   QFontMetrics(font_(16, bold=True)).elidedText(pt.name, Qt.TextElideMode.ElideRight, 140))
        bits = []
        if pt.kind == "wifi" and pt.link and pt.ssid:
            bits.append(pt.ssid)
        elif pt.speed:
            bits.append(fmt_speed(pt.speed))
        if pt.ip:
            bits.append(pt.ip)
        if not bits:
            bits.append("link UP" if pt.link else "bağlı değil")
        f = font_(11)
        p.setFont(f)
        p.setPen(QColor("#8f9bb0"))
        aw = W - 2 * M - 146
        p.drawText(QRectF(M + 146, y0, aw, 24), AL.AlignVCenter | AL.AlignRight,
                   QFontMetrics(f).elidedText("  ·  ".join(bits), Qt.TextElideMode.ElideLeft, int(aw)))

        # anlık hızlar
        half = (W - 2 * M) / 2 - 2
        p.setFont(font_(15, bold=True, mono=True))
        p.setPen(GREEN)
        p.drawText(QRectF(M, y0 + 26, half, 26), AL.AlignVCenter | AL.AlignLeft, "↓ " + fmt_rate(pt.rx_rate))
        p.setPen(QColor("#ff5a5a"))
        p.drawText(QRectF(W - M - half, y0 + 26, half, 26), AL.AlignVCenter | AL.AlignRight,
                   "↑ " + fmt_rate(pt.tx_rate))

        p.setPen(QPen(QColor(255, 255, 255, 48), 1))
        p.drawLine(M, int(y0 + 56), W - M, int(y0 + 56))

        rows = [("Toplam Download", fmt_bytes(pt.rx_b)),
                ("Toplam Upload", fmt_bytes(pt.tx_b)),
                ("Çalışma süresi", fmt_uptime(self.uptime))]
        y = y0 + 62
        fv = font_(11, bold=True)
        for label, val in rows:
            p.setFont(font_(11))
            p.setPen(QColor("#8f9bb0"))
            p.drawText(QRectF(M, y, 110, 20), AL.AlignVCenter | AL.AlignLeft, label)
            p.setFont(fv)
            p.setPen(QColor("#e8eef7"))
            vw = W - 2 * M - 112
            p.drawText(QRectF(M + 112, y, vw, 20), AL.AlignVCenter | AL.AlignRight,
                       QFontMetrics(fv).elidedText(val, Qt.TextElideMode.ElideRight, int(vw)))
            y += 22

        self.draw_graph(p, pt, y0 + 136)

    def draw_graph(self, p, pt, y):
        W = self.W
        gx, gw = M, W - 2 * M
        inner_x, inner_w = gx + 4, gw - 8
        nb = int(inner_w // 5)
        samples = list(pt.hist)[-nb:]
        pk = max([10240.0] + [max(a, b) for a, b in samples])

        # etiket satırı
        p.setFont(font_(10, bold=True))
        p.setPen(GREEN)
        p.drawText(QRectF(gx, y, 60, 14), AL.AlignVCenter | AL.AlignLeft, "▼ DOWN")
        p.setPen(QColor("#ff5a5a"))
        p.drawText(QRectF(gx + gw - 60, y, 60, 14), AL.AlignVCenter | AL.AlignRight, "UP ▲")
        p.setFont(font_(10))
        p.setPen(QColor("#7d8aa0"))
        p.drawText(QRectF(gx + 60, y, gw - 120, 14), AL.AlignCenter,
                   f"son {int(nb * 0.5)} sn  ·  tepe {fmt_rate(pk)}")

        gy = y + 16
        p.setPen(QPen(QColor(255, 255, 255, 30), 1))
        p.setBrush(QColor(6, 8, 12, 170))
        p.drawRoundedRect(QRectF(gx, gy, gw, GRAPH_H), 6, 6)

        inner_h = GRAPH_H - 8
        half = (inner_h - 2) // 2
        nblk = int(half // 4)                       # 3 px blok + 1 px boşluk
        mid = gy + 4 + half                         # üst yarının alt kenarı
        p.setPen(Qt.PenStyle.NoPen)
        # soluk piksel matris zemini
        p.setBrush(QColor(255, 255, 255, 9))
        for i in range(nb):
            cx = inner_x + i * 5
            p.drawRect(QRectF(cx, mid - nblk * 4 + 1, 4, nblk * 4 - 1))
            p.drawRect(QRectF(cx, mid + 2, 4, nblk * 4 - 1))
        # orta çizgi
        p.setBrush(QColor(255, 255, 255, 40))
        p.drawRect(QRectF(inner_x, mid + 0.5, inner_w, 1))

        off = nb - len(samples)                      # yeni veri sağda
        for i, (rx, tx) in enumerate(samples):
            cx = inner_x + (off + i) * 5
            for rate, col, up in ((rx, GREEN, True), (tx, RED, False)):
                if rate < 256:
                    n = 0
                else:
                    n = max(1, min(nblk, int(math.ceil(rate / pk * nblk))))
                for b in range(n):
                    c = QColor(col)
                    c.setAlpha(255 if b == n - 1 else 170)
                    p.setBrush(c)
                    if up:      # download: orta çizgiden yukarı
                        p.drawRect(QRectF(cx, mid - (b + 1) * 4 + 1, 4, 3))
                    else:       # upload: orta çizgiden aşağı
                        p.drawRect(QRectF(cx, mid + 2 + b * 4 + 1, 4, 3))

    # ---- fare: seç / sürükle / menü / balon
    def event(self, e):
        if e.type() == QEvent.Type.ToolTip:
            pt = self.port_at(e.pos())
            if pt:
                QToolTip.showText(e.globalPos(), pt.tooltip(), self)
            else:
                QToolTip.hideText()
            return True
        return super().event(e)

    def mousePressEvent(self, e):
        pt = self.port_at(e.position().toPoint())
        if e.button() == Qt.MouseButton.LeftButton:
            if pt:
                self.select(pt.name)
                return
            wh = self.windowHandle()
            if wh:
                wh.startSystemMove()
        elif e.button() == Qt.MouseButton.RightButton:
            if pt:
                self.select(pt.name)
            self.show_menu(e.globalPosition().toPoint())

    def wheelEvent(self, e):
        step = 0.05 if e.angleDelta().y() > 0 else -0.05
        self.set_scale(self.s + step)

    def set_scale(self, v):
        v = round(min(MAX_SCALE, max(MIN_SCALE, v)), 3)
        if abs(v - self.s) < 1e-6:
            return
        self.s = v
        self.setFixedSize(int(self.W * v), int(self.H * v))
        self.update()
        self.save_cfg()

    def mouseReleaseEvent(self, e):
        self.save_cfg()

    def moveEvent(self, e):
        super().moveEvent(e)
        if self.isVisible():
            QTimer.singleShot(400, self.save_cfg)

    def show_menu(self, pos):
        m = QMenu(self)
        cur = self.cur
        if cur:
            m.addAction(f"MAC adresini kopyala  ({cur.mac})",
                        lambda *_: QApplication.clipboard().setText(cur.mac))
            if cur.ip:
                m.addAction(f"IP adresini kopyala  ({cur.ip})",
                            lambda *_: QApplication.clipboard().setText(cur.ip))
            m.addSeparator()

        virt = QAction("Sanal arayüzleri de göster (docker, tun, bridge...)", m, checkable=True)
        virt.setChecked(self.show_virtual)
        virt.triggered.connect(self.toggle_virtual)
        m.addAction(virt)

        szm = m.addMenu("Boyut (fare tekerleği de çalışır)")
        szg = QActionGroup(szm)
        for pct in (50, 75, 100, 125, 150, 200, 250, 300):
            a = QAction(f"%{pct}", szm, checkable=True)
            a.setChecked(abs(self.s * 100 - pct) < 2.5)
            a.triggered.connect(lambda _, pct=pct: self.set_scale(pct / 100))
            szg.addAction(a)
            szm.addAction(a)

        below = QAction("Masaüstünde (en altta) tut", m, checkable=True)
        below.setChecked(self.cfg.get("keep_below", True))
        below.triggered.connect(lambda c: (self.apply_flags(c), self.save_cfg()))
        m.addAction(below)

        auto = QAction("Oturum açılışında başlat", m, checkable=True)
        auto.setChecked(os.path.exists(AUTOSTART))
        auto.triggered.connect(self.toggle_autostart)
        m.addAction(auto)

        m.addSeparator()
        m.addAction("Çıkış", QApplication.quit)
        m.exec(pos)

    def toggle_virtual(self, on):
        self.show_virtual = bool(on)
        self.rescan()
        self.save_cfg()

    def toggle_autostart(self, on):
        if on:
            os.makedirs(os.path.dirname(AUTOSTART), exist_ok=True)
            script = os.path.abspath(__file__)
            with open(AUTOSTART, "w") as f:
                f.write("[Desktop Entry]\nType=Application\n"
                        f"Name={APP_NAME} {APP_VERSION}\n"
                        f"Exec=python3 \"{script}\"\nX-KDE-autostart-after=panel\n")
        else:
            try:
                os.remove(AUTOSTART)
            except OSError:
                pass


def main():
    app = QApplication([a for a in sys.argv if a != "--native"])
    app.setApplicationName("rj45monitor")
    app.setWindowIcon(logo_icon())
    w = RJ45Widget()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
