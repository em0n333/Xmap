#!/usr/bin/env python3

import json, math, os, re, sys, time
from PySide6.QtCore import Qt, QPointF, QRectF, QSizeF, QMarginsF, QLineF, QPoint, QSize, Signal, QMimeData, QSettings
from PySide6.QtGui import (QPainter, QPainterPath, QColor, QPen, QFont, QTextLayout, QTextOption, QImage,
                           QPalette, QPdfWriter, QPageSize, QActionGroup)
from PySide6.QtSvg import QSvgGenerator
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QTextEdit, QFrame, QVBoxLayout,
                               QAbstractButton, QMenu, QFileDialog, QMessageBox, QHBoxLayout, QTabBar,
                               QLineEdit, QLabel, QDialog, QDialogButtonBox, QFontComboBox, QColorDialog)

FAMILIES = ["Inter", "Helvetica", "Arial", "Liberation Sans", "Sans Serif"]
DEFAULT_FAMILIES = list(FAMILIES)     # what "Default" in the font picker goes back to
FONT_PX = (40, 31, 31, 29)            # root, main, sub, deeper (same sizes as the GTK build, in px)
BOLD = (True, True, False, False)
PADS = ((38, 24), (26, 20), (20, 10), (14, 10))
MAXW = 800
MINFW = 30          # narrowest text width a topic can be dragged to
GRIP = 7            # grab-handle width on a selected topic (screen px)
MIME = "application/x-xmap-nodes"  # clipboard format for copied topics
SHAPES = ["Square", "Rounded", "Pill"]
LINES = ["Curved", "Straight", "Rounded", "Elbow"]
COLORS = [("Red", "#ed283f"), ("Green", "#00b87d"), ("Orange", "#ffa31a"), ("Off-white", "#e6e6e6")]
ICON_SIZES = (40, 36, 34, 32)
ICON_GAP = 12
NOTE_SIZES = (28, 24, 22, 20)  # note badge size per depth
NOTE_GAP = 10

DEFAULT_LINE = "#ffffff"  # colour of the mindmap lines until the user picks another
WHITE, BLACK = QColor(255, 255, 255), QColor(0, 0, 0)
NOPEN, NOBRUSH = Qt.PenStyle.NoPen, Qt.BrushStyle.NoBrush


def use_family(fam):  # put fam first in the font fallback list (None = the built-in default list)
    FAMILIES[:] = [fam] + [f for f in DEFAULT_FAMILIES if f != fam] if fam else DEFAULT_FAMILIES


def hex_rgb(h):
    return tuple(int(h[i:i + 2], 16) / 255 for i in (1, 3, 5))


def qc(rgb):
    return QColor.fromRgbF(*rgb)


def text_on(h):  # black or white text, whichever contrasts more with background h
    def lin(v):
        return v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4
    r, g, b = (lin(c) for c in hex_rgb(h))
    L = 0.2126 * r + 0.7152 * g + 0.0722 * b
    return (0, 0, 0) if (L + 0.05) / 0.05 > 1.05 / (L + 0.05) else (1, 1, 1)


def tint(h, a=70):  # see-through version of colour h, like the search highlight
    c = QColor(h)
    c.setAlpha(a)
    return c


def pen(color, w, dash=None, round_=False):
    p = QPen(color, w)
    cap = Qt.PenCapStyle.RoundCap if round_ else Qt.PenCapStyle.FlatCap
    join = Qt.PenJoinStyle.RoundJoin if round_ else Qt.PenJoinStyle.MiterJoin
    p.setCapStyle(cap)
    p.setJoinStyle(join)
    if dash:
        p.setDashPattern([d / w for d in dash])  # Qt dash lengths are in units of pen width
    return p


def draw_icon(p, kind, x, y, s):  # round check / error badge in a box of size s
    cx, cy = x + s / 2, y + s / 2
    p.setPen(pen(WHITE, 1.5))
    p.setBrush(QColor(0, 184, 125) if kind == "check" else QColor(237, 84, 84))
    p.drawEllipse(QPointF(cx, cy), s / 2 - 1, s / 2 - 1)
    p.setPen(pen(WHITE, s * 0.14, round_=True))
    p.setBrush(NOBRUSH)
    if kind == "check":
        p.drawPolyline([QPointF(x + s * .27, y + s * .52), QPointF(x + s * .44, y + s * .69),
                        QPointF(x + s * .74, y + s * .33)])
    else:
        p.drawLine(QLineF(x + s * .33, y + s * .33, x + s * .67, y + s * .67))
        p.drawLine(QLineF(x + s * .67, y + s * .33, x + s * .33, y + s * .67))


def draw_note(p, x, y, s, color):  # note badge: three rounded lines, the last one shorter
    p.setPen(pen(color, s * 0.13, round_=True))
    p.setBrush(NOBRUSH)
    for i, end in enumerate((1.0, 1.0, 0.6)):
        yy = y + s * (0.2 + 0.3 * i)
        p.drawLine(QLineF(x + s * .08, yy, x + s * (.08 + .84 * end), yy))


def hgap(depth):  # gap between a node and its children
    return 90 if depth == 0 else 38 if depth == 1 else 28


def rect_path(x, y, w, h, r=0):
    path = QPainterPath()
    if r <= 0:
        path.addRect(QRectF(x, y, w, h))
    else:
        r = min(r, w / 2, h / 2)
        path.addRoundedRect(QRectF(x, y, w, h), r, r)
    return path


def elbow_path(x0, y0, xm, x1, y1, r):
    """Xmind-style elbow: horizontal from (x0,y0), a rounded corner at x=xm, vertical, a second rounded
    corner, then horizontal into (x1,y1). The corner radius shrinks when there is not enough room."""
    path = QPainterPath()
    path.moveTo(x0, y0)
    dy = y1 - y0
    if abs(dy) < 1:
        path.lineTo(x1, y1)
        return path
    sx = 1 if x1 > x0 else -1
    sy = 1 if dy > 0 else -1
    r = min(r, abs(dy) / 2, abs(xm - x0), abs(x1 - xm))
    k = r * 0.4477  # control-point distance that makes a true circular quarter arc
    path.lineTo(xm - sx * r, y0)
    path.cubicTo(xm - sx * k, y0, xm, y0 + sy * k, xm, y0 + sy * r)
    path.lineTo(xm, y1 - sy * r)
    path.cubicTo(xm, y1 - sy * k, xm + sx * k, y1, xm + sx * r, y1)
    path.lineTo(x1, y1)
    return path


class Node:
    def __init__(self, text="New topic", side="R"):
        self.text, self.side, self.folded = text, side, False
        self.children, self.parent = [], None
        self.x = self.y = self.w = self.h = self.tw = self.th = self.sh = 0
        self.depth, self.eff = 0, "R"
        self.color, self.icon, self.note = None, None, ""
        self.fw = None  # custom text width set by dragging the side handle (None = automatic)

    @property
    def iw(self):  # extra width taken by the icon
        return ICON_SIZES[min(self.depth, 3)] + ICON_GAP if self.icon else 0

    @property
    def nw(self):  # extra width taken by the note badge
        return NOTE_SIZES[min(self.depth, 3)] + NOTE_GAP if self.note else 0

    def add(self, c, i=None):
        c.parent = self
        self.children.insert(len(self.children) if i is None else i, c)

    @property
    def cx(self): return self.x + self.w / 2

    @property
    def cy(self): return self.y + self.h / 2

    @property
    def ay(self):  # y where lines attach: box middle, or underline for sub topics
        return self.cy if self.depth <= 1 else self.y + self.h

    def under(self, other):
        n = self
        while n:
            if n is other:
                return True
            n = n.parent
        return False

    def to_dict(self):
        d = {"text": self.text, "side": self.side, "folded": self.folded}
        if self.color:
            d["color"] = self.color
        if self.icon:
            d["icon"] = self.icon
        if self.fw:
            d["fw"] = self.fw
        if self.note:
            d["note"] = self.note
        d["children"] = [c.to_dict() for c in self.children]
        return d

    @staticmethod
    def from_dict(d):
        n = Node(d.get("text", ""), d.get("side", "R"))
        n.folded = d.get("folded", False)
        n.color, n.icon = d.get("color"), d.get("icon")
        n.note = d.get("note") if isinstance(d.get("note"), str) else ""
        fw = d.get("fw")
        n.fw = int(fw) if isinstance(fw, (int, float)) and fw > 0 else None
        for c in d.get("children", []):
            n.add(Node.from_dict(c))
        return n


BULLET = re.compile(r"^(?:[-*+\u2022\u2013\u25E6\u25AA]|\d+[.)])\s+")  # "- ", "* ", "+ ", "• ", "1. ", "1) "


def parse_outline(txt):
    """Turn bulleted / indented plain text into [{"text":..., "children":[...]}].
    Returns None when the text has no bullets and no indentation (so it stays one topic)."""
    lines = [l.rstrip() for l in txt.replace("\r\n", "\n").replace("\r", "\n").split("\n") if l.strip()]
    if not lines:
        return None
    rows, bullets, indented = [], False, False
    for l in lines:
        lead = len(l) - len(l.lstrip(" \t"))
        ind = len(l[:lead].replace("\t", "    "))
        body = l.lstrip(" \t")
        m = BULLET.match(body)
        if m:
            bullets = True
            body = body[m.end():]
        indented = indented or ind > 0
        rows.append((ind, body.strip()))
    if not (bullets or (indented and len(rows) > 1)):
        return None
    top, stack = [], []  # stack of (indent, node dict)
    for ind, body in rows:
        if not body:
            continue
        while stack and stack[-1][0] >= ind:
            stack.pop()
        d = {"text": body, "children": []}
        (stack[-1][1]["children"] if stack else top).append(d)
        stack.append((ind, d))
    return top or None


def build(spec, i=0):
    text, kids = spec
    n = Node(text, "R" if i % 2 == 0 else "L")
    for k in kids:
        n.add(build(k))
    return n


def default_tree():
    t = ("My Mind Map", [
        ("Information Gathering", [
            ("Internet Scanning", [("Censys", [("https://censys.io/", [])]),
                                   ("Shodan", [("http://shodan.io/", [])])]),
            ("Ports Services", [("nmap", [("https://nmap.org/", [])]),
                                ("masscan", [("https://github.com/masscan", [])])]),
            ("Passive DNS monitoring", [("Sublert", [("https://github.com/sublert", [])])])]),
        ("Wordlists", [
            ("Common Files", [("dirsearch Wordlist", [("https://github.com/dirsearch", [])])]),
            ("Subdomains", [("CommonSpeak", [("https://github.com/commonspeak2", [])])]),
            ("Mixed", [("Seclist", [("https://github.com/SecLists", [])])])]),
        ("Android", [
            ("Emulator", [("Bluestacks", [("https://www.bluestacks.com/", [])]),
                          ("Genymotion", [("https://www.genymotion.com/", [])])]),
            ("Decompiler", [("Jadx", [("https://github.com/skylot/jadx", [])])])]),
        ("Web Application Scanners", [
            ("Nessus", [("https://www.tenable.com/products/nessus", [])]),
            ("OWASP ZAP", [("https://owasp.org/www-project-zap/", [])])])])
    r = build(t)
    for i, c in enumerate(r.children):
        c.side = "R" if i % 2 == 0 else "L"
    return r


class Doc:
    """Everything that belongs to one tab. The canvas is shared; its state is swapped in and out."""

    def __init__(self, root=None, layout="Map", shape="Square", line="Curved", path=None, line_color=DEFAULT_LINE):
        self.line_color = line_color if QColor(line_color).isValid() else DEFAULT_LINE
        self.root = root or Node("My Mind Map")
        self.layout_mode = layout if layout in ("Map", "Logic chart") else "Map"
        self.shape = shape if shape in SHAPES else "Square"
        self.line = line if line in LINES else "Straight"
        self.path, self.dirty, self.sel_path = path, False, []
        self.undo, self.redo = [], []
        self.zoom, self.ox, self.oy, self.need_fit = 1.0, 0.0, 0.0, True
        self.id, self.untitled = 0, 0

    def name(self, path=None):
        path = path if path is not None else self.path
        if path:
            return os.path.basename(path)
        return "Untitled" if self.untitled <= 1 else f"Untitled {self.untitled}"


class EditBox(QTextEdit):
    """Multi-line topic editor. Enter = finish, Shift/Ctrl/Alt+Enter = new line."""
    cancelled = Signal()
    blurred = Signal()
    returnPressed = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptRichText(False)  # pasting always gives plain text, line breaks kept
        self.setTabChangesFocus(True)
        self.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textChanged.connect(self.refit)

    def text(self):
        return self.toPlainText().replace("\r\n", "\n").replace("\r", "\n").replace("\u2028", "\n").replace("\u2029", "\n")

    def setText(self, t):
        self.setPlainText(t)

    def refit(self):  # grow/shrink the box with its content
        self.document().setTextWidth(max(self.width() - 18, 20))
        h = max(38, int(math.ceil(self.document().size().height())) + 14)
        if h != self.height():
            self.resize(self.width(), h)

    def keyPressEvent(self, e):
        k = e.key()
        if k == Qt.Key.Key_Escape:
            self.cancelled.emit()
            return
        if k in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            mods = Qt.KeyboardModifier.ShiftModifier | Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.AltModifier
            if e.modifiers() & mods:
                self.insertPlainText("\n")
            else:
                self.returnPressed.emit()
            e.accept()
            return
        super().keyPressEvent(e)
        e.accept()  # don't let keys reach the map while typing

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        self.blurred.emit()


class NoteBox(QTextEdit):
    """Popup editor for a topic's note. Esc or a click elsewhere closes it (and keeps the text)."""
    closed = Signal()
    blurred = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptRichText(False)
        self.setPlaceholderText("Write a note...")
        self.setStyleSheet("QTextEdit{background:#111113;color:#fff;border:1px solid #fff;"
                           "border-radius:8px;padding:6px 10px;font-size:18.5px;"
                           "font-family:'Inter','Helvetica','Arial',sans-serif;font-weight:500;"
                           "selection-background-color:#3a6ea5;}")
        self.setVisible(False)

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.closed.emit()
            return
        super().keyPressEvent(e)
        e.accept()  # don't let keys reach the map while typing

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        if e.reason() != Qt.FocusReason.PopupFocusReason:  # right-click menu keeps the note open
            self.blurred.emit()


class MapView(QWidget):
    def __init__(self, win):
        super().__init__()
        self.win = win
        self.rail = None
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setMouseTracking(True)
        self._lc = {}
        self.line_color = DEFAULT_LINE
        #self.root, self.layout_mode, self.shape, self.line = default_tree(), "Map", "Square", "Straight"
        self.root, self.layout_mode, self.shape, self.line = Node("My Mind Map"), "Map", "Square", "Curved"
        self.sel, self.path, self.dirty = self.root, None, False
        self.undo, self.redo, self.vis = [], [], []
        self.zoom, self.ox, self.oy, self.need_fit = 1.0, 0.0, 0.0, True
        self.edit_node, self.edit_new, self.drag, self.mx, self.my = None, False, None, 0, 0

        self.entry = EditBox(self)
        self.entry.setVisible(False)
        self.entry.setStyleSheet("QTextEdit{background:#111113;color:#fff;border:1px solid #fff;"
                                 "border-radius:6px;padding:4px 8px;font-size:18px;"
                                 "selection-background-color:#3a6ea5;}")
        self.entry.returnPressed.connect(lambda: self.commit_edit())
        self.entry.cancelled.connect(lambda: self.commit_edit(False))
        self.entry.blurred.connect(lambda: self.commit_edit())
        self.note_node, self._nb = None, None  # note being edited; (node, time) of a note closed by a click elsewhere
        self.note_box = NoteBox(self)
        self.note_box.closed.connect(lambda: self.close_note())
        self.note_box.blurred.connect(lambda: self.close_note(True))
        self.search_q, self.found, self._fs, self.found_cur = "", [], set(), None  # Ctrl+F state
        self.sbar = SearchBar(self)
        self.relayout()

    def focusNextPrevChild(self, nxt):  # keep Tab for "add child"
        return False

    @property
    def sel(self):  # primary selected node; assigning it collapses any multi-selection
        return self._sel

    @sel.setter
    def sel(self, n):
        self._sel, self.sels = n, [n]

    def targets(self):  # all selected, visible nodes in map order
        ids = {id(n) for n in self.sels}
        return [n for n in self.vis if id(n) in ids]

    def select_all(self):
        ns = [n for n in self.vis if n is not self.root]
        if ns:
            self.sel = ns[0]
            self.sels = ns
            self.update()

    def collapse_sel(self):
        self.sel = self.sel
        self.update()

    # ---------- layout ----------
    def lay(self, text, depth, fw=None):
        d = min(depth, 3)
        key = (text, d, fw)
        hit = self._lc.get(key)
        if hit:
            return hit
        f = QFont()
        f.setFamilies(FAMILIES)
        f.setPixelSize(FONT_PX[d])
        f.setBold(BOLD[d])
        tl = QTextLayout((text or " ").replace("\n", "\u2028"), f)  # U+2028 = hard line break in QTextLayout
        opt = QTextOption(Qt.AlignmentFlag.AlignLeft)
        opt.setWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
        tl.setTextOption(opt)
        tl.beginLayout()
        y, lines = 0.0, []
        while True:
            ln = tl.createLine()
            if not ln.isValid():
                break
            ln.setLineWidth(fw or MAXW)
            ln.setPosition(QPointF(0, y))
            y += ln.height()
            lines.append(ln)
        tl.endLayout()
        res = (tl, lines, math.ceil(max(l.naturalTextWidth() for l in lines)), math.ceil(y))
        if len(self._lc) > 3000:
            self._lc.clear()
        self._lc[key] = res
        return res

    def measure(self, n, depth, eff):
        n.depth, n.eff = depth, eff
        _, _, n.tw, n.th = self.lay(n.text, depth, n.fw)
        if n.fw:
            n.tw = n.fw  # custom width: the box is exactly that wide, lines centred inside
        px, py = PADS[min(depth, 3)]
        n.w, n.h = n.tw + 2 * px + n.iw + n.nw, n.th + 2 * py
        kids = [] if n.folded else n.children
        for c in kids:
            self.measure(c, depth + 1, ("R" if self.layout_mode != "Map" else c.side) if depth == 0 else eff)
        n.sh = max(n.h, sum(c.sh for c in kids) + 20 * (len(kids) - 1)) if kids else n.h

    def place(self, n, cy):
        n.y = cy - n.h / 2
        kids = [] if n.folded else n.children
        if not kids:
            return
        hg = hgap(n.depth)
        tot = sum(c.sh for c in kids) + 20 * (len(kids) - 1)
        y = cy - tot / 2
        for c in kids:
            c.x = n.x + n.w + hg if c.eff == "R" else n.x - hg - c.w
            self.vis.append(c)
            self.place(c, y + c.sh / 2)
            y += c.sh + 20

    def relayout(self):
        r = self.root
        self.measure(r, 0, "R")
        r.x, r.y, self.vis = -r.w / 2, -r.h / 2, [r]
        for side in "RL":
            kids = [c for c in r.children if c.eff == side]
            if not kids:
                continue
            tot = sum(c.sh for c in kids) + 28 * (len(kids) - 1)
            y = -tot / 2
            for c in kids:
                c.x = r.x + r.w + hgap(0) if side == "R" else r.x - hgap(0) - c.w
                self.vis.append(c)
                self.place(c, y + c.sh / 2)
                y += c.sh + 28
        if self.search_q:  # the tree may have changed (edit, undo, tab switch): keep the matches current
            self.search_scan()
        self.update()

    def bounds(self):
        return (min(n.x for n in self.vis) - 24, min(n.y for n in self.vis) - 8,
                max(n.x + n.w for n in self.vis) + 24, max(n.y + n.h for n in self.vis) + 8)

    def fit(self, W, H):
        x0, y0, x1, y1 = self.bounds()
        #self.zoom = max(0.1, min(1.0, (W - 80) / max(x1 - x0, 1), (H - 80) / max(y1 - y0, 1)))
        self.zoom = 0.62
        self.ox = W / 2 - (x0 + x1) / 2 * self.zoom
        self.oy = H / 2 - (y0 + y1) / 2 * self.zoom
        self.need_fit = False

    def refont(self):  # FAMILIES changed: drop cached text layouts and re-measure everything
        self._lc.clear()
        f = self.entry.font()
        f.setFamilies(FAMILIES)
        self.entry.setFont(f)
        self.relayout()

    def fit_now(self):
        self.need_fit = True
        self.update()

    # ---------- drawing ----------
    def paintEvent(self, ev):
        W, H = self.width(), self.height()
        if self.need_fit and W > 10:
            self.fit(W, H)
        self.place_note()
        p = QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.TextAntialiasing)
        p.fillRect(self.rect(), BLACK)
        p.translate(self.ox, self.oy)
        p.scale(self.zoom, self.zoom)
        self.draw_scene(p, True)
        p.end()

    def box_path(self, n, x, y, g=0):  # outline path of a root/main topic, grown by g
        r = 0 if n.depth > 1 else {"Square": 0, "Rounded": 16, "Pill": n.h / 2}[self.shape]
        return rect_path(x - g, y - g, n.w + 2 * g, n.h + 2 * g, r + g if r else 0)

    def draw_scene(self, p, interactive):
        for n in self.vis:
            if n.parent:
                self.draw_conn(p, n.parent, n)
        for n in self.vis:
            self.draw_node(p, n)
        if not interactive:
            return
        if self.found:  # search matches: yellow for all, orange for the current one
            for n in self.vis:
                if id(n) in self._fs:
                    cur = n is self.found_cur
                    # p.setPen(pen(QColor(237, 40, 63) if cur else QColor(255, 204, 0), 3 if cur else 2))
                    # p.setBrush(QColor(237, 40, 63, 120) if cur else QColor(255, 204, 0, 70))
                    p.setPen(pen(QColor(0, 126, 217) if cur else QColor(73, 166, 209), 3 if cur else 2))
                    p.setBrush(QColor(0, 126, 217, 120) if cur else QColor(73, 166, 209, 70))
                    p.drawPath(self.box_path(n, n.x, n.y, 3) if n.depth <= 1
                               else rect_path(n.x - 3, n.y - 3, n.w + 6, n.h + 6, 6))
        if not self.edit_node:
            p.setPen(pen(WHITE, 1.5, [5, 4]))
            p.setBrush(NOBRUSH)
            for n in self.sels:
                if n in self.vis:
                    p.drawPath(self.box_path(n, n.x, n.y, 6))
            if len(self.sels) == 1 and self.sel in self.vis:  # width handles
                z = self.zoom
                p.setPen(NOPEN)
                p.setBrush(WHITE)
                for hx, _, gy in self.grips(self.sel):
                    p.drawRoundedRect(QRectF(hx - 2 / z, gy - 11 / z, 4 / z, 22 / z), 2 / z, 2 / z)
                p.setPen(pen(WHITE, 1.5, [5, 4]))
                p.setBrush(NOBRUSH)
        d = self.drag
        if d and d["mode"] == "node" and d["active"]:
            p.save()
            p.setOpacity(0.55)
            n0 = d["node"]
            for g in d["group"]:
                self.draw_node(p, g, d["px"] - d["gx"] + g.x - n0.x, d["py"] - d["gy"] + g.y - n0.y, False)
            p.restore()
            if d["target"]:  # drawn after the ghost so it is never hidden behind it
                m, pos = d["target"]
                p.setBrush(NOBRUSH)
                if m is self.root:
                    p.setPen(pen(WHITE, 4))
                    xx = m.x + m.w + 10 if self.drop_side(d["px"]) == "R" else m.x - 10
                    p.drawLine(QLineF(xx, m.y, xx, m.y + m.h))
                elif pos == "child":
                    p.setPen(pen(WHITE, 4, [6, 4]))
                    p.drawPath(self.box_path(m, m.x, m.y, 6))
                else:
                    p.setPen(pen(WHITE, 4))
                    yy = m.y - 8 if pos == "before" else m.y + m.h + 8
                    p.drawLine(QLineF(m.x - 10, yy, m.x + m.w + 10, yy))
        if d and d["mode"] == "marquee" and d["active"]:
            x0, y0, x1, y1 = d["rect"]
            p.setPen(pen(WHITE, 1.5, [5, 4]))
            p.setBrush(QColor(255, 255, 255, 26))
            p.drawRect(QRectF(x0, y0, x1 - x0, y1 - y0))

    def dotpos(self, n, x=None, y=None):
        x = n.x if x is None else x
        y = n.y if y is None else y
        R = n.eff == "R"
        edge = x + n.w if R else x
        off = 6 if n.depth == 1 else 0
        return edge + (off if R else -off), y + (n.h / 2 if n.depth <= 1 else n.h)

    def draw_conn(self, p, pa, c):
        R = c.eff == "R"
        p.setBrush(NOBRUSH)
        path = QPainterPath()
        if pa.parent is None:
            ex = c.x if R else c.x + c.w
            if self.line == "Curved":
                mx = (pa.cx + ex) / 2
                path.moveTo(pa.cx, pa.cy)
                path.cubicTo(mx, pa.cy, mx, c.cy, ex, c.cy)
            elif self.line == "Rounded":  # leaves the root vertically, bends round into the topic horizontally
                # start where the Curved line to this topic would cross the root's top/bottom edge,
                # so the lines are spaced out along the root exactly like Curved (and never cross)
                dyy = c.cy - pa.cy
                q = (pa.h / 2) / abs(dyy) if dyy else 1.0  # share of the way up/down that the root edge is
                f = 1.0
                if q < 1:
                    lo, hi = 0.0, 1.0
                    for _ in range(30):  # solve 3t^2 - 2t^3 = q (the Curved line's height at parameter t)
                        t = (lo + hi) / 2
                        lo, hi = (t, hi) if 3 * t * t - 2 * t ** 3 < q else (lo, t)
                    f = 1.5 * t - 1.5 * t * t + t ** 3  # the Curved line's sideways travel at that point
                lim = pa.w / 2 - 14  # keep the start inside the root's width
                x0 = pa.cx + max(-lim, min(lim, (ex - pa.cx) * f))
                dxx = ex - x0
                k = 0.5523  # makes the cubic a true quarter ellipse
                path.moveTo(x0, pa.cy)
                path.cubicTo(x0, pa.cy + k * dyy, ex - k * dxx, c.cy, ex, c.cy)
            elif self.line == "Elbow":  # horizontal - rounded corner - vertical - rounded corner - horizontal
                edge = pa.x + pa.w if R else pa.x
                path = elbow_path(pa.cx, pa.cy, (edge + ex) / 2, ex, c.cy, 24)
            else:
                path.moveTo(ex, c.cy)
                path.lineTo(pa.cx, pa.cy)
            p.setPen(pen(QColor(self.line_color), 4))
            p.drawPath(path)
            return
        dx, dy = self.dotpos(pa)
        bus = c.x if R else c.x + c.w
        if self.line == "Elbow":  # corner into the vertical, second corner into the topic's underline
            path = elbow_path(dx, dy, bus, bus + (14 if R else -14), c.ay, 14)
        else:
            path.moveTo(dx, dy)
            path.lineTo(bus, dy)
            path.lineTo(bus, c.ay)
        p.setPen(pen(QColor(self.line_color), 3.0))
        p.drawPath(path)

    def draw_node(self, p, n, x=None, y=None, marker=True):
        x = n.x if x is None else x
        y = n.y if y is None else y
        px, py = PADS[min(n.depth, 3)]
        fg = WHITE
        if n.depth <= 1:
            p.setBrush(tint(n.color) if n.color else BLACK)
            p.setPen(pen(QColor(n.color) if n.color else QColor(self.line_color), 4 if not n.color else 3))
            p.drawPath(self.box_path(n, x, y, -1))
        else:
            if n.color:  # sub topics get a filled background behind the text
                p.setPen(pen(QColor(n.color), 2))
                p.setBrush(tint(n.color))
                p.drawPath(rect_path(x, y, n.w, n.h, 4))
            p.setPen(pen(QColor(self.line_color), 3.0))
            p.drawLine(QLineF(x, y + n.h, x + n.w, y + n.h))
        if n.icon:
            s = ICON_SIZES[min(n.depth, 3)]
            draw_icon(p, n.icon, x + px, y + n.h / 2 - s / 2, s)
        _, lines, _, _ = self.lay(n.text, n.depth, n.fw)
        p.setPen(fg)
        ox = x + px + n.iw
        for ln in lines:
            ln.draw(p, QPointF(ox + (n.tw - ln.naturalTextWidth()) / 2, y + py))
        if n.note:
            draw_note(p, *self.note_pos(n, x, y), fg)
        if marker and n.children and n.parent:
            dx, dy = self.dotpos(n, x, y)
            p.setPen(NOPEN)
            p.setBrush(QColor(self.line_color))
            if n.folded:
                p.drawEllipse(QPointF(dx, dy), 8, 8)
                f = QFont()
                f.setFamilies(FAMILIES)
                f.setPixelSize(12)
                f.setBold(True)
                p.setFont(f)
                p.setPen(qc(text_on(self.line_color)))
                p.drawText(QRectF(dx - 8, dy - 8, 16, 16), Qt.AlignmentFlag.AlignCenter, str(len(n.children)))
            else:
                r = 9 if n.depth <= 2 else 8
                p.drawEllipse(QPointF(dx, dy), r, r)

    # ---------- notes ----------
    def note_pos(self, n, x=None, y=None):  # (x, y, size) of the note badge, at the right end of the topic
        x = n.x if x is None else x
        y = n.y if y is None else y
        s = NOTE_SIZES[min(n.depth, 3)]
        px = PADS[min(n.depth, 3)][0]
        return x + px + n.iw + n.tw + NOTE_GAP, y + n.h / 2 - s / 2, s

    def on_badge(self, n, wx, wy):
        bx, by, s = self.note_pos(n)
        return bx - 6 <= wx <= bx + s + 6 and by - 6 <= wy <= by + s + 6

    def place_note(self):  # keep the popup just below its topic (above it near the bottom edge)
        n = self.note_node
        if n is None:
            return
        z, w, h = self.zoom, 600, 240
        x, y = int(n.x * z + self.ox), int((n.y + n.h) * z + self.oy + 10)
        if y + h > self.height() - 8:
            y = int(n.y * z + self.oy - h - 10)
        self.note_box.setGeometry(max(8, min(x, self.width() - w - 8)), max(8, y), w, h)

    def open_note(self, n):
        self.commit_edit()
        self.note_node = n
        self.note_box.setPlainText(n.note)
        self.place_note()
        self.note_box.setVisible(True)
        self.note_box.setFocus()
        self.note_box.moveCursor(self.note_box.textCursor().MoveOperation.End)

    def close_note(self, by_blur=False):  # saves the text; empty text removes the note
        n = self.note_node
        if n is None:
            return
        self.note_node = None
        txt = self.note_box.toPlainText().strip()
        self.note_box.setVisible(False)
        if txt != n.note:
            self.push_undo()
            n.note = txt
            self.relayout()
        if by_blur:
            self._nb = (n, time.monotonic())
        self.setFocus()
        self.update()

    def toggle_note(self):  # key N / toolbar button: write or show the note of the selected topic
        if self.note_node is self.sel:
            self.close_note()
        else:
            self.open_note(self.sel)

    def note_click(self, n):  # click on a badge: open the note, or close it if it was open
        was = self.note_node or (self._nb[0] if self._nb and time.monotonic() - self._nb[1] < 0.5 else None)
        self._nb = None
        self.close_note()
        self.sel = n
        if was is not n:
            self.open_note(n)
        self.update()

    # ---------- coordinates / hit testing ----------
    def to_world(self, x, y):
        return (x - self.ox) / self.zoom, (y - self.oy) / self.zoom

    def hit(self, wx, wy):
        for n in reversed(self.vis):
            if n.children and n.parent:
                dx, dy = self.dotpos(n)
                if math.hypot(wx - dx, wy - dy) < 9:
                    return n, True
            if n.x - 3 <= wx <= n.x + n.w + 3 and n.y - 3 <= wy <= n.y + n.h + 3:
                return n, False
        return None, False

    def zoom_at(self, f, sx, sy):
        wx, wy = self.to_world(sx, sy)
        self.zoom = max(0.1, min(3.0, self.zoom * f))
        self.ox, self.oy = sx - wx * self.zoom, sy - wy * self.zoom
        self.update()

    def zoom_center(self, f):
        self.zoom_at(f, self.width() / 2, self.height() / 2)

    def ensure_visible(self, n):
        W, H, z = self.width(), self.height(), self.zoom
        sx, sy = n.x * z + self.ox, n.y * z + self.oy
        if sx < 30: self.ox += 30 - sx
        if sx + n.w * z > W - 30: self.ox -= sx + n.w * z - (W - 30)
        if sy < 30: self.oy += 30 - sy
        if sy + n.h * z > H - 30: self.oy -= sy + n.h * z - (H - 30)

    # ---------- width handle on the selected topic ----------
    def grips(self, n):  # [(x, side, y)] of the grab handles: on the edge facing away from the parent
        gy = n.y + n.h * 0.22 if (n.parent and n.children and n.depth <= 1) else n.cy  # keep clear of the fold dot
        if n.parent is None:
            return [(n.x - 6, -1, gy), (n.x + n.w + 6, 1, gy)]
        return [(n.x + n.w + 6, 1, gy)] if n.eff == "R" else [(n.x - 6, -1, gy)]

    def handle_at(self, wx, wy):
        if self.edit_node or len(self.sels) != 1 or self.sels[0] not in self.vis:
            return None
        n = self.sels[0]
        if not (n.y - 6 <= wy <= n.y + n.h + 6):
            return None
        if n.parent and n.children:  # the fold dot wins over the handle
            dx, dy = self.dotpos(n)
            if math.hypot(wx - dx, wy - dy) < 9:
                return None
        for hx, side, _ in self.grips(n):
            if abs(wx - hx) <= (GRIP + 2) / self.zoom:
                return n, side
        return None

    def update_cursor(self, x, y):
        on = self.handle_at(*self.to_world(x, y)) is not None
        if on != getattr(self, "_hcur", False):
            self._hcur = on
            if on:
                self.setCursor(Qt.CursorShape.SizeHorCursor)
            else:
                self.unsetCursor()

    # ---------- mouse ----------
    def has_mods(self, e):  # Ctrl or Shift held
        return bool(e.modifiers() & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.ShiftModifier))

    def mousePressEvent(self, e):
        self.setFocus()
        self.commit_edit()
        x, y = e.position().x(), e.position().y()
        self.mx, self.my = x, y
        self.drag = {"mode": "none", "sx": x, "sy": y}
        b, M = e.button(), Qt.MouseButton
        if b in (M.MiddleButton, M.RightButton):  # middle / right button pans
            self.drag.update(mode="pan", ox=self.ox, oy=self.oy)
            return
        if b != M.LeftButton:
            return
        mods = self.has_mods(e)
        wx, wy = self.to_world(x, y)
        h = None if mods else self.handle_at(wx, wy)
        if h:  # grab the width handle of the selected topic
            hn, side = h
            edge = hn.x + hn.w if side > 0 else hn.x
            root = hn.parent is None
            anchor = hn.cx if root else (hn.x if side > 0 else hn.x + hn.w)
            self.drag.update(mode="resize", node=hn, side=side, off=wx - edge, anchor=anchor,
                             k=2 if root else 1, active=False)
            self.setCursor(Qt.CursorShape.SizeHorCursor)
            return
        n, mk = self.hit(wx, wy)
        if n is not None:
            if mk:
                self.push_undo()
                n.folded = not n.folded
                self.relayout()
                return
            if n.note and not mods and self.on_badge(n, wx, wy):
                return self.note_click(n)
            if mods:  # Ctrl/Shift+click adds or removes a node
                cur = list(self.sels)
                if n in cur and len(cur) > 1:
                    cur.remove(n)
                elif n not in cur:
                    cur.append(n)
                self.sel = n if n in cur else cur[-1]
                self.sels = cur
            elif not (n in self.sels and len(self.sels) > 1 and n is not self.root):
                self.sel = n  # (a click inside a group keeps it, so the group can be dragged)
            self.update()
        if n is None:  # left drag on empty canvas draws a selection box
            self.sels = list(self.sels) if mods else []
            self.drag.update(mode="marquee", wx=wx, wy=wy, rect=(wx, wy, wx, wy), active=False,
                             base=list(self.sels))
        elif n is self.root and not self.edit_node:  # dragging the root moves the whole map
            self.drag.update(mode="pan", ox=self.ox, oy=self.oy)
        elif n is not self.root and not self.edit_node:
            ts = self.targets()
            multi = n in ts and len(ts) > 1
            group = [m for m in ts if m is not self.root and not any(m is not o and m.under(o) for o in ts)] if multi else [n]
            self.drag.update(mode="node", node=n, group=group, gx=wx - n.x, gy=wy - n.y,
                             active=False, target=None, px=wx, py=wy,
                             collapse=multi and not mods)
        self.update()

    def mouseDoubleClickEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton:
            return
        wx, wy = self.to_world(e.position().x(), e.position().y())
        h = self.handle_at(wx, wy)
        if h:  # double-click the handle: back to automatic width
            if h[0].fw:
                self.push_undo()
                h[0].fw = None
                self.relayout()
            return
        n, mk = self.hit(wx, wy)
        if n is None:
            return
        if mk:
            self.push_undo()
            n.folded = not n.folded
            self.relayout()
            return
        if n.note and self.on_badge(n, wx, wy):
            return self.note_click(n)
        self.sel = n
        self.start_edit(n)

    def mouseMoveEvent(self, e):
        x, y = e.position().x(), e.position().y()
        self.mx, self.my = x, y
        d = self.drag
        if not d or d["mode"] == "none":
            if not d:
                self.update_cursor(x, y)
            return
        dx, dy = x - d["sx"], y - d["sy"]
        if d["mode"] == "resize":
            if not d["active"]:
                if abs(dx) < 2:
                    return
                d["active"] = True
                self.push_undo()  # one undo step for the whole drag
            n = d["node"]
            wx = self.to_world(x, y)[0]
            w = d["k"] * d["side"] * ((wx - d["off"]) - d["anchor"])
            fw = int(round(w - 2 * PADS[min(n.depth, 3)][0] - n.iw - n.nw))
            n.fw = max(MINFW, min(4000, fw))
            self.relayout()
            return
        if d["mode"] == "pan":
            self.ox, self.oy = d["ox"] + dx, d["oy"] + dy
        else:
            if math.hypot(dx, dy) > 6:
                d["active"] = True
            if d["active"]:
                px, py = self.to_world(d["sx"] + dx, d["sy"] + dy)
                if d["mode"] == "node":
                    d["px"], d["py"] = px, py
                    d["target"] = self.find_target(d["node"], px, py, d["group"])
                else:
                    r = d["rect"] = (min(d["wx"], px), min(d["wy"], py), max(d["wx"], px), max(d["wy"], py))
                    hit = [m for m in self.vis if m is not self.root and m.x < r[2] and m.x + m.w > r[0]
                           and m.y < r[3] and m.y + m.h > r[1]]
                    self.sels = d["base"] + [m for m in hit if m not in d["base"]]
        self.update()

    def mouseReleaseEvent(self, e):
        d, self.drag = self.drag, None
        self._hcur = True  # force the cursor to be re-evaluated below
        self.update_cursor(e.position().x(), e.position().y())
        if d and d["mode"] == "node":
            if d["active"] and d["target"]:
                self.do_move(d["group"], *d["target"], side=self.drop_side(d["px"]))
            elif not d["active"] and d["collapse"]:
                self.sel = d["node"]
        elif d and d["mode"] == "marquee":
            ss = [m for m in self.sels if m in self.vis]
            if ss:
                self.sel = self.sel if self.sel in ss else ss[0]
                self.sels = ss
            else:
                self.sels = []  # clicked / dragged over empty space: deselect everything
        self.update()

    def drop_side(self, wx):
        return "R" if self.layout_mode != "Map" or wx >= self.root.cx else "L"

    def find_target(self, node, wx, wy, group=None):
        group = group or [node]
        GX, GY = 14, 10  # grow every box so the gaps between siblings are droppable
        cand = [m for m in self.vis if not any(m.under(g) for g in group)]
        for m in reversed(cand):
            if m.x - GX <= wx <= m.x + m.w + GX and m.y - GY <= wy <= m.y + m.h + GY:
                if m is self.root:
                    return m, "child"
                f = (wy - (m.y - GY)) / (m.h + 2 * GY)
                return m, ("before" if f < .3 else "after" if f > .7 else "child")
        if all(g.parent is self.root for g in group):
            # main topic(s) released in free space: side from pointer x, slot from pointer y
            kids = [c for c in self.root.children if c not in group and c.eff == self.drop_side(wx)]
            for c in kids:
                if wy < c.cy:
                    return c, "before"
            return (kids[-1], "after") if kids else (self.root, "child")
        # nothing under the pointer: snap to the nearest node in the same column
        best, bd = None, 40
        for m in cand:
            if m is self.root or not (m.x - GX <= wx <= m.x + m.w + GX):
                continue
            d = max(m.y - wy, wy - (m.y + m.h), 0)
            if d < bd:
                best, bd = m, d
        if best:
            return best, ("before" if wy < best.cy else "after")
        return None

    def wheelEvent(self, e):
        ad, pd, mods, pos = e.angleDelta(), e.pixelDelta(), e.modifiers(), e.position()
        if mods & Qt.KeyboardModifier.ControlModifier:
            if ad.y():
                self.zoom_at(1.1 if ad.y() > 0 else 0.9, pos.x(), pos.y())
        elif mods & Qt.KeyboardModifier.ShiftModifier:  # Shift+wheel scrolls sideways
            self.ox += (ad.y() or ad.x()) / 120 * 40
        elif not pd.isNull():
            self.ox += pd.x()
            self.oy += pd.y()
        else:
            self.ox += ad.x() / 120 * 40
            self.oy += ad.y() / 120 * 40
        self.update()
        e.accept()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.rail:
            self.rail.move((self.width() - self.rail.width()) // 2, 14)
        if not self.sbar.isHidden():
            self.sbar.place()

    # ---------- undo ----------
    def path_of(self, n):
        p = []
        while n.parent:
            p.append(n.parent.children.index(n))
            n = n.parent
        return p[::-1]

    def node_at(self, path):
        n = self.root
        for i in path:
            if i >= len(n.children):
                break
            n = n.children[i]
        return n

    def snap(self):
        return json.dumps(self.root.to_dict()), self.path_of(self.sel)

    def push_undo(self):
        self.undo.append(self.snap())
        del self.undo[:-100]
        self.redo.clear()
        self.set_dirty(True)

    def restore(self, s):
        self.root = Node.from_dict(json.loads(s[0]))
        self.sel = self.node_at(s[1])
        self.edit_node, self.note_node = None, None
        self.entry.setVisible(False)
        self.note_box.setVisible(False)
        self.set_dirty(True)
        self.relayout()

    def undo_op(self):
        if self.undo:
            self.redo.append(self.snap())
            self.restore(self.undo.pop())

    def redo_op(self):
        if self.redo:
            self.undo.append(self.snap())
            self.restore(self.redo.pop())

    def set_dirty(self, v):
        self.dirty = v
        self.win.update_title()

    # ---------- editing ----------
    def fewer_side(self, exclude=None):
        k = [c for c in self.root.children if c is not exclude]
        return "R" if sum(c.side == "R" for c in k) <= sum(c.side == "L" for c in k) else "L"

    def new_node(self, parent, idx=None):
        self.push_undo()
        n = Node("New topic", self.fewer_side() if parent is self.root else "R")
        parent.folded = False
        parent.add(n, idx)
        self.sel = n
        self.relayout()
        self.ensure_visible(n)
        self.start_edit(n, True)

    def add_child(self):
        self.new_node(self.sel)

    def add_sibling(self):
        s = self.sel
        if s is self.root:
            return self.add_child()
        self.new_node(s.parent, s.parent.children.index(s) + 1)
        if s.parent is self.root:
            self.sel.side = s.side
            self.relayout()

    def delete(self):
        ts = [n for n in self.targets() if n is not self.root]
        if not ts:
            return
        self.push_undo()
        top = [n for n in ts if not any(n is not m and n.under(m) for m in ts)]
        p, i = top[0].parent, top[0].parent.children.index(top[0])
        for n in top:
            n.parent.children.remove(n)
        self.sel = p.children[min(i, len(p.children) - 1)] if p.children else p
        self.relayout()

    def reset_width(self):  # back to automatic width for every selected topic
        ts = [n for n in self.targets() if n.fw]
        if ts:
            self.push_undo()
            for n in ts:
                n.fw = None
            self.relayout()

    def toggle_fold(self):
        ts = [n for n in self.targets() if n is not self.root and n.children]
        if ts:
            self.push_undo()
            f = not ts[0].folded
            for n in ts:
                n.folded = f
            self.relayout()

    def set_color(self, hexv):  # None clears; applying the colour every target already has clears it
        ts = self.targets()
        if not ts:
            return
        self.push_undo()
        clear = hexv is None or all(n.color == hexv for n in ts)
        for n in ts:
            n.color = None if clear else hexv
        self.relayout()

    def toggle_icon(self, kind):
        ts = self.targets()
        if not ts:
            return
        self.push_undo()
        off = all(n.icon == kind for n in ts)
        for n in ts:
            n.icon = None if off else kind
        self.relayout()

    def clear_icon(self):
        ts = [n for n in self.targets() if n.icon]
        if ts:
            self.push_undo()
            for n in ts:
                n.icon = None
            self.relayout()

    def do_move(self, nodes, t, pos, side=None):
        nodes = nodes if isinstance(nodes, list) else [nodes]
        self.push_undo()
        for n in nodes:
            n.parent.children.remove(n)
        if pos == "child":
            t.folded = False
            for n in nodes:
                t.add(n)
                if t is self.root:
                    n.side = side or self.fewer_side(n)
        else:
            p = t.parent
            i = p.children.index(t) + (1 if pos == "after" else 0)
            for k, n in enumerate(nodes):
                p.add(n, i + k)
                if p is self.root:
                    n.side = t.side
        self.relayout()

    # ---------- copy / cut / paste of topics (with their children) ----------
    def top_selected(self):  # selected topics, without ones already inside another selected topic
        ts = self.targets()
        return [n for n in ts if not any(n is not m and n.under(m) for m in ts)]

    def copy_nodes(self):
        ns = self.top_selected()
        if not ns:
            return False

        def outline(n, d):
            out = ["\t" * d + n.text.replace("\n", " ")]
            for c in n.children:
                out += outline(c, d + 1)
            return out

        data = QMimeData()
        data.setData(MIME, json.dumps([n.to_dict() for n in ns]).encode("utf-8"))
        data.setText("\n".join(l for n in ns for l in outline(n, 0)))  # plain-text outline for other apps
        QApplication.clipboard().setMimeData(data)
        return True

    def cut_nodes(self):
        if self.copy_nodes():
            self.delete()

    def paste_nodes(self):
        md = QApplication.clipboard().mimeData()
        if md is None:
            return
        specs = None
        if md.hasFormat(MIME):
            try:
                specs = json.loads(bytes(md.data(MIME)).decode("utf-8"))
            except Exception:
                specs = None
            if not (isinstance(specs, list) and all(isinstance(d, dict) for d in specs)):
                specs = None
        elif md.hasText():  # plain text: bullet/indented lists become topics, anything else one topic
            txt = md.text().replace("\r\n", "\n").replace("\r", "\n").strip()
            if txt:
                specs = parse_outline(txt) or [{"text": txt}]  # bullets / indentation -> child topics
        if not specs:
            return
        t = self.sel
        self.push_undo()
        t.folded = False
        new = []
        for d in specs:
            n = Node.from_dict(d)
            t.add(n)
            if t is self.root:
                n.side = self.fewer_side(n)
            new.append(n)
        self.relayout()
        self.sel = new[0]
        self.sels = new
        self.ensure_visible(self.sel)
        self.update()

    def start_edit(self, n, new=False):
        self.edit_node, self.edit_new = n, new
        z = self.zoom
        self.entry.setText(n.text)
        self.entry.setGeometry(max(0, int(n.x * z + self.ox - 8)), max(0, int(n.y * z + self.oy - 6)),
                               int(max(160, n.w * z + 24)), 38)
        self.entry.refit()
        self.entry.setVisible(True)
        self.entry.setFocus()
        self.entry.selectAll()
        self.update()

    def commit_edit(self, save=True):
        self.close_note()
        n = self.edit_node
        if n is None:
            return
        self.edit_node = None
        txt = self.entry.text().strip()
        self.entry.setVisible(False)
        if save and txt and txt != n.text:
            if not self.edit_new:
                self.push_undo()
            n.text = txt
            self.set_dirty(True)
            self.relayout()
        self.setFocus()
        self.update()

    def navigate(self, key):
        s = self.sel
        if key in (Qt.Key.Key_Up, Qt.Key.Key_Down):
            up = key == Qt.Key.Key_Up
            c = [m for m in self.vis if m is not s and m.depth == s.depth and m.eff == s.eff
                 and (m.cy < s.cy if up else m.cy > s.cy)]
            if c:
                self.sel = min(c, key=lambda m: abs(m.cy - s.cy))
        else:
            right = key == Qt.Key.Key_Right
            if s is self.root:
                k = [c for c in s.children if c.eff == ("R" if right else "L")]
                if k:
                    self.sel = k[0]
            elif (s.eff == "R") == right:
                if s.children:
                    s.folded = False
                    self.relayout()
                    self.sel = s.children[0]
            else:
                self.sel = s.parent
        self.ensure_visible(self.sel)
        self.update()

    # ---------- search (Ctrl+F) ----------
    @staticmethod
    def fold_text(s):  # case- and whitespace-insensitive form used for matching
        return " ".join(s.split()).casefold()

    def walk(self, n):  # every topic, including ones inside folded branches
        yield n
        for c in n.children:
            yield from self.walk(c)

    def search_scan(self):  # rebuild the match list for the current query
        q = self.search_q
        self.found = [n for n in self.walk(self.root) if q in self.fold_text(n.text)] if q else []
        self._fs = {id(n) for n in self.found}
        if self.found_cur not in self.found:
            self.found_cur = None
        self.search_label()

    def search_label(self):
        n = len(self.found)
        if not self.search_q:
            txt = ""
        elif not n:
            txt = "No results"
        elif self.found_cur in self.found:
            txt = f"{self.found.index(self.found_cur) + 1} of {n}"
        else:
            txt = f"{n} found"
        self.sbar.set_state(txt, bool(self.search_q) and not n)

    def search_set(self, text):  # called on every keystroke in the search box
        self.search_q = self.fold_text(text)
        self.search_scan()
        if self.found and self.found_cur is None:  # jump to the first match at or after the selection
            order = {id(n): i for i, n in enumerate(self.walk(self.root))}
            at = order.get(id(self.sel), 0)
            self.search_show(next((n for n in self.found if order[id(n)] >= at), self.found[0]))
        self.update()

    def search_show(self, n):  # make n the current match: unfold its ancestors, select it, bring it into view
        self.found_cur = n
        p, opened = n.parent, False
        while p:
            if p.folded:
                p.folded, opened = False, True
            p = p.parent
        if opened:
            self.relayout()
        self.sel = n
        self.reveal(n)
        self.search_label()
        self.update()

    def reveal(self, n):  # centre n unless it is already comfortably on screen
        z, W, H = self.zoom, self.width(), self.height()
        sx, sy = n.x * z + self.ox, n.y * z + self.oy
        if not (sx > 40 and sy > 120 and sx + n.w * z < W - 40 and sy + n.h * z < H - 40):
            self.ox = W / 2 - (n.x + n.w / 2) * z
            self.oy = H / 2 - (n.y + n.h / 2) * z

    def search_step(self, d):  # next (+1) / previous (-1) match, wrapping around
        if not self.found:
            return
        if self.found_cur in self.found:
            i = (self.found.index(self.found_cur) + d) % len(self.found)
        else:
            i = 0 if d > 0 else len(self.found) - 1
        self.search_show(self.found[i])

    def search_open(self):
        self.commit_edit()
        self.sbar.open()
        self.search_set(self.sbar.edit.text())  # reopening restores the previous query's highlights

    def search_close(self):
        self.sbar.hide()
        self.search_q, self.found, self._fs, self.found_cur = "", [], set(), None
        self.setFocus()  # the last match stays selected
        self.update()

    def escape(self):
        if self.sbar.isHidden():
            self.collapse_sel()
        else:
            self.search_close()

    # ---------- keyboard ----------
    def keyPressEvent(self, e):
        if self.edit_node:
            return super().keyPressEvent(e)
        w, K = self.win, Qt.Key
        ctl = bool(e.modifiers() & Qt.KeyboardModifier.ControlModifier)
        sh = bool(e.modifiers() & Qt.KeyboardModifier.ShiftModifier)
        k = e.key()
        if ctl:
            acts = {K.Key_Z: self.redo_op if sh else self.undo_op, K.Key_Y: self.redo_op,
                    K.Key_S: w.save_as if sh else w.save, K.Key_O: w.open, K.Key_N: w.new,
                    K.Key_E: w.export, K.Key_0: self.fit_now, K.Key_A: self.select_all,
                    K.Key_C: self.copy_nodes, K.Key_V: self.paste_nodes, K.Key_X: self.cut_nodes,
                    K.Key_D: self.reset_width,
                    K.Key_F: self.search_open, K.Key_G: lambda: self.search_step(-1 if sh else 1),
                    K.Key_T: w.new, K.Key_W: w.close_current,
                    K.Key_Tab: lambda: w.next_tab(1), K.Key_Backtab: lambda: w.next_tab(-1),
                    K.Key_PageDown: lambda: w.next_tab(1), K.Key_PageUp: lambda: w.next_tab(-1)}
        else:
            acts = {K.Key_Escape: self.escape, K.Key_F3: lambda: self.search_step(-1 if sh else 1),
                    K.Key_Tab: self.add_child, K.Key_Return: self.add_sibling,
                    K.Key_Enter: self.add_sibling, K.Key_Delete: self.delete, K.Key_Backspace: self.delete,
                    #K.Key_Space: self.toggle_fold, K.Key_F2: lambda: self.start_edit(self.sel),
                    K.Key_Space: self.toggle_fold, K.Key_F: self.toggle_fold, K.Key_F2: lambda: self.start_edit(self.sel),
                    K.Key_E: lambda: self.start_edit(self.sel),
                    K.Key_1: lambda: self.set_color(COLORS[0][1]), K.Key_2: lambda: self.set_color(COLORS[1][1]),
                    K.Key_3: lambda: self.set_color(COLORS[2][1]), K.Key_4: lambda: self.set_color(COLORS[3][1]),
                    K.Key_0: lambda: self.set_color(None),
                    K.Key_C: lambda: self.toggle_icon("check"), K.Key_X: lambda: self.toggle_icon("error"),
                    K.Key_R: self.clear_icon, K.Key_A: self.toggle_note,
                    K.Key_Plus: lambda: self.zoom_center(1.15), K.Key_Equal: lambda: self.zoom_center(1.15),
                    K.Key_Minus: lambda: self.zoom_center(1 / 1.15)}
            for a in (K.Key_Up, K.Key_Down, K.Key_Left, K.Key_Right):
                acts[a] = (lambda a=a: self.navigate(a))
            # vim-style: h/j/k/l mirror left/down/up/right
            for a, tgt in ((K.Key_H, K.Key_Left), (K.Key_J, K.Key_Down),
                           (K.Key_K, K.Key_Up), (K.Key_L, K.Key_Right)):
                acts[a] = (lambda t=tgt: self.navigate(t))
        fn = acts.get(k)
        if fn:
            fn()
            e.accept()
        else:
            super().keyPressEvent(e)

    # ---------- tabs: swap a document in and out of the canvas ----------
    def capture(self, d):
        d.root, d.layout_mode, d.shape, d.line = self.root, self.layout_mode, self.shape, self.line
        d.line_color = self.line_color
        d.sel_path = self.path_of(self.sel)
        d.path, d.dirty, d.undo, d.redo = self.path, self.dirty, self.undo, self.redo
        d.zoom, d.ox, d.oy, d.need_fit = self.zoom, self.ox, self.oy, self.need_fit

    def apply(self, d):
        self.root, self.layout_mode, self.shape, self.line = d.root, d.layout_mode, d.shape, d.line
        self.line_color = d.line_color
        self.sel = self.node_at(d.sel_path)
        self.path, self.dirty, self.undo, self.redo = d.path, d.dirty, d.undo, d.redo
        self.zoom, self.ox, self.oy, self.need_fit = d.zoom, d.ox, d.oy, d.need_fit
        self.edit_node, self.drag = None, None
        self.entry.setVisible(False)
        self.relayout()
        self.win.sync_controls()
        self.win.update_title()

    # ---------- files ----------
    def write(self, path):
        data = {"layout": self.layout_mode, "shape": self.shape, "line": self.line, "line_color": self.line_color,
                "root": self.root.to_dict()}
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=1)
        self.path = path
        self.set_dirty(False)

    def load(self, d, path=None):
        self.root = Node.from_dict(d["root"]) if d else default_tree()
        self.layout_mode = d.get("layout", "Map") if d else self.layout_mode
        self.shape = d.get("shape", "Square") if d else self.shape
        self.line = d.get("line", "Straight") if d else self.line
        if self.line not in LINES:  # e.g. old files saved with the removed "Round" style
            self.line = "Straight"
        lc = d.get("line_color") if d else None
        self.line_color = lc if isinstance(lc, str) and QColor(lc).isValid() else DEFAULT_LINE
        self.sel, self.path = self.root, path
        self.undo.clear()
        self.redo.clear()
        self.need_fit = True
        self.set_dirty(False)
        self.relayout()
        self.win.sync_controls()

    def export(self, path):
        x0, y0, x1, y1 = self.bounds()
        pad, S = 40, 2
        W, H = x1 - x0 + 2 * pad, y1 - y0 + 2 * pad
        ext = path.lower().rsplit(".", 1)[-1]
        img = None
        if ext == "svg":
            gen = QSvgGenerator()
            gen.setFileName(path)
            gen.setSize(QSize(int(W), int(H)))
            gen.setViewBox(QRectF(0, 0, W, H))
            p = QPainter(gen)
        elif ext == "pdf":
            wr = QPdfWriter(path)
            wr.setResolution(72)
            wr.setPageSize(QPageSize(QSizeF(W, H), QPageSize.Unit.Point))
            wr.setPageMargins(QMarginsF(0, 0, 0, 0))
            p = QPainter(wr)
        else:
            img = QImage(int(W * S), int(H * S), QImage.Format.Format_ARGB32)
            img.fill(BLACK)
            p = QPainter(img)
            p.scale(S, S)
        p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.TextAntialiasing)
        p.fillRect(QRectF(0, 0, W, H), BLACK)
        p.translate(pad - x0, pad - y0)
        self.draw_scene(p, False)
        p.end()
        if img is not None:
            img.save(path, "PNG")


# ---------- toolbar ----------
def gpen():
    return pen(QColor(205, 205, 210), 1.7, round_=True)


def L(p, x1, y1, x2, y2):
    p.drawLine(QLineF(x1, y1, x2, y2))


def poly(p, pts):
    path = QPainterPath()
    path.moveTo(*pts[0])
    for pt in pts[1:]:
        path.lineTo(*pt)
    p.drawPath(path)


def g_new(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(6, 3), (14, 3), (18, 7), (18, 21), (6, 21), (6, 3)])
    L(p, 12, 11, 12, 17); L(p, 9, 14, 15, 14)


def g_plus(p):
    p.setPen(gpen()); L(p, 12, 5, 12, 19); L(p, 5, 12, 19, 12)


def g_open(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(3, 7), (9, 7), (11, 9), (21, 9), (21, 19), (3, 19), (3, 7)])


def g_save(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    L(p, 12, 4, 12, 15); L(p, 7, 10, 12, 15); L(p, 17, 10, 12, 15); L(p, 5, 19, 19, 19)


def g_undo(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(9, 6), (5, 10), (9, 14)])
    path = QPainterPath()
    path.moveTo(5, 10); path.lineTo(14, 10)
    path.cubicTo(18, 10, 19.5, 12.5, 19.5, 15)
    path.cubicTo(19.5, 17.5, 18, 19.5, 14, 19.5)
    path.lineTo(9, 19.5)
    p.drawPath(path)


def g_redo(p):
    p.save(); p.translate(24, 0); p.scale(-1, 1); g_undo(p); p.restore()


def g_export(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    L(p, 12, 15, 12, 4); L(p, 8, 8, 12, 4); L(p, 16, 8, 12, 4)
    poly(p, [(5, 12), (5, 20), (19, 20), (19, 12)])


def g_style(p):
    p.setPen(gpen()); p.setBrush(QColor(28, 28, 31))
    L(p, 4, 8, 20, 8); L(p, 4, 16, 20, 16)
    p.drawEllipse(QPointF(9, 8), 2.4, 2.4); p.drawEllipse(QPointF(15, 16), 2.4, 2.4)


def g_font(p):  # big "A" + small "a"
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(3, 19), (8, 5), (13, 19)]); L(p, 4.8, 14, 11.2, 14)
    p.drawEllipse(QPointF(17.5, 15.5), 2.7, 2.7); L(p, 20.2, 12.8, 20.2, 18.2)


def g_clear(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    p.drawEllipse(QPointF(12, 12), 7.5, 7.5); L(p, 7, 17, 17, 7)


def g_x(p):
    p.setPen(gpen()); L(p, 7, 7, 17, 17); L(p, 17, 7, 7, 17)


def g_search(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    p.drawEllipse(QPointF(10.5, 10.5), 6, 6); L(p, 15, 15, 20, 20)


def g_up(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(6, 15), (12, 9), (18, 15)])


def g_down(p):
    p.setPen(gpen()); p.setBrush(NOBRUSH)
    poly(p, [(6, 9), (12, 15), (18, 9)])


def g_note(p):  # three lines, the last one shorter
    p.setPen(gpen()); L(p, 5, 7, 19, 7); L(p, 5, 12, 19, 12); L(p, 5, 17, 13, 17)


def g_icon(kind):
    return lambda p: draw_icon(p, kind, 2, 2, 20)


def g_swatch(col):
    def f(p):
        p.setPen(QPen(QColor(255, 255, 255, 110), 1.5)); p.setBrush(QColor(col))
        p.drawEllipse(QPointF(12, 12), 7.5, 7.5)
    return f


def g_linecolor(get):  # a line segment drawn in the current line colour, inside a rounded box
    def f(p):
        p.setPen(QPen(QColor(255, 255, 255, 110), 1.5)); p.setBrush(NOBRUSH)
        p.drawRoundedRect(QRectF(4.5, 4.5, 15, 15), 4, 4)
        p.setPen(pen(QColor(get()), 3.2, round_=True))
        L(p, 7.5, 16.5, 16.5, 7.5)
    return f


class RailButton(QAbstractButton):
    def __init__(self, glyph, tip, cb=None, parent=None):
        super().__init__(parent)
        self.glyph = glyph
        self.setToolTip(tip)
        self.setFixedSize(34, 34)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover)
        if cb:
            self.clicked.connect(lambda *_: cb())

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.isDown() or self.underMouse():
            p.setPen(NOPEN)
            p.setBrush(QColor(255, 255, 255, 46 if self.isDown() else 24))
            p.drawRoundedRect(QRectF(1, 1, 32, 32), 8, 8)
        p.translate(5, 5)
        self.glyph(p)
        p.end()


class CloseBtn(QAbstractButton):
    def __init__(self):
        super().__init__()
        self.setFixedSize(18, 18)
        self.setToolTip("Close tab (Ctrl+W)")
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.underMouse():
            p.setPen(NOPEN)
            p.setBrush(QColor(255, 255, 255, 40))
            p.drawEllipse(QRectF(1, 1, 16, 16))
        p.setPen(pen(QColor(200, 200, 205), 1.5, round_=True))
        L(p, 6, 6, 12, 12)
        L(p, 12, 6, 6, 12)
        p.end()


class SearchEdit(QLineEdit):
    """Find box. Enter / Down / F3 / Ctrl+G = next, Shift+Enter / Up / Shift+F3 = previous, Esc = close."""
    stepped = Signal(int)
    closed = Signal()

    def focusNextPrevChild(self, nxt):  # keep Tab inside the box
        return False

    def keyPressEvent(self, e):
        K, k = Qt.Key, e.key()
        ctl = bool(e.modifiers() & Qt.KeyboardModifier.ControlModifier)
        back = bool(e.modifiers() & Qt.KeyboardModifier.ShiftModifier)
        if k == K.Key_Escape:
            self.closed.emit()
        elif k in (K.Key_Return, K.Key_Enter, K.Key_F3, K.Key_Up, K.Key_Down) or (ctl and k == K.Key_G):
            self.stepped.emit(-1 if k == K.Key_Up else 1 if k == K.Key_Down else -1 if back else 1)
        elif ctl and k == K.Key_F:
            self.selectAll()
        else:
            super().keyPressEvent(e)
            if not ctl:
                e.accept()  # plain keys (Tab, arrows...) must not reach the map
            return  # unhandled Ctrl shortcuts (Ctrl+S ...) still reach the map
        e.accept()


class SearchBar(QFrame):
    """Floating find bar (Ctrl+F) in the top-right corner of the canvas."""

    def __init__(self, view):
        super().__init__(view)
        self.view = view
        self.setObjectName("search")
        self.setAttribute(Qt.WidgetAttribute.WA_NoMousePropagation)  # clicks on the bar don't hit the map
        self.setStyleSheet(
            "#search{background:#1c1c1f;border:1px solid #2e2e33;border-radius:14px;}"
            "QLineEdit{background:#111113;color:#fff;border:1px solid #3a3a40;border-radius:6px;"
            "padding:2px 8px;font-size:15px;selection-background-color:#3a6ea5;}"
            "QLineEdit:focus{border-color:#fff;}"
            "QLineEdit[bad=\"true\"]{border-color:#ed5454;}"
            "QLabel{color:#8a8a90;font-size:13px;}"
            "QToolTip{background:#2a2a2e;color:#eee;border:1px solid #3a3a40;padding:3px 6px;}")
        lay = QHBoxLayout(self)
        lay.setContentsMargins(10, 6, 8, 6)
        lay.setSpacing(1)
        self.edit = SearchEdit()
        self.edit.setPlaceholderText("Find topic")
        self.edit.setFixedSize(200, 30)
        self.count = QLabel()
        self.count.setFixedWidth(76)
        self.count.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(self.edit)
        lay.addWidget(self.count)
        for glyph, tip, cb in ((g_up, "Previous match (Shift+Enter)", lambda: view.search_step(-1)),
                               (g_down, "Next match (Enter)", lambda: view.search_step(1)),
                               (g_x, "Close (Esc)", view.search_close)):
            lay.addWidget(RailButton(glyph, tip, cb))
        self.edit.textChanged.connect(view.search_set)
        self.edit.stepped.connect(view.search_step)
        self.edit.closed.connect(view.search_close)
        self.hide()

    def open(self):
        self.show()
        self.place()
        self.raise_()
        self.edit.setFocus()
        self.edit.selectAll()

    def place(self):  # just below the toolbar, right-aligned
        v = self.view
        self.adjustSize()
        y = v.rail.geometry().bottom() + 10 if v.rail else 14
        self.move(max(8, v.width() - self.width() - 16), y)

    def set_state(self, text, bad):  # match counter text; red outline when nothing matches
        self.count.setText(text)
        if bool(self.edit.property("bad")) != bad:
            self.edit.setProperty("bad", bad)
            st = self.edit.style()
            st.unpolish(self.edit)
            st.polish(self.edit)


class TabBar(QTabBar):
    middleClicked = Signal(int)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.MiddleButton:
            i = self.tabAt(e.position().toPoint())
            if i >= 0:
                self.middleClicked.emit(i)
                return
        super().mouseReleaseEvent(e)


class Win(QMainWindow):
    def __init__(self):
        super().__init__()
        self.resize(1200, 760)
        self.setMinimumSize(700, 640)
        self.docs, self.cur, self._next_id, self._untitled = {}, None, 1, 0
        self.view = MapView(self)
        v = self.view

        central = QWidget()
        cl = QVBoxLayout(central)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)
        cl.addWidget(v, 1)
        bar = QFrame()
        bar.setObjectName("tabbar")
        bar.setFixedHeight(34)
        bar.setStyleSheet("#tabbar{background:#0d0d0d;border-top:1px solid #26262a;}")
        bl = QHBoxLayout(bar)
        bl.setContentsMargins(10, 0, 10, 0)
        bl.setSpacing(4)
        self.tabs = TabBar()
        self.tabs.setShape(QTabBar.Shape.RoundedSouth)
        self.tabs.setExpanding(False)
        self.tabs.setMovable(True)
        self.tabs.setDrawBase(False)
        self.tabs.setUsesScrollButtons(True)
        self.tabs.setElideMode(Qt.TextElideMode.ElideRight)
        self.tabs.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.tabs.setStyleSheet(
            "QTabBar{background:transparent;}"
            "QTabBar::tab{background:#151518;color:#8a8a90;padding:6px 10px 6px 14px;margin:0 3px 0 0;"
            "border:1px solid #26262a;border-top:none;border-bottom-left-radius:8px;"
            "border-bottom-right-radius:8px;min-width:90px;max-width:220px;font-size:13px;}"
            "QTabBar::tab:selected{background:#26262b;color:#f2f2f4;}"
            "QTabBar::tab:hover:!selected{background:#1c1c20;color:#d0d0d5;}"
            "QToolTip{background:#2a2a2e;color:#eee;border:1px solid #3a3a40;padding:3px 6px;}")
        self.tabs.currentChanged.connect(self.on_tab_changed)
        self.tabs.middleClicked.connect(lambda i: self.close_id(self.tabs.tabData(i)))
        bl.addWidget(self.tabs)
        bl.addWidget(RailButton(g_plus, "New tab (Ctrl+T)", self.new))
        bl.addStretch(1)
        cl.addWidget(bar)
        self.setCentralWidget(central)

        rail = QFrame(v)
        rail.setObjectName("rail")
        rail.setStyleSheet("#rail{background:#1c1c1f;border:1px solid #2e2e33;border-radius:14px;}"
                           "QToolTip{background:#2a2a2e;color:#eee;border:1px solid #3a3a40;padding:3px 6px;}")
        lay = QHBoxLayout(rail)
        lay.setContentsMargins(8, 6, 8, 6)
        lay.setSpacing(1)

        def add(glyph, tip, cb):
            b = RailButton(glyph, tip, cb)
            lay.addWidget(b)
            return b

        def sep():
            f = QFrame()
            f.setFixedSize(1, 20)
            f.setStyleSheet("background:#33333a;")
            lay.addSpacing(4)
            lay.addWidget(f, 0, Qt.AlignmentFlag.AlignVCenter)
            lay.addSpacing(4)

        add(g_new, "New tab (Ctrl+N)", self.new)
        add(g_open, "Open (Ctrl+O)", self.open)
        add(g_save, "Save (Ctrl+S)", self.save)
        add(g_export, "Export PNG / SVG / PDF (Ctrl+E)", self.export)
        add(g_search, "Search (Ctrl+F)", v.search_open)
        add(g_note, "Note on selected topic (key N)", v.toggle_note)
        sep()
        add(g_undo, "Undo (Ctrl+Z)", v.undo_op)
        add(g_redo, "Redo (Ctrl+Y)", v.redo_op)
        sep()
        self.line_btn = add(g_linecolor(lambda: v.line_color), "Line colour (all mindmap lines)", self.pick_line_color)
        for i, (name, h) in enumerate(COLORS):
            add(g_swatch(h), f"{name} {h} (key {i + 1})", lambda h=h: v.set_color(h))
        add(g_clear, "Clear colour (key 0)", lambda: v.set_color(None))
        sep()
        add(g_icon("check"), "Done icon (key C)", lambda: v.toggle_icon("check"))
        add(g_icon("error"), "Error icon (key X)", lambda: v.toggle_icon("error"))
        add(g_x, "Remove icon (key R)", v.clear_icon)
        #add(g_note, "Note on selected topic (key N)", v.toggle_note)
        sep()
        self.style_btn = add(g_style, "Layout, shape and branch lines", self.show_style_menu)
        add(g_font, "Font", self.pick_font)

        self.menu = QMenu(self)
        self.menu.setStyleSheet("QMenu{font-size:18px;} QMenu::item{padding:8px 28px 8px 20px;}")  # menu text size
        self.acts = {}
        for title, items, attr in (("Layout", ["Map", "Logic chart"], "layout_mode"),
                                   ("Topic shape", SHAPES, "shape"), ("Branch lines", LINES, "line")):
            sub = self.menu.addMenu(title)
            grp = QActionGroup(sub)
            grp.setExclusive(True)
            self.acts[attr] = {}
            for it in items:
                a = sub.addAction(it)
                a.setCheckable(True)
                grp.addAction(a)
                a.triggered.connect(lambda _c=False, it=it, attr=attr: self.set_style(attr, it))
                self.acts[attr][it] = a

        rail.adjustSize()
        v.rail = rail
        rail.move((v.width() - rail.width()) // 2, 14)
        self.sync_controls()
        d = Doc()
        v.capture(d)  # the first tab holds the starting map already on the canvas
        d.untitled = self.next_untitled()
        self.tabs.blockSignals(True)
        self.add_tab(d)
        self.tabs.blockSignals(False)
        self.cur = d.id
        self.update_title()

    def pick_line_color(self):  # one colour for every line of the current mindmap; saved with the file
        v = self.view
        c = QColorDialog.getColor(QColor(v.line_color), self, "Line colour")
        if c.isValid() and c.name() != QColor(v.line_color).name():
            v.line_color = c.name()
            v.set_dirty(True)
            v.update()
        self.line_btn.update()
        v.setFocus()

    def pick_font(self):  # choose any installed font for all topics; remembered between runs
        dlg = QDialog(self)
        dlg.setWindowTitle("Font")
        dlg.setMinimumWidth(340)
        lay = QVBoxLayout(dlg)
        lay.addWidget(QLabel("Font for topics"))
        combo = QFontComboBox()
        combo.setCurrentFont(QFont(FAMILIES[0]))
        lay.addWidget(combo)
        B = QDialogButtonBox.StandardButton
        bb = QDialogButtonBox(B.Ok | B.Cancel | B.RestoreDefaults)
        lay.addWidget(bb)
        reset = []

        def on_click(b):
            if bb.buttonRole(b) == QDialogButtonBox.ButtonRole.ResetRole:
                reset.append(1)
                dlg.accept()

        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        bb.clicked.connect(on_click)
        if not dlg.exec():
            self.view.setFocus()
            return
        fam = None if reset else combo.currentFont().family()
        use_family(fam)
        QSettings("xmap", "xmap").setValue("font", fam or "")
        self.view.refont()
        self.view.setFocus()

    def show_style_menu(self):
        b = self.style_btn
        self.menu.exec(b.mapToGlobal(QPoint(0, b.height() + 8)))

    def set_style(self, attr, val):
        v = self.view
        if getattr(v, attr) == val:
            return
        setattr(v, attr, val)
        v.set_dirty(True)
        if attr == "layout_mode":
            v.relayout()
            v.fit_now()
        else:
            v.update()

    def update_title(self):
        d = self.docs.get(self.cur)
        if d is None:
            self.setWindowTitle("xmap")
            return
        v = self.view
        label = f"{d.name(v.path)}{' *' if v.dirty else ''}"
        self.setWindowTitle(f"{label} - xmap")
        i = self.tab_index(self.cur)
        if i >= 0:
            self.tabs.setTabText(i, label)
            self.tabs.setTabToolTip(i, v.path or d.name(v.path))

    def sync_controls(self):
        v = self.view
        if hasattr(self, "line_btn"):
            self.line_btn.update()
        for attr, acts in self.acts.items():
            acts[getattr(v, attr)].setChecked(True)

    # ---------- tabs ----------
    def next_untitled(self):
        self._untitled += 1
        return self._untitled

    def tab_index(self, id):
        for i in range(self.tabs.count()):
            if self.tabs.tabData(i) == id:
                return i
        return -1

    def add_tab(self, d):
        d.id = self._next_id
        self._next_id += 1
        self.docs[d.id] = d
        prev = self.tabs.blockSignals(True)  # the tab's id isn't attached yet
        i = self.tabs.addTab(d.name())
        self.tabs.setTabData(i, d.id)
        self.tabs.blockSignals(prev)
        b = CloseBtn()
        b.clicked.connect(lambda _=False, id=d.id: self.close_id(id))
        self.tabs.setTabButton(i, QTabBar.ButtonPosition.RightSide, b)
        self.tabs.setTabToolTip(i, d.name())
        return i

    def snapshot(self):  # copy the live canvas state back into the current tab's document
        d = self.docs.get(self.cur)
        if d:
            self.view.commit_edit()
            self.view.capture(d)

    def on_tab_changed(self, i):
        if i < 0:
            return
        id = self.tabs.tabData(i)
        if id == self.cur or id not in self.docs:
            return
        self.snapshot()
        self.cur = id
        self.view.apply(self.docs[id])
        self.view.setFocus()

    def show_doc(self, d):
        i = self.add_tab(d)
        self.tabs.setCurrentIndex(i)
        self.on_tab_changed(i)  # also covers the case where the bar was empty
        self.save_session()

    # ---------- remember open files between runs ----------
    _restoring = False

    def save_session(self):
        if self._restoring:
            return
        files, cur = [], None
        for i in range(self.tabs.count()):
            id = self.tabs.tabData(i)
            d = self.docs.get(id)
            if d is None:
                continue
            path = self.view.path if id == self.cur else d.path  # live canvas holds the current tab's path
            if path:
                files.append(os.path.abspath(path))
                if id == self.cur:
                    cur = files[-1]
        QSettings("xmap", "xmap").setValue("session", json.dumps({"files": files, "current": cur}))

    def restore_session(self):
        try:
            data = json.loads(QSettings("xmap", "xmap").value("session", "") or "{}")
            files, cur = data.get("files", []), data.get("current")
        except (ValueError, AttributeError):
            return
        self._restoring = True
        try:
            for p in files:
                if os.path.isfile(p):  # files that were moved/deleted are skipped silently
                    self.open_path(p)
            if cur and os.path.isfile(cur):
                self.open_path(cur)  # already open -> just switches to that tab
        finally:
            self._restoring = False
        self.save_session()

    def next_tab(self, step):
        n = self.tabs.count()
        if n > 1:
            self.tabs.setCurrentIndex((self.tabs.currentIndex() + step) % n)

    def close_current(self):
        self.close_id(self.cur)

    def close_id(self, id):
        if id == self.cur:
            self.snapshot()
        d = self.docs.get(id)
        if d is None:
            return
        if d.dirty:
            B = QMessageBox.StandardButton
            r = QMessageBox.question(self, "xmap", f'Discard unsaved changes in "{d.name()}"?',
                                     B.Discard | B.Cancel, B.Cancel)
            if r != B.Discard:
                return
        i = self.tab_index(id)
        if id == self.cur:
            self.cur = None
        del self.docs[id]
        self.tabs.removeTab(i)
        if self.tabs.count() == 0:
            self.new()
        self.view.setFocus()
        self.save_session()

    def closeEvent(self, e):
        self.snapshot()
        n = sum(1 for d in self.docs.values() if d.dirty)
        if n:
            B = QMessageBox.StandardButton
            msg = f"{n} tab{'s have' if n > 1 else ' has'} unsaved changes. Discard?"
            if QMessageBox.question(self, "xmap", msg, B.Discard | B.Cancel, B.Cancel) != B.Discard:
                e.ignore()
                return
        self.save_session()
        e.accept()

    def new(self):
        d = Doc()
        d.untitled = self.next_untitled()
        self.show_doc(d)

    def open(self):
        ps, _ = QFileDialog.getOpenFileNames(self, "Open", "", "Mind maps (*.json);;All files (*)")
        for p in ps:
            self.open_path(p)

    def open_path(self, p):
        p = os.path.abspath(p)
        self.snapshot()
        for d in self.docs.values():  # already open: just switch to it
            if d.path and os.path.abspath(d.path) == p:
                self.tabs.setCurrentIndex(self.tab_index(d.id))
                return
        try:
            with open(p, encoding="utf-8") as f:
                data = json.load(f)
            root = Node.from_dict(data["root"])
        except (OSError, ValueError, KeyError, AttributeError) as ex:
            QMessageBox.warning(self, "xmap", f"Couldn't open that file.\n{ex}")
            return
        cur = self.docs.get(self.cur)
        if cur and not cur.path and not cur.dirty and not cur.undo:  # reuse an untouched Untitled tab
            self.view.load(data, p)
            return
        self.show_doc(Doc(root, data.get("layout", "Map"), data.get("shape", "Square"),
                          data.get("line", "Straight"), p, data.get("line_color", DEFAULT_LINE)))

    def save(self):
        if self.view.path:
            self.view.write(self.view.path)
        else:
            self.save_as()

    def save_as(self):
        p, _ = QFileDialog.getSaveFileName(self, "Save", "mindmap.json", "Mind maps (*.json);;All files (*)")
        if p:
            try:
                self.view.write(p)
                self.save_session()
            except OSError as ex:
                QMessageBox.warning(self, "xmap", f"Couldn't save the file.\n{ex}")

    def export(self):
        p, _ = QFileDialog.getSaveFileName(self, "Export", "mindmap.png", "PNG (*.png);;SVG (*.svg);;PDF (*.pdf)")
        if p:
            try:
                self.view.export(p if "." in os.path.basename(p) else p + ".png")
            except OSError as ex:
                QMessageBox.warning(self, "xmap", f"Couldn't export the file.\n{ex}")


def dark_palette():
    pal = QPalette()
    C, R = QColor, QPalette.ColorRole
    for role, col in ((R.Window, "#1c1c1f"), (R.WindowText, "#e8e8ea"), (R.Base, "#141416"),
                      (R.AlternateBase, "#1c1c1f"), (R.Text, "#e8e8ea"), (R.Button, "#2a2a2e"),
                      (R.ButtonText, "#e8e8ea"), (R.Highlight, "#3a6ea5"), (R.HighlightedText, "#ffffff"),
                      (R.ToolTipBase, "#2a2a2e"), (R.ToolTipText, "#e8e8ea"), (R.PlaceholderText, "#8a8a90")):
        pal.setColor(role, C(col))
    return pal


def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setPalette(dark_palette())
    fam = str(QSettings("xmap", "xmap").value("font", "") or "")
    if fam:
        use_family(fam)
    w = Win()
    if fam:
        w.view.refont()  # also gives the edit box the saved font
    w.restore_session()  # reopen the files that were open last time
    for a in sys.argv[1:]:
        if os.path.isfile(a):
            w.open_path(a)
    w.show()
    w.view.setFocus()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()