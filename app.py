#!/usr/bin/env python3
"""
Day Planner v10 — Layout, GUI & Workflow Overhaul.

Improvements:
- Minimalist monochrome base with support for custom schemes (Light, Dark, Sepia, Nordic).
- Custom Accent and Category colors.
- Side-by-side column layout for overlapping tasks in the Day Timeline.
- Auto-advance task selection upon completion.
- Keyboard nudging (Shift time: Ctrl+Shift+Up/Down, Shift day: Ctrl+Shift+Left/Right).
- Quick-schedule from backlog to the next available free slot.
- Upgraded context menus for fast time/day shifting.
- Unified Command Palette (Ctrl+K) that searches both actions and tasks.
- Visual progress ring in Focus Mode.
- Grouped deadlines dialog (Overdue, Today, Tomorrow, Upcoming).
"""

from __future__ import annotations

import csv
import json
import math
import re
import shutil
import sqlite3
import sys
import time
import uuid
from dataclasses import asdict, dataclass, field, fields
from functools import partial
from pathlib import Path

from PySide6.QtCore import (QDate, QDateTime, QMimeData, QPoint, QPointF,
                            QRectF, QSettings, QSize, Qt, QTime, QTimer, Signal)
from PySide6.QtGui import (QAction, QActionGroup, QColor, QDrag, QFont, QIcon,
                           QKeySequence, QPainter, QPalette, QPen, QPixmap,
                           QShortcut, QUndoCommand, QUndoStack)
from PySide6.QtWidgets import (
    QAbstractItemView, QApplication, QCheckBox, QColorDialog, QComboBox, QDialog,
    QDialogButtonBox, QDateEdit, QFileDialog, QFormLayout, QFrame,
    QHBoxLayout, QInputDialog, QLabel, QLineEdit, QListWidget, QListWidgetItem,
    QMainWindow, QMenu, QMessageBox, QPlainTextEdit, QPushButton, QScrollArea,
    QSizePolicy, QSpinBox, QSplitter, QStackedWidget, QStatusBar, QSystemTrayIcon,
    QTimeEdit, QToolBar, QToolButton, QVBoxLayout, QWidget,
)

# ----------------------------------------------------------------- constants
APP_TITLE = "Day Planner"
STORE_DB = Path.home() / ".day_planner.db"
LEGACY_JSON = Path.home() / ".day_planner.json"
SEED_DEMO_TASKS = True

DEFAULT_CATEGORIES = {
    "Work": "#3a3a3a",
    "Personal": "#6b6b6b",
    "Health": "#3a5a3a",
    "Learning": "#3a3a5a",
    "Other": "#9a9a9a",
}
CATEGORIES = DEFAULT_CATEGORIES.copy()
ACCENT_COLOR = "#1a1a1a"

PRIORITIES = [("low", "Low"), ("med", "Medium"), ("high", "High")]
RECURRENCE = [("none", "Doesn't repeat"), ("daily", "Daily"),
              ("weekdays", "Every weekday (Mon–Fri)"), ("weekly", "Weekly")]

HOUR_H = 56
PX_PER_MIN = HOUR_H / 60.0
LABEL_W = 58
DAY_HOURS = 24
DAY_MINUTES = DAY_HOURS * 60
MIME_TASK = "application/x-dayplanner-task"
ICS_EXPAND_CAP = 400
ICS_EXPAND_HORIZON = 730

IDLE_ACTIVE_SEC = 90
ACTIVITY_KEEP_DAYS = 730

# Configurable constants (defaults)
WORK_START = 8
WORK_END = 18
NOTIFY_LEAD_MIN = 10
POMODORO_WORK_MIN = 25
POMODORO_BREAK_MIN = 5
SNAP_MIN = 5
PLAN_BUFFER_MIN = 5


def fmt_minutes(m: int) -> str:
    h, mm = divmod(int(m), 60)
    return f"{h}h {mm:02d}m" if h else f"{mm}m"


def mm_to_str(m: int) -> str:
    return f"{int(m) // 60:02d}:{int(m) % 60:02d}"


def rec_label(key: str) -> str:
    return dict(RECURRENCE).get(key, key)


def is_instance(task_id: str) -> bool:
    return "@" in task_id


def base_id(task_id: str) -> str:
    return task_id.split("@", 1)[0]


def _safe_int(v, default: int) -> int:
    try:
        return int(str(v).strip())
    except (TypeError, ValueError):
        return default


def parse_tags(text: str) -> list[str]:
    return [x.strip().lstrip("#") for x in (text or "").split(",")
            if x.strip()]


# ----------------------------------------------------------------- idle monitor
class IdleMonitor:
    def __init__(self):
        self.available = False
        self._mode: str | None = None
        self._quartz = None
        self._x11 = self._xss = self._disp = self._root = self._info = None
        if sys.platform.startswith("win"):
            self._mode = "win"
            self.available = True
        elif sys.platform == "darwin":
            try:
                import Quartz
                self._quartz = Quartz
                self._mode = "mac"
                self.available = True
            except Exception:
                pass
        else:
            try:
                self._init_x11()
                self._mode = "x11"
                self.available = True
            except Exception:
                pass

    def _init_x11(self):
        import ctypes

        class XScreenSaverInfo(ctypes.Structure):
            _fields_ = [("window", ctypes.c_ulong), ("state", ctypes.c_int),
                        ("kind", ctypes.c_int), ("til_or_since", ctypes.c_ulong),
                        ("idle", ctypes.c_ulong), ("eventMask", ctypes.c_ulong)]

        for name in ("libX11.so.6", "libX11.so"):
            try:
                self._x11 = ctypes.CDLL(name)
                break
            except OSError:
                continue
        else:
            raise OSError("libX11 not found")
        for name in ("libXss.so.1", "libXss.so"):
            try:
                self._xss = ctypes.CDLL(name)
                break
            except OSError:
                continue
        else:
            raise OSError("libXss not found")
        self._x11.XOpenDisplay.restype = ctypes.c_void_p
        self._x11.XOpenDisplay.argtypes = [ctypes.c_char_p]
        self._disp = self._x11.XOpenDisplay(None)
        if not self._disp:
            raise OSError("cannot open display")
        self._x11.XDefaultRootWindow.restype = ctypes.c_void_p
        self._x11.XDefaultRootWindow.argtypes = [ctypes.c_void_p]
        self._root = self._x11.XDefaultRootWindow(self._disp)
        self._xss.XScreenSaverAllocInfo.restype = ctypes.POINTER(XScreenSaverInfo)
        self._info = self._xss.XScreenSaverAllocInfo()
        self._xss.XScreenSaverQueryInfo.argtypes = [
            ctypes.c_void_p, ctypes.c_void_p, ctypes.POINTER(XScreenSaverInfo)]

    def idle_seconds(self) -> float | None:
        try:
            if self._mode == "win":
                import ctypes

                class LASTINPUTINFO(ctypes.Structure):
                    _fields_ = [("cbSize", ctypes.c_uint),
                                ("dwTime", ctypes.c_uint)]

                lii = LASTINPUTINFO()
                lii.cbSize = ctypes.sizeof(LASTINPUTINFO)
                if ctypes.windll.user32.GetLastInputInfo(ctypes.byref(lii)):
                    return (ctypes.windll.kernel32.GetTickCount()
                            - lii.dwTime) / 1000.0
                return None
            if self._mode == "mac":
                return float(self._quartz.CGEventSourceSecondsSinceLastEventType(
                    self._quartz.kCGEventSourceStateCombinedSessionState, -1))
            if self._mode == "x11":
                if self._xss.XScreenSaverQueryInfo(
                        self._disp, self._root, self._info):
                    return self._info.contents.idle / 1000.0
        except Exception:
            pass
        return None


# ----------------------------------------------------------------- data model
@dataclass
class Task:
    id: str
    title: str
    date: str = ""
    start: str = "09:00"
    duration: int = 30
    category: str = "Other"
    priority: str = "med"
    notes: str = ""
    completed: bool = False
    recurrence: str = "none"
    deadline: str = ""
    until: str = ""
    tags: list = field(default_factory=list)
    subtasks: list = field(default_factory=list)
    ex_dates: list = field(default_factory=list)
    done_dates: list = field(default_factory=list)
    work_dates: dict = field(default_factory=dict)
    recurring_instance: bool = False

    @property
    def start_minutes(self) -> int:
        h, m = self.start.split(":")
        return int(h) * 60 + int(m)

    @start_minutes.setter
    def start_minutes(self, value: int):
        value = max(0, min(int(value), DAY_MINUTES - 1))
        self.start = f"{value // 60:02d}:{value % 60:02d}"

    @property
    def end_minutes(self) -> int:
        return self.start_minutes + self.duration

    @property
    def end(self) -> str:
        e = min(self.end_minutes, DAY_MINUTES)
        return f"{e // 60:02d}:{e % 60:02d}"

    @property
    def time_range(self) -> str:
        return f"{self.start}–{self.end}"

    @property
    def duration_label(self) -> str:
        return fmt_minutes(self.duration)

    def worked_on(self, date_key: str) -> int:
        return int((self.work_dates or {}).get(date_key, 0))

    @property
    def sub_done(self) -> tuple[int, int]:
        st = self.subtasks or []
        return sum(1 for s in st if s.get("done")), len(st)

    @staticmethod
    def from_dict(d: dict) -> "Task":
        known = {f.name for f in fields(Task)}
        return Task(**{k: v for k, v in d.items() if k in known})


def deadline_badge(t: Task) -> tuple[str, QColor] | None:
    if not t.deadline or t.completed:
        return None
    d = QDate.fromString(t.deadline, "yyyy-MM-dd")
    if not d.isValid():
        return None
    days = QDate.currentDate().daysTo(d)
    if days < 0:
        return (f"{-days}d late", QColor(ACCENT_COLOR))
    if days == 0:
        return ("due now", QColor(ACCENT_COLOR))
    if days == 1:
        return ("tmrw", QColor("#555555"))
    if days <= 7:
        return (f"{days}d", QColor("#888888"))
    return (d.toString("d MMM"), QColor("#aaa"))


def deadline_span_html(t: Task) -> str:
    if not t.deadline:
        return ""
    d = QDate.fromString(t.deadline, "yyyy-MM-dd")
    if not d.isValid():
        return ""
    if t.completed:
        return f" · <span style='color:#aaa;'>⚑ {d.toString('d MMM')}</span>"
    days = QDate.currentDate().daysTo(d)
    if days < 0:
        return f" · <span style='color:{ACCENT_COLOR};'><b>⚑ {-days}d overdue</b></span>"
    if days == 0:
        return f" · <span style='color:{ACCENT_COLOR};'><b>⚑ today</b></span>"
    if days == 1:
        return " · <span style='color:#555;'>⚑ tomorrow</span>"
    if days <= 7:
        return f" · <span style='color:#888;'>⚑ {days}d</span>"
    return f" · <span style='color:#aaa;'>⚑ {d.toString('d MMM')}</span>"


def matches_recurrence(t: Task, qdate: QDate) -> bool:
    anchor = QDate.fromString(t.date, "yyyy-MM-dd")
    if not anchor.isValid() or qdate < anchor:
        return False
    if t.until:
        u = QDate.fromString(t.until, "yyyy-MM-dd")
        if u.isValid() and qdate > u:
            return False
    if t.recurrence == "daily":
        return True
    if t.recurrence == "weekdays":
        return 1 <= qdate.dayOfWeek() <= 5
    if t.recurrence == "weekly":
        return qdate.dayOfWeek() == anchor.dayOfWeek()
    return False


def materialize(t: Task, date_key: str) -> Task | None:
    if t.recurrence == "none" or date_key in (t.ex_dates or []):
        return None
    qd = QDate.fromString(date_key, "yyyy-MM-dd")
    if not qd.isValid() or not matches_recurrence(t, qd):
        return None
    inst = Task(**{**asdict(t), "id": f"{t.id}@{date_key}", "date": date_key})
    inst.recurring_instance = True
    return inst


# ----------------------------------------------------------------- store (SQLite)
class TaskStore:
    def __init__(self, db_path: Path, legacy_json: Path):
        self.path = db_path
        self.legacy_json = legacy_json
        self.tasks: list[Task] = []
        self.settings: dict = {"dark": False, "reminders": True, "track": True,
                               "close_to_tray": True, "eod_hour": 18,
                               "templates": []}
        db_existed = self.path.exists()
        self._conn = sqlite3.connect(str(self.path))
        self._init_db()
        if not db_existed and self.legacy_json.exists():
            self._import_legacy_json()
            self.fresh_file = False
        else:
            self.fresh_file = not db_existed
        self.load()

    def _init_db(self):
        self._conn.execute("PRAGMA journal_mode=WAL;")
        self._conn.execute("PRAGMA synchronous=NORMAL;")
        self._conn.executescript("""
            CREATE TABLE IF NOT EXISTS tasks (
                id TEXT PRIMARY KEY, title TEXT NOT NULL DEFAULT '', date TEXT NOT NULL DEFAULT '',
                start TEXT NOT NULL DEFAULT '09:00', duration INTEGER NOT NULL DEFAULT 30,
                category TEXT NOT NULL DEFAULT 'Other', priority TEXT NOT NULL DEFAULT 'med',
                notes TEXT NOT NULL DEFAULT '', completed INTEGER NOT NULL DEFAULT 0,
                recurrence TEXT NOT NULL DEFAULT 'none', deadline TEXT NOT NULL DEFAULT '',
                ex_dates TEXT NOT NULL DEFAULT '[]', done_dates TEXT NOT NULL DEFAULT '[]',
                work_dates TEXT NOT NULL DEFAULT '{}', updated_at REAL NOT NULL DEFAULT 0
            );
            CREATE INDEX IF NOT EXISTS idx_tasks_date ON tasks(date);
            CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS activity (
                date TEXT NOT NULL, minute INTEGER NOT NULL, active INTEGER NOT NULL DEFAULT 1,
                PRIMARY KEY (date, minute)
            );
            CREATE INDEX IF NOT EXISTS idx_activity_date ON activity(date);
            CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
        """)
        cols = {r[1] for r in self._conn.execute("PRAGMA table_info(tasks)")}
        for col, decl in (("deadline", "TEXT NOT NULL DEFAULT ''"), ("until", "TEXT NOT NULL DEFAULT ''"),
                          ("tags", "TEXT NOT NULL DEFAULT '[]'"), ("subtasks", "TEXT NOT NULL DEFAULT '[]'"),
                          ("work_dates", "TEXT NOT NULL DEFAULT '{}'")):
            if col not in cols:
                self._conn.execute(f"ALTER TABLE tasks ADD COLUMN {col} {decl}")
        row = self._conn.execute("SELECT value FROM meta WHERE key='schema_version'").fetchone()
        if not row:
            self._conn.execute("INSERT INTO meta(key,value) VALUES('schema_version','1')")
        self._conn.commit()

    def _import_legacy_json(self):
        try:
            raw = json.loads(self.legacy_json.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                self.tasks = [Task.from_dict(d) for d in raw.get("tasks", [])]
                st = raw.get("settings", {})
                if isinstance(st, dict): self.settings.update(st)
            else:
                self.tasks = [Task.from_dict(d) for d in raw]
            self.save()
            for t in self.tasks: self.upsert_task(t)
            try:
                self.legacy_json.rename(self.legacy_json.with_name(self.legacy_json.name + ".bak"))
            except OSError: pass
        except Exception as exc:
            print(f"Legacy import failed: {exc}", file=sys.stderr)

    def load(self):
        try:
            rows = self._conn.execute(
                "SELECT id,title,date,start,duration,category,priority,notes,completed,recurrence,deadline,until,tags,subtasks,ex_dates,done_dates,work_dates FROM tasks").fetchall()
            for k, v in self._conn.execute("SELECT key,value FROM settings"):
                try: self.settings[k] = json.loads(v)
                except: self.settings[k] = v
        except sqlite3.Error as exc:
            print(f"DB load failed: {exc}", file=sys.stderr); return
        self.tasks = []
        for r in rows:
            try:
                self.tasks.append(Task(id=r[0], title=r[1], date=r[2], start=r[3], duration=int(r[4]),
                    category=r[5], priority=r[6], notes=r[7], completed=bool(r[8]), recurrence=r[9],
                    deadline=r[10], until=r[11], tags=json.loads(r[12]), subtasks=json.loads(r[13]),
                    ex_dates=json.loads(r[14]), done_dates=json.loads(r[15]), work_dates=json.loads(r[16]) or {}))
            except Exception as exc:
                print(f"Skipping bad row {r[0]}: {exc}", file=sys.stderr)

    def save(self):
        try:
            self._conn.execute("DELETE FROM settings")
            self._conn.executemany("INSERT INTO settings (key,value) VALUES (?,?)", [(k, json.dumps(v)) for k, v in self.settings.items()])
            self._conn.commit()
        except sqlite3.Error as exc:
            print(f"DB save failed: {exc}", file=sys.stderr)

    def upsert_task(self, t: Task):
        self._conn.execute("""
            INSERT INTO tasks (id,title,date,start,duration,category,priority,notes,completed,recurrence,deadline,until,tags,subtasks,ex_dates,done_dates,work_dates,updated_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(id) DO UPDATE SET
                title=excluded.title, date=excluded.date, start=excluded.start, duration=excluded.duration,
                category=excluded.category, priority=excluded.priority, notes=excluded.notes, completed=excluded.completed,
                recurrence=excluded.recurrence, deadline=excluded.deadline, until=excluded.until, tags=excluded.tags,
                subtasks=excluded.subtasks, ex_dates=excluded.ex_dates, done_dates=excluded.done_dates,
                work_dates=excluded.work_dates, updated_at=excluded.updated_at
        """, (t.id, t.title, t.date, t.start, int(t.duration), t.category, t.priority, t.notes, int(t.completed),
              t.recurrence, t.deadline, t.until, json.dumps(t.tags or []), json.dumps(t.subtasks or []),
              json.dumps(t.ex_dates or []), json.dumps(t.done_dates or []), json.dumps(t.work_dates or {}), time.time()))
        self._conn.commit()

    def delete_task(self, task_id: str):
        self._conn.execute("DELETE FROM tasks WHERE id=?", (task_id,))
        self._conn.commit()

    def close(self): self._conn.close()

    def record_active(self, date_key: str, minute: int):
        try:
            self._conn.execute("INSERT OR REPLACE INTO activity VALUES (?,?,1)", (date_key, int(minute)))
            self._conn.commit()
        except sqlite3.Error: pass

    def activity_minutes(self, date_key: str) -> set[int]:
        try:
            rows = self._conn.execute("SELECT minute FROM activity WHERE date=? AND active=1", (date_key,)).fetchall()
            return {int(r[0]) for r in rows}
        except sqlite3.Error: return set()

    def activity_between(self, start_key: str, end_key: str) -> dict[str, int]:
        try:
            rows = self._conn.execute("SELECT date, COUNT(*) FROM activity WHERE active=1 AND date>=? AND date<=? GROUP BY date", (start_key, end_key)).fetchall()
            return {r[0]: int(r[1]) for r in rows}
        except sqlite3.Error: return {}

    def prune_activity(self, keep_days: int):
        cutoff = QDate.currentDate().addDays(-keep_days).toString("yyyy-MM-dd")
        try:
            self._conn.execute("DELETE FROM activity WHERE date < ?", (cutoff,))
            self._conn.commit()
        except sqlite3.Error: pass

    def add(self, task: Task): self.tasks.append(task)
    def get(self, task_id: str): return next((t for t in self.tasks if t.id == task_id), None)
    def remove(self, task_id: str): self.tasks = [t for t in self.tasks if t.id != task_id]
    def replace(self, task_id: str, task: Task):
        for i, t in enumerate(self.tasks):
            if t.id == task_id: self.tasks[i] = task; return

    def search(self, query: str, limit: int = 500) -> list[Task]:
        q = query.strip()
        if not q: return []
        esc = q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
        pat = f"%{esc}%"
        try:
            rows = self._conn.execute("SELECT id FROM tasks WHERE title LIKE ? ESCAPE '\\' OR notes LIKE ? ESCAPE '\\' OR category LIKE ? ESCAPE '\\' OR tags LIKE ? ESCAPE '\\' ORDER BY date DESC, start LIMIT ?", (pat, pat, pat, pat, limit)).fetchall()
        except sqlite3.Error: return []
        by_id = {t.id: t for t in self.tasks}
        return [by_id[r[0]] for r in rows if r[0] in by_id]


# ----------------------------------------------------------------- ICS helpers
_ICS_WD = {"MO": 1, "TU": 2, "WE": 3, "TH": 4, "FR": 5, "SA": 6, "SU": 7}
_ICS_WD_REV = {v: k for k, v in _ICS_WD.items()}

def _ics_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace(";", "\\;").replace(",", "\\,").replace("\n", "\\n")

def _ics_unescape(text: str) -> str:
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c == "\\" and i + 1 < len(text):
            n = text[i + 1]
            out.append("\n" if n in ("n", "N") else n); i += 2
        else: out.append(c); i += 1
    return "".join(out)

def _ics_fold(line: str) -> str:
    chunks, s, first = [], line, True
    while len(s) > 74:
        cut = 74 if first else 73
        chunks.append(s[:cut]); s = " " + s[cut:]; first = False
    chunks.append(s)
    return "\r\n".join(chunks)

def _ics_dt(qdate: QDate, minutes: int) -> str:
    return f"{qdate.toString('yyyyMMdd')}T{minutes // 60:02d}{minutes % 60:02d}00"

def build_ics(tasks: list[Task]) -> str:
    stamp = QDateTime.currentDateTimeUtc().toString("yyyyMMdd'T'HHmmss'Z'")
    lines = ["BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//Day Planner//PySide6//EN", "CALSCALE:GREGORIAN"]
    for t in tasks:
        if not t.date: continue
        qd = QDate.fromString(t.date, "yyyy-MM-dd")
        if not qd.isValid(): continue
        end_total = t.end_minutes
        end_date, end_min = ((qd.addDays(1), 0) if end_total >= DAY_MINUTES else (qd, end_total))
        lines += ["BEGIN:VEVENT", f"UID:{t.id}@dayplanner.local", f"DTSTAMP:{stamp}",
                  f"DTSTART:{_ics_dt(qd, t.start_minutes)}", f"DTEND:{_ics_dt(end_date, end_min)}",
                  f"SUMMARY:{_ics_escape(t.title)}"]
        if t.notes: lines.append(f"DESCRIPTION:{_ics_escape(t.notes)}")
        lines.append(f"CATEGORIES:{_ics_escape(t.category)}")
        rule = ""
        if t.recurrence == "daily": rule = "RRULE:FREQ=DAILY"
        elif t.recurrence == "weekdays": rule = "RRULE:FREQ=WEEKLY;BYDAY=MO,TU,WE,TH,FR"
        elif t.recurrence == "weekly": rule = "RRULE:FREQ=WEEKLY"
        if rule and t.until:
            u = QDate.fromString(t.until, "yyyy-MM-dd")
            if u.isValid(): rule += f";UNTIL={u.toString('yyyyMMdd')}T235900"
        if rule: lines.append(rule)
        for ex in (t.ex_dates or []):
            exd = QDate.fromString(ex, "yyyy-MM-dd")
            if exd.isValid(): lines.append(f"EXDATE:{_ics_dt(exd, t.start_minutes)}")
        lines.append("END:VEVENT")
    lines.append("END:VCALENDAR")
    return "\r\n".join(_ics_fold(ln) for ln in lines) + "\r\n"

def _parse_ics_events(text: str) -> list[dict]:
    lines: list[str] = []
    for raw in text.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        if raw[:1] in (" ", "\t") and lines: lines[-1] += raw[1:]
        else: lines.append(raw)
    events, cur = [], None
    for line in lines:
        if ":" not in line: continue
        head, _, value = line.partition(":")
        name = head.split(";", 1)[0].strip().upper()
        val = value.strip()
        if name == "BEGIN" and val.upper() == "VEVENT": cur = {}
        elif name == "END" and val.upper() == "VEVENT":
            if cur is not None: events.append(cur)
            cur = None
        elif cur is not None and name:
            if name == "EXDATE": cur.setdefault("EXDATE", []).append(val)
            else: cur.setdefault(name, val)
    return events

def _parse_ics_dt(value: str):
    v = value.strip().strip('"')
    if v.upper().endswith("Z"): v = v[:-1]
    if "T" in v.upper():
        date_part, _, tm = v.partition("T")
        qd = QDate.fromString(date_part, "yyyyMMdd")
        tm = tm.replace(":", "")[:4]
        if qd.isValid() and len(tm) == 4 and tm.isdigit(): return qd, int(tm[:2]) * 60 + int(tm[2:])
    else:
        qd = QDate.fromString(v, "yyyyMMdd")
        if qd.isValid(): return qd, None
    return None

def _parse_ics_duration(value: str) -> int | None:
    m = re.match(r"^([+-])?P(?:(\d+)W)?(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?$", value.strip().upper())
    if not m: return None
    _s, w, d, h, mi, sec = m.groups()
    total = int(w or 0) * 10080 + int(d or 0) * 1440 + int(h or 0) * 60 + int(mi or 0) + (1 if int(sec or 0) else 1)
    return max(5, total)

def _parse_rrule(value: str) -> dict:
    rule = {}
    for part in value.split(";"):
        k, _, v = part.partition("=")
        if k.strip(): rule[k.strip().upper()] = v.strip()
    return rule

def _expand_rrule(start: QDate, freq: str, interval: int, count: int, until: QDate | None, byday: set[str], cap: int = ICS_EXPAND_CAP, horizon_days: int = ICS_EXPAND_HORIZON) -> list[QDate]:
    allowed = {_ICS_WD[b[-2:]] for b in byday if len(b) >= 2 and b[-2:] in _ICS_WD}
    d0, out = start, []
    d, end = start, start.addDays(horizon_days)
    while d <= end and len(out) < cap:
        hit = False
        if freq == "DAILY": hit = d0.daysTo(d) % interval == 0
        elif freq == "WEEKLY": hit = ((d0.daysTo(d) // 7) % interval == 0 and (not allowed or d.dayOfWeek() in allowed))
        elif freq == "MONTHLY":
            months = (d.year() - d0.year()) * 12 + (d.month() - d0.month())
            hit = d.day() == d0.day() and months % interval == 0
        elif freq == "YEARLY": hit = (d.day() == d0.day() and d.month() == d0.month() and (d.year() - d0.year()) % interval == 0)
        if hit:
            if until is not None and d > until: break
            out.append(d)
            if count and len(out) >= count: break
        d = d.addDays(1)
    return out

def _tasks_from_event(ev: dict) -> list[Task]:
    if ev.get("STATUS", "").upper() == "CANCELLED": return []
    dt = _parse_ics_dt(ev.get("DTSTART", ""))
    if dt is None: return []
    start_date, start_min = dt
    if start_min is None: start_min = 9 * 60
    dur = None
    if ev.get("DURATION"): dur = _parse_ics_duration(ev["DURATION"])
    elif ev.get("DTEND"):
        end = _parse_ics_dt(ev["DTEND"])
        if end is not None:
            ed, em = end
            span = start_date.daysTo(ed) * 1440 + (em or 0) - start_min
            dur = max(5, span)
    if dur is None: dur = 60
    dur = max(5, min(dur, DAY_MINUTES - start_min))
    title = _ics_unescape(ev.get("SUMMARY", "")).strip() or "(imported event)"
    notes = _ics_unescape(ev.get("DESCRIPTION", "")).strip()
    cat = _ics_unescape(ev.get("CATEGORIES", "")).split(",")[0].strip().title()
    if cat not in CATEGORIES: cat = "Other"
    ex: set[str] = set()
    for raw in ev.get("EXDATE", []) or []:
        for chunk in raw.split(","):
            d = _parse_ics_dt(chunk)
            if d: ex.add(d[0].toString("yyyy-MM-dd"))

    def mk(date_key: str, rec: str) -> Task:
        return Task(id=uuid.uuid4().hex[:10], title=title, date=date_key, start=mm_to_str(start_min),
                    duration=dur, category=cat, priority="med", notes=notes, completed=False, recurrence=rec, ex_dates=sorted(ex))

    if not ev.get("RRULE"): return [mk(start_date.toString("yyyy-MM-dd"), "none")]
    rule = _parse_rrule(ev["RRULE"])
    freq = rule.get("FREQ", "").upper()
    interval = max(1, _safe_int(rule.get("INTERVAL"), 1))
    count = _safe_int(rule.get("COUNT"), 0)
    until = None
    if rule.get("UNTIL"):
        u = _parse_ics_dt(rule["UNTIL"])
        if u: until = u[0]
    byday = {b.strip().upper() for b in rule.get("BYDAY", "").split(",") if b.strip()}
    anchor_key = start_date.toString("yyyy-MM-dd")
    if freq == "DAILY" and interval == 1 and not count and not until: return [mk(anchor_key, "daily")]
    if freq == "WEEKLY" and interval == 1 and not count and not until:
        weekdays_set = {"MO", "TU", "WE", "TH", "FR"}
        own = {_ICS_WD_REV[start_date.dayOfWeek()]}
        if not byday or byday == own: return [mk(anchor_key, "weekly")]
        if byday == weekdays_set: return [mk(anchor_key, "weekdays")]
    occurrences = _expand_rrule(start_date, freq, interval, count, until, byday)
    if not occurrences: return [mk(anchor_key, "none")]
    out = []
    for d in occurrences:
        dk = d.toString("yyyy-MM-dd")
        if dk not in ex: out.append(mk(dk, "none"))
    return out


# ----------------------------------------------------------------- undo commands
class AddCmd(QUndoCommand):
    def __init__(self, mw, task: Task, text="Add task", select=True):
        super().__init__(text)
        self.mw, self.d, self.select = mw, asdict(task), select

    def redo(self):
        if self.mw.store.get(self.d["id"]) is None:
            t = Task.from_dict(self.d)
            self.mw.store.tasks.append(t)
            self.mw.store.upsert_task(t)
        self.mw._after_mutation(self.d["id"] if self.select else None)

    def undo(self):
        self.mw.store.remove(self.d["id"])
        self.mw.store.delete_task(self.d["id"])
        self.mw._after_mutation(None)

class BulkAddCmd(QUndoCommand):
    def __init__(self, mw, tasks: list[Task], text="Add tasks"):
        super().__init__(text)
        self.mw, self.ds = mw, [asdict(t) for t in tasks]

    def redo(self):
        for d in self.ds:
            if self.mw.store.get(d["id"]) is None:
                t = Task.from_dict(d)
                self.mw.store.tasks.append(t)
                self.mw.store.upsert_task(t)
        self.mw._after_mutation(None)

    def undo(self):
        for d in self.ds:
            self.mw.store.remove(d["id"])
            self.mw.store.delete_task(d["id"])
        self.mw._after_mutation(None)

class DeleteCmd(QUndoCommand):
    def __init__(self, mw, tasks: list[Task], text="Delete"):
        super().__init__(text)
        self.mw, self.ds = mw, [asdict(t) for t in tasks]

    def redo(self):
        for d in self.ds:
            self.mw.store.remove(d["id"])
            self.mw.store.delete_task(d["id"])
        self.mw._after_mutation(None)

    def undo(self):
        for d in self.ds:
            if self.mw.store.get(d["id"]) is None:
                t = Task.from_dict(d)
                self.mw.store.tasks.append(t)
                self.mw.store.upsert_task(t)
        self.mw._after_mutation(self.ds[0]["id"] if self.ds else None)

class ModifyCmd(QUndoCommand):
    def __init__(self, mw, before: dict, after: dict, text="Edit"):
        super().__init__(text)
        self.mw = mw
        self.before = {k: v for k, v in before.items() if k != "work_dates"}
        self.after = {k: v for k, v in after.items() if k != "work_dates"}

    def _apply(self, d: dict):
        cur = self.mw.store.get(d["id"])
        if cur is None: return
        t = Task.from_dict(d)
        t.work_dates = dict(cur.work_dates or {})
        self.mw.store.replace(d["id"], t)
        self.mw.store.upsert_task(t)

    def redo(self): self._apply(self.after); self.mw._after_mutation(self.after["id"])
    def undo(self): self._apply(self.before); self.mw._after_mutation(self.before["id"])

class ToggleOccurrenceCmd(QUndoCommand):
    def __init__(self, mw, anchor: Task, date_key: str, on: bool):
        super().__init__("Complete occurrence" if on else "Reopen occurrence")
        self.mw, self.anchor_id, self.date_key, self.on = mw, anchor.id, date_key, on

    def _apply(self, on: bool):
        a = self.mw.store.get(self.anchor_id)
        if a is None: return
        done = set(a.done_dates or [])
        if on: done.add(self.date_key)
        else: done.discard(self.date_key)
        a.done_dates = sorted(done)
        self.mw.store.upsert_task(a)
        self.mw._after_mutation(None)

    def redo(self): self._apply(self.on)
    def undo(self): self._apply(not self.on)

class SkipOccurrenceCmd(QUndoCommand):
    def __init__(self, mw, anchor: Task, date_key: str, skip: bool):
        super().__init__("Skip occurrence" if skip else "Restore occurrence")
        self.mw, self.anchor_id, self.date_key, self.skip = mw, anchor.id, date_key, skip

    def _apply(self, skip: bool):
        a = self.mw.store.get(self.anchor_id)
        if a is None: return
        ex = set(a.ex_dates or [])
        if skip: ex.add(self.date_key)
        else: ex.discard(self.date_key)
        a.ex_dates = sorted(ex)
        self.mw.store.upsert_task(a)
        self.mw._after_mutation(None)

    def redo(self): self._apply(self.skip)
    def undo(self): self._apply(not self.skip)


# ----------------------------------------------------------------- day timeline
class Timeline(QWidget):
    taskClicked = Signal(object)
    taskActivated = Signal(object)
    taskMoved = Signal(str, str)
    slotActivated = Signal(int)
    backlogDropped = Signal(str, int)
    rangeSelected = Signal(int, int)

    def __init__(self):
        super().__init__()
        self._tasks: list[Task] = []
        self._selected: str | None = None
        self._date: QDate = QDate.currentDate()
        self._now = QTime.currentTime()
        self._drag_id: str | None = None
        self._drag_grab = 0.0
        self._drag_moved = False
        self._drag_orig: str | None = None
        self._drop_min: int | None = None
        self._dark = False
        self._filter = ""
        self._activity: set[int] = set()
        self._creating = False
        self._create_anchor: int | None = None
        self._create_cur: int | None = None
        self._layout_cache: dict[str, tuple[int, int]] = {}
        
        self.setMouseTracking(True)
        self.setAcceptDrops(True)
        self.setMinimumWidth(440)
        self.setMinimumHeight(int(DAY_MINUTES * PX_PER_MIN) + 10)

    def set_date(self, qdate: QDate): self._date = qdate; self.update()
    def set_tasks(self, tasks: list[Task]): 
        self._tasks = tasks
        self._compute_layout()
        self.update()
    def set_selected(self, task_id: str | None): self._selected = task_id; self.update()
    def set_dark(self, dark: bool): self._dark = dark; self.update()
    def set_filter(self, text: str): self._filter = (text or "").strip().lower(); self.update()
    def set_activity(self, minutes: set[int]): self._activity = minutes or set(); self.update()
    def tick(self): self._now = QTime.currentTime(); self.update()

    def _compute_layout(self):
        """Group overlapping tasks and assign them side-by-side columns."""
        items = sorted(self._tasks, key=lambda t: (t.start_minutes, t.end_minutes))
        self._layout_cache.clear()
        clusters = []
        cur_cluster = []
        cur_end = -1
        
        for t in items:
            if t.start_minutes >= cur_end:
                if cur_cluster: clusters.append(cur_cluster)
                cur_cluster = [t]
                cur_end = t.end_minutes
            else:
                cur_cluster.append(t)
                cur_end = max(cur_end, t.end_minutes)
        if cur_cluster: clusters.append(cur_cluster)
            
        for cluster in clusters:
            cols = [] 
            for t in cluster:
                placed = False
                for i, c in enumerate(cols):
                    if c[-1].end_minutes <= t.start_minutes:
                        c.append(t)
                        placed = True
                        break
                if not placed:
                    cols.append([t])
            total_cols = len(cols)
            for i, c in enumerate(cols):
                for t in c:
                    self._layout_cache[t.id] = (i, total_cols)

    def _rect(self, t: Task) -> QRectF:
        col_idx, total_cols = self._layout_cache.get(t.id, (0, 1))
        x_start = LABEL_W + 12
        total_w = max(self.width() - x_start - 18, 40)
        gap = 4 if total_cols > 1 else 0
        col_w = (total_w - gap * (total_cols - 1)) / total_cols
        x = x_start + col_idx * (col_w + gap)
        w = col_w
        y = t.start_minutes * PX_PER_MIN + 2
        h = max(t.duration * PX_PER_MIN - 4, 26)
        return QRectF(x, y, w, h)

    def _task_at(self, pos: QPointF):
        for t in reversed(self._tasks):
            if self._rect(t).contains(pos): return t
        return None

    def _y_to_minutes(self, y: float) -> int:
        m = int(y / PX_PER_MIN) // SNAP_MIN * SNAP_MIN
        return max(0, min(m, DAY_MINUTES - 5))

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        dark = self._dark
        canvas = "#0d0d0d" if dark else "#ffffff"
        band = "#141414" if dark else "#fafafa"
        grid_c = "#222222" if dark else "#ececec"
        grid_half = "#1a1a1a" if dark else "#f5f5f5"
        label_c = "#777777" if dark else "#999999"
        hint_c = "#555555" if dark else "#bbb"
        now_c = ACCENT_COLOR
        sel_c = ACCENT_COLOR
        accent = sel_c
        comp_fill = QColor("#1a1a1a") if dark else QColor("#f5f5f5")
        comp_border = QColor("#333333") if dark else QColor("#ddd")
        comp_text = QColor("#666666") if dark else QColor("#999")
        worked_c = QColor("#888888") if dark else QColor("#555555")
        activity_c = QColor("#666666") if dark else QColor("#ccc")

        p.fillRect(self.rect(), QColor(canvas))
        wy = WORK_START * 60 * PX_PER_MIN
        wh = (WORK_END - WORK_START) * 60 * PX_PER_MIN
        p.fillRect(QRectF(LABEL_W, wy, self.width() - LABEL_W, wh), QColor(band))

        small = QFont(self.font())
        small.setPointSizeF(max(self.font().pointSizeF() - 2.0, 7.5))

        p.setFont(small)
        for h in range(DAY_HOURS + 1):
            y = h * 60 * PX_PER_MIN
            if 0 < h < DAY_HOURS:
                p.setPen(QPen(QColor(grid_c), 1))
                p.drawLine(QPointF(LABEL_W, y), QPointF(self.width() - 1, y))
            if h < DAY_HOURS:
                p.setPen(QColor(label_c))
                p.drawText(QRectF(0, y - 9, LABEL_W - 12, 18), Qt.AlignRight | Qt.AlignVCenter, f"{h:02d}:00")
        p.setPen(QPen(QColor(grid_half), 1, Qt.DotLine))
        for half in range(1, DAY_HOURS * 2, 2):
            y = half * 30 * PX_PER_MIN
            p.drawLine(QPointF(LABEL_W, y), QPointF(self.width() - 1, y))

        for t in self._tasks:
            r = self._rect(t)
            base = QColor(CATEGORIES.get(t.category, "#94a3b8"))
            hay = " ".join([t.title, t.category, t.notes] + [f"#{x}" for x in (t.tags or [])]).lower()
            dimmed = bool(self._filter) and self._filter not in hay
            if t.completed:
                fill, border, text = comp_fill, comp_border, comp_text
            else:
                fill = QColor(base)
                fill.setAlpha(55 if dark else 38)
                border = base
                text = QColor(base).lighter(125) if dark else QColor(base).darker(165)
            if dimmed:
                fill = QColor("#8b93a0"); fill.setAlpha(45 if dark else 30)
                border = QColor("#8b93a0"); border.setAlpha(110)
                text = QColor("#8b93a0")
            selected = t.id == self._selected
            p.setPen(QPen(QColor(sel_c) if selected else border, 2.2 if selected else 1.4))
            p.setBrush(fill)
            p.drawRoundedRect(r, 8, 8)

            inner = r.adjusted(8, 4, -8, -4)
            tf = QFont(self.font())
            tf.setBold(True)
            tf.setStrikeOut(t.completed)
            p.setFont(tf)
            p.setPen(text)
            worked = t.worked_on(t.date) if t.date else 0
            sub = f"{t.time_range} · {t.duration_label} · {t.category}"
            sd, sn = t.sub_done
            if sn: sub += f" · ☑{sd}/{sn}"
            if worked > 0: sub += f" · ⏱ {fmt_minutes(worked)}"
            
            elide_w = int(inner.width())
            if r.height() >= 42:
                fm = p.fontMetrics()
                elided = fm.elidedText(t.title, Qt.ElideRight, elide_w)
                p.drawText(QRectF(inner.left(), inner.top(), inner.width(), 20), Qt.AlignLeft | Qt.AlignVCenter | Qt.TextSingleLine, elided)
                p.setFont(small)
                fm_s = p.fontMetrics()
                elided_s = fm_s.elidedText(sub, Qt.ElideRight, elide_w)
                p.drawText(QRectF(inner.left(), inner.top() + 20, inner.width(), 17), Qt.AlignLeft | Qt.AlignVCenter | Qt.TextSingleLine, elided_s)
            else:
                fm = p.fontMetrics()
                elided = fm.elidedText(t.title, Qt.ElideRight, elide_w)
                p.drawText(inner, Qt.AlignVCenter | Qt.AlignLeft | Qt.TextSingleLine, elided)
                
            if t.date and t.duration > 0:
                frac = min(1.0, worked / t.duration)
                if frac > 0:
                    p.setPen(Qt.NoPen)
                    p.setBrush(worked_c)
                    p.drawRoundedRect(QRectF(r.left() + 4, r.bottom() - 6, max((r.width() - 8) * frac, 3.0), 3.0), 2, 2)

        if not self._tasks:
            p.setFont(self.font())
            p.setPen(QColor(hint_c))
            p.drawText(QRectF(LABEL_W, 0, self.width() - LABEL_W, self.height()), Qt.AlignCenter, "Nothing scheduled.\nDouble-click or DRAG on empty space to\nblock out hours, or drag one in from the backlog.")

        if self._date == QDate.currentDate():
            y = (self._now.hour() * 60 + self._now.minute()) * PX_PER_MIN
            p.setPen(QPen(QColor(now_c), 1.6))
            p.drawLine(QPointF(LABEL_W, y), QPointF(self.width() - 1, y))
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(now_c))
            p.drawEllipse(QPointF(LABEL_W + 3, y), 4.0, 4.0)
            p.setFont(small)
            p.setPen(QColor(now_c))
            p.drawText(QRectF(self.width() - 70, y - 19, 64, 15), Qt.AlignRight | Qt.AlignVCenter, self._now.toString("HH:mm"))

        if self._activity:
            p.setPen(Qt.NoPen)
            p.setBrush(activity_c)
            runs: list[list[int]] = []
            for m in sorted(self._activity):
                if runs and m == runs[-1][1]: runs[-1][1] = m + 1
                else: runs.append([m, m + 1])
            for s, e in runs:
                x = LABEL_W + s * PX_PER_MIN
                w = max((e - s) * PX_PER_MIN, 1.2)
                p.drawRoundedRect(QRectF(x, 2, w, 6), 3, 3)

        if self._drop_min is not None:
            y = self._drop_min * PX_PER_MIN
            p.setPen(QPen(QColor(ACCENT_COLOR), 2, Qt.DashLine))
            p.drawLine(QPointF(LABEL_W, y), QPointF(self.width() - 1, y))
            p.setFont(small)
            p.setPen(QColor(ACCENT_COLOR))
            p.drawText(QRectF(self.width() - 100, y - 18, 94, 16), Qt.AlignRight | Qt.AlignVCenter, f"↳ {mm_to_str(self._drop_min)}")

        if (self._creating and self._create_anchor is not None and self._create_cur is not None):
            a, c = self._create_anchor, self._create_cur
            s, e = min(a, c), min(max(a, c) + SNAP_MIN, DAY_MINUTES)
            gr = QRectF(LABEL_W + 12, s * PX_PER_MIN + 2, max(self.width() - LABEL_W - 30, 40), max((e - s) * PX_PER_MIN - 4, 12))
            p.setPen(QPen(QColor(accent), 1.4, Qt.DashLine))
            c = QColor(accent); c.setAlpha(60)
            p.setBrush(c)
            p.drawRoundedRect(gr, 8, 8)
            p.setFont(small)
            p.setPen(QColor(accent))
            label = f"{mm_to_str(s)} – {mm_to_str(e)}  ·  {fmt_minutes(e - s)}"
            ly = gr.top() - 16 if gr.top() > 20 else gr.bottom() + 4
            p.drawText(QRectF(gr.left(), ly, gr.width(), 15), Qt.AlignLeft | Qt.AlignVCenter, label)

    def mousePressEvent(self, ev):
        if ev.button() != Qt.LeftButton: return
        pos = ev.position()
        t = self._task_at(pos)
        if t is not None:
            self.taskClicked.emit(t.id)
            if not t.recurring_instance:
                self._drag_id = t.id
                self._drag_grab = pos.y() / PX_PER_MIN - t.start_minutes
                self._drag_orig = t.start
                self._drag_moved = False
                self.setCursor(Qt.ClosedHandCursor)
        else:
            self.taskClicked.emit(None)
            self._creating = True
            self._create_anchor = self._create_cur = self._y_to_minutes(pos.y())
            self.setCursor(Qt.CrossCursor)

    def mouseMoveEvent(self, ev):
        pos = ev.position()
        if self._creating:
            self._create_cur = self._y_to_minutes(pos.y())
            self.update()
            return
        if self._drag_id:
            t = next((x for x in self._tasks if x.id == self._drag_id), None)
            if t is None: return
            raw = pos.y() / PX_PER_MIN - self._drag_grab
            snapped = int(round(raw / SNAP_MIN)) * SNAP_MIN
            snapped = max(0, min(snapped, DAY_MINUTES - t.duration))
            if snapped != t.start_minutes:
                t.start_minutes = snapped
                self._drag_moved = True
                self.update()
        else:
            self.setCursor(Qt.PointingHandCursor if self._task_at(pos) else Qt.ArrowCursor)

    def mouseReleaseEvent(self, _ev):
        if self._creating:
            self._creating = False
            self.setCursor(Qt.ArrowCursor)
            a, c = self._create_anchor, self._create_cur
            self._create_anchor = self._create_cur = None
            self.update()
            if a is not None and c is not None and abs(c - a) >= SNAP_MIN:
                s = min(a, c)
                e = min(max(a, c) + SNAP_MIN, DAY_MINUTES)
                self.rangeSelected.emit(s, e)
            return
        if self._drag_id and self._drag_moved and self._drag_orig is not None:
            self.taskMoved.emit(self._drag_id, self._drag_orig)
        self._drag_id = None
        self._drag_moved = False
        self._drag_orig = None
        self.setCursor(Qt.ArrowCursor)

    def mouseDoubleClickEvent(self, ev):
        pos = ev.position()
        t = self._task_at(pos)
        if t is not None: self.taskActivated.emit(t.id)
        else: self.slotActivated.emit(self._y_to_minutes(pos.y()))

    def dragEnterEvent(self, ev):
        if ev.mimeData().hasFormat(MIME_TASK): ev.acceptProposedAction()

    def dragMoveEvent(self, ev):
        if ev.mimeData().hasFormat(MIME_TASK):
            m = self._y_to_minutes(ev.position().y())
            if m != self._drop_min: self._drop_min = m; self.update()
            ev.acceptProposedAction()

    def dragLeaveEvent(self, _ev):
        if self._drop_min is not None: self._drop_min = None; self.update()

    def dropEvent(self, ev):
        if ev.mimeData().hasFormat(MIME_TASK):
            tid = bytes(ev.mimeData().data(MIME_TASK)).decode()
            m = self._y_to_minutes(ev.position().y())
            self._drop_min = None
            self.update()
            ev.acceptProposedAction()
            self.backlogDropped.emit(tid, m)


# ----------------------------------------------------------------- week view
class WeekView(QWidget):
    HEADER_H = 38
    MIN_COL_W = 80

    taskClicked = Signal(object)
    taskActivated = Signal(object)
    taskMoved = Signal(str, str, str)
    slotActivated = Signal(str, int)
    backlogDroppedAt = Signal(str, str, int)
    headerClicked = Signal(str)
    weekRangeSelected = Signal(str, int, int)

    def __init__(self):
        super().__init__()
        self._start: QDate | None = None
        self._days: dict[str, list[Task]] = {}
        self._selected: str | None = None
        self._now = QTime.currentTime()
        self._dark = False
        self._filter = ""
        self._drag_id: str | None = None
        self._drag_grab = 0.0
        self._drag_col = 0
        self._drag_min = 0
        self._drag_moved = False
        self._drag_orig_date: str | None = None
        self._drag_orig_start: str | None = None
        self._drop_day: str | None = None
        self._drop_min: int | None = None
        self._creating = False
        self._create_col = 0
        self._create_anchor: int | None = None
        self._create_cur: int | None = None

        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)
        self.setAcceptDrops(True)
        self.setMinimumWidth(LABEL_W + 7 * self.MIN_COL_W + 8)
        self.setMinimumHeight(self.HEADER_H + int(DAY_MINUTES * PX_PER_MIN) + 8)

    def set_range(self, start: QDate): self._start = start; self.update()
    def set_days(self, days: dict[str, list[Task]]): self._days = days; self.update()
    def set_selected(self, task_id: str | None): self._selected = task_id; self.update()
    def set_dark(self, dark: bool): self._dark = dark; self.update()
    def set_filter(self, text: str): self._filter = (text or "").strip().lower(); self.update()
    def tick(self): self._now = QTime.currentTime(); self.update()

    def _col_w(self) -> float: return max((self.width() - LABEL_W) / 7.0, self.MIN_COL_W)
    def _col_at(self, x: float) -> int:
        if x < LABEL_W: return -1
        return max(0, min(int((x - LABEL_W) / self._col_w()), 6))
    def _key_at(self, col: int) -> str: return self._start.addDays(col).toString("yyyy-MM-dd")
    def _col_of_key(self, key: str) -> int:
        d = QDate.fromString(key, "yyyy-MM-dd")
        if self._start is None or not d.isValid(): return 0
        return max(0, min(self._start.daysTo(d), 6))

    def _rect_at(self, col: int, minutes: int, duration: int) -> QRectF:
        cw = self._col_w()
        x = LABEL_W + col * cw + 4
        y = self.HEADER_H + minutes * PX_PER_MIN + 2
        h = max(duration * PX_PER_MIN - 4, 22)
        return QRectF(x, y, cw - 8, h)

    def _task_at(self, pos: QPointF):
        if self._start is None: return None, -1
        col = self._col_at(pos.x())
        if col < 0: return None, -1
        for t in reversed(self._days.get(self._key_at(col), [])):
            if self._rect_at(col, t.start_minutes, t.duration).contains(pos): return t, col
        return None, -1

    def _find_display(self, task_id: str) -> Task | None:
        for lst in self._days.values():
            for t in lst:
                if t.id == task_id: return t
        return None

    def _y_minutes(self, y: float) -> int:
        m = int((y - self.HEADER_H) / PX_PER_MIN)
        m = max(0, m) // SNAP_MIN * SNAP_MIN
        return min(m, DAY_MINUTES - SNAP_MIN)

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        dark = self._dark
        cw = self._col_w()
        canvas = "#0d0d0d" if dark else "#ffffff"
        band = "#141414" if dark else "#fafafa"
        weekend = QColor(128, 128, 128, 18 if dark else 12)
        grid_c = "#222222" if dark else "#ececec"
        label_c = "#777777" if dark else "#999999"
        hint_c = "#555555" if dark else "#bbb"
        now_c = ACCENT_COLOR
        sel_c = ACCENT_COLOR
        accent = sel_c
        today_txt = "#e8e8e8" if dark else "#1a1a1a"
        comp_fill = QColor("#1a1a1a") if dark else QColor("#f5f5f5")
        comp_border = QColor("#333333") if dark else QColor("#ddd")
        comp_text = QColor("#666666") if dark else QColor("#999")
        worked_c = QColor("#888888") if dark else QColor("#555555")

        p.fillRect(self.rect(), QColor(canvas))
        working = QRectF(LABEL_W, self.HEADER_H + WORK_START * 60 * PX_PER_MIN, self.width() - LABEL_W, (WORK_END - WORK_START) * 60 * PX_PER_MIN)
        p.fillRect(working, QColor(band))

        small = QFont(self.font()); small.setPointSizeF(max(self.font().pointSizeF() - 2.0, 7.5))
        tiny = QFont(self.font()); tiny.setPointSizeF(max(self.font().pointSizeF() - 3.0, 6.8))

        today = QDate.currentDate()
        for i in range(7):
            d = self._start.addDays(i)
            if d.dayOfWeek() > 5: p.fillRect(QRectF(LABEL_W + i * cw, 0, cw, self.height()), weekend)
        for i in range(8):
            x = LABEL_W + i * cw
            p.setPen(QPen(QColor(grid_c), 1))
            p.drawLine(QPointF(x, self.HEADER_H), QPointF(x, self.height() - 1))
        p.setFont(small)
        for h in range(DAY_HOURS + 1):
            y = self.HEADER_H + h * 60 * PX_PER_MIN
            if 0 < h < DAY_HOURS:
                p.setPen(QPen(QColor(grid_c), 1))
                p.drawLine(QPointF(LABEL_W, y), QPointF(self.width() - 1, y))
            if h < DAY_HOURS:
                p.setPen(QColor(label_c))
                p.drawText(QRectF(0, y - 9, LABEL_W - 10, 18), Qt.AlignRight | Qt.AlignVCenter, f"{h:02d}")

        for i in range(7):
            d = self._start.addDays(i)
            planned = sum(t.duration for t in self._days.get(d.toString("yyyy-MM-dd"), []) if not t.completed)
            x = LABEL_W + i * cw
            r = QRectF(x + 2, 4, cw - 4, self.HEADER_H - 8)
            is_today = d == today
            p.setFont(self.font())
            p.setPen(QColor(today_txt) if is_today else QColor(label_c))
            f = p.font(); f.setBold(is_today); p.setFont(f)
            p.drawText(r, Qt.AlignHCenter | Qt.AlignTop, d.toString("ddd d MMM"))
            p.setFont(tiny)
            p.setPen(QColor(today_txt) if is_today and planned else QColor(label_c))
            p.drawText(QRectF(r.left(), r.top() + 18, r.width(), 14), Qt.AlignHCenter | Qt.AlignTop, fmt_minutes(planned) if planned else "—")
            if is_today:
                p.setPen(QPen(QColor(accent), 2))
                p.drawLine(QPointF(x + 10, self.HEADER_H - 3), QPointF(x + cw - 10, self.HEADER_H - 3))

        for col in range(7):
            key = self._key_at(col)
            for t in self._days.get(key, []):
                if self._drag_id and t.id == self._drag_id: continue
                r = self._rect_at(col, t.start_minutes, t.duration)
                base = QColor(CATEGORIES.get(t.category, "#94a3b8"))
                hay = " ".join([t.title, t.category, t.notes] + [f"#{x}" for x in (t.tags or [])]).lower()
                dimmed = bool(self._filter) and self._filter not in hay
                if t.completed:
                    fill, border, text = comp_fill, comp_border, comp_text
                else:
                    fill = QColor(base)
                    fill.setAlpha(55 if dark else 38)
                    border = base
                    text = QColor(base).lighter(125) if dark else QColor(base).darker(165)
                if dimmed:
                    fill = QColor("#8b93a0"); fill.setAlpha(45 if dark else 30)
                    border = QColor("#8b93a0"); border.setAlpha(110)
                    text = QColor("#8b93a0")
                selected = t.id == self._selected
                p.setPen(QPen(QColor(sel_c) if selected else border, 2.2 if selected else 1.4))
                p.setBrush(fill)
                p.drawRoundedRect(r, 8, 8)

                inner = r.adjusted(8, 3, -8, -3)
                tf = QFont(self.font()); tf.setBold(True); tf.setStrikeOut(t.completed)
                p.setFont(tf)
                p.setPen(text)
                elide_w = int(inner.width())
                fm = p.fontMetrics()
                elided = fm.elidedText(t.title, Qt.ElideRight, elide_w)
                p.drawText(QRectF(inner.left(), inner.top(), inner.width(), 18), Qt.AlignLeft | Qt.AlignVCenter | Qt.TextSingleLine, elided)
                if r.height() >= 36:
                    p.setFont(small)
                    worked = t.worked_on(t.date) if t.date else 0
                    sub = t.time_range
                    sd, sn = t.sub_done
                    if sn: sub += f" · ☑{sd}/{sn}"
                    if worked > 0: sub += f" · ⏱{fmt_minutes(worked)}"
                    fm_s = p.fontMetrics()
                    elided_s = fm_s.elidedText(sub, Qt.ElideRight, int(inner.width()))
                    p.drawText(QRectF(inner.left(), inner.top() + 17, inner.width(), 14), Qt.AlignLeft | Qt.AlignVCenter | Qt.TextSingleLine, elided_s)
                if t.date and t.duration > 0:
                    frac = min(1.0, t.worked_on(t.date) / t.duration)
                    if frac > 0:
                        p.setPen(Qt.NoPen)
                        p.setBrush(worked_c)
                        p.drawRoundedRect(QRectF(r.left() + 4, r.bottom() - 7, max((r.width() - 8) * frac, 2.0), 3.5), 2, 2)

        if self._start is not None and not any(self._days.values()):
            p.setFont(self.font())
            p.setPen(QColor(hint_c))
            p.drawText(QRectF(LABEL_W, self.HEADER_H, self.width() - LABEL_W, self.height() - self.HEADER_H), Qt.AlignCenter, "Empty week.\nDouble-click or DRAG inside a column to block\ntime, or drag backlog items onto any day.")

        if self._start is not None:
            col = self._col_of_key(today.toString("yyyy-MM-dd"))
            if self._start.addDays(col) == today:
                y = self.HEADER_H + (self._now.hour() * 60 + self._now.minute()) * PX_PER_MIN
                x0 = LABEL_W + col * cw
                p.setPen(QPen(QColor(now_c), 1.6))
                p.drawLine(QPointF(x0, y), QPointF(x0 + cw - 2, y))
                p.setPen(Qt.NoPen)
                p.setBrush(QColor(now_c))
                p.drawEllipse(QPointF(x0 + 3, y), 4.0, 4.0)
                p.setFont(small)
                p.setPen(QColor(now_c))
                p.setBackgroundMode(Qt.OpaqueMode)
                p.setBackground(QColor(canvas))
                p.drawText(QRectF(x0 + 8, y - 18, 60, 15), Qt.AlignLeft | Qt.AlignVCenter, self._now.toString("HH:mm"))
                p.setBackgroundMode(Qt.TransparentMode)

        if self._drag_id and self._drag_moved:
            t = self._find_display(self._drag_id)
            if t is not None:
                gr = self._rect_at(self._drag_col, self._drag_min, t.duration)
                p.setPen(QPen(QColor(accent), 1.4, Qt.DashLine))
                p.setBrush(QColor(26, 26, 26, 45))
                p.drawRoundedRect(gr, 8, 8)
                orig_col = self._col_of_key(self._drag_orig_date or "")
                moved_day = orig_col != self._drag_col
                p.setFont(small)
                p.setPen(QColor(accent))
                label = mm_to_str(self._drag_min)
                if moved_day: label += (f"  {self._start.addDays(self._drag_col).toString('ddd')}")
                p.drawText(QRectF(gr.left(), gr.top() - 16, gr.width() + 60, 14), Qt.AlignLeft | Qt.AlignVCenter, label)

        if (self._creating and self._create_anchor is not None and self._create_cur is not None and self._start is not None):
            a, c = self._create_anchor, self._create_cur
            s = min(a, c)
            e = min(max(a, c) + SNAP_MIN, DAY_MINUTES)
            gr = self._rect_at(self._create_col, s, max(e - s, SNAP_MIN))
            p.setPen(QPen(QColor(accent), 1.4, Qt.DashLine))
            p.setBrush(QColor(26, 26, 26, 40))
            p.drawRoundedRect(gr, 8, 8)
            p.setFont(small)
            p.setPen(QColor(accent))
            label = f"{mm_to_str(s)} – {mm_to_str(e)}  ·  {fmt_minutes(e - s)}"
            ly = gr.top() - 16 if gr.top() > self.HEADER_H + 20 else gr.bottom() + 4
            p.drawText(QRectF(gr.left(), ly, gr.width() + 40, 15), Qt.AlignLeft | Qt.AlignVCenter, label)

        if self._drop_day is not None and self._drop_min is not None:
            col = self._col_of_key(self._drop_day)
            x0 = LABEL_W + col * cw
            y = self.HEADER_H + self._drop_min * PX_PER_MIN
            p.setPen(QPen(QColor(ACCENT_COLOR), 2, Qt.DashLine))
            p.drawLine(QPointF(x0 + 4, y), QPointF(x0 + cw - 6, y))
            p.setFont(small)
            p.setPen(QColor(ACCENT_COLOR))
            p.drawText(QRectF(x0, y - 18, cw - 8, 15), Qt.AlignRight | Qt.AlignVCenter, f"↳ {mm_to_str(self._drop_min)}")

    def mousePressEvent(self, ev):
        pos = ev.position()
        if self._start is not None and pos.y() <= self.HEADER_H:
            col = self._col_at(pos.x())
            if col >= 0: self.headerClicked.emit(self._key_at(col))
            return
        if ev.button() != Qt.LeftButton: return
        t, col = self._task_at(pos)
        if t is not None:
            self.taskClicked.emit(t.id)
            if not t.recurring_instance:
                self._drag_id = t.id
                self._drag_grab = ((pos.y() - self.HEADER_H) / PX_PER_MIN - t.start_minutes)
                self._drag_col = col
                self._drag_min = t.start_minutes
                self._drag_orig_date = t.date
                self._drag_orig_start = t.start
                self._drag_moved = False
                self.setCursor(Qt.ClosedHandCursor)
        else:
            self.taskClicked.emit(None)
            col = self._col_at(max(pos.x(), LABEL_W))
            if col >= 0:
                self._creating = True
                self._create_col = col
                self._create_anchor = self._create_cur = self._y_minutes(pos.y())
                self.setCursor(Qt.CrossCursor)

    def mouseMoveEvent(self, ev):
        pos = ev.position()
        if self._creating:
            col = self._col_at(max(pos.x(), LABEL_W))
            if col >= 0: self._create_col = col
            self._create_cur = self._y_minutes(pos.y())
            self.update()
            return
        if self._drag_id:
            t = self._find_display(self._drag_id)
            if t is None: return
            col = self._col_at(pos.x())
            if col < 0: col = self._drag_col
            raw = (pos.y() - self.HEADER_H) / PX_PER_MIN - self._drag_grab
            m = int(round(raw / SNAP_MIN)) * SNAP_MIN
            m = max(0, min(m, DAY_MINUTES - t.duration))
            if m != self._drag_min or col != self._drag_col:
                self._drag_min = m
                self._drag_col = col
                self._drag_moved = True
                self.update()
        else:
            t, _ = self._task_at(pos)
            self.setCursor(Qt.PointingHandCursor if t else Qt.ArrowCursor)

    def mouseReleaseEvent(self, _ev):
        if self._creating:
            self._creating = False
            self.setCursor(Qt.ArrowCursor)
            a, c = self._create_anchor, self._create_cur
            self._create_anchor = self._create_cur = None
            self.update()
            if (a is not None and c is not None and self._start is not None and abs(c - a) >= SNAP_MIN):
                s = min(a, c)
                e = min(max(a, c) + SNAP_MIN, DAY_MINUTES)
                self.weekRangeSelected.emit(self._key_at(self._create_col), s, e)
            return
        if (self._drag_id and self._drag_moved and self._drag_orig_date and self._start is not None):
            self.taskMoved.emit(self._drag_id, self._key_at(self._drag_col), mm_to_str(self._drag_min))
        self._drag_id = None
        self._drag_moved = False
        self._drag_orig_date = None
        self._drag_orig_start = None
        self.setCursor(Qt.ArrowCursor)

    def mouseDoubleClickEvent(self, ev):
        pos = ev.position()
        if self._start is None or pos.y() <= self.HEADER_H: return
        t, col = self._task_at(pos)
        if t is not None: self.taskActivated.emit(t.id)
        else:
            col = self._col_at(max(pos.x(), LABEL_W))
            m = self._y_minutes(pos.y())
            self.slotActivated.emit(self._key_at(col), m)

    def dragEnterEvent(self, ev):
        if ev.mimeData().hasFormat(MIME_TASK): ev.acceptProposedAction()

    def dragMoveEvent(self, ev):
        if not ev.mimeData().hasFormat(MIME_TASK) or self._start is None: return
        col = self._col_at(max(ev.position().x(), LABEL_W))
        if col < 0: return
        k = self._key_at(col)
        m = self._y_minutes(ev.position().y())
        if (k, m) != (self._drop_day, self._drop_min):
            self._drop_day, self._drop_min = k, m
            self.update()
        ev.acceptProposedAction()

    def dragLeaveEvent(self, _ev):
        if self._drop_day is not None: self._drop_day, self._drop_min = None, None; self.update()

    def dropEvent(self, ev):
        if ev.mimeData().hasFormat(MIME_TASK) and self._start is not None:
            tid = bytes(ev.mimeData().data(MIME_TASK)).decode()
            col = self._col_at(max(ev.position().x(), LABEL_W))
            m = self._y_minutes(ev.position().y())
            k = self._key_at(col)
            self._drop_day, self._drop_min = None, None
            self.update()
            ev.acceptProposedAction()
            self.backlogDroppedAt.emit(tid, k, m)


# ----------------------------------------------------------------- backlog list
class BacklogList(QListWidget):
    def __init__(self):
        super().__init__()
        self.setDragEnabled(True)
        self.setSelectionMode(QAbstractItemView.SingleSelection)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

    def startDrag(self, actions):
        item = self.currentItem()
        if item is None: return
        tid = item.data(Qt.UserRole)
        title = item.data(Qt.UserRole + 1) or "task"
        md = QMimeData()
        md.setData(MIME_TASK, tid.encode())
        drag = QDrag(self)
        drag.setMimeData(md)
        
        pm = QPixmap(240, 34)
        pm.fill(Qt.transparent)
        p = QPainter(pm)
        p.setRenderHint(QPainter.Antialiasing)
        
        pal = self.palette()
        bg = pal.color(QPalette.Base)
        text = pal.color(QPalette.Text)
        
        p.setPen(Qt.NoPen)
        p.setBrush(bg)
        p.drawRoundedRect(0, 0, 239, 33, 6, 6)
        p.setPen(QPen(text, 1))
        p.setBrush(Qt.NoBrush)
        p.drawRoundedRect(0, 0, 239, 33, 6, 6)
        
        p.setPen(text)
        p.setFont(self.font())
        p.drawText(pm.rect().adjusted(12, 0, -12, 0), Qt.AlignVCenter | Qt.AlignLeft, title)
        p.end()
        
        drag.setPixmap(pm)
        drag.setHotSpot(QPoint(24, 15))
        drag.exec(Qt.CopyAction)


# ----------------------------------------------------------------- task row
class TaskRow(QWidget):
    def __init__(self, task: Task):
        super().__init__()
        self.setObjectName("TaskCard")
        self.task = task
        color = CATEGORIES.get(task.category, "#9a9a9a")
        
        self.check = QCheckBox()
        self.check.setChecked(task.completed)
        
        bar = QFrame()
        bar.setFixedSize(4, 38)
        bar.setStyleSheet(f"background:{color};border-radius:2px;")
        
        self.title = QLabel(task.title)
        f = self.title.font()
        f.setBold(True)
        self.title.setFont(f)

        if task.date:
            timepart = f"{task.time_range} · {task.duration_label}"
            worked = task.worked_on(task.date)
            if worked > 0: timepart += f" · ⏱ {fmt_minutes(worked)}"
        else:
            timepart = f"unscheduled · {task.duration_label}"
        sd, sn = task.sub_done
        if sn: timepart += f" · ☑{sd}/{sn}"
        if task.recurring_instance: timepart += " · ↻"
        prio = {"low": "",
                "med": " · <span style='color:#888;'>medium</span>",
                "high": f" · <span style='color:{ACCENT_COLOR};'>high</span>"}[task.priority]
        tags_html = ""
        if task.tags:
            tags_html = " · <span style='color:#7c8698;'>" + " ".join(f"#{t}" for t in task.tags) + "</span>"
        self.meta = QLabel(
            f"<span style='color:{color};'>●</span> {timepart}{prio}"
            f"{tags_html}{deadline_span_html(task)}")

        text = QVBoxLayout()
        text.setContentsMargins(0, 0, 0, 0)
        text.setSpacing(2)
        text.addWidget(self.title)
        text.addWidget(self.meta)
        
        lay = QHBoxLayout(self)
        lay.setContentsMargins(10, 8, 12, 8)
        lay.setSpacing(10)
        lay.addWidget(self.check)
        lay.addWidget(bar)
        lay.addLayout(text, 1)

        tips = []
        if task.recurring_instance: tips.append(f"Repeats {rec_label(task.recurrence).lower()} — double-click to edit")
        if task.until:
            u = QDate.fromString(task.until, "yyyy-MM-dd")
            if u.isValid(): tips.append(f"Repeats until {u.toString('ddd, d MMM yyyy')}")
        if task.deadline:
            d = QDate.fromString(task.deadline, "yyyy-MM-dd")
            if d.isValid(): tips.append(f"Deadline: {d.toString('ddd, d MMM yyyy')}")
        if not task.date: tips.append("Drag onto the timeline to schedule")
        if task.notes: tips.append(task.notes)
        if tips: self.setToolTip("\n".join(tips))
        self.apply_completed_style()

    def apply_completed_style(self):
        done = self.task.completed
        f = self.title.font()
        f.setStrikeOut(done)
        self.title.setFont(f)
        self.title.setEnabled(not done)
        self.meta.setEnabled(not done)


# ----------------------------------------------------------------- dialogs
class TaskDialog(QDialog):
    def __init__(self, parent=None, *, qdate=None, start_min=None, duration=None, task=None, backlog=False, allow_backlog=True):
        super().__init__(parent)
        self.setWindowTitle("Edit task" if task else "New task")
        self.setMinimumWidth(440)
        self._task = task

        self.ed_title = QLineEdit()
        self.ed_title.setPlaceholderText("What needs to be done?")
        self.chk_backlog = QCheckBox("No fixed time — keep in backlog")
        if not allow_backlog:
            self.chk_backlog.setEnabled(False)
            self.chk_backlog.setToolTip("Repeating tasks always have a time of day")
        self.chk_backlog.setChecked(bool(backlog) or bool(task and not task.date))

        self.ed_date = QDateEdit(qdate or QDate.currentDate())
        self.ed_date.setCalendarPopup(True)
        self.ed_date.setDisplayFormat("ddd, d MMM yyyy")
        self.ed_start = QTimeEdit(QTime(9, 0))
        self.ed_start.setDisplayFormat("HH:mm")
        if start_min is not None: self.ed_start.setTime(QTime(start_min // 60, start_min % 60))
        self.ed_duration = QSpinBox()
        self.ed_duration.setRange(5, DAY_MINUTES)
        self.ed_duration.setSingleStep(15)
        self.ed_duration.setSuffix(" min")
        self.ed_duration.setValue(30 if (backlog or (task and not task.date)) else 60)
        if duration is not None: self.ed_duration.setValue(duration)

        self.ed_recur = QComboBox()
        for key, label in RECURRENCE: self.ed_recur.addItem(label, key)
        self.ed_recur.setToolTip("Weekly repeats on the weekday of the start date.")
        self.ed_until = QDateEdit(QDate.currentDate().addMonths(1))
        self.ed_until.setCalendarPopup(True)
        self.ed_until.setDisplayFormat("ddd, d MMM yyyy")
        self.ed_until.setEnabled(False)

        self.chk_deadline = QCheckBox()
        self.ed_deadline = QDateEdit(QDate.currentDate().addDays(1))
        self.ed_deadline.setCalendarPopup(True)
        self.ed_deadline.setDisplayFormat("ddd, d MMM yyyy")
        self.ed_deadline.setEnabled(False)
        self.dl_hint = QLabel("")
        self.dl_hint.setStyleSheet("color:#8a93a0;")
        dl_box = QHBoxLayout()
        dl_box.setContentsMargins(0, 0, 0, 0)
        dl_box.addWidget(self.chk_deadline)
        dl_box.addWidget(self.ed_deadline, 1)
        dl_box.addWidget(self.dl_hint)
        dl_widget = QWidget()
        dl_widget.setLayout(dl_box)
        self.chk_deadline.toggled.connect(self.ed_deadline.setEnabled)
        self.ed_deadline.dateChanged.connect(self._update_dl_hint)

        self.ed_tags = QLineEdit()
        self.ed_tags.setPlaceholderText("comma, separated, #optional")

        self.sub_list = QListWidget()
        self.sub_list.setFixedHeight(84)
        self.sub_edit = QLineEdit()
        self.sub_edit.setPlaceholderText("Add subtask and press Enter…")
        self.sub_add_btn = QToolButton()
        self.sub_add_btn.setText("＋")
        self.sub_del_btn = QToolButton()
        self.sub_del_btn.setText("－")
        sub_row = QHBoxLayout()
        sub_row.setContentsMargins(0, 0, 0, 0)
        sub_row.addWidget(self.sub_edit, 1)
        sub_row.addWidget(self.sub_add_btn)
        sub_row.addWidget(self.sub_del_btn)
        sub_widget = QWidget()
        sv = QVBoxLayout(sub_widget)
        sv.setContentsMargins(0, 0, 0, 0)
        sv.setSpacing(3)
        sv.addWidget(self.sub_list)
        sv.addLayout(sub_row)
        self.sub_add_btn.clicked.connect(self._sub_add)
        self.sub_del_btn.clicked.connect(self._sub_del)
        self.sub_edit.returnPressed.connect(self._sub_add)

        self.ed_category = QComboBox()
        for name, color in CATEGORIES.items():
            self.ed_category.addItem(name)
            self.ed_category.setItemData(self.ed_category.count() - 1, QColor(color), Qt.DecorationRole)
        self.ed_priority = QComboBox()
        for _key, label in PRIORITIES: self.ed_priority.addItem(label)
        self.ed_notes = QPlainTextEdit()
        self.ed_notes.setPlaceholderText("Optional notes…")
        self.ed_notes.setFixedHeight(64)

        form = QFormLayout()
        form.setSpacing(8)
        form.addRow("Title:", self.ed_title)
        form.addRow("", self.chk_backlog)
        form.addRow("Date:", self.ed_date)
        form.addRow("Start:", self.ed_start)
        form.addRow("Duration:", self.ed_duration)
        form.addRow("Repeats:", self.ed_recur)
        form.addRow("Until:", self.ed_until)
        form.addRow("Deadline:", dl_widget)
        form.addRow("Tags:", self.ed_tags)
        form.addRow("Subtasks:", sub_widget)
        form.addRow("Category:", self.ed_category)
        form.addRow("Priority:", self.ed_priority)
        form.addRow("Notes:", self.ed_notes)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        lay = QVBoxLayout(self)
        lay.addLayout(form)
        lay.addWidget(buttons)

        if task:
            self.ed_title.setText(task.title)
            d = QDate.fromString(task.date, "yyyy-MM-dd") if task.date else QDate.currentDate()
            if d.isValid(): self.ed_date.setDate(d)
            tm = QTime.fromString(task.start, "HH:mm")
            if tm.isValid(): self.ed_start.setTime(tm)
            self.ed_duration.setValue(task.duration)
            j = next((k for k, (key, _l) in enumerate(PRIORITIES) if key == task.priority), 1)
            self.ed_priority.setCurrentIndex(j)
            c = self.ed_category.findText(task.category)
            if c >= 0: self.ed_category.setCurrentIndex(c)
            self.ed_notes.setPlainText(task.notes)
            self.ed_tags.setText(", ".join(task.tags or []))
            dl = QDate.fromString(task.deadline, "yyyy-MM-dd") if task.deadline else QDate()
            if dl.isValid():
                self.chk_deadline.setChecked(True)
                self.ed_deadline.setDate(dl)
            un = QDate.fromString(task.until, "yyyy-MM-dd") if task.until else QDate()
            if un.isValid(): self.ed_until.setDate(un)
            for s in task.subtasks or []:
                it = QListWidgetItem(s.get("title", ""))
                it.setFlags(it.flags() | Qt.ItemIsUserCheckable)
                it.setCheckState(Qt.Checked if s.get("done") else Qt.Unchecked)
                self.sub_list.addItem(it)
        rec = task.recurrence if task else "none"
        i = next((k for k, (key, _l) in enumerate(RECURRENCE) if key == rec), 0)
        self.ed_recur.setCurrentIndex(i)
        self.chk_backlog.toggled.connect(self._sync)
        self.ed_recur.currentIndexChanged.connect(self._sync)
        self._sync()
        self._update_dl_hint()
        self.ed_title.setFocus()

    def _sub_add(self):
        txt = self.sub_edit.text().strip()
        if not txt: return
        it = QListWidgetItem(txt)
        it.setFlags(it.flags() | Qt.ItemIsUserCheckable)
        it.setCheckState(Qt.Unchecked)
        self.sub_list.addItem(it)
        self.sub_edit.clear()

    def _sub_del(self):
        row = self.sub_list.currentRow()
        if row >= 0: self.sub_list.takeItem(row)

    def _update_dl_hint(self):
        if not self.chk_deadline.isChecked():
            self.dl_hint.setText("")
            return
        days = QDate.currentDate().daysTo(self.ed_deadline.date())
        self.dl_hint.setText("overdue" if days < 0 else "today" if days == 0 else "tomorrow" if days == 1 else f"in {days} days")

    def _sync(self):
        off = self.chk_backlog.isChecked()
        for w in (self.ed_date, self.ed_start, self.ed_recur): w.setEnabled(not off and self.chk_backlog.isEnabled())
        self.ed_until.setEnabled((not off) and self.ed_recur.currentData() != "none")

    def accept(self):
        if not self.ed_title.text().strip():
            QMessageBox.warning(self, "Missing title", "Please enter a title for the task.")
            self.ed_title.setFocus()
            return
        if not self.chk_backlog.isChecked():
            s = self.ed_start.time()
            if s.hour() * 60 + s.minute() + self.ed_duration.value() > DAY_MINUTES:
                QMessageBox.warning(self, "Past midnight", "This task would end after midnight.\nChoose an earlier start or shorter duration.")
                return
        if self.ed_until.isEnabled() and self.ed_recur.currentData() != "none":
            if self.ed_until.date() < self.ed_date.date():
                QMessageBox.warning(self, "Invalid 'until' date", "'Until' date must be on or after the start date.")
                self.ed_until.setFocus()
                return
        super().accept()

    def build_task(self) -> Task:
        s = self.ed_start.time()
        prio = PRIORITIES[self.ed_priority.currentIndex()][0]
        in_backlog = self.chk_backlog.isChecked()
        rec = "none" if in_backlog else (self.ed_recur.currentData() or "none")
        subs = []
        for i in range(self.sub_list.count()):
            it = self.sub_list.item(i)
            subs.append({"title": it.text(), "done": it.checkState() == Qt.Checked})
        return Task(
            id=(self._task.id if self._task else uuid.uuid4().hex[:10]),
            title=self.ed_title.text().strip(),
            date="" if in_backlog else self.ed_date.date().toString("yyyy-MM-dd"),
            start=f"{s.hour():02d}:{s.minute():02d}",
            duration=self.ed_duration.value(),
            category=self.ed_category.currentText(),
            priority=prio,
            notes=self.ed_notes.toPlainText().strip(),
            completed=self._task.completed if self._task else False,
            recurrence=rec,
            deadline=(self.ed_deadline.date().toString("yyyy-MM-dd") if self.chk_deadline.isChecked() else ""),
            until=(self.ed_until.date().toString("yyyy-MM-dd") if self.ed_until.isEnabled() and rec != "none" else ""),
            tags=parse_tags(self.ed_tags.text()),
            subtasks=subs,
            ex_dates=list(self._task.ex_dates) if self._task else [],
            done_dates=list(self._task.done_dates) if self._task else [],
            work_dates=dict(self._task.work_dates) if self._task else {},
            recurring_instance=self._task.recurring_instance if self._task else False,
        )


class FreeSlotDialog(QDialog):
    def __init__(self, parent, gap_fn, default_from_min: int):
        super().__init__(parent)
        self.setWindowTitle("Find a free slot")
        self.setMinimumWidth(400)
        self._gap_fn = gap_fn
        self.ed_needed = QSpinBox()
        self.ed_needed.setRange(5, 480)
        self.ed_needed.setSingleStep(15)
        self.ed_needed.setSuffix(" min")
        self.ed_needed.setValue(30)
        self.ed_from = QTimeEdit()
        self.ed_from.setDisplayFormat("HH:mm")
        self.ed_from.setTime(QTime(default_from_min // 60, default_from_min % 60))
        self.results = QListWidget()
        self.buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        ok_btn = self.buttons.button(QDialogButtonBox.Ok)
        ok_btn.setText("Schedule here")
        ok_btn.setEnabled(False)
        self.buttons.accepted.connect(self.accept)
        self.buttons.rejected.connect(self.reject)
        self.ed_needed.valueChanged.connect(self._refill)
        self.ed_from.timeChanged.connect(self._refill)
        self.results.itemDoubleClicked.connect(lambda _i: self.accept())
        self.results.itemSelectionChanged.connect(lambda: ok_btn.setEnabled(self.results.currentItem() is not None))
        form = QFormLayout()
        form.addRow("Need:", self.ed_needed)
        form.addRow("Search from:", self.ed_from)
        lay = QVBoxLayout(self)
        lay.addLayout(form)
        lay.addWidget(self.results)
        lay.addWidget(self.buttons)
        self._refill()

    def _refill(self):
        needed = self.ed_needed.value()
        tm = self.ed_from.time()
        from_min = tm.hour() * 60 + tm.minute()
        self.results.clear()
        for s, e in self._gap_fn(needed, from_min):
            it = QListWidgetItem(f"{mm_to_str(s)}–{mm_to_str(e)}    {fmt_minutes(e - s)} free")
            it.setData(Qt.UserRole, s)
            self.results.addItem(it)
        if self.results.count(): self.results.setCurrentRow(0)

    def chosen_start(self):
        it = self.results.currentItem()
        return it.data(Qt.UserRole) if it else None


class SearchDialog(QDialog):
    jumpRequested = Signal(str)

    def __init__(self, parent, store: TaskStore):
        super().__init__(parent)
        self.setWindowTitle("Search all tasks")
        self.setMinimumSize(580, 480)
        self.store = store
        self.ed = QLineEdit()
        self.ed.setPlaceholderText("Search title, notes, tags or category…")
        self.ed.setClearButtonEnabled(True)
        self.results = QListWidget()
        self.results.setAlternatingRowColors(True)
        self.count = QLabel("Type at least 2 characters")
        lay = QVBoxLayout(self)
        lay.addWidget(self.ed)
        lay.addWidget(self.results, 1)
        lay.addWidget(self.count)
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(180)
        self._timer.timeout.connect(self._run)
        self.ed.textChanged.connect(self._timer.start)
        self.results.itemActivated.connect(self._activate)
        self.ed.setFocus()

    def _run(self):
        q = self.ed.text().strip()
        self.results.clear()
        if len(q) < 2:
            self.count.setText("Type at least 2 characters")
            return
        found = self.store.search(q)[:300]
        for t in found:
            where = t.date if t.date else "backlog"
            line = (f"{where}  {t.start if t.date else '       '}  {t.title}   · {t.category}")
            if t.tags: line += "  " + " ".join(f"#{x}" for x in t.tags)
            if t.notes: line += "   — " + t.notes[:60]
            it = QListWidgetItem(line)
            it.setData(Qt.UserRole, t.id)
            self.results.addItem(it)
        tip = " — Enter or double-click to jump" if found else ""
        self.count.setText(f"{len(found)} result(s){tip}")

    def _activate(self, item):
        self.jumpRequested.emit(item.data(Qt.UserRole))
        self.accept()


class DeadlinesDialog(QDialog):
    jumpRequested = Signal(str)

    def __init__(self, parent, tasks: list[Task]):
        super().__init__(parent)
        self.setWindowTitle("Deadlines")
        self.setMinimumSize(580, 470)
        self.listw = QListWidget()
        self.count = QLabel()
        
        rows = []
        for t in tasks:
            if not t.deadline: continue
            d = QDate.fromString(t.deadline, "yyyy-MM-dd")
            if d.isValid(): rows.append((d, t))
        rows.sort(key=lambda x: (x[0], x[1].start_minutes))
        
        today = QDate.currentDate()
        groups = {"Overdue": [], "Today": [], "Tomorrow": [], "Upcoming": []}
        
        for d, t in rows[:200]:
            days = today.daysTo(d)
            if t.completed: continue
            if days < 0: groups["Overdue"].append((d, t))
            elif days == 0: groups["Today"].append((d, t))
            elif days == 1: groups["Tomorrow"].append((d, t))
            else: groups["Upcoming"].append((d, t))
            
        for name, items in groups.items():
            if not items: continue
            header = QListWidgetItem(f"  {name.upper()}  ({len(items)})")
            header.setFlags(Qt.NoItemFlags)
            f = header.font(); f.setBold(True); header.setFont(f)
            if name == "Overdue": header.setBackground(QColor("#3a1212"))
            elif name == "Today": header.setBackground(QColor("#3a3a12"))
            elif name == "Tomorrow": header.setBackground(QColor("#123a23"))
            else: header.setBackground(QColor("#1a1a1a"))
            self.listw.addItem(header)
            
            for d, t in items:
                mark, extra = "⚑", f"in {today.daysTo(d)}d"
                if today.daysTo(d) < 0: mark, extra = "⚠", f"{-today.daysTo(d)}d overdue"
                elif today.daysTo(d) == 0: mark, extra = "⚑", "today"
                elif today.daysTo(d) == 1: mark, extra = "⚑", "tomorrow"
                
                where = t.time_range if t.date else "backlog"
                it = QListWidgetItem(f"   {mark} {d.toString('ddd d MMM')}   ·   {where}   ·   {t.title}")
                it.setData(Qt.UserRole, t.id)
                self.listw.addItem(it)
                
        overdue = len(groups["Overdue"])
        head = f"{len(rows)} task(s) with a deadline"
        if overdue: head += f"  ·  {overdue} overdue"
        self.count.setText(head + "   — Enter or double-click to jump")
        
        buttons = QDialogButtonBox(QDialogButtonBox.Close)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addWidget(self.listw, 1)
        lay.addWidget(self.count)
        lay.addWidget(buttons)
        self.listw.itemActivated.connect(self._activate)
        for i in range(self.listw.count()):
            if self.listw.item(i).flags() & Qt.ItemIsEnabled:
                self.listw.setCurrentRow(i)
                break

    def _activate(self, item):
        if not item.data(Qt.UserRole): return
        self.jumpRequested.emit(item.data(Qt.UserRole))
        self.accept()


class PlanDialog(QDialog):
    def __init__(self, parent, placements, date_key: str):
        super().__init__(parent)
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        self.setWindowTitle("Plan for " + d.toString("ddd, d MMM"))
        self.setMinimumSize(520, 420)
        lst = QListWidget()
        for t, m in placements:
            end = min(m + t.duration, DAY_MINUTES)
            extra = []
            if t.deadline: extra.append(f"⚑{t.deadline}")
            if t.tags: extra += [f"#{x}" for x in t.tags]
            txt = (f"{mm_to_str(m)}–{mm_to_str(end)}   {t.title}   ·   {t.duration_label}")
            if extra: txt += "   ·   " + " ".join(extra)
            lst.addItem(txt)
        hint = QLabel(f"{len(placements)} task(s) will be scheduled into free working hours (5-min buffers).\nTasks that don't fit stay in the backlog.")
        hint.setWordWrap(True)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.button(QDialogButtonBox.Ok).setText("Apply plan")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addWidget(hint)
        lay.addWidget(lst, 1)
        lay.addWidget(buttons)


class ReviewDialog(QDialog):
    def __init__(self, mw):
        super().__init__(mw)
        self.mw = mw
        self.setWindowTitle("Daily review")
        self.setMinimumSize(560, 480)
        tasks = mw._day_tasks
        key = mw.date_key()
        done = [t for t in tasks if t.completed]
        open_tasks = [t for t in tasks if not t.completed and t.date and not is_instance(t.id)]
        planned = sum(t.duration for t in tasks)
        worked = sum(min(t.worked_on(key), t.duration) for t in tasks)
        score = int(round(100 * worked / planned)) if planned else 0
        head = QLabel(f"Planned <b>{fmt_minutes(planned)}</b> · worked <b>{fmt_minutes(worked)}</b> · focus score <b>{score}%</b> · {len(done)} done, {len(open_tasks)} open")
        head.setWordWrap(True)
        self.lst = QListWidget()
        for t in open_tasks:
            w = t.worked_on(key)
            extra = f" · ⏱ {fmt_minutes(w)}" if w else ""
            self.lst.addItem(f"{t.time_range}   {t.title}{extra}")
        if not open_tasks: self.lst.addItem("Nothing open — clean slate. 🎉")
        self.btn_move = QPushButton(f"Move {len(open_tasks)} unfinished → tomorrow")
        self.btn_move.setEnabled(bool(open_tasks))
        self.btn_move.clicked.connect(self._move)
        self.btn_plan = QPushButton("⚡ Auto-plan tomorrow from backlog")
        self.btn_plan.clicked.connect(self._plan)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.accept)
        row = QHBoxLayout()
        row.addWidget(self.btn_move)
        row.addWidget(self.btn_plan)
        row.addStretch(1)
        row.addWidget(btn_close)
        lay = QVBoxLayout(self)
        lay.addWidget(head)
        lay.addWidget(QLabel("Unfinished today:"))
        lay.addWidget(self.lst, 1)
        lay.addLayout(row)

    def _move(self): self.mw._move_unfinished(); self.accept()
    def _plan(self):
        key = self.mw.current_date.addDays(1).toString("yyyy-MM-dd")
        pl = self.mw.compute_plan(key)
        if not pl:
            QMessageBox.information(self, "Plan tomorrow", "Backlog is empty or nothing fits in tomorrow's free slots.")
            return
        dlg = PlanDialog(self.mw, pl, key)
        if dlg.exec() == QDialog.Accepted:
            self.mw._apply_plan(key, pl)
            self.accept()


class SettingsDialog(QDialog):
    def __init__(self, mw):
        super().__init__(mw)
        self.setWindowTitle("Settings")
        self.setMinimumWidth(420)
        self.mw = mw
        s = mw.store.settings

        self.eod_hour = QSpinBox(); self.eod_hour.setRange(0, 23)
        self.eod_hour.setValue(int(s.get("eod_hour", 18)))
        self.work_start = QSpinBox(); self.work_start.setRange(0, 23)
        self.work_start.setValue(int(s.get("work_start", 8)))
        self.work_end   = QSpinBox(); self.work_end.setRange(1, 24)
        self.work_end.setValue(int(s.get("work_end", 18)))
        self.pomo_work = QSpinBox(); self.pomo_work.setRange(5, 90)
        self.pomo_work.setValue(int(s.get("pomo_work_min", 25)))
        self.pomo_break = QSpinBox(); self.pomo_break.setRange(1, 30)
        self.pomo_break.setValue(int(s.get("pomo_break_min", 5)))
        self.long_every = QSpinBox(); self.long_every.setRange(0, 8)
        self.long_every.setValue(int(s.get("long_break_every", 4)))
        self.long_mult = QSpinBox(); self.long_mult.setRange(2, 5)
        self.long_mult.setValue(int(s.get("long_break_mult", 3)))
        self.snap = QSpinBox(); self.snap.setRange(1, 30); self.snap.setSingleStep(5)
        self.snap.setValue(int(s.get("snap_min", 5)))
        self.buffer = QSpinBox(); self.buffer.setRange(0, 60); self.buffer.setSingleStep(5)
        self.buffer.setValue(int(s.get("plan_buffer_min", 5)))
        
        self.cmb_scheme = QComboBox()
        self.cmb_scheme.addItems(["Minimal Light", "Minimal Dark", "Sepia", "Nordic"])
        self.cmb_scheme.setCurrentText(s.get("scheme", "Minimal Dark" if s.get("dark") else "Minimal Light"))

        self.btn_accent = QPushButton("Select...")
        self.accent_color = s.get("accent", "#1a1a1a")
        self._update_btn_color(self.btn_accent, self.accent_color)
        self.btn_accent.clicked.connect(self._pick_accent)

        self.chk_rem = QCheckBox("Enable reminders")
        self.chk_rem.setChecked(s.get("reminders", True))
        self.chk_track = QCheckBox("Track activity")
        self.chk_track.setChecked(s.get("track", True))
        self.chk_tray = QCheckBox("Close to tray (keep running)")
        self.chk_tray.setChecked(s.get("close_to_tray", True))

        form = QFormLayout()
        form.setSpacing(8)
        
        lbl_schedule = QLabel("Scheduling")
        lbl_schedule.setStyleSheet("font-weight: bold; font-size: 12pt; border-bottom: 1px solid #888; padding-bottom: 4px;")
        form.addRow(lbl_schedule)
        form.addRow("End-of-day summary hour:", self.eod_hour)
        form.addRow("Working hours start:", self.work_start)
        form.addRow("Working hours end:",   self.work_end)
        form.addRow("Snap increment (min):", self.snap)
        form.addRow("Plan-day buffer (min):", self.buffer)
        
        lbl_pomo = QLabel("Pomodoro")
        lbl_pomo.setStyleSheet("font-weight: bold; font-size: 12pt; border-bottom: 1px solid #888; padding-bottom: 4px; margin-top: 10px;")
        form.addRow(lbl_pomo)
        form.addRow("Work (min):", self.pomo_work)
        form.addRow("Break (min):", self.pomo_break)
        form.addRow("Long break every N pomodoros (0=off):", self.long_every)
        form.addRow("Long break multiplier:", self.long_mult)
        
        lbl_appearance = QLabel("Appearance")
        lbl_appearance.setStyleSheet("font-weight: bold; font-size: 12pt; border-bottom: 1px solid #888; padding-bottom: 4px; margin-top: 10px;")
        form.addRow(lbl_appearance)
        form.addRow("Color Scheme:", self.cmb_scheme)
        form.addRow("Accent Color:", self.btn_accent)
        
        self.cat_btns = {}
        cats = s.get("categories", {})
        for name in DEFAULT_CATEGORIES.keys():
            btn = QPushButton("Select...")
            c = cats.get(name, DEFAULT_CATEGORIES[name])
            btn.setProperty("color", c)
            self._update_btn_color(btn, c)
            btn.clicked.connect(lambda _, n=name: self._pick_cat(n))
            form.addRow(f"{name} Color:", btn)
            self.cat_btns[name] = btn
            
        lbl_behavior = QLabel("Behavior")
        lbl_behavior.setStyleSheet("font-weight: bold; font-size: 12pt; border-bottom: 1px solid #888; padding-bottom: 4px; margin-top: 10px;")
        form.addRow(lbl_behavior)
        form.addRow("", self.chk_rem)
        form.addRow("", self.chk_track)
        form.addRow("", self.chk_tray)

        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._save)
        bb.rejected.connect(self.reject)
        lay = QVBoxLayout(self); lay.addLayout(form); lay.addWidget(bb)

    def _update_btn_color(self, btn: QPushButton, color: str):
        c = QColor(color)
        btn.setStyleSheet(f"background: {c.name()}; color: {'#fff' if c.lightness() < 128 else '#000'}; border: 1px solid #999; padding: 6px 14px; border-radius: 6px;")
        btn.setText(color.upper())

    def _pick_accent(self):
        c = QColorDialog.getColor(QColor(self.accent_color), self, "Select Accent Color")
        if c.isValid():
            self.accent_color = c.name()
            self._update_btn_color(self.btn_accent, self.accent_color)

    def _pick_cat(self, name: str):
        btn = self.cat_btns[name]
        c = QColorDialog.getColor(QColor(btn.property("color")), self, f"Select {name} Color")
        if c.isValid():
            btn.setProperty("color", c.name())
            self._update_btn_color(btn, c.name())

    def _save(self):
        s = self.mw.store.settings
        s["eod_hour"] = self.eod_hour.value()
        s["work_start"] = self.work_start.value()
        s["work_end"] = self.work_end.value()
        s["pomo_work_min"] = self.pomo_work.value()
        s["pomo_break_min"] = self.pomo_break.value()
        s["long_break_every"] = self.long_every.value()
        s["long_break_mult"] = self.long_mult.value()
        s["snap_min"] = self.snap.value()
        s["plan_buffer_min"] = self.buffer.value()
        s["scheme"] = self.cmb_scheme.currentText()
        s["accent"] = self.accent_color
        s["categories"] = {n: b.property("color") for n, b in self.cat_btns.items()}
        s["reminders"] = self.chk_rem.isChecked()
        s["track"] = self.chk_track.isChecked()
        s["close_to_tray"] = self.chk_tray.isChecked()
        self.mw.store.save()
        self.mw._apply_config()
        self.accept()


class PaletteDialog(QDialog):
    def __init__(self, parent, commands: list[tuple[str, object]]):
        super().__init__(parent)
        self.setWindowTitle("Command palette")
        self.setMinimumSize(460, 380)
        self.commands = commands
        self._chosen = None
        self.ed = QLineEdit()
        self.ed.setPlaceholderText("Type a command…")
        self.lst = QListWidget()
        lay = QVBoxLayout(self)
        lay.addWidget(self.ed)
        lay.addWidget(self.lst, 1)
        self.ed.textChanged.connect(self._refill)
        self.ed.returnPressed.connect(self._run_current)
        self.lst.itemActivated.connect(lambda _i: self._run_current())
        self._refill()
        self.ed.setFocus()

    def _refill(self):
        q = self.ed.text().strip().lower()
        self.lst.clear()
        for i, (label, _fn) in enumerate(self.commands):
            if not q or q in label.lower():
                it = QListWidgetItem(label)
                it.setData(Qt.UserRole, i)
                self.lst.addItem(it)
        if self.lst.count(): self.lst.setCurrentRow(0)

    def _run_current(self):
        it = self.lst.currentItem()
        if it is None: return
        self._chosen = self.commands[it.data(Qt.UserRole)][1]
        self.accept()


# ----------------------------------------------------------------- focus overlay
class FocusOverlay(QWidget):
    def __init__(self, mw):
        super().__init__(None, Qt.FramelessWindowHint | Qt.Window)
        self.mw = mw
        self.t0 = time.time()
        self.setWindowTitle("Focus")
        self.setWindowState(Qt.WindowFullScreen)
        pal = self.palette()
        pal.setColor(QPalette.Window, QColor("#000000"))
        self.setPalette(pal)
        self.setAutoFillBackground(True)
        self.setCursor(Qt.BlankCursor)
        self._timer = QTimer(self)
        self._timer.setInterval(500)
        self._timer.timeout.connect(self.update)
        self._timer.start()

    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key_Escape: self.close()
        elif ev.key() == Qt.Key_Space: self.mw._pomo_toggle(); self.update()
        elif ev.key() == Qt.Key_S: self.mw._pomo_stop(); self.close()

    def mousePressEvent(self, _ev): pass

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        w, h = self.width(), self.height()
        mw = self.mw
        
        pal = self.palette()
        bg_c = pal.color(QPalette.Window)
        text_c = pal.color(QPalette.WindowText)
        muted_c = QColor(text_c); muted_c.setAlpha(150)
        hint_c = QColor(text_c); hint_c.setAlpha(90)
        accent_c = QColor(ACCENT_COLOR)

        if mw.pomo_state == "running":
            secs = mw.pomo_end - time.time()
            phase = "focus" if mw.pomo_phase == "work" else "break"
        elif mw.pomo_state == "paused":
            secs = mw.pomo_remaining
            phase = "paused"
        else:
            secs = time.time() - self.t0
            phase = "elapsed"
            
        secs = max(0, int(secs + 0.999))
        m, s = divmod(secs, 60)
        txt = f"{m:02d}:{s:02d}"
        title = (mw.pomo_title if mw.pomo_state != "idle" else (mw.pomo_title or "Focus"))
        
        if mw.pomo_state != "idle" and mw.pomo_total_duration > 0:
            if mw.pomo_state == "paused":
                elapsed = mw.pomo_total_duration - mw.pomo_remaining
            else:
                elapsed = mw.pomo_total_duration - max(0, mw.pomo_end - time.time())
            frac = max(0, min(elapsed / mw.pomo_total_duration, 1.0))
        else:
            frac = (secs % 60) / 60.0
            
        ring_w = min(w, h) * 0.55
        ring_rect = QRectF(w/2 - ring_w/2, h/2 - ring_w/2 - 40, ring_w, ring_w)
        
        p.setPen(QPen(muted_c, 6, Qt.SolidLine, Qt.RoundCap))
        p.drawArc(ring_rect, 0, 360 * 16)
        
        p.setPen(QPen(accent_c, 6, Qt.SolidLine, Qt.RoundCap))
        start_angle = 90 * 16
        span_angle = int(-360 * 16 * frac)
        p.drawArc(ring_rect, start_angle, span_angle)
        
        for i in range(5, 0, -1):
            color = QColor(text_c)
            color.setAlpha(12 * i)
            p.setPen(color)
            f_big = QFont(self.font())
            f_big.setBold(True)
            f_big.setPointSizeF(max(min(w, h) / 7.0, 40) + i*2)
            p.setFont(f_big)
            p.drawText(QRectF(0, h / 2 - 150, w, 220), Qt.AlignCenter, txt)
            
        f_big = QFont(self.font())
        f_big.setBold(True)
        f_big.setPointSizeF(max(min(w, h) / 7.0, 40))
        p.setFont(f_big)
        p.setPen(text_c)
        p.drawText(QRectF(0, h / 2 - 150, w, 220), Qt.AlignCenter, txt)
        
        f_mid = QFont(self.font())
        f_mid.setPointSizeF(max(min(w, h) / 24.0, 14))
        p.setFont(f_mid)
        p.setPen(muted_c)
        p.drawText(QRectF(0, h / 2 - 270, w, 100), Qt.AlignCenter, title)
        
        f_sml = QFont(self.font())
        f_sml.setPointSizeF(max(min(w, h) / 48.0, 9))
        p.setFont(f_sml)
        p.setPen(hint_c)
        p.drawText(QRectF(0, h - 70, w, 30), Qt.AlignCenter, f"{phase}  ·  Esc to exit  ·  Space to pause")


# ----------------------------------------------------------------- stats
class StatsCanvas(QWidget):
    dayClicked = Signal(QDate)

    def __init__(self):
        super().__init__()
        self._data: dict | None = None
        self._cells: list[tuple[QRectF, QDate]] = []
        self.setMinimumHeight(430)
        self.setMinimumWidth(540)

    def set_data(self, data: dict):
        self._data = data
        self.update()

    def mousePressEvent(self, ev):
        pos = ev.position()
        for rect, d in self._cells:
            if rect.contains(pos):
                self.dayClicked.emit(d)
                return

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        pal = self.palette()
        text = pal.color(QPalette.WindowText)
        muted = QColor(text); muted.setAlpha(150)
        axis = QColor(text); axis.setAlpha(70)
        dark = pal.color(QPalette.Window).lightness() < 128
        planned_c = QColor("#999999") if dark else QColor("#cccccc")
        done_c = QColor("#dddddd") if dark else QColor("#555555")
        self._cells = []
        p.fillRect(self.rect(), pal.color(QPalette.Window))
        m = 22
        w = self.width()
        if not self._data or not self._data["days"]:
            p.setFont(self.font())
            p.setPen(muted)
            p.drawText(self.rect(), Qt.AlignCenter, "No data in this range.")
            return
        bold = QFont(self.font()); bold.setBold(True)
        days = self._data["days"]
        heatmap = len(days) > 35

        if heatmap: y0 = self._paint_heatmap(p, days, m, dark, text, muted)
        else: y0 = self._paint_bars(p, days, m, w, dark, text, muted, axis, planned_c, done_c)
        p.setFont(bold)
        p.setPen(text)
        p.drawText(QRectF(m, y0, w - 2 * m, 20), Qt.AlignLeft | Qt.AlignVCenter, "Time per category")
        cats = self._data["cats"]
        total_cat = sum(v for _, v in cats) or 1
        row_h = 26
        y = y0 + 26
        label_x = m + 190
        f_norm = self.font()
        for name, mins in cats:
            color = QColor(CATEGORIES.get(name, "#9a9a9a"))
            frac = mins / total_cat
            bw = max(4.0, 170.0 * frac)
            p.setPen(Qt.NoPen)
            p.setBrush(color)
            p.drawRoundedRect(QRectF(m, y + 3, bw, 14), 4, 4)
            p.setFont(f_norm)
            p.setPen(text)
            p.drawText(QRectF(m, y, 90, 20), Qt.AlignLeft | Qt.AlignVCenter, name)
            p.setPen(muted)
            p.drawText(QRectF(label_x, y, 200, 20), Qt.AlignLeft | Qt.AlignVCenter, f"{fmt_minutes(mins)}   ·   {frac * 100:.0f}%")
            y += row_h
            if y > self.height() - 10: break

    def _paint_bars(self, p, days, m, w, dark, text, muted, axis, planned_c, done_c) -> float:
        p.setFont(QFont(self.font(), -1, QFont.Bold))
        p.setPen(text)
        p.drawText(QRectF(m, 8, w - 2 * m, 20), Qt.AlignLeft | Qt.AlignVCenter, "Planned vs actually worked, per day")
        n = len(days)
        chart_top = 38
        chart_h = min(200, max(120, int(self.height() * 0.34)))
        baseline = chart_top + chart_h
        maxv = max(60, max((pl for _, pl, _ in days), default=60))
        slot = (w - 2 * m) / max(n, 1)
        bar_w = max(5.0, min((slot - 8.0) / 2.0, 26.0))
        label_step = max(1, int(round(36 / max(slot, 1))))
        p.setPen(QPen(axis, 1))
        p.drawLine(QPointF(m, baseline), QPointF(w - m, baseline))
        f_small = QFont(self.font())
        f_small.setPointSizeF(max(self.font().pointSizeF() - 2.0, 7.0))
        for i, (d, pl, wk) in enumerate(days):
            cx = m + i * slot + slot / 2
            x_pl = cx - bar_w - 1
            x_wk = cx + 1
            if pl > 0:
                p.setPen(Qt.NoPen)
                p.setBrush(planned_c)
                p.drawRoundedRect(QRectF(x_pl, baseline - chart_h * pl / maxv, bar_w, chart_h * pl / maxv), 3, 3)
                if wk > 0:
                    p.setBrush(done_c)
                    p.drawRoundedRect(QRectF(x_wk, baseline - chart_h * wk / maxv, bar_w, chart_h * wk / maxv), 3, 3)
                p.setFont(f_small)
                p.setPen(muted)
                if chart_h * pl / maxv > 15:
                    p.drawText(QRectF(cx - bar_w - 20, baseline - chart_h * pl / maxv - 16, bar_w * 2 + 40, 14), Qt.AlignCenter, fmt_minutes(pl))
            if i % label_step == 0:
                p.setFont(f_small)
                p.setPen(muted)
                p.drawText(QRectF(m + i * slot, baseline + 4, slot, 14), Qt.AlignCenter, d.toString("ddd d"))
        lx, ly = m, baseline + 22
        p.setFont(f_small)
        p.setPen(Qt.NoPen)
        p.setBrush(planned_c)
        p.drawRoundedRect(QRectF(lx, ly + 3, 10, 10), 3, 3)
        p.setBrush(done_c)
        p.drawRoundedRect(QRectF(lx + 88, ly + 3, 10, 10), 3, 3)
        p.setPen(text)
        p.drawText(QRectF(lx + 14, ly, 70, 16), Qt.AlignVCenter, "planned")
        p.drawText(QRectF(lx + 102, ly, 90, 16), Qt.AlignVCenter, "worked")
        return ly + 34

    def _paint_heatmap(self, p, days, m, dark, text, muted) -> float:
        p.setFont(QFont(self.font(), -1, QFont.Bold))
        p.setPen(text)
        p.drawText(QRectF(m, 8, self.width() - 2 * m, 20), Qt.AlignLeft | Qt.AlignVCenter, "Last 3 months — planned (blue) vs worked (green); click a day to open it")
        f_small = QFont(self.font())
        f_small.setPointSizeF(max(self.font().pointSizeF() - 2.0, 7.0))
        p.setFont(f_small)
        cell = 16
        pitch = 19
        top = 40
        start = days[0][0]
        end = days[-1][0]
        fm = start.addDays(-(start.dayOfWeek() - 1))
        maxp = max((pl for _, pl, _ in days), default=1) or 1
        base_c = QColor("#555555") if not dark else QColor("#aaaaaa")
        green_c = QColor("#cccccc") if dark else QColor("#333333")
        today = QDate.currentDate()
        data = {d.toString("yyyy-MM-dd"): (pl, wk) for d, pl, wk in days}
        col = 0
        d = fm
        last_month = -1
        while d <= end:
            mon = fm.addDays(col * 7)
            if mon.month() != last_month:
                last_month = mon.month()
                p.setPen(muted)
                p.drawText(QRectF(m + col * pitch, top - 16, pitch * 3, 14), Qt.AlignLeft | Qt.AlignVCenter, mon.toString("MMM"))
            for row in range(7):
                if d > end: break
                x = m + col * pitch
                y = top + row * pitch
                key = d.toString("yyyy-MM-dd")
                pl, wk = data.get(key, (0, 0))
                rect = QRectF(x, y, cell, cell)
                if pl == 0 and wk == 0:
                    p.setPen(Qt.NoPen)
                    c = QColor(text)
                    c.setAlpha(18)
                    p.setBrush(c)
                else:
                    p.setPen(Qt.NoPen)
                    c = QColor(base_c)
                    c.setAlpha(35 + int(190 * min(1.0, pl / maxp)))
                    p.setBrush(c)
                p.drawRoundedRect(rect, 3, 3)
                if pl > 0 and wk > 0:
                    c = QColor(green_c)
                    c.setAlpha(int(210 * min(1.0, wk / pl)))
                    p.setBrush(c)
                    p.drawRoundedRect(rect.adjusted(2, 2, -2, -2), 2, 2)
                elif wk > 0:
                    c = QColor(green_c)
                    c.setAlpha(150)
                    p.setBrush(c)
                    p.drawRoundedRect(rect.adjusted(2, 2, -2, -2), 2, 2)
                if d == today:
                    p.setPen(QPen(QColor("#ffffff" if dark else "#1a1a1a"), 1.4))
                    p.setBrush(Qt.NoBrush)
                    p.drawRoundedRect(rect, 3, 3)
                self._cells.append((rect, d))
                d = d.addDays(1)
            col += 1
        p.setPen(muted)
        for row, lbl in ((0, "Mon"), (2, "Wed"), (4, "Fri")):
            p.drawText(QRectF(0, top + row * pitch, m - 6, cell), Qt.AlignRight | Qt.AlignVCenter, lbl)
        return top + 7 * pitch + 14


class StatsDialog(QDialog):
    jumpTo = Signal(QDate)

    def __init__(self, parent, provider):
        super().__init__(parent)
        self.setWindowTitle("Statistics")
        self.setMinimumSize(720, 640)
        self._provider = provider
        self.combo = QComboBox()
        for label in ("This week", "Last 7 days", "Last 30 days", "Last 3 months"): self.combo.addItem(label)
        self.combo.currentIndexChanged.connect(self._reload)
        self.range_label = QLabel()
        self.summary = QLabel()
        self.summary.setWordWrap(True)
        self.canvas = StatsCanvas()
        self.canvas.dayClicked.connect(self._jump)
        top = QHBoxLayout()
        top.addWidget(QLabel("Range:"))
        top.addWidget(self.combo)
        top.addStretch(1)
        buttons = QDialogButtonBox(QDialogButtonBox.Close)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addLayout(top)
        lay.addWidget(self.range_label)
        lay.addWidget(self.canvas, 1)
        lay.addWidget(self.summary)
        lay.addWidget(buttons)
        self._reload()

    def _jump(self, d: QDate):
        self.jumpTo.emit(d)
        self.accept()

    def _reload(self):
        today = QDate.currentDate()
        i = self.combo.currentIndex()
        if i == 0: start, end = today.addDays(1 - today.dayOfWeek()), today.addDays(6 - (today.dayOfWeek() - 1))
        elif i == 1: start, end = today.addDays(-6), today
        elif i == 2: start, end = today.addDays(-29), today
        else: start, end = today.addDays(-89), today
        data = self._provider(start, end)
        self.range_label.setText(f"{start.toString('ddd, d MMM')}  –  {end.toString('ddd, d MMM yyyy')}")
        self.canvas.set_data(data)
        total, done = data["total"], data["done"]
        pct = int(round(100 * done / total)) if total else 0
        busiest = max(data["days"], key=lambda x: x[1]) if data["days"] else None
        btxt = ""
        if busiest and busiest[1]: btxt = (f"  ·  busiest day {busiest[0].toString('ddd d MMM')} ({fmt_minutes(busiest[1])})")
        self.summary.setText(f"Planned <b>{fmt_minutes(total)}</b>  ·  worked <b>{fmt_minutes(data['worked'])}</b>  ·  screen-active <b>{fmt_minutes(data['active'])}</b>  ·  completed {fmt_minutes(done)} ({pct}%){btxt}")
        self.setWindowTitle(f"Statistics — {self.combo.currentText()}")


# ----------------------------------------------------------------- theme helpers
def _make_icon(color: str = "#1a1a1a") -> QIcon:
    pm = QPixmap(64, 64)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.setPen(Qt.NoPen)
    p.setBrush(QColor(color))
    p.drawRoundedRect(4, 4, 56, 56, 14, 14)
    f = QFont(); f.setBold(True); f.setPixelSize(34)
    p.setFont(f)
    c = QColor(color)
    p.setPen(QColor("#ffffff") if c.lightness() < 128 else QColor("#000000"))
    p.drawText(pm.rect(), Qt.AlignCenter, "D")
    p.end()
    return QIcon(pm)


def _make_palette(dark: bool) -> QPalette:
    pal = QPalette()
    if not dark:
        pal.setColor(QPalette.Window, QColor("#ffffff"))
        pal.setColor(QPalette.WindowText, QColor("#1a1a1a"))
        pal.setColor(QPalette.Base, QColor("#ffffff"))
        pal.setColor(QPalette.AlternateBase, QColor("#f7f7f7"))
        pal.setColor(QPalette.ToolTipBase, QColor("#1a1a1a"))
        pal.setColor(QPalette.ToolTipText, QColor("#ffffff"))
        pal.setColor(QPalette.Text, QColor("#1a1a1a"))
        pal.setColor(QPalette.Button, QColor("#f5f5f5"))
        pal.setColor(QPalette.ButtonText, QColor("#1a1a1a"))
        pal.setColor(QPalette.BrightText, QColor("#cc0000"))
        pal.setColor(QPalette.Link, QColor("#1a1a1a"))
        pal.setColor(QPalette.Highlight, QColor("#1a1a1a"))
        pal.setColor(QPalette.HighlightedText, QColor("#ffffff"))
        pal.setColor(QPalette.PlaceholderText, QColor("#999999"))
        pal.setColor(QPalette.Disabled, QPalette.Text, QColor("#bbb"))
        pal.setColor(QPalette.Disabled, QPalette.ButtonText, QColor("#bbb"))
    else:
        pal.setColor(QPalette.Window, QColor("#0d0d0d"))
        pal.setColor(QPalette.WindowText, QColor("#e8e8e8"))
        pal.setColor(QPalette.Base, QColor("#141414"))
        pal.setColor(QPalette.AlternateBase, QColor("#1a1a1a"))
        pal.setColor(QPalette.ToolTipBase, QColor("#1a1a1a"))
        pal.setColor(QPalette.ToolTipText, QColor("#e8e8e8"))
        pal.setColor(QPalette.Text, QColor("#e8e8e8"))
        pal.setColor(QPalette.Button, QColor("#1a1a1a"))
        pal.setColor(QPalette.ButtonText, QColor("#e8e8e8"))
        pal.setColor(QPalette.BrightText, QColor("#ff5f5f"))
        pal.setColor(QPalette.Link, QColor("#e8e8e8"))
        pal.setColor(QPalette.Highlight, QColor("#e8e8e8"))
        pal.setColor(QPalette.HighlightedText, QColor("#0d0d0d"))
        pal.setColor(QPalette.PlaceholderText, QColor("#666666"))
        pal.setColor(QPalette.Disabled, QPalette.Text, QColor("#555"))
        pal.setColor(QPalette.Disabled, QPalette.ButtonText, QColor("#555"))
    return pal

def _make_sepia_palette() -> QPalette:
    pal = QPalette()
    pal.setColor(QPalette.Window, QColor("#FDF6E3"))
    pal.setColor(QPalette.WindowText, QColor("#586E75"))
    pal.setColor(QPalette.Base, QColor("#FDF6E3"))
    pal.setColor(QPalette.AlternateBase, QColor("#EEE8D5"))
    pal.setColor(QPalette.ToolTipBase, QColor("#073642"))
    pal.setColor(QPalette.ToolTipText, QColor("#93A1A1"))
    pal.setColor(QPalette.Text, QColor("#586E75"))
    pal.setColor(QPalette.Button, QColor("#EEE8D5"))
    pal.setColor(QPalette.ButtonText, QColor("#586E75"))
    pal.setColor(QPalette.BrightText, QColor("#CB4B16"))
    pal.setColor(QPalette.Link, QColor("#268BD2"))
    pal.setColor(QPalette.Highlight, QColor("#B58900"))
    pal.setColor(QPalette.HighlightedText, QColor("#FDF6E3"))
    pal.setColor(QPalette.PlaceholderText, QColor("#93A1A1"))
    pal.setColor(QPalette.Disabled, QPalette.Text, QColor("#93A1A1"))
    return pal

def _make_nordic_palette() -> QPalette:
    pal = QPalette()
    pal.setColor(QPalette.Window, QColor("#2E3440"))
    pal.setColor(QPalette.WindowText, QColor("#D8DEE9"))
    pal.setColor(QPalette.Base, QColor("#3B4252"))
    pal.setColor(QPalette.AlternateBase, QColor("#434C5E"))
    pal.setColor(QPalette.ToolTipBase, QColor("#3B4252"))
    pal.setColor(QPalette.ToolTipText, QColor("#D8DEE9"))
    pal.setColor(QPalette.Text, QColor("#D8DEE9"))
    pal.setColor(QPalette.Button, QColor("#434C5E"))
    pal.setColor(QPalette.ButtonText, QColor("#D8DEE9"))
    pal.setColor(QPalette.BrightText, QColor("#BF616A"))
    pal.setColor(QPalette.Link, QColor("#88C0D0"))
    pal.setColor(QPalette.Highlight, QColor("#88C0D0"))
    pal.setColor(QPalette.HighlightedText, QColor("#2E3440"))
    pal.setColor(QPalette.PlaceholderText, QColor("#4C566A"))
    pal.setColor(QPalette.Disabled, QPalette.Text, QColor("#4C566A"))
    return pal


LIGHT_STYLESHEET = """
QMainWindow, QDialog { background: #ffffff; }
QToolBar { background: #ffffff; border: none; border-bottom: 1px solid #ececec; padding: 8px; spacing: 6px; }
QToolButton { padding: 6px 12px; border-radius: 6px; color: #333; font-weight: 500; border: none; background: transparent; }
QToolButton:hover { background: #f5f5f5; color: #1a1a1a; }
QToolButton:pressed { background: #ebebeb; }
QToolButton:checked { background: #1a1a1a; color: #ffffff; }
QListWidget { background: transparent; border: none; padding: 4px; outline: none; }
QListWidget::item { border-bottom: 1px solid transparent; padding: 2px; }
QListWidget::item:selected { background: transparent; }
QScrollArea { background: #ffffff; border: 1px solid #ececec; border-radius: 8px; }
QScrollBar:vertical { border: none; background: transparent; width: 6px; margin: 4px 0; }
QScrollBar::handle:vertical { background: #d0d0d0; border-radius: 3px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #aaa; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar:horizontal { border: none; background: transparent; height: 6px; margin: 0 4px; }
QScrollBar::handle:horizontal { background: #d0d0d0; border-radius: 3px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #aaa; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
QStatusBar { background: #ffffff; border-top: 1px solid #ececec; padding: 4px 8px; }
QStatusBar QLabel { color: #888; margin: 0 4px; }
QDateEdit, QTimeEdit, QSpinBox, QComboBox { background: #ffffff; border: 1px solid #e0e0e0; border-radius: 6px; padding: 6px 10px; selection-background-color: #1a1a1a; selection-color: #ffffff; }
QDateEdit:hover, QTimeEdit:hover, QSpinBox:hover, QComboBox:hover { border-color: #bbb; }
QPushButton { background: #ffffff; border: 1px solid #e0e0e0; border-radius: 6px; padding: 6px 14px; color: #333; font-weight: 500; }
QPushButton:hover { background: #f5f5f5; border-color: #bbb; }
QLineEdit, QPlainTextEdit { background: #ffffff; border: 1px solid #e0e0e0; border-radius: 6px; padding: 6px 10px; selection-background-color: #1a1a1a; selection-color: #ffffff; }
QLineEdit:focus, QPlainTextEdit:focus { border-color: #888; }
QSplitter::handle { background: transparent; }
QSplitter::handle:hover { background: #f5f5f5; }
QLabel#HeaderLabel { font-size: 11pt; font-weight: bold; color: #1a1a1a; padding: 6px 4px; }
QWidget#TaskCard { background: #ffffff; border: 1px solid #ececec; border-radius: 8px; }
QWidget#TaskCard:hover { border-color: #ccc; background: #fafafa; }
"""

DARK_STYLESHEET = """
QMainWindow, QDialog { background: #0d0d0d; }
QToolBar { background: #0d0d0d; border: none; border-bottom: 1px solid #222; padding: 8px; spacing: 6px; }
QToolButton { padding: 6px 12px; border-radius: 6px; color: #ccc; font-weight: 500; border: none; background: transparent; }
QToolButton:hover { background: #1c1c1c; color: #fff; }
QToolButton:pressed { background: #282828; }
QToolButton:checked { background: #e8e8e8; color: #0d0d0d; }
QListWidget { background: transparent; border: none; padding: 4px; outline: none; }
QListWidget::item { border-bottom: 1px solid transparent; padding: 2px; }
QListWidget::item:selected { background: transparent; }
QScrollArea { background: #141414; border: 1px solid #222; border-radius: 8px; }
QScrollBar:vertical { border: none; background: transparent; width: 6px; margin: 4px 0; }
QScrollBar::handle:vertical { background: #333; border-radius: 3px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #4a4a4a; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar:horizontal { border: none; background: transparent; height: 6px; margin: 0 4px; }
QScrollBar::handle:horizontal { background: #333; border-radius: 3px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #4a4a4a; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
QStatusBar { background: #0d0d0d; border-top: 1px solid #222; padding: 4px 8px; }
QStatusBar QLabel { color: #777; margin: 0 4px; }
QDateEdit, QTimeEdit, QSpinBox, QComboBox { background: #161616; border: 1px solid #2a2a2a; border-radius: 6px; padding: 6px 10px; color: #e8e8e8; selection-background-color: #e8e8e8; selection-color: #0d0d0d; }
QDateEdit:hover, QTimeEdit:hover, QSpinBox:hover, QComboBox:hover { border-color: #444; }
QPushButton { background: #1a1a1a; border: 1px solid #2a2a2a; border-radius: 6px; padding: 6px 14px; color: #e8e8e8; font-weight: 500; }
QPushButton:hover { background: #222; border-color: #444; }
QLineEdit, QPlainTextEdit { background: #161616; border: 1px solid #2a2a2a; border-radius: 6px; padding: 6px 10px; color: #e8e8e8; selection-background-color: #e8e8e8; selection-color: #0d0d0d; }
QLineEdit:focus, QPlainTextEdit:focus { border-color: #555; }
QSplitter::handle { background: transparent; }
QSplitter::handle:hover { background: #1a1a1a; }
QMenu { background: #161616; border: 1px solid #2a2a2a; border-radius: 6px; padding: 4px; }
QMenu::item { padding: 6px 24px 6px 16px; border-radius: 4px; color: #e8e8e8; }
QMenu::item:selected { background: #e8e8e8; color: #0d0d0d; }
QToolTip { background: #161616; color: #e8e8e8; border: 1px solid #2a2a2a; border-radius: 4px; padding: 4px; }
QLabel#HeaderLabel { font-size: 11pt; font-weight: bold; color: #e8e8e8; padding: 6px 4px; }
QWidget#TaskCard { background: #141414; border: 1px solid #222; border-radius: 8px; }
QWidget#TaskCard:hover { border-color: #3a3a3a; background: #181818; }
"""

SEPIA_STYLESHEET = """
QMainWindow, QDialog { background: #FDF6E3; }
QToolBar { background: #FDF6E3; border: none; border-bottom: 1px solid #EEE8D5; padding: 8px; spacing: 6px; }
QToolButton { padding: 6px 12px; border-radius: 6px; color: #586E75; font-weight: 500; border: none; background: transparent; }
QToolButton:hover { background: #EEE8D5; color: #073642; }
QToolButton:pressed { background: #E5DCC5; }
QToolButton:checked { background: #586E75; color: #FDF6E3; }
QListWidget { background: transparent; border: none; padding: 4px; outline: none; }
QListWidget::item { border-bottom: 1px solid transparent; padding: 2px; }
QListWidget::item:selected { background: transparent; }
QScrollArea { background: #FDF6E3; border: 1px solid #EEE8D5; border-radius: 8px; }
QScrollBar:vertical { border: none; background: transparent; width: 6px; margin: 4px 0; }
QScrollBar::handle:vertical { background: #93A1A1; border-radius: 3px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #586E75; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar:horizontal { border: none; background: transparent; height: 6px; margin: 0 4px; }
QScrollBar::handle:horizontal { background: #93A1A1; border-radius: 3px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #586E75; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
QStatusBar { background: #FDF6E3; border-top: 1px solid #EEE8D5; padding: 4px 8px; }
QStatusBar QLabel { color: #93A1A1; margin: 0 4px; }
QDateEdit, QTimeEdit, QSpinBox, QComboBox { background: #FDF6E3; border: 1px solid #EEE8D5; border-radius: 6px; padding: 6px 10px; selection-background-color: #586E75; selection-color: #FDF6E3; }
QDateEdit:hover, QTimeEdit:hover, QSpinBox:hover, QComboBox:hover { border-color: #93A1A1; }
QPushButton { background: #FDF6E3; border: 1px solid #EEE8D5; border-radius: 6px; padding: 6px 14px; color: #586E75; font-weight: 500; }
QPushButton:hover { background: #EEE8D5; border-color: #93A1A1; }
QLineEdit, QPlainTextEdit { background: #FDF6E3; border: 1px solid #EEE8D5; border-radius: 6px; padding: 6px 10px; selection-background-color: #586E75; selection-color: #FDF6E3; }
QLineEdit:focus, QPlainTextEdit:focus { border-color: #586E75; }
QSplitter::handle { background: transparent; }
QSplitter::handle:hover { background: #EEE8D5; }
QLabel#HeaderLabel { font-size: 11pt; font-weight: bold; color: #073642; padding: 6px 4px; }
QWidget#TaskCard { background: #FDF6E3; border: 1px solid #EEE8D5; border-radius: 8px; }
QWidget#TaskCard:hover { border-color: #93A1A1; background: #F5EFD8; }
"""

NORDIC_STYLESHEET = """
QMainWindow, QDialog { background: #2E3440; }
QToolBar { background: #2E3440; border: none; border-bottom: 1px solid #434C5E; padding: 8px; spacing: 6px; }
QToolButton { padding: 6px 12px; border-radius: 6px; color: #D8DEE9; font-weight: 500; border: none; background: transparent; }
QToolButton:hover { background: #434C5E; color: #88C0D0; }
QToolButton:pressed { background: #4C566A; }
QToolButton:checked { background: #88C0D0; color: #2E3440; }
QListWidget { background: transparent; border: none; padding: 4px; outline: none; }
QListWidget::item { border-bottom: 1px solid transparent; padding: 2px; }
QListWidget::item:selected { background: transparent; }
QScrollArea { background: #3B4252; border: 1px solid #434C5E; border-radius: 8px; }
QScrollBar:vertical { border: none; background: transparent; width: 6px; margin: 4px 0; }
QScrollBar::handle:vertical { background: #4C566A; border-radius: 3px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #5E6A7E; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar:horizontal { border: none; background: transparent; height: 6px; margin: 0 4px; }
QScrollBar::handle:horizontal { background: #4C566A; border-radius: 3px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #5E6A7E; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
QStatusBar { background: #2E3440; border-top: 1px solid #434C5E; padding: 4px 8px; }
QStatusBar QLabel { color: #81A1C1; margin: 0 4px; }
QDateEdit, QTimeEdit, QSpinBox, QComboBox { background: #3B4252; border: 1px solid #434C5E; border-radius: 6px; padding: 6px 10px; color: #D8DEE9; selection-background-color: #88C0D0; selection-color: #2E3440; }
QDateEdit:hover, QTimeEdit:hover, QSpinBox:hover, QComboBox:hover { border-color: #4C566A; }
QPushButton { background: #434C5E; border: 1px solid #4C566A; border-radius: 6px; padding: 6px 14px; color: #D8DEE9; font-weight: 500; }
QPushButton:hover { background: #4C566A; border-color: #5E6A7E; }
QLineEdit, QPlainTextEdit { background: #3B4252; border: 1px solid #434C5E; border-radius: 6px; padding: 6px 10px; color: #D8DEE9; selection-background-color: #88C0D0; selection-color: #2E3440; }
QLineEdit:focus, QPlainTextEdit:focus { border-color: #88C0D0; }
QSplitter::handle { background: transparent; }
QSplitter::handle:hover { background: #434C5E; }
QMenu { background: #3B4252; border: 1px solid #434C5E; border-radius: 6px; padding: 4px; }
QMenu::item { padding: 6px 24px 6px 16px; border-radius: 4px; color: #D8DEE9; }
QMenu::item:selected { background: #88C0D0; color: #2E3440; }
QToolTip { background: #3B4252; color: #D8DEE9; border: 1px solid #434C5E; border-radius: 4px; padding: 4px; }
QLabel#HeaderLabel { font-size: 11pt; font-weight: bold; color: #88C0D0; padding: 6px 4px; }
QWidget#TaskCard { background: #3B4252; border: 1px solid #434C5E; border-radius: 8px; }
QWidget#TaskCard:hover { border-color: #4C566A; background: #434C5E; }
"""


# ----------------------------------------------------------------- main window
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_TITLE)
        self.resize(1180, 760)
        self.setMinimumSize(940, 560)

        self._backup_db()
        self.store = TaskStore(STORE_DB, LEGACY_JSON)
        self.store.prune_activity(ACTIVITY_KEEP_DAYS)
        if self.store.fresh_file and SEED_DEMO_TASKS: self._seed_demo()

        self.current_date = QDate.currentDate()
        self.view_mode = "day"
        self._selected_id: str | None = None
        self._pending_select: str | None = None
        self._day_tasks: list[Task] = []
        self._visible: list[Task] = []
        self._display_index: dict[str, Task] = {}
        self._filter = ""
        self._notified: set[str] = set()
        self._dl_notified: set[tuple] = set()
        self._eod_done = ""
        self._force_quit = False
        self._tray_hinted = False
        self._focus: FocusOverlay | None = None

        self.idle = IdleMonitor()
        self._activity_cache: dict[str, set[int]] = {}
        self._recorded: set[int] = set()
        self._last_idle: float | None = None
        self._track_date = QDate.currentDate().toString("yyyy-MM-dd")

        self.pomo_state = "idle"
        self.pomo_phase = "work"
        self.pomo_end = 0.0
        self.pomo_remaining = 0.0
        self.pomo_title = ""
        self.pomo_count = 0
        self.pomo_total_duration = 0
        self.pomo_timer = QTimer(self)
        self.pomo_timer.setInterval(1000)
        self.pomo_timer.timeout.connect(self._pomo_tick)

        self._wt_id: str | None = None
        self._wt_t0 = 0.0
        self.wt_timer = QTimer(self)
        self.wt_timer.setInterval(1000)
        self.wt_timer.timeout.connect(self._wt_paint)

        self._build_toolbar()
        self._build_central()
        self._build_statusbar()
        self._build_undo()
        self._bind_shortcuts()

        self._app_icon = _make_icon(ACCENT_COLOR)
        self.setWindowIcon(self._app_icon)
        self._apply_config()
        self._init_tray()
        self._restore_state()

        self.refresh()
        QTimer.singleShot(80, self._scroll_to_working_area)

        clock = QTimer(self)
        clock.timeout.connect(self._on_clock)
        clock.start(30_000)

    def _build_toolbar(self):
        tb = QToolBar("Main")
        tb.setMovable(False)
        tb.setObjectName("MainToolbar")
        self.addToolBar(tb)

        self.act_prev = QAction("◀", self)
        self.act_next = QAction("▶", self)
        self.act_today = QAction("Today", self)
        self.act_new = QAction("＋ New task", self)
        self.act_new.setShortcut(QKeySequence("Ctrl+N"))
        self.act_backlog_new = QAction("＋ Backlog", self)
        self.act_backlog_new.setShortcut(QKeySequence("Ctrl+B"))
        self.act_edit = QAction("Edit", self)
        self.act_edit.setShortcut(QKeySequence("Ctrl+E"))
        self.act_delete = QAction("Delete", self)
        self.act_duplicate = QAction("Duplicate", self)
        self.act_duplicate.setShortcut(QKeySequence("Ctrl+D"))
        self.act_copy_day = QAction("Copy day →", self)
        self.act_plan = QAction("⚡ Plan day", self)
        self.act_plan.setToolTip("Auto-schedule the backlog into free slots")
        self.act_review = QAction("🌙 Review", self)
        self.act_review.setToolTip("End-of-day review wizard")
        self.act_find_slot = QAction("Find free slot…", self)
        self.act_stats = QAction("📊 Stats…", self)
        self.act_search = QAction("🔍 Search…", self)
        self.act_search.setShortcut(QKeySequence("Ctrl+Shift+F"))
        self.act_due = QAction("⚑ Due…", self)
        self.act_palette = QAction("⌘ Commands…", self)
        self.act_palette.setShortcut(QKeySequence("Ctrl+K"))
        self.act_import_ics = QAction("Import ICS…", self)
        self.act_export_ics = QAction("Export ICS…", self)
        self.act_export = QAction("Export CSV…", self)
        self.act_cleanup = QAction("Clean up completed…", self)
        self.act_settings = QAction("⚙ Settings…", self)

        self.act_day = QAction("Day", self)
        self.act_day.setCheckable(True)
        self.act_day.setChecked(True)
        self.act_week = QAction("Week", self)
        self.act_week.setCheckable(True)
        grp = QActionGroup(self)
        grp.setExclusive(True)
        grp.addAction(self.act_day)
        grp.addAction(self.act_week)

        tb.addAction(self.act_prev)
        tb.addAction(self.act_today)
        tb.addWidget(self._build_date_edit())
        tb.addAction(self.act_next)
        tb.addSeparator()
        tb.addAction(self.act_day)
        tb.addAction(self.act_week)
        tb.addSeparator()
        tb.addAction(self.act_new)
        tb.addAction(self.act_backlog_new)
        tb.addAction(self.act_edit)
        tb.addAction(self.act_duplicate)
        tb.addAction(self.act_delete)
        tb.addSeparator()
        tb.addAction(self.act_plan)
        tb.addAction(self.act_copy_day)
        tb.addAction(self.act_review)
        tb.addSeparator()
        tb.addAction(self.act_find_slot)
        tb.addAction(self.act_search)
        tb.addAction(self.act_due)
        tb.addAction(self.act_stats)
        tb.addAction(self.act_palette)

        gear = QToolButton()
        gear.setText("⚙")
        gear.setToolTip("Settings and data")
        gear.setPopupMode(QToolButton.InstantPopup)
        gear_menu = QMenu(gear)
        gear_menu.addAction(self.act_settings)
        gear_menu.addSeparator()
        self.templates_menu = QMenu("Templates", gear_menu)
        gear_menu.addMenu(self.templates_menu)
        self.templates_menu.aboutToShow.connect(self._fill_templates)
        gear_menu.addSeparator()
        gear_menu.addAction(self.act_import_ics)
        gear_menu.addAction(self.act_export_ics)
        gear_menu.addAction(self.act_export)
        gear_menu.addSeparator()
        gear_menu.addAction(self.act_cleanup)
        gear.setMenu(gear_menu)
        tb.addWidget(gear)
        
        self.gear_menu = gear_menu

        self.act_prev.triggered.connect(lambda: self._shift_day(-1))
        self.act_next.triggered.connect(lambda: self._shift_day(1))
        self.act_today.triggered.connect(self._go_today)
        self.act_day.triggered.connect(lambda: self._set_view_mode("day"))
        self.act_week.triggered.connect(lambda: self._set_view_mode("week"))
        self.act_new.triggered.connect(lambda: self.new_task())
        self.act_backlog_new.triggered.connect(self.new_backlog_task)
        self.act_edit.triggered.connect(self.edit_selected)
        self.act_duplicate.triggered.connect(self.duplicate_selected)
        self.act_delete.triggered.connect(self.delete_selected)
        self.act_plan.triggered.connect(self.plan_my_day)
        self.act_copy_day.triggered.connect(self.copy_day_forward)
        self.act_review.triggered.connect(self.open_review)
        self.act_find_slot.triggered.connect(self.find_free_slot)
        self.act_search.triggered.connect(self.open_search)
        self.act_due.triggered.connect(self.open_deadlines)
        self.act_stats.triggered.connect(self.open_stats)
        self.act_palette.triggered.connect(self.open_palette)
        self.act_settings.triggered.connect(lambda: SettingsDialog(self).exec())
        self.act_export.triggered.connect(self.export_csv)
        self.act_import_ics.triggered.connect(self.import_ics)
        self.act_export_ics.triggered.connect(self.export_ics)
        self.act_cleanup.triggered.connect(self.cleanup_old_completed)

    def _apply_config(self):
        global WORK_START, WORK_END, SNAP_MIN, PLAN_BUFFER_MIN, POMODORO_WORK_MIN, POMODORO_BREAK_MIN, NOTIFY_LEAD_MIN, CATEGORIES, ACCENT_COLOR
        s = self.store.settings
        WORK_START = int(s.get("work_start", 8))
        WORK_END = int(s.get("work_end", 18))
        SNAP_MIN = int(s.get("snap_min", 5))
        PLAN_BUFFER_MIN = int(s.get("plan_buffer_min", 5))
        POMODORO_WORK_MIN = int(s.get("pomo_work_min", 25))
        POMODORO_BREAK_MIN = int(s.get("pomo_break_min", 5))
        NOTIFY_LEAD_MIN = int(s.get("notify_lead_min", 10))

        CATEGORIES.clear()
        CATEGORIES.update(DEFAULT_CATEGORIES)
        CATEGORIES.update(s.get("categories", {}))
        
        ACCENT_COLOR = s.get("accent", "#1a1a1a")
        scheme = s.get("scheme", "Minimal Dark" if s.get("dark") else "Minimal Light")
        
        app = QApplication.instance()
        dark_mode = False
        
        if scheme == "Minimal Dark":
            dark_mode = True
            app.setPalette(_make_palette(True))
            app.setStyleSheet(DARK_STYLESHEET)
        elif scheme == "Sepia":
            dark_mode = False
            app.setPalette(_make_sepia_palette())
            app.setStyleSheet(SEPIA_STYLESHEET)
        elif scheme == "Nordic":
            dark_mode = True
            app.setPalette(_make_nordic_palette())
            app.setStyleSheet(NORDIC_STYLESHEET)
        else:
            dark_mode = False
            app.setPalette(_make_palette(False))
            app.setStyleSheet(LIGHT_STYLESHEET)

        self._app_icon = _make_icon(ACCENT_COLOR)
        app.setWindowIcon(self._app_icon)
        self.setWindowIcon(self._app_icon)
        if hasattr(self, 'tray') and self.tray is not None:
            self.tray.setIcon(self._app_icon)
            
        self.timeline.set_dark(dark_mode)
        self.week.set_dark(dark_mode)
        self.timeline.update()
        self.week.update()
        if hasattr(self, 'stats'): self.refresh()
        self._update_title()

    def _build_undo(self):
        self.undo_stack = QUndoStack(self)
        self.undo_stack.setUndoLimit(200)
        self.act_undo = QAction("Undo", self)
        self.act_undo.setShortcut(QKeySequence("Ctrl+Z"))
        self.act_undo.triggered.connect(self._smart_undo)
        self.act_redo = QAction("Redo", self)
        self.act_redo.setShortcuts([QKeySequence("Ctrl+Y"), QKeySequence("Ctrl+Shift+Z")])
        self.act_redo.triggered.connect(self._smart_redo)
        self.act_undo.setEnabled(False)
        self.act_redo.setEnabled(False)
        self.undo_stack.canUndoChanged.connect(self.act_undo.setEnabled)
        self.undo_stack.canRedoChanged.connect(self.act_redo.setEnabled)
        self.undo_stack.undoTextChanged.connect(lambda t: self.act_undo.setText(f"Undo · {t}" if t else "Undo"))
        self.undo_stack.redoTextChanged.connect(lambda t: self.act_redo.setText(f"Redo · {t}" if t else "Redo"))
        
        if hasattr(self, 'gear_menu'):
            self.gear_menu.insertAction(self.act_settings, self.act_undo)
            self.gear_menu.insertAction(self.act_settings, self.act_redo)
            self.gear_menu.insertSeparator(self.act_settings)

    def _smart_undo(self):
        w = QApplication.focusWidget()
        if isinstance(w, (QLineEdit, QPlainTextEdit)) and w.isUndoRedoEnabled(): w.undo()
        else: self.undo_stack.undo()

    def _smart_redo(self):
        w = QApplication.focusWidget()
        if isinstance(w, (QLineEdit, QPlainTextEdit)) and w.isUndoRedoEnabled(): w.redo()
        else: self.undo_stack.redo()

    def _build_date_edit(self):
        self.date_edit = QDateEdit(self.current_date)
        self.date_edit.setCalendarPopup(True)
        self.date_edit.setDisplayFormat("ddd, d MMM yyyy")
        self.date_edit.setFixedWidth(175)
        self.date_edit.dateChanged.connect(self._on_date_changed)
        return self.date_edit

    def _build_central(self):
        left_widget = QWidget()
        left_widget.setMaximumWidth(360)
        left_widget.setMinimumWidth(280)
        lv = QVBoxLayout(left_widget)
        lv.setContentsMargins(12, 12, 8, 12)
        lv.setSpacing(12)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Filter today…  (Ctrl+F)")
        self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(self._on_filter_changed)
        lv.addWidget(self.search)

        today_header = QHBoxLayout()
        today_label = QLabel("Today's Plan")
        today_label.setObjectName("HeaderLabel")
        today_header.addWidget(today_label)
        today_header.addStretch(1)
        add_btn = QToolButton()
        add_btn.setText("＋")
        add_btn.setToolTip("New task")
        add_btn.setAutoRaise(True)
        add_btn.clicked.connect(lambda: self.new_task())
        today_header.addWidget(add_btn)
        lv.addLayout(today_header)

        self.list = QListWidget()
        self.list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._list_menu)
        self.list.itemDoubleClicked.connect(lambda _item: self.edit_selected())
        self.list.currentRowChanged.connect(self._on_row_changed)
        self.list.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        self.list.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        lv.addWidget(self.list, 1)

        backlog_header = QHBoxLayout()
        self.backlog_header = QLabel("Backlog")
        self.backlog_header.setObjectName("HeaderLabel")
        backlog_header.addWidget(self.backlog_header)
        backlog_header.addStretch(1)
        add_bl_btn = QToolButton()
        add_bl_btn.setText("＋")
        add_bl_btn.setToolTip("New backlog task")
        add_bl_btn.setAutoRaise(True)
        add_bl_btn.clicked.connect(self.new_backlog_task)
        backlog_header.addWidget(add_bl_btn)
        lv.addLayout(backlog_header)

        self.backlog = BacklogList()
        self.backlog.itemDoubleClicked.connect(self._backlog_double_clicked)
        self.backlog.customContextMenuRequested.connect(self._backlog_menu)
        lv.addWidget(self.backlog)

        self.timeline = Timeline()
        self.timeline.taskClicked.connect(self._on_timeline_click)
        self.timeline.taskActivated.connect(self._on_timeline_activate)
        self.timeline.taskMoved.connect(self._on_task_moved)
        self.timeline.slotActivated.connect(self._on_slot_double_clicked)
        self.timeline.backlogDropped.connect(self._on_backlog_dropped)
        self.timeline.rangeSelected.connect(self._on_day_range)

        self.timeline_scroll = QScrollArea()
        self.timeline_scroll.setWidgetResizable(True)
        self.timeline_scroll.setWidget(self.timeline)
        self.timeline_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        self.week = WeekView()
        self.week.taskClicked.connect(self._on_week_click)
        self.week.taskActivated.connect(self._on_week_activate)
        self.week.taskMoved.connect(self._on_week_task_moved)
        self.week.slotActivated.connect(self._on_week_slot)
        self.week.backlogDroppedAt.connect(self._on_week_backlog_dropped)
        self.week.headerClicked.connect(self._on_week_header)
        self.week.weekRangeSelected.connect(self._on_week_range)

        self.week_scroll = QScrollArea()
        self.week_scroll.setWidgetResizable(True)
        self.week_scroll.setWidget(self.week)
        self.week_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        self.stack = QStackedWidget()
        self.stack.addWidget(self.timeline_scroll)
        self.stack.addWidget(self.week_scroll)

        splitter = QSplitter(Qt.Horizontal)
        splitter.setHandleWidth(6)
        splitter.addWidget(left_widget)
        splitter.addWidget(self.stack)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([320, 800])
        self.main_splitter = splitter
        self.setCentralWidget(splitter)

    def _build_statusbar(self):
        self.stats = QLabel()
        self.next_up = QLabel()
        sb = QStatusBar()
        sb.addWidget(self.stats)
        sb.addPermanentWidget(self._build_pomodoro())
        sb.addPermanentWidget(self.next_up)
        self.setStatusBar(sb)

    def _build_pomodoro(self) -> QWidget:
        w = QWidget()
        h = QHBoxLayout(w)
        h.setContentsMargins(0, 0, 0, 0)
        h.setSpacing(6)
        self.pomo_btn = QToolButton()
        self.pomo_btn.setText("▶")
        self.pomo_btn.setToolTip("Start / pause pomodoro for the selected task")
        self.pomo_stop = QToolButton()
        self.pomo_stop.setText("⏹")
        self.pomo_stop.setEnabled(False)
        self.pomo_stop.setToolTip("Stop the pomodoro")
        self.focus_btn = QToolButton()
        self.focus_btn.setText("🎯")
        self.focus_btn.setToolTip("Focus mode — fullscreen the current task (F)")
        self.pomo_label = QLabel("")
        self.wt_btn = QToolButton()
        self.wt_btn.setText("⏱ Start")
        self.wt_btn.setToolTip("Start / stop the work timer for the selected task")
        self.wt_label = QLabel("")
        h.addWidget(self.pomo_btn)
        h.addWidget(self.pomo_stop)
        h.addWidget(self.focus_btn)
        h.addWidget(self.wt_btn)
        h.addWidget(self.wt_label)
        h.addWidget(self.pomo_label)
        self.pomo_btn.clicked.connect(self._pomo_toggle)
        self.pomo_stop.clicked.connect(self._pomo_stop)
        self.focus_btn.clicked.connect(self.enter_focus)
        self.wt_btn.clicked.connect(self._wt_toggle)
        return w

    def _bind_shortcuts(self):
        QShortcut(QKeySequence("Ctrl+F"), self, self._focus_search)
        QShortcut(QKeySequence("Ctrl+K"), self, self.open_palette)
        QShortcut(QKeySequence("Ctrl+Shift+Up"), self.list, lambda: self._shift_selected_time(-SNAP_MIN))
        QShortcut(QKeySequence("Ctrl+Shift+Down"), self.list, lambda: self._shift_selected_time(SNAP_MIN))
        QShortcut(QKeySequence("Ctrl+Shift+Left"), self.list, lambda: self._shift_selected_day(-1))
        QShortcut(QKeySequence("Ctrl+Shift+Right"), self.list, lambda: self._shift_selected_day(1))
        for target in (self.list, self.week):
            for key in (Qt.Key_Delete, Qt.Key_Backspace):
                sc = QShortcut(QKeySequence(key), target)
                sc.setContext(Qt.WidgetShortcut)
                sc.activated.connect(self.delete_selected)
        for seq, fn in (("J", lambda: self._nav(1)),
                        ("K", lambda: self._nav(-1)),
                        ("T", self._toggle_selected_done),
                        ("F", self.enter_focus),
                        ("1", lambda: self._apply_category(0)),
                        ("2", lambda: self._apply_category(1)),
                        ("3", lambda: self._apply_category(2)),
                        ("4", lambda: self._apply_category(3)),
                        ("5", lambda: self._apply_category(4))):
            sc = QShortcut(QKeySequence(seq), self.list)
            sc.setContext(Qt.WidgetShortcut)
            sc.activated.connect(fn)

    def _focus_search(self): self.search.setFocus(); self.search.selectAll()
    def _nav(self, delta: int):
        n = self.list.count()
        if n == 0: return
        r = self.list.currentRow()
        if r < 0: self.list.setCurrentRow(0 if delta > 0 else n - 1)
        else: self.list.setCurrentRow(max(0, min(n - 1, r + delta)))

    def _apply_category(self, index: int):
        t = self._selected_task()
        if t is None: return
        if is_instance(t.id):
            self.statusBar().showMessage("Repeating instance — edit the series instead (double-click)", 4000)
            return
        cat = list(CATEGORIES.keys())[index]
        before = asdict(t)
        after = dict(before)
        after["category"] = cat
        self.undo_stack.push(ModifyCmd(self, before, after, "Set category"))

    def _seed_demo(self):
        today = QDate.currentDate()
        d2 = today.addDays(2).toString("yyyy-MM-dd")
        d5 = today.addDays(5).toString("yyyy-MM-dd")
        demo = [
            ("Plan the day", "09:00", 15, "Personal", "low", "Review calendar, pick top 3 priorities.", "none", "", [], []),
            ("Team standup", "09:15", 15, "Work", "med", "", "weekdays", "", [], []),
            ("Deep work: project X", "09:30", 90, "Work", "high", "Phone on silent.", "none", d2, ["project-x"], [{"title": "Draft section 1", "done": True}, {"title": "Draft section 2", "done": False}]),
            ("Lunch + short walk", "12:30", 45, "Health", "med", "", "none", "", [], []),
            ("Study: PySide6", "16:00", 60, "Learning", "med", "", "none", d5, ["learning"], [{"title": "Chapter 4", "done": False}, {"title": "Exercises", "done": False}]),
            ("Evening review", "21:30", 10, "Personal", "low", "What went well? What moves tomorrow?", "daily", "", [], []),
        ]
        for title, start, dur, cat, prio, notes, rec, dl, tags, subs in demo:
            t = Task(id=uuid.uuid4().hex[:10], title=title, date=today.toString("yyyy-MM-dd"), start=start, duration=dur, category=cat, priority=prio, notes=notes, recurrence=rec, deadline=dl, tags=tags, subtasks=subs)
            self.store.add(t)
            self.store.upsert_task(t)
        t = Task(id=uuid.uuid4().hex[:10], title="Prepare slides for talk", date="", duration=60, category="Work", priority="high", deadline=d2)
        self.store.add(t)
        self.store.upsert_task(t)
        self.store.settings.setdefault("templates", [{"title": "Deep work block", "duration": 90, "category": "Work", "priority": "high", "notes": "Phone on silent.", "tags": [], "subtasks": []}])
        self.store.save()

    def _init_tray(self):
        self.tray: QSystemTrayIcon | None = None
        if QSystemTrayIcon.isSystemTrayAvailable():
            self.tray = QSystemTrayIcon(self._app_icon, self)
            menu = QMenu()
            act_show = QAction("Show / hide", menu)
            act_show.triggered.connect(self._toggle_visible)
            act_quit = QAction("Quit Day Planner", menu)
            act_quit.triggered.connect(self._quit_app)
            menu.addAction(act_show)
            menu.addSeparator()
            menu.addAction(act_quit)
            self.tray.setContextMenu(menu)
            self.tray.activated.connect(self._tray_activated)
            self.tray.messageClicked.connect(self._on_tray_msg_clicked)
            self._last_msg_payload = None
            self.tray.show()

    def _tray_activated(self, reason):
        if reason in (QSystemTrayIcon.Trigger, QSystemTrayIcon.DoubleClick): self._toggle_visible()

    def _toggle_visible(self):
        if self.isVisible() and not self.isMinimized(): self.hide()
        else: self.showNormal(); self.activateWindow()

    def _quit_app(self): self._force_quit = True; self.close()

    def _notify_tray(self, title: str, body: str, payload=None):
        self._last_msg_payload = payload
        if self.tray is not None: self.tray.showMessage(title, body, QSystemTrayIcon.Information, 5000)
        else: self.statusBar().showMessage(f"{title} — {body}", 5000)

    def _on_tray_msg_clicked(self):
        p = self._last_msg_payload
        self._last_msg_payload = None
        if not p: return
        if p.get("type") == "task":
            self._jump_to_search(p["id"])
            self.showNormal(); self.activateWindow()
        elif p.get("type") == "review":
            self.open_review()
            self.showNormal(); self.activateWindow()

    def _restore_state(self):
        st = QSettings("DayPlanner", "DayPlanner")
        geo = st.value("geometry")
        if geo is not None:
            try: self.restoreGeometry(geo)
            except Exception: pass
        view = st.value("view", "day")
        if view == "week": self._set_view_mode("week")
        v = st.value("split_main")
        if v is not None:
            try: self.main_splitter.restoreState(v)
            except Exception: pass

    def _save_state(self):
        st = QSettings("DayPlanner", "DayPlanner")
        st.setValue("geometry", self.saveGeometry())
        st.setValue("view", self.view_mode)
        st.setValue("split_main", self.main_splitter.saveState())

    def _check_reminders(self):
        if not self.store.settings.get("reminders", True): return
        if self.current_date != QDate.currentDate(): return
        now_ms = QTime.currentTime().msecsSinceStartOfDay()
        lead_ms = NOTIFY_LEAD_MIN * 60_000
        for t in self._day_tasks:
            if t.completed or t.id in self._notified: continue
            delta = t.start_minutes * 60_000 - now_ms
            if -60_000 <= delta <= lead_ms:
                self._notified.add(t.id)
                when = ("starting now" if delta <= 0 else f"in {max(1, math.ceil(delta / 60_000))} min")
                self._notify_tray("Upcoming task", f"{t.title} · {when}", payload={"type": "task", "id": t.id})

    def date_key(self) -> str: return self.current_date.toString("yyyy-MM-dd")

    def _effective_for(self, date_key: str) -> list[Task]:
        out: list[Task] = []
        for t in self.store.tasks:
            if not t.date: continue
            if t.recurrence == "none":
                if t.date == date_key: out.append(t)
            else:
                inst = materialize(t, date_key)
                if inst is not None: out.append(inst)
        out.sort(key=lambda t: t.start_minutes)
        return out

    def _matches(self, t: Task) -> bool:
        q = self._filter
        if not q: return True
        hay = " ".join([t.title, t.category, t.notes] + list(t.tags or [])).lower()
        return q in hay

    def _selected_task(self) -> Task | None: return self._display_index.get(self._selected_id or "")

    def _after_mutation(self, select_id: str | None):
        if select_id is not None: self._selected_id = select_id
        self.refresh()

    def _activity_for(self, date_key: str) -> set[int]:
        if date_key not in self._activity_cache:
            self._activity_cache[date_key] = self.store.activity_minutes(date_key)
        return self._activity_cache[date_key]

    def refresh(self):
        key = self.date_key()
        eff = self._effective_for(key)
        self._day_tasks = eff
        self._visible = sorted(eff, key=lambda t: (t.completed, t.start_minutes))

        wk = self.current_date.addDays(1 - self.current_date.dayOfWeek())
        week_days: dict[str, list[Task]] = {}
        week_index: dict[str, Task] = {}
        for i in range(7):
            k = wk.addDays(i).toString("yyyy-MM-dd")
            lst = self._effective_for(k)
            week_days[k] = lst
            for t in lst: week_index[t.id] = t

        day_ids = [t.id for t in self._visible]
        self._display_index = {t.id: t for t in self._visible}
        self._display_index.update(week_index)

        if self._selected_id not in self._display_index: self._selected_id = None
        restore = (day_ids.index(self._selected_id) if self._selected_id in day_ids else -1)

        self.list.blockSignals(True)
        self.list.clear()
        for t in self._visible:
            row = TaskRow(t)
            row.check.toggled.connect(lambda on, task=t: self._set_completed(task, on, advance=True))
            item = QListWidgetItem()
            item.setSizeHint(QSize(0, 62))
            self.list.addItem(item)
            self.list.setItemWidget(item, row)
        self.list.blockSignals(False)

        self.list.setCurrentRow(restore)
        self._on_row_changed(self.list.currentRow())

        self.timeline.set_date(self.current_date)
        self.timeline.set_tasks(eff)
        self.timeline.set_filter(self._filter)
        self.timeline.set_activity(self._activity_for(key))

        self.week.set_range(wk)
        self.week.set_days(week_days)
        self.week.set_selected(self._selected_id)
        self.week.set_filter(self._filter)

        self._rebuild_backlog()
        self._update_status()
        self._update_title()

        if self._pending_select is not None:
            pid = self._pending_select
            self._pending_select = None
            self._consume_pending_select(pid)

    def _update_title(self):
        if self.view_mode == "week":
            wk = self.current_date.addDays(1 - self.current_date.dayOfWeek())
            self.setWindowTitle(f"{APP_TITLE} — Week of {wk.toString('MMM d, yyyy')}")
        else:
            self.setWindowTitle(f"{APP_TITLE} — {self.current_date.toString('ddd, MMM d, yyyy')}")

    def _rebuild_backlog(self):
        bl = self.backlog
        bl.clear()
        items = [t for t in self.store.tasks if not t.date]
        for t in items:
            row = TaskRow(t)
            row.check.toggled.connect(lambda on, task=t: self._set_completed(task, on, advance=False))
            it = QListWidgetItem()
            it.setSizeHint(QSize(0, 62))
            it.setData(Qt.UserRole, t.id)
            it.setData(Qt.UserRole + 1, t.title)
            bl.addItem(it)
            bl.setItemWidget(it, row)
        self.backlog_header.setText(f"Backlog  ·  {len(items)}")

    def _on_row_changed(self, index: int):
        if 0 <= index < len(self._visible): self._selected_id = self._visible[index].id
        elif self._selected_id not in self._display_index: self._selected_id = None
        self.timeline.set_selected(self._selected_id)
        self.week.set_selected(self._selected_id)
        self._update_buttons()
        self._ensure_selected_visible()

    def _ensure_selected_visible(self):
        if self.view_mode != "day": return
        t = self._selected_task()
        if t is None or not t.date: return
        y1 = t.start_minutes * PX_PER_MIN
        y2 = t.end_minutes * PX_PER_MIN
        sb = self.timeline_scroll.verticalScrollBar()
        vh = self.timeline_scroll.viewport().height()
        top, bot = sb.value(), sb.value() + vh
        if y1 < top: sb.setValue(max(0, int(y1 - 24)))
        elif y2 > bot: sb.setValue(int(y2 - vh + 24))

    def _select_none(self):
        self._selected_id = None
        self.list.setCurrentRow(-1)
        self.timeline.set_selected(None)
        self.week.set_selected(None)
        self._update_buttons()

    def _on_timeline_click(self, tid):
        if tid is None: self._select_none(); return
        idx = next((i for i, t in enumerate(self._visible) if t.id == tid), -1)
        if idx >= 0: self.list.setCurrentRow(idx)

    def _on_timeline_activate(self, tid):
        idx = next((i for i, t in enumerate(self._visible) if t.id == tid), -1)
        if idx >= 0: self.list.setCurrentRow(idx)
        self.edit_selected()

    def _on_week_click(self, tid):
        if tid is None: self._select_none(); return
        self._selected_id = tid
        t = self._display_index.get(tid)
        if t is not None and t.date == self.date_key():
            idx = next((i for i, x in enumerate(self._visible) if x.id == tid), -1)
            if idx >= 0: self.list.setCurrentRow(idx); return
        self.week.set_selected(tid)
        self._update_buttons()

    def _on_week_activate(self, tid):
        t = self._display_index.get(tid)
        if t is None: return
        self._selected_id = tid
        self.week.set_selected(tid)
        if t.date == self.date_key():
            idx = next((i for i, x in enumerate(self._visible) if x.id == tid), -1)
            if idx >= 0: self.list.setCurrentRow(idx)
        self.edit_task(t)

    def _on_week_task_moved(self, task_id: str, new_date: str, new_start: str):
        t = self.store.get(task_id)
        if t is None: self.refresh(); return
        before = asdict(t)
        if before.get("date") == new_date and before.get("start") == new_start: self.refresh(); return
        after = dict(before)
        after["date"] = new_date
        after["start"] = new_start
        if not self._confirm_overlap(Task(**after)): self.refresh(); return
        self.undo_stack.push(ModifyCmd(self, before, after, "Move task"))

    def _on_week_slot(self, date_key: str, minutes: int):
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        if d.isValid(): self.new_task(start_min=minutes, qdate=d)

    def _on_week_backlog_dropped(self, task_id: str, date_key: str, minutes: int):
        t = self.store.get(task_id)
        if t is None or t.date: return
        after = asdict(t)
        after["date"] = date_key
        after["start"] = mm_to_str(minutes)
        if not self._confirm_overlap(Task(**after)):
            self.statusBar().showMessage("Cancelled — task stays in the backlog", 4000)
            self.refresh(); return
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        if d.isValid() and d != self.current_date: self.date_edit.setDate(d)
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Schedule from backlog"))

    def _on_week_header(self, date_key: str):
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        if d.isValid() and d != self.current_date: self.date_edit.setDate(d)

    def _on_day_range(self, start_min: int, end_min: int):
        self.new_task(start_min=start_min, duration=max(5, end_min - start_min))

    def _on_week_range(self, date_key: str, start_min: int, end_min: int):
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        if d.isValid(): self.new_task(start_min=start_min, duration=max(5, end_min - start_min), qdate=d)

    def _set_completed(self, task: Task, on: bool, advance: bool = False):
        if is_instance(task.id):
            a = self.store.get(base_id(task.id))
            if a is None: return
            if (task.date in (a.done_dates or [])) == on: return
            self.undo_stack.push(ToggleOccurrenceCmd(self, a, task.date, on))
        else:
            if task.completed == on: return
            before = asdict(task)
            after = dict(before)
            after["completed"] = on
            self.undo_stack.push(ModifyCmd(self, before, after, "Mark done" if on else "Mark not done"))
            
        if on and advance:
            QTimer.singleShot(50, self._select_next_undone)

    def _select_next_undone(self):
        if not self._visible: return
        curr_idx = self.list.currentRow()
        for i in range(curr_idx + 1, len(self._visible)):
            if not self._visible[i].completed:
                self.list.setCurrentRow(i)
                return
        for i in range(0, curr_idx):
            if not self._visible[i].completed:
                self.list.setCurrentRow(i)
                return

    def _toggle_selected_done(self):
        t = self._selected_task()
        if t is not None: self._set_completed(t, not t.completed, advance=True)

    def _on_filter_changed(self, text: str): self._filter = text.strip(); self.refresh()
    def _on_date_changed(self, qdate: QDate):
        self.current_date = qdate
        self._selected_id = None
        self._notified.clear()
        self.refresh()
        self._scroll_to_working_area()

    def _shift_day(self, delta: int):
        step = 7 if self.view_mode == "week" else 1
        self.date_edit.setDate(self.current_date.addDays(delta * step))

    def _go_today(self): self.date_edit.setDate(QDate.currentDate())

    def _set_view_mode(self, mode: str):
        if mode == self.view_mode:
            self.stack.setCurrentIndex(0 if mode == "day" else 1)
            return
        self.view_mode = mode
        self.stack.setCurrentIndex(0 if mode == "day" else 1)
        self.refresh()
        QTimer.singleShot(40, self._scroll_to_working_area)
        self._update_title()

    def _scroll_to_working_area(self):
        scroll = self.timeline_scroll if self.view_mode == "day" else self.week_scroll
        y = 7 * HOUR_H
        if self.current_date == QDate.currentDate():
            n = QTime.currentTime()
            y = max(0, (n.hour() * 60 + n.minute() - 40) * PX_PER_MIN)
        scroll.verticalScrollBar().setValue(int(y))

    def _on_task_moved(self, task_id: str, orig_start: str):
        t = self.store.get(task_id)
        if t is None or t.start == orig_start: self.refresh(); return
        before = asdict(t)
        before["start"] = orig_start
        self.undo_stack.push(ModifyCmd(self, before, asdict(t), "Move task"))

    def _on_slot_double_clicked(self, minutes: int): self.new_task(start_min=minutes)

    def _on_backlog_dropped(self, task_id: str, minutes: int):
        t = self.store.get(task_id)
        if t is None or t.date: return
        after = asdict(t)
        after["date"] = self.date_key()
        after["start"] = mm_to_str(minutes)
        if not self._confirm_overlap(Task(**after)):
            self.statusBar().showMessage("Cancelled — task stays in the backlog", 4000)
            return
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Schedule from backlog"))

    def _busy_blocks(self, date_key: str) -> list[list[int]]:
        merged: list[list[int]] = []
        for t in self._effective_for(date_key):
            s, e = t.start_minutes, min(t.end_minutes, DAY_MINUTES)
            if merged and s <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], e)
            else: merged.append([s, e])
        return merged

    def _plan_gaps(self, date_key: str, from_min: int | None = None) -> list[tuple[int, int]]:
        lo = WORK_START * 60
        hi = WORK_END * 60
        if from_min is not None: lo = max(lo, from_min)
        elif date_key == QDate.currentDate().toString("yyyy-MM-dd"):
            n = QTime.currentTime()
            m = ((n.hour() * 60 + n.minute()) + SNAP_MIN - 1) // SNAP_MIN * SNAP_MIN
            lo = max(lo, m)
        gaps: list[tuple[int, int]] = []
        cur = lo
        for s, e in self._busy_blocks(date_key):
            if cur >= hi: break
            if s > cur: gaps.append((cur, min(s, hi)))
            cur = max(cur, e)
        if cur < hi: gaps.append((cur, hi))
        return gaps

    def compute_plan(self, date_key: str) -> list[tuple[Task, int]]:
        items = [t for t in self.store.tasks if not t.date]
        if not items: return []
        today = QDate.currentDate()
        prio = {"high": 0, "med": 1, "low": 2}
        def sort_key(t: Task):
            d = QDate.fromString(t.deadline, "yyyy-MM-dd") if t.deadline else QDate()
            if d.isValid(): return (0, today.daysTo(d), prio.get(t.priority, 1), -t.duration)
            return (1, 0, prio.get(t.priority, 1), -t.duration)
        items.sort(key=sort_key)
        gaps = self._plan_gaps(date_key)
        out: list[tuple[Task, int]] = []
        if not gaps: return out
        gi = 0
        cur = gaps[0][0]
        for t in items:
            placed = False
            while gi < len(gaps):
                s, e = gaps[gi]
                cur = max(cur, s)
                if cur + t.duration <= e:
                    out.append((t, cur))
                    cur += t.duration + PLAN_BUFFER_MIN
                    placed = True
                    break
                gi += 1
                if gi < len(gaps): cur = gaps[gi][0]
            if not placed: break
        return out

    def _apply_plan(self, date_key: str, placements: list[tuple[Task, int]]):
        self.undo_stack.beginMacro("Plan day")
        for t, m in placements:
            before = asdict(t)
            after = dict(before)
            after["date"] = date_key
            after["start"] = mm_to_str(m)
            self.undo_stack.push(ModifyCmd(self, before, after, "Schedule task"))
        self.undo_stack.endMacro()
        d = QDate.fromString(date_key, "yyyy-MM-dd")
        if d.isValid() and d != self.current_date: self.date_edit.setDate(d)

    def plan_my_day(self):
        key = self.date_key()
        placements = self.compute_plan(key)
        if not placements:
            QMessageBox.information(self, "Plan my day", "Backlog is empty or nothing fits in today's free slots.\nAdd unscheduled tasks with ＋ Backlog first.")
            return
        dlg = PlanDialog(self, placements, key)
        if dlg.exec() == QDialog.Accepted: self._apply_plan(key, placements)

    def open_review(self): ReviewDialog(self).exec()

    def enter_focus(self):
        if self._focus is not None:
            self._focus.raise_()
            self._focus.activateWindow()
            return
        t = self._selected_task()
        if t is not None: self.pomo_title = t.title
        if self.pomo_state == "idle":
            if t is None:
                self.statusBar().showMessage("Select a task first, then enter focus mode", 4000)
                return
            self.pomo_title = t.title
            self.pomo_count = 0
            self._pomo_begin("work")
        self._focus = FocusOverlay(self)
        self._focus.show()

    def new_task(self, start_min: int | None = None, duration: int | None = None, qdate: QDate | None = None):
        dlg = TaskDialog(self, qdate=qdate or self.current_date, start_min=start_min, duration=duration)
        while dlg.exec() == QDialog.Accepted:
            task = dlg.build_task()
            if self._confirm_overlap(task):
                if task.date and task.date != self.date_key():
                    d = QDate.fromString(task.date, "yyyy-MM-dd")
                    if d.isValid(): self.date_edit.setDate(d)
                if self._filter and task.date and not self._matches(task): self.search.clear()
                self.undo_stack.push(AddCmd(self, task))
                break

    def new_backlog_task(self):
        dlg = TaskDialog(self, qdate=self.current_date, backlog=True)
        while dlg.exec() == QDialog.Accepted:
            task = dlg.build_task()
            self.undo_stack.push(AddCmd(self, task, "Add to backlog"))
            break

    def edit_selected(self):
        t = self._selected_task()
        if t is not None: self.edit_task(t)

    def edit_task(self, t: Task):
        if is_instance(t.id): self._edit_occurrence(t)
        else: self._edit_single(t)

    def _edit_single(self, t: Task):
        dlg = TaskDialog(self, task=t, qdate=QDate.fromString(t.date, "yyyy-MM-dd") if t.date else self.current_date)
        while dlg.exec() == QDialog.Accepted:
            updated = dlg.build_task()
            if self._confirm_overlap(updated):
                self.undo_stack.push(ModifyCmd(self, asdict(t), asdict(updated), "Edit task"))
                break

    def _edit_occurrence(self, inst: Task):
        anchor = self.store.get(base_id(inst.id))
        if anchor is None: return
        dlg = TaskDialog(self, task=inst, allow_backlog=False)
        while dlg.exec() == QDialog.Accepted:
            updated = dlg.build_task()
            box = QMessageBox(self)
            box.setIcon(QMessageBox.Question)
            box.setWindowTitle("Repeating task")
            box.setText(f"“{inst.title}” repeats ({rec_label(anchor.recurrence).lower()}).\nApply changes to just this occurrence or the whole series?")
            only_b = box.addButton("Only this occurrence", QMessageBox.ActionRole)
            all_b = box.addButton("All occurrences", QMessageBox.ActionRole)
            box.addButton(QMessageBox.Cancel)
            box.exec()
            if box.clickedButton() == only_b:
                one = updated
                one.id = uuid.uuid4().hex[:10]
                one.date = updated.date or inst.date
                one.recurrence = "none"
                one.ex_dates = []
                one.done_dates = []
                one.work_dates = {}
                one.recurring_instance = False
                if not self._confirm_overlap(one, exclude_base=anchor.id): continue
                self.undo_stack.beginMacro("Edit this occurrence")
                self.undo_stack.push(SkipOccurrenceCmd(self, anchor, inst.date, True))
                self.undo_stack.push(AddCmd(self, one, "Add occurrence"))
                self.undo_stack.endMacro()
                break
            if box.clickedButton() == all_b:
                after = asdict(updated)
                after.update(id=anchor.id, date=anchor.date, ex_dates=list(anchor.ex_dates), done_dates=list(anchor.done_dates), completed=anchor.completed)
                if not self._confirm_overlap(Task(**after), exclude_base=anchor.id): continue
                self.undo_stack.push(ModifyCmd(self, asdict(anchor), after, "Edit series"))
                break

    def duplicate_selected(self):
        t = self._selected_task()
        if t is None: return
        d = asdict(t)
        d["id"] = uuid.uuid4().hex[:10]
        d["completed"] = False
        d["ex_dates"] = []
        d["done_dates"] = []
        d["work_dates"] = {}
        d["recurring_instance"] = False
        if t.date:
            d["start"] = mm_to_str(min(t.end_minutes, DAY_MINUTES - t.duration))
            if is_instance(t.id): d["recurrence"] = "none"
        self.undo_stack.push(AddCmd(self, Task(**d), "Duplicate task"))

    def delete_selected(self):
        t = self._selected_task()
        if t is None: return
        if is_instance(t.id):
            anchor = self.store.get(base_id(t.id))
            if anchor is None: return
            box = QMessageBox(self)
            box.setIcon(QMessageBox.Question)
            box.setWindowTitle("Delete repeating task")
            box.setText(f"“{t.title}” repeats ({rec_label(anchor.recurrence).lower()}).\nDelete just this occurrence or the whole series?")
            occ_b = box.addButton("Only this occurrence", QMessageBox.ActionRole)
            ser_b = box.addButton("Whole series", QMessageBox.ActionRole)
            box.addButton(QMessageBox.Cancel)
            box.exec()
            if box.clickedButton() == occ_b: self.undo_stack.push(SkipOccurrenceCmd(self, anchor, t.date, True))
            elif box.clickedButton() == ser_b:
                if QMessageBox.question(self, "Delete series", f"Delete “{anchor.title}” and all its occurrences?") == QMessageBox.StandardButton.Yes:
                    self.undo_stack.push(DeleteCmd(self, [anchor], "Delete series"))
            return
        if QMessageBox.question(self, "Delete task", f"Delete “{t.title}”?") == QMessageBox.StandardButton.Yes:
            self.undo_stack.push(DeleteCmd(self, [t], "Delete task"))

    def _confirm_overlap(self, task: Task, exclude_base: str | None = None) -> bool:
        if not task.date: return True
        base = base_id(task.id)
        clashes = [o for o in self._effective_for(task.date)
                   if base_id(o.id) != base
                   and (exclude_base is None or base_id(o.id) != exclude_base)
                   and o.start_minutes < task.end_minutes
                   and task.start_minutes < o.end_minutes]
        if not clashes: return True
        detail = "\n".join(f"•  {o.time_range}   {o.title}" for o in clashes)
        answer = QMessageBox.question(self, "Overlapping tasks", f"“{task.title}” ({task.time_range}) overlaps with:\n\n{detail}\n\nSchedule anyway?")
        return answer == QMessageBox.StandardButton.Yes

    def copy_day_forward(self):
        key = self.date_key()
        src = [t for t in self.store.tasks if t.date == key and t.recurrence == "none"]
        if not src:
            QMessageBox.information(self, "Copy day", "Nothing to copy — this day is empty.")
            return
        target = self.current_date.addDays(1)
        tkey = target.toString("yyyy-MM-dd")
        existing = sum(1 for t in self.store.tasks if t.date == tkey)
        msg = (f"Copy {len(src)} task(s) to {target.toString('ddd, d MMM yyyy')}?")
        if existing: msg += (f"\n\nThat day already has {existing} task(s) — copies will be added alongside them.")
        msg += "\nRepeating tasks are not copied (they continue automatically)."
        if QMessageBox.question(self, "Copy day", msg) != QMessageBox.StandardButton.Yes: return
        self.undo_stack.beginMacro(f"Copy day → {target.toString('d MMM')}")
        for t in src:
            d = asdict(t)
            d.update(id=uuid.uuid4().hex[:10], date=tkey, completed=False, work_dates={})
            self.undo_stack.push(AddCmd(self, Task(**d), "Add copy", select=False))
        self.undo_stack.endMacro()
        if QMessageBox.question(self, "Copy day", "Copies created. Open the next day now?") == QMessageBox.StandardButton.Yes:
            self.date_edit.setDate(target)

    def move_to_tomorrow(self):
        t = self._selected_task()
        if t is None or is_instance(t.id) or not t.date: return
        d = QDate.fromString(t.date, "yyyy-MM-dd").addDays(1)
        if not d.isValid(): return
        after = asdict(t)
        after["date"] = d.toString("yyyy-MM-dd")
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Move to tomorrow"))

    def _move_to_backlog(self):
        t = self._selected_task()
        if t is None or is_instance(t.id) or not t.date: return
        after = asdict(t)
        after["date"] = ""
        after["completed"] = False
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Move to backlog"))

    def _move_to_next_week(self):
        t = self._selected_task()
        if t is None or is_instance(t.id) or not t.date: return
        d = QDate.fromString(t.date, "yyyy-MM-dd").addDays(7)
        if not d.isValid(): return
        after = asdict(t)
        after["date"] = d.toString("yyyy-MM-dd")
        if not self._confirm_overlap(Task(**after)): return
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Move to next week"))

    def _shift_selected_time(self, delta_min: int):
        t = self._selected_task()
        if t is None or is_instance(t.id) or not t.date: return
        new_start = max(0, min(t.start_minutes + delta_min, DAY_MINUTES - t.duration))
        if new_start == t.start_minutes: return
        before = asdict(t)
        after = dict(before)
        after["start"] = mm_to_str(new_start)
        self.undo_stack.push(ModifyCmd(self, before, after, "Shift time"))

    def _shift_selected_day(self, delta_day: int):
        t = self._selected_task()
        if t is None or is_instance(t.id) or not t.date: return
        d = QDate.fromString(t.date, "yyyy-MM-dd").addDays(delta_day)
        if not d.isValid(): return
        after = asdict(t)
        after["date"] = d.toString("yyyy-MM-dd")
        if not self._confirm_overlap(Task(**after)): return
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Shift day"))

    def _quick_schedule_today(self, t: Task):
        if t.date: return
        gaps = self._plan_gaps(self.date_key())
        if not gaps:
            self.statusBar().showMessage("No free working slots available today", 4000)
            return
        start_min = gaps[0][0]
        after = asdict(t)
        after["date"] = self.date_key()
        after["start"] = mm_to_str(start_min)
        if not self._confirm_overlap(Task(**after)): return
        self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Quick schedule"))

    def _move_unfinished(self):
        open_tasks = [t for t in self._day_tasks if not t.completed and t.date and not is_instance(t.id)]
        if not open_tasks:
            QMessageBox.information(self, "Nothing to move", "No unfinished tasks today. Nice.")
            return
        if QMessageBox.question(self, "Move unfinished", f"Move {len(open_tasks)} unfinished task(s) to tomorrow?") == QMessageBox.StandardButton.Yes:
            self.undo_stack.beginMacro("Move unfinished to tomorrow")
            for t in open_tasks:
                after = asdict(t)
                after["date"] = QDate.fromString(t.date, "yyyy-MM-dd").addDays(1).toString("yyyy-MM-dd")
                self.undo_stack.push(ModifyCmd(self, asdict(t), after, "Move"))
            self.undo_stack.endMacro()

    def _delete_completed(self):
        targets = [t for t in self.store.tasks if t.date == self.date_key() and t.completed and t.recurrence == "none"]
        if not targets: return
        if QMessageBox.question(self, "Delete completed", f"Delete {len(targets)} completed task(s)?") == QMessageBox.StandardButton.Yes:
            self.undo_stack.push(DeleteCmd(self, targets, "Delete completed"))

    def _backlog_task_at(self, item) -> Task | None: return self.store.get(item.data(Qt.UserRole)) if item else None
    def _backlog_double_clicked(self, item):
        t = self._backlog_task_at(item)
        if t is not None: self.edit_task(t)

    def _backlog_menu(self, pos):
        menu = QMenu(self)
        item = self.backlog.itemAt(pos)
        if item is not None:
            t = self._backlog_task_at(item)
            if t is not None:
                menu.addAction("Quick schedule (next free today)", lambda: self._quick_schedule_today(t))
                menu.addAction("Schedule for today…", lambda: self._schedule_backlog(t))
                menu.addAction("Edit…", lambda: self.edit_task(t))
                menu.addSeparator()
                menu.addAction("Delete", lambda: self.undo_stack.push(DeleteCmd(self, [t], "Delete task")))
        else: menu.addAction("New backlog task…", self.new_backlog_task)
        menu.exec(self.backlog.viewport().mapToGlobal(pos))

    def _schedule_backlog(self, t: Task):
        dlg = TaskDialog(self, task=t, qdate=self.current_date)
        while dlg.exec() == QDialog.Accepted:
            updated = dlg.build_task()
            if self._confirm_overlap(updated):
                self.undo_stack.push(ModifyCmd(self, asdict(t), asdict(updated), "Schedule task"))
                break

    def _free_gaps(self, needed: int, from_min: int) -> list[tuple[int, int]]:
        return [(s, e) for s, e in self._plan_gaps(self.date_key(), from_min=from_min) if e - s >= needed]

    def find_free_slot(self):
        if self.current_date == QDate.currentDate():
            now = QTime.currentTime()
            frm = (now.hour() * 60 + now.minute()) // SNAP_MIN * SNAP_MIN
        else: frm = WORK_START * 60
        dlg = FreeSlotDialog(self, self._free_gaps, frm)
        if dlg.exec() == QDialog.Accepted and dlg.chosen_start() is not None:
            self.new_task(start_min=dlg.chosen_start(), duration=dlg.ed_needed.value())

    def _fill_templates(self):
        m = self.templates_menu
        m.clear()
        tpls = self.store.settings.get("templates", []) or []
        for i, tp in enumerate(tpls):
            m.addAction(f"{tp.get('title', '?')}  ·  {fmt_minutes(tp.get('duration', 30))}", lambda i=i: self.insert_template(i))
        if tpls: m.addSeparator()
        m.addAction("Save selected task as template…", self.save_template)
        if tpls: m.addAction("Delete template…", self.delete_template)

    def save_template(self):
        t = self._selected_task()
        if t is None:
            QMessageBox.information(self, "Templates", "Select a task first.")
            return
        tpl = {"title": t.title, "duration": t.duration, "category": t.category, "priority": t.priority, "notes": t.notes, "tags": list(t.tags or []), "subtasks": [dict(s) for s in (t.subtasks or [])]}
        tpls = [x for x in (self.store.settings.get("templates") or []) if x.get("title") != t.title]
        tpls.append(tpl)
        self.store.settings["templates"] = tpls
        self.store.save()
        self.statusBar().showMessage(f"Template “{t.title}” saved", 4000)

    def insert_template(self, idx: int):
        tpls = self.store.settings.get("templates") or []
        if not (0 <= idx < len(tpls)): return
        tp = tpls[idx]
        task = Task(id=uuid.uuid4().hex[:10], title=tp.get("title", "Task"), date="", duration=int(tp.get("duration", 30)), category=tp.get("category", "Other"), priority=tp.get("priority", "med"), notes=tp.get("notes", ""), tags=list(tp.get("tags", [])), subtasks=[dict(s) for s in tp.get("subtasks", [])])
        self.undo_stack.push(AddCmd(self, task, "Add from template"))

    def delete_template(self):
        tpls = self.store.settings.get("templates") or []
        if not tpls: return
        names = [tp.get("title", "?") for tp in tpls]
        name, ok = QInputDialog.getItem(self, "Delete template", "Template:", names, 0, False)
        if not ok: return
        tpls = [tp for tp in tpls if tp.get("title") != name]
        self.store.settings["templates"] = tpls
        self.store.save()

    def _palette_commands(self) -> list[tuple[str, object]]:
        acts = [self.act_new, self.act_backlog_new, self.act_edit, self.act_duplicate, self.act_delete, self.act_plan, self.act_copy_day, self.act_review, self.act_find_slot, self.act_search, self.act_due, self.act_stats, self.act_export, self.act_export_ics, self.act_import_ics, self.act_cleanup, self.act_today, self.act_undo, self.act_redo, self.act_day, self.act_week, self.act_settings]
        out = []
        for a in acts:
            label = (a.text() or "").replace("&", "")
            if label: out.append((label, a.trigger))
        out += [
            ("Focus mode 🎯", self.enter_focus),
            ("Save selected as template", self.save_template),
            ("Toggle dark mode", lambda: self._toggle_setting("dark", not self.store.settings.get("dark", False))),
            ("Plan my day ⚡", self.plan_my_day),
            ("Daily review 🌙", self.open_review),
        ]
        return out

    def _toggle_setting(self, key: str, val: bool):
        self.store.settings[key] = val
        self.store.save()
        self._apply_config()

    def open_palette(self):
        commands = self._palette_commands()
        for t in self.store.tasks[:100]:
            label = f"🔎 {t.title}"
            if t.date: label += f"  ({t.date} {t.start})"
            else: label += "  (Backlog)"
            commands.append((label, lambda tid=t.id: self._jump_to_search(tid)))
        dlg = PaletteDialog(self, commands)
        if dlg.exec() == QDialog.Accepted and dlg._chosen is not None: dlg._chosen()

    def open_search(self):
        dlg = SearchDialog(self, self.store)
        dlg.jumpRequested.connect(self._jump_to_search)
        dlg.exec()

    def open_deadlines(self):
        dlg = DeadlinesDialog(self, self.store.tasks)
        dlg.jumpRequested.connect(self._jump_to_search)
        dlg.exec()

    def _jump_to_search(self, task_id: str):
        t = self.store.get(task_id)
        if t is None: return
        self._pending_select = task_id
        if t.date:
            d = QDate.fromString(t.date, "yyyy-MM-dd")
            if d.isValid() and d != self.current_date:
                self.date_edit.setDate(d)
                return
        self.refresh()

    def _consume_pending_select(self, pid: str):
        t = self.store.get(pid)
        if t is None: return
        if not t.date:
            for i in range(self.backlog.count()):
                if self.backlog.item(i).data(Qt.UserRole) == pid:
                    self.backlog.setCurrentRow(i)
                    self.backlog.scrollToItem(self.backlog.item(i))
                    break
            return
        idx = next((i for i, x in enumerate(self._visible) if x.id == pid or base_id(x.id) == base_id(pid)), -1)
        if idx >= 0: self.list.setCurrentRow(idx)

    def export_ics(self):
        dated = [t for t in self.store.tasks if t.date]
        if not dated:
            QMessageBox.information(self, "Export ICS", "No scheduled tasks to export yet.")
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export ICS", str(Path.home() / "day_planner.ics"), "iCalendar files (*.ics)")
        if not path: return
        try: Path(path).write_text(build_ics(dated), encoding="utf-8")
        except OSError as exc:
            QMessageBox.critical(self, "Export failed", str(exc))
            return
        QMessageBox.information(self, "Export ICS", f"Exported {len(dated)} event(s) to\n{path}")

    def import_ics(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import ICS", str(Path.home()), "iCalendar files (*.ics *.ical);;All files (*)")
        if not path: return
        try: text = Path(path).read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            QMessageBox.critical(self, "Import failed", str(exc))
            return
        drafts: list[Task] = []
        for ev in _parse_ics_events(text): drafts.extend(_tasks_from_event(ev))
        existing = {(t.title, t.date, t.start, t.recurrence) for t in self.store.tasks}
        seen: set = set()
        to_add: list[Task] = []
        skipped = 0
        for dft in drafts:
            key = (dft.title, dft.date, dft.start, dft.recurrence)
            if key in existing or key in seen: skipped += 1; continue
            seen.add(key)
            to_add.append(dft)
        if not to_add:
            QMessageBox.information(self, "Import ICS", f"No new events found ({skipped} duplicates/unsupported skipped).")
            return
        n_series = sum(1 for t in to_add if t.recurrence != "none")
        msg = (f"Import {len(to_add)} task(s)?\n\n•  {len(to_add) - n_series} one-off tasks\n•  {n_series} repeating series")
        if skipped: msg += f"\n•  {skipped} duplicates skipped"
        if QMessageBox.question(self, "Import ICS", msg) != QMessageBox.StandardButton.Yes: return
        self.undo_stack.push(BulkAddCmd(self, to_add, f"Import ICS ({len(to_add)})"))
        self.statusBar().showMessage(f"Imported {len(to_add)} task(s) from ICS", 6000)

    def cleanup_old_completed(self):
        days, ok = QInputDialog.getInt(self, "Clean up completed tasks", "Delete completed tasks that were scheduled more than this many days ago:", 90, 1, 3650)
        if not ok: return
        cutoff = QDate.currentDate().addDays(-days)
        targets = [t for t in self.store.tasks if t.completed and t.recurrence == "none" and t.date and QDate.fromString(t.date, "yyyy-MM-dd") < cutoff]
        if not targets:
            QMessageBox.information(self, "Clean up", f"No completed tasks older than {days} days.")
            return
        if QMessageBox.question(self, "Clean up", f"Delete {len(targets)} completed task(s) older than {days} days?\n(You can undo this with Ctrl+Z.)") != QMessageBox.StandardButton.Yes: return
        self.undo_stack.push(DeleteCmd(self, targets, "Clean up completed"))

    def open_stats(self):
        dlg = StatsDialog(self, self._stats_data)
        dlg.jumpTo.connect(lambda d: self.date_edit.setDate(d))
        dlg.exec()

    def _stats_data(self, start: QDate, end: QDate) -> dict:
        per_day = []
        cat_min: dict[str, int] = {}
        total = done = worked_total = 0
        d = start
        while d <= end:
            key = d.toString("yyyy-MM-dd")
            planned = worked = 0
            for t in self._effective_for(key):
                planned += t.duration
                cat_min[t.category] = cat_min.get(t.category, 0) + t.duration
                worked += min(t.worked_on(key), t.duration)
                if t.completed: done += t.duration
            per_day.append((d, planned, worked))
            total += planned
            worked_total += worked
            d = d.addDays(1)
        act = self.store.activity_between(start.toString("yyyy-MM-dd"), end.toString("yyyy-MM-dd"))
        cats = sorted(cat_min.items(), key=lambda kv: -kv[1])
        return {"days": per_day, "cats": cats, "total": total, "done": done, "worked": worked_total, "active": sum(act.values())}

    def export_csv(self):
        if not self.store.tasks:
            QMessageBox.information(self, "Export", "No tasks to export yet.")
            return
        today = QDate.currentDate()
        oneoffs = [t for t in self.store.tasks if t.recurrence == "none"]
        anchors = [t for t in self.store.tasks if t.recurrence != "none"]
        horizon = today
        for t in oneoffs:
            if t.date:
                q = QDate.fromString(t.date, "yyyy-MM-dd")
                if q.isValid() and q > horizon: horizon = q
        expanded: list[Task] = []
        for a in anchors:
            d = QDate.fromString(a.date, "yyyy-MM-dd")
            if not d.isValid(): continue
            for _ in range(366 * 3):
                if d > horizon: break
                inst = materialize(a, d.toString("yyyy-MM-dd"))
                if inst is not None: expanded.append(inst)
                d = d.addDays(1)
        rows = sorted(oneoffs + expanded, key=lambda t: (t.date, t.start_minutes))
        path, _ = QFileDialog.getSaveFileName(self, "Export CSV", str(Path.home() / "day_planner_export.csv"), "CSV files (*.csv)")
        if not path: return
        try:
            with open(path, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["date", "title", "start", "end", "duration_min", "worked_min", "category", "priority", "deadline", "tags", "recurrence", "completed", "notes"])
                for t in rows:
                    wk = t.worked_on(t.date) if t.date else 0
                    w.writerow([t.date, t.title, t.start, t.end, t.duration, wk, t.category, t.priority, t.deadline, "|".join(t.tags or []), t.recurrence, int(t.completed), t.notes])
            QMessageBox.information(self, "Export", f"Exported {len(rows)} rows to\n{path}")
        except OSError as exc:
            QMessageBox.critical(self, "Export failed", str(exc))

    def _list_menu(self, pos):
        menu = QMenu(self)
        item = self.list.itemAt(pos)
        if item is not None:
            row = self.list.row(item)
            t = self._visible[row] if 0 <= row < len(self._visible) else None
            if t is not None:
                menu.addAction("Edit…", lambda: self.edit_task(t))
                menu.addAction("Duplicate", self.duplicate_selected)
                menu.addAction("Toggle done", self._toggle_selected_done)
                menu.addAction("Save as template…", self.save_template)
                if not is_instance(t.id) and t.date:
                    menu.addSeparator()
                    menu.addAction("Move to tomorrow", self.move_to_tomorrow)
                    menu.addAction("Move to next week", self._move_to_next_week)
                    menu.addAction("Move to backlog", self._move_to_backlog)
                    menu.addSeparator()
                    menu.addAction("Shift earlier (⌃⇧↑)", lambda: self._shift_selected_time(-SNAP_MIN))
                    menu.addAction("Shift later (⌃⇧↓)", lambda: self._shift_selected_time(SNAP_MIN))
                    menu.addAction("Shift day back (⌃⇧←)", lambda: self._shift_selected_day(-1))
                    menu.addAction("Shift day forward (⌃⇧→)", lambda: self._shift_selected_day(1))
                menu.addSeparator()
                menu.addAction("Delete…", self.delete_selected)
        else: menu.addAction("New task…", lambda: self.new_task())
        unfinished = sum(1 for t in self._day_tasks if not t.completed and t.date and not is_instance(t.id))
        if unfinished: menu.addAction(f"Move all unfinished to tomorrow ({unfinished})", self._move_unfinished)
        if any(t.completed for t in self._day_tasks):
            menu.addSeparator()
            menu.addAction("Delete completed", self._delete_completed)
        menu.exec(self.list.viewport().mapToGlobal(pos))

    def _update_status(self):
        tasks = self._day_tasks
        key = self.date_key()
        planned = sum(t.duration for t in tasks)
        done = sum(1 for t in tasks if t.completed)
        worked = sum(min(t.worked_on(key), t.duration) for t in tasks)
        backlog_n = sum(1 for t in self.store.tasks if not t.date)
        text = (f"  {len(tasks)} task{'' if len(tasks) == 1 else 's'}  ·  {fmt_minutes(planned)} planned  ·  {done} done  ·  {backlog_n} in backlog")
        if planned > 0:
            score = int(round(100 * worked / planned))
            text += f"  ·  🎯 {score}%"
        n_act = len(self._activity_for(key))
        if n_act: text += f"  ·  ⏱ {fmt_minutes(n_act)} active"
        if not self.idle.available: text += "  (idle n/a)"
        if self._filter: text += f'  ·  filter “{self._filter}”'
        self.stats.setText(text)
        self.next_up.setText(self._now_next_text(tasks))

    def _now_next_text(self, tasks) -> str:
        if self.current_date != QDate.currentDate() or not tasks: return ""
        now = QTime.currentTime()
        now_m = now.hour() * 60 + now.minute()
        away = (self._last_idle is not None and self._last_idle > IDLE_ACTIVE_SEC)
        for t in tasks:
            if not t.completed and t.start_minutes <= now_m < t.end_minutes:
                icon = "🟡" if away else "🟢"
                return f"{icon} Now: {t.title} · until {t.end}   "
        for t in tasks:
            if not t.completed and t.start_minutes > now_m: return f"Next: {t.title} · {t.time_range}   "
        return "All done for today ✓   " if tasks else ""

    def _update_buttons(self):
        has = self._selected_task() is not None
        self.act_edit.setEnabled(has)
        self.act_duplicate.setEnabled(has)
        self.act_delete.setEnabled(has)

    def _on_clock(self):
        self._track_tick()
        self.timeline.tick()
        self.week.tick()
        self._update_status()
        self._check_reminders()
        self._check_deadlines()
        self._check_eod()

    def _track_tick(self):
        if not self.store.settings.get("track", True): return
        today = QDate.currentDate().toString("yyyy-MM-dd")
        if today != self._track_date:
            self._track_date = today
            self._recorded.clear()
            self._activity_cache.pop(today, None)
        self._last_idle = self.idle.idle_seconds()
        if self._last_idle is not None and self._last_idle > IDLE_ACTIVE_SEC: return
        t = QTime.currentTime()
        minute = t.hour() * 60 + t.minute()
        if minute in self._recorded: return
        self._recorded.add(minute)
        self.store.record_active(today, minute)
        self._activity_cache.setdefault(today, set()).add(minute)

        attributed = False
        if self._wt_id:
            tgt = self.store.get(self._wt_id)
            if tgt is None or tgt.completed: self._wt_stop()
            else:
                tgt.work_dates[today] = tgt.worked_on(today) + 1
                self.store.upsert_task(tgt)
                attributed = True
        if not attributed:
            cands = [x for x in self._effective_for(today) if not x.completed and x.start_minutes <= minute < x.end_minutes]
            if len(cands) == 1:
                inst = cands[0]
                tgt = self.store.get(base_id(inst.id)) or self.store.get(inst.id)
                if tgt is not None:
                    tgt.work_dates[today] = tgt.worked_on(today) + 1
                    self.store.upsert_task(tgt)
        if self.date_key() == today: self.timeline.set_activity(self._activity_for(today))

    def _wt_toggle(self):
        if self._wt_id is None:
            t = self._selected_task()
            if t is None:
                self.statusBar().showMessage("Select a task, then start the timer", 4000)
                return
            self._wt_id = base_id(t.id)
            self._wt_t0 = time.time()
            self.wt_btn.setText("⏹ Stop")
            self.wt_timer.start()
            self._wt_paint()
        else: self._wt_stop()

    def _wt_stop(self):
        if self._wt_id is None: return
        self._wt_id = None
        self.wt_btn.setText("⏱ Start")
        self.wt_label.setText("")
        self.wt_timer.stop()

    def _wt_paint(self):
        if self._wt_id is None: return
        el = int(time.time() - self._wt_t0)
        m, s = divmod(el, 60)
        t = self.store.get(self._wt_id)
        title = t.title if t else ""
        self.wt_label.setText(f"⏱ {m:02d}:{s:02d} · {title[:20]}")

    def _check_deadlines(self):
        if not self.store.settings.get("reminders", True): return
        today = QDate.currentDate()
        tkey = today.toString("yyyy-MM-dd")
        sent = 0
        for t in self.store.tasks:
            if sent >= 3: break
            if not t.deadline or t.completed: continue
            d = QDate.fromString(t.deadline, "yyyy-MM-dd")
            if not d.isValid(): continue
            days = today.daysTo(d)
            kind = ("overdue" if days < 0 else "today" if days == 0 else "tomorrow" if days == 1 else None)
            if kind is None: continue
            k = (t.id, kind, tkey)
            if k in self._dl_notified: continue
            self._dl_notified.add(k)
            sent += 1
            msg = {"overdue": f"⚠ “{t.title}” is {-days}d overdue", "today": f"⚑ “{t.title}” is due today", "tomorrow": f"⚑ “{t.title}” is due tomorrow"}[kind]
            self._notify_tray("Deadline", msg, payload={"type": "task", "id": t.id})

    def _check_eod(self):
        if self.current_date != QDate.currentDate(): return
        tkey = QDate.currentDate().toString("yyyy-MM-dd")
        if self._eod_done == tkey: return
        hour = _safe_int(self.store.settings.get("eod_hour", 18), 18)
        if QTime.currentTime().hour() < hour: return
        self._eod_done = tkey
        tasks = self._day_tasks
        planned = sum(t.duration for t in tasks)
        worked = sum(min(t.worked_on(tkey), t.duration) for t in tasks)
        left = sum(1 for t in tasks if not t.completed and t.date)
        score = int(round(100 * worked / planned)) if planned else 0
        self._notify_tray("🌙 Day summary", f"Planned {fmt_minutes(planned)} · worked {fmt_minutes(worked)} ({score}%) · {left} task(s) left\nTry 🌙 Review to close out the day.", payload={"type": "review"})

    def _pomo_toggle(self):
        if self.pomo_state == "idle":
            t = self._selected_task()
            if t is None:
                self.statusBar().showMessage("Select a task first, then start the timer", 4000)
                return
            self.pomo_title = t.title
            self.pomo_count = 0
            self._pomo_begin("work")
        elif self.pomo_state == "running":
            self.pomo_remaining = max(0.0, self.pomo_end - time.time())
            self.pomo_state = "paused"
            self.pomo_timer.stop()
            self.pomo_btn.setText("▶")
            self._pomo_paint()
        else:
            self.pomo_end = time.time() + self.pomo_remaining
            self.pomo_state = "running"
            self.pomo_timer.start()
            self.pomo_btn.setText("⏸")
            self._pomo_paint()

    def _pomo_begin(self, phase: str):
        s = self.store.settings
        work_min = int(s.get("pomo_work_min", POMODORO_WORK_MIN))
        break_min = int(s.get("pomo_break_min", POMODORO_BREAK_MIN))
        long_every = int(s.get("long_break_every", 4))
        long_mult = int(s.get("long_break_mult", 3))

        if phase == "work": secs = work_min * 60
        elif phase == "break":
            if long_every and self.pomo_count > 0 and self.pomo_count % long_every == 0:
                secs = break_min * long_mult * 60
                phase = "long_break"
            else: secs = break_min * 60
        else: return
        self.pomo_total_duration = secs
        self.pomo_phase = phase
        self.pomo_state = "running"
        self.pomo_end = time.time() + secs
        self.pomo_btn.setText("⏸")
        self.pomo_stop.setEnabled(True)
        self.pomo_timer.start()
        self._pomo_paint()

    def _pomo_tick(self):
        if self.pomo_state != "running": return
        if self.pomo_end - time.time() <= 0:
            QApplication.beep()
            if self.pomo_phase == "work":
                self.pomo_count += 1
                self._notify_tray("Pomodoro complete 🍅", f"“{self.pomo_title}” · take a break")
                self._pomo_begin("break")
            else:
                self._notify_tray("Break over ☕", f"Back to “{self.pomo_title}”")
                self._pomo_begin("work")
        else: self._pomo_paint()

    def _pomo_stop(self):
        if self.pomo_state == "idle": return
        self.pomo_timer.stop()
        n = self.pomo_count
        self.pomo_state = "idle"
        self.pomo_phase = "work"
        self.pomo_btn.setText("▶")
        self.pomo_stop.setEnabled(False)
        self.pomo_label.setText("")
        if n: self.statusBar().showMessage(f"Pomodoro stopped · {n} completed", 6000)

    def _pomo_paint(self):
        if self.pomo_state == "idle":
            self.pomo_label.setText("")
            return
        if self.pomo_state == "paused":
            total = int(self.pomo_remaining + 0.999)
            pre = "⏸"
        else:
            total = int(max(0.0, self.pomo_end - time.time()) + 0.999)
            if self.pomo_phase == "work": pre = "🍅"
            elif self.pomo_phase == "long_break": pre = "🌴"
            else: pre = "☕"
        m, s = divmod(total, 60)
        title = (self.pomo_title[:23] + "…" if len(self.pomo_title) > 24 else self.pomo_title)
        suffix = "" if self.pomo_phase == "work" else " · break"
        self.pomo_label.setText(f"{pre} {m:02d}:{s:02d} · {title}{suffix}")

    def _backup_db(self):
        try:
            if STORE_DB.exists(): shutil.copy2(STORE_DB, STORE_DB.parent / (STORE_DB.name + ".bak"))
        except OSError: pass

    def closeEvent(self, ev):
        if (self.tray is not None and self.store.settings.get("close_to_tray", True) and not self._force_quit):
            ev.ignore()
            self.hide()
            if not self._tray_hinted:
                self._tray_hinted = True
                self._notify_tray("Still running", "Tracking continues in the tray.\nTray ▸ Quit to exit completely.")
            return
        self._save_state()
        self.pomo_timer.stop()
        self.wt_timer.stop()
        if self._focus is not None: self._focus.close()
        self.store.save()
        self.store.close()
        ev.accept()


# ----------------------------------------------------------------- app
def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_TITLE)
    app.setOrganizationName("DayPlanner")
    app.setStyle("Fusion")
    app.setWindowIcon(_make_icon())
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()