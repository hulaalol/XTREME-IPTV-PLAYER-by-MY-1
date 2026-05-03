import sys
import os
import time
import uuid
import hashlib
import requests
import subprocess
import configparser
import re
import json
import qdarkstyle
import html
import os
import ssl
import urllib.request
from urllib.parse import urlparse, parse_qs
from PyQt5 import QtCore
from PyQt5.QtWidgets import QToolTip
from pathlib import Path
from lxml import etree
from datetime import datetime
from dateutil import parser, tz
import xml.etree.ElementTree as ET
from PyQt5.QtGui import QIcon, QFont, QBrush, QColor
from PyQt5.QtCore import (
    Qt, QTimer, QPropertyAnimation, QEasingCurve, QSize, QObject, pyqtSignal, QRunnable, pyqtSlot, QThreadPool, QDir
)
from PyQt5 import QtWidgets
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QVBoxLayout, QLineEdit, QLabel, QPushButton,
    QListWidget, QWidget, QFileDialog, QCheckBox, QSizePolicy, QHBoxLayout,
    QDialog, QFormLayout, QDialogButtonBox, QTabWidget, QListWidgetItem,
    QSpinBox, QMenu, QAction, QTextEdit,
    QStyledItemDelegate, QTreeWidget, QTreeWidgetItem, QAbstractItemView,
    QInputDialog, QMessageBox, QStyle,
)

is_windows = sys.platform.startswith('win')
is_mac = sys.platform.startswith('darwin')
is_linux = sys.platform.startswith('linux')

# EPG cache directory: per-server XML files keyed by sha1(server_url).
# Using the server URL (not the profile name) means two profiles pointing
# at the same Xtream server share one EPG cache.
EPG_DIR = Path.home() / '.iptv' / 'epg'
os.makedirs(EPG_DIR, exist_ok=True)
EPG_CACHE_TTL_SECONDS = 60 * 60  # 1 hour
EPG_REFRESH_INTERVAL_MS = 60 * 60 * 1000  # 60 min


def _epg_cache_file_for(server_url):
    safe = hashlib.sha1((server_url or "").encode("utf-8")).hexdigest()[:16]
    return EPG_DIR / f"{safe}.xml"

CUSTOM_USER_AGENT = (
    "Connection: Keep-Alive User-Agent: okhttp/5.0.0-alpha.2 "
    "Accept-Encoding: gzip, deflate"
)

def normalize_channel_name(name):
    name = name.lower().strip()
    name = re.sub(r'\s+', ' ', name)
    name = re.sub(r'[^\w\s]', '', name)
    name = re.sub(r'\b(hd|sd|channel|tv)\b', '', name)
    name = name.strip()
    return name

class EPGWorkerSignals(QObject):
    finished = pyqtSignal(dict, dict)
    error = pyqtSignal(str)

class EPGWorker(QRunnable):
    def __init__(self, server, username, password, http_method, cache_file_path):
        super().__init__()
        self.server = server
        self.username = username
        self.password = password
        self.http_method = http_method
        self.cache_file_path = str(cache_file_path)
        self.signals = EPGWorkerSignals()

    @pyqtSlot()
    def run(self):
        try:
            cache_file = self.cache_file_path
            cache_valid = False
            if os.path.exists(cache_file):
                cache_age = time.time() - os.path.getmtime(cache_file)
                if cache_age < EPG_CACHE_TTL_SECONDS:
                    cache_valid = True

            if cache_valid:
                with open(cache_file, 'rb') as f:
                    epg_xml_data = f.read()
            else:
                epg_url = f"{self.server}/xmltv.php?username={self.username}&password={self.password}"
                headers = {'User-Agent': CUSTOM_USER_AGENT}
                if self.http_method == 'POST':
                    response = requests.post(epg_url, headers=headers, timeout=10)
                else:
                    response = requests.get(epg_url, headers=headers, timeout=10)
                response.raise_for_status()
                epg_xml_data = response.content
                os.makedirs(os.path.dirname(cache_file) or ".", exist_ok=True)
                with open(cache_file, 'wb') as f:
                    f.write(epg_xml_data)

            epg_data, channel_id_to_names = self.parse_epg_data(epg_xml_data)
            self.signals.finished.emit(epg_data, channel_id_to_names)
        except Exception as e:
            self.signals.error.emit(str(e))

    def parse_epg_data(self, epg_xml_data):
        epg_dict = {}
        channel_id_to_names = {}
        try:
            epg_tree = ET.fromstring(epg_xml_data)
            for channel in epg_tree.findall('channel'):
                channel_id = channel.get('id')
                if channel_id:
                    channel_id = channel_id.strip().lower()
                    display_names = []
                    for display_name_elem in channel.findall('display-name'):
                        if display_name_elem.text:
                            display_name = display_name_elem.text.strip()
                            normalized_name = normalize_channel_name(display_name)
                            display_names.append(normalized_name)
                    channel_id_to_names[channel_id] = display_names

            for programme in epg_tree.findall('programme'):
                channel_id = programme.get('channel')
                if channel_id:
                    channel_id = channel_id.strip().lower()
                start_time = programme.get('start')
                stop_time = programme.get('stop')
                title_elem = programme.find('title')
                description_elem = programme.find('desc')

                title = title_elem.text.strip() if title_elem is not None and title_elem.text else ''
                description = description_elem.text.strip() if description_elem is not None and description_elem.text else ''

                epg_entry = {
                    'start_time': start_time,
                    'stop_time': stop_time,
                    'title': title,
                    'description': description
                }

                if channel_id not in epg_dict:
                    epg_dict[channel_id] = []
                epg_dict[channel_id].append(epg_entry)

            return epg_dict, channel_id_to_names

        except Exception as e:
            print(f"Error parsing EPG data: {e}")
            return {}, {}


import hashlib

PLAYLIST_CACHE_DIR = Path.home() / '.iptv' / 'playlists'

_EXTINF_RE = re.compile(r'#EXTINF:[^,]*,(.*)$')
_ATTR_RE = re.compile(r'([\w-]+)="([^"]*)"')
_VOD_GROUP_RE = re.compile(r'\b(vod|movie|movies|film|films|cinema)\b', re.IGNORECASE)
_SERIES_GROUP_RE = re.compile(r'\b(series|tv\s*shows?|shows?|seasons?)\b', re.IGNORECASE)
_EPISODE_RE = re.compile(r'\bS\d{1,2}\s?E\d{1,3}\b', re.IGNORECASE)
_MOVIE_EXT_RE = re.compile(r'\.(mp4|mkv|avi|mov|webm|flv|wmv)(\?|$)', re.IGNORECASE)


def _classify_entry(group_title, name, url):
    g = (group_title or "").strip()
    if g:
        if _SERIES_GROUP_RE.search(g):
            return 'Series'
        if _VOD_GROUP_RE.search(g):
            return 'Movies'
    if _EPISODE_RE.search(name or ""):
        return 'Series'
    if _MOVIE_EXT_RE.search(url or ""):
        return 'Movies'
    return 'LIVE'


def _slug_id(text):
    return hashlib.sha1(text.encode('utf-8')).hexdigest()[:12]


def parse_m3u_file(path):
    abs_path = os.path.abspath(path)
    entries_by_cat = {}
    groups_by_tab = {'LIVE': {}, 'Movies': {}, 'Series': {}}

    pending = None  # dict built from #EXTINF, waiting for URL line
    try:
        with open(abs_path, 'r', encoding='utf-8-sig', errors='replace') as f:
            for raw_line in f:
                line = raw_line.strip()
                if not line:
                    continue
                if line.startswith('#EXTINF'):
                    try:
                        attrs = dict(_ATTR_RE.findall(line))
                        m = _EXTINF_RE.match(line)
                        display_name = m.group(1).strip() if m else attrs.get('tvg-name', '').strip()
                        pending = {
                            'name': display_name or attrs.get('tvg-name', '').strip() or 'Unnamed',
                            'epg_channel_id': (attrs.get('tvg-id') or '').strip().lower() or None,
                            'stream_icon': attrs.get('tvg-logo', '').strip(),
                            'group_title': attrs.get('group-title', '').strip(),
                            'container_extension': 'm3u8',
                        }
                    except Exception as ex:
                        print(f"Skipping malformed #EXTINF: {ex}")
                        pending = None
                    continue
                if line.startswith('#'):
                    continue
                # URL line
                if pending is None:
                    continue
                try:
                    url = line
                    ext_m = re.search(r'\.([a-z0-9]{2,5})(?:\?|$)', url, re.IGNORECASE)
                    if ext_m:
                        pending['container_extension'] = ext_m.group(1).lower()
                    pending['url'] = url
                    group_title = pending.pop('group_title') or 'Uncategorized'
                    tab = _classify_entry(group_title, pending.get('name', ''), url)
                    key = f"{tab}||{group_title}"
                    if group_title not in groups_by_tab[tab]:
                        groups_by_tab[tab][group_title] = _slug_id(f"{tab}:{group_title}")
                    entries_by_cat.setdefault(key, []).append(pending)
                except Exception as ex:
                    print(f"Skipping malformed M3U entry: {ex}")
                finally:
                    pending = None
    except FileNotFoundError:
        raise
    except Exception as ex:
        print(f"Error reading M3U file: {ex}")

    groups = {
        tab: [{'category_name': name, 'category_id': cid}
              for name, cid in sorted(groups_by_tab[tab].items(), key=lambda kv: kv[0].lower())]
        for tab in ('LIVE', 'Movies', 'Series')
    }
    return {
        'groups': groups,
        'entries_by_category': entries_by_cat,
        'source_path': abs_path,
        'source_mtime': os.path.getmtime(abs_path),
        'parsed_at': time.time(),
    }


def load_or_parse_m3u_with_cache(path):
    abs_path = os.path.abspath(path)
    os.makedirs(PLAYLIST_CACHE_DIR, exist_ok=True)
    cache_file = PLAYLIST_CACHE_DIR / f"{hashlib.sha1(abs_path.encode('utf-8')).hexdigest()[:16]}.json"

    try:
        src_mtime = os.path.getmtime(abs_path)
    except OSError:
        raise

    if cache_file.exists():
        try:
            with open(cache_file, 'r', encoding='utf-8') as f:
                cached = json.load(f)
            if (cached.get('source_path') == abs_path
                    and cached.get('source_mtime') == src_mtime):
                return cached
        except Exception as ex:
            print(f"Playlist cache read failed, re-parsing: {ex}")

    parsed = parse_m3u_file(abs_path)
    try:
        with open(cache_file, 'w', encoding='utf-8') as f:
            json.dump(parsed, f)
    except Exception as ex:
        print(f"Playlist cache write failed: {ex}")
    return parsed


# ---------------------------------------------------------------------------
# Favorites: per-profile, persisted under ~/.iptv/favorites/<sha1(name)[:16]>.json
# Note: file is keyed by sha1 of the profile NAME. If the user renames a
# profile in credentials.ini, the saved favorites become orphaned.
# ---------------------------------------------------------------------------

FAVORITES_DIR = Path.home() / '.iptv' / 'favorites'

ROLE_STARRABLE = Qt.UserRole + 1
ROLE_EPG_TEXT = Qt.UserRole + 2
ROLE_NODE_ID = Qt.UserRole
ROLE_NODE_KIND = Qt.UserRole + 1


def _favorites_file_for(name):
    safe = hashlib.sha1((name or "").encode("utf-8")).hexdigest()[:16]
    return FAVORITES_DIR / f"{safe}.json"


def _empty_favorites_tree():
    return {
        "version": 1,
        "root": {
            "id": str(uuid.uuid4()),
            "type": "group",
            "name": "Favorites",
            "children": [],
        },
    }


def _walk_tree(node, fn):
    fn(node)
    if node.get("type") == "group":
        for child in node.get("children", []):
            _walk_tree(child, fn)


def _find_node(root, node_id):
    """Return (parent, node, index_in_parent) or None. parent is None for root."""
    if root.get("id") == node_id:
        return (None, root, -1)

    def search(parent):
        for i, child in enumerate(parent.get("children", [])):
            if child.get("id") == node_id:
                return (parent, child, i)
            if child.get("type") == "group":
                hit = search(child)
                if hit is not None:
                    return hit
        return None

    return search(root)


def _remove_node(root, node_id):
    found = _find_node(root, node_id)
    if found is None or found[0] is None:
        return None
    parent, node, idx = found
    parent["children"].pop(idx)
    return node


def _atomic_write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, path)


class FavoritesStarDelegate(QStyledItemDelegate):
    STAR_BOX = 22
    STAR_GAP = 8     # gap between EPG text and star
    EPG_GAP = 12     # gap between channel name and EPG text
    STAR_SOLID = "★"
    STAR_HOLLOW = "☆"

    def __init__(self, app, source_tab, parent=None):
        super().__init__(parent)
        self._app = app
        self._source_tab = source_tab

    def _star_rect(self, option):
        from PyQt5.QtCore import QRect
        rect = option.rect
        size = self.STAR_BOX
        x = rect.right() - size - 4
        y = rect.top() + (rect.height() - size) // 2
        return QRect(x, y, size, size)

    def _reserved_right_width(self, index):
        """Total width to subtract from text area for star + EPG column."""
        w = 0
        if index.data(ROLE_STARRABLE):
            w += self.STAR_BOX + 4
        if index.data(ROLE_EPG_TEXT):
            # EPG column gets up to 45% of row width, capped at 360px
            row_w = max(0, w)  # placeholder; actual cap computed in paint where rect is known
        return w

    def sizeHint(self, option, index):
        sh = super().sizeHint(option, index)
        if index.data(ROLE_STARRABLE):
            sh.setWidth(sh.width() + self.STAR_BOX + 6)
        return sh

    def paint(self, painter, option, index):
        from PyQt5.QtCore import QRect
        from PyQt5.QtGui import QFontMetrics
        from PyQt5.QtWidgets import QStyleOptionViewItem

        epg_text = index.data(ROLE_EPG_TEXT) or ""
        starrable = bool(index.data(ROLE_STARRABLE))

        star_w = (self.STAR_BOX + 4) if starrable else 0
        # EPG column width: up to ~45% of row, capped 360px, min 0 if not enough room
        epg_col_w = 0
        if epg_text:
            avail = option.rect.width() - star_w - self.EPG_GAP - 16
            epg_col_w = min(360, max(0, int(avail * 0.45)))

        # Render the base item with a narrowed rect so the channel name elides
        opt = QStyleOptionViewItem(option)
        opt.rect = QRect(
            option.rect.x(),
            option.rect.y(),
            max(0, option.rect.width() - star_w - epg_col_w - (self.EPG_GAP if epg_col_w else 0)),
            option.rect.height(),
        )
        super().paint(painter, opt, index)

        # Paint EPG text right-aligned in its reserved column
        if epg_col_w > 0:
            epg_rect = QRect(
                option.rect.right() - star_w - epg_col_w - 4,
                option.rect.y(),
                epg_col_w,
                option.rect.height(),
            )
            fm = QFontMetrics(option.font)
            elided = fm.elidedText(epg_text, Qt.ElideRight, epg_col_w)
            painter.save()
            painter.setPen(QColor("#7aa3c4"))   # muted blue-grey, readable on light/dark
            painter.drawText(epg_rect, Qt.AlignRight | Qt.AlignVCenter, elided)
            painter.restore()

        # Paint the star (or skip if row isn't starrable)
        if not starrable:
            return
        entry = index.data(Qt.UserRole)
        url = (entry or {}).get("url") if isinstance(entry, dict) else None
        is_fav = bool(url) and self._app.is_favorited(url)

        painter.save()
        if is_fav:
            painter.setPen(QColor("#f5b301"))
            glyph = self.STAR_SOLID
        else:
            painter.setPen(QColor("#888888"))
            glyph = self.STAR_HOLLOW
        font = QFont(option.font)
        font.setPointSize(max(font.pointSize(), 12))
        painter.setFont(font)
        painter.drawText(self._star_rect(option), Qt.AlignCenter, glyph)
        painter.restore()

    def editorEvent(self, event, model, option, index):
        if event.type() == QtCore.QEvent.MouseButtonRelease:
            if event.button() == Qt.LeftButton and index.data(ROLE_STARRABLE):
                if self._star_rect(option).contains(event.pos()):
                    entry = index.data(Qt.UserRole)
                    if isinstance(entry, dict) and entry.get("url"):
                        self._app.toggle_favorite(entry, self._source_tab)
                    return True
        return super().editorEvent(event, model, option, index)


class FavoritesTreeWidget(QTreeWidget):
    """QTreeWidget subclass with cycle/leaf-drop validation."""

    def __init__(self, panel, parent=None):
        super().__init__(parent)
        self._panel = panel

    def dropEvent(self, event):
        target = self.itemAt(event.pos())
        indicator = self.dropIndicatorPosition()
        dragged = self.currentItem()
        if dragged is None:
            event.ignore()
            return

        dragged_id = dragged.data(0, ROLE_NODE_ID)
        dragged_kind = dragged.data(0, ROLE_NODE_KIND)

        # Reject dropping ON an entry (entries are leaves)
        if (target is not None
                and target.data(0, ROLE_NODE_KIND) == "entry"
                and indicator == QAbstractItemView.OnItem):
            event.ignore()
            return

        # Cycle prevention: cannot drop a group onto itself or a descendant
        if dragged_kind == "group" and target is not None:
            target_id = target.data(0, ROLE_NODE_ID)
            if self._panel._is_descendant(dragged_id, target_id):
                event.ignore()
                return
            if dragged_id == target_id:
                event.ignore()
                return

        # Compute new parent + index based on drop position
        if target is None:
            # Drop in empty space -> append to root
            new_parent_id = self._panel._app._favorites_tree["root"]["id"]
            new_index = len(self._panel._app._favorites_tree["root"]["children"])
        elif indicator == QAbstractItemView.OnItem:
            # Drop into the group
            new_parent_id = target.data(0, ROLE_NODE_ID)
            target_node = _find_node(self._panel._app._favorites_tree["root"], new_parent_id)
            new_index = len(target_node[1]["children"]) if target_node else 0
        else:
            # Above or below -> sibling of target
            target_id = target.data(0, ROLE_NODE_ID)
            found = _find_node(self._panel._app._favorites_tree["root"], target_id)
            if found is None or found[0] is None:
                event.ignore()
                return
            parent_node, _node, idx = found
            new_parent_id = parent_node["id"]
            new_index = idx if indicator == QAbstractItemView.AboveItem else idx + 1

        # Adjust index if moving within the same parent above its old position
        old = _find_node(self._panel._app._favorites_tree["root"], dragged_id)
        if old is not None and old[0] is not None and old[0]["id"] == new_parent_id and old[2] < new_index:
            new_index -= 1

        event.accept()
        self._panel._app.move_node(dragged_id, new_parent_id, new_index)


class FavoritesPanel(QWidget):
    def __init__(self, app, parent=None):
        super().__init__(parent)
        self._app = app

        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(6)

        toolbar = QHBoxLayout()
        self.search_bar = QLineEdit()
        self.search_bar.setPlaceholderText("Search favorites (Enter for instant)...")
        self.search_bar.setClearButtonEnabled(True)
        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.setInterval(300)
        self._search_timer.timeout.connect(lambda: self._on_search(self.search_bar.text()))
        self.search_bar.textChanged.connect(lambda _t: self._search_timer.start())
        self.search_bar.returnPressed.connect(
            lambda: (self._search_timer.stop(), self._on_search(self.search_bar.text()))
        )

        self.new_group_button = QPushButton("New Group")
        self.new_group_button.setIcon(self.style().standardIcon(QStyle.SP_FileDialogNewFolder))
        self.new_group_button.clicked.connect(self._on_new_group_button)

        toolbar.addWidget(self.search_bar)
        toolbar.addWidget(self.new_group_button)
        layout.addLayout(toolbar)

        self.tree = FavoritesTreeWidget(self)
        self.tree.setHeaderHidden(True)
        self.tree.setDragEnabled(True)
        self.tree.setAcceptDrops(True)
        self.tree.setDropIndicatorShown(True)
        self.tree.setDragDropMode(QAbstractItemView.InternalMove)
        self.tree.setDefaultDropAction(Qt.MoveAction)
        self.tree.setSelectionMode(QAbstractItemView.SingleSelection)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self._on_context_menu)
        self.tree.itemDoubleClicked.connect(self._on_double_click)
        layout.addWidget(self.tree)

    # -- helpers -------------------------------------------------------

    def _is_descendant(self, ancestor_id, candidate_id):
        """True if candidate_id is ancestor_id or any of its descendants."""
        found = _find_node(self._app._favorites_tree["root"], ancestor_id)
        if found is None:
            return False
        ancestor = found[1]
        hit = {"v": False}

        def visit(n):
            if n.get("id") == candidate_id:
                hit["v"] = True

        _walk_tree(ancestor, visit)
        return hit["v"]

    # -- rendering -----------------------------------------------------

    def _epg_snippet_for(self, entry):
        """Look up the on-air programme for a LIVE entry; '' if no EPG match."""
        if not (self._app.epg_data and entry):
            return ""
        epg_id = (entry.get("epg_channel_id") or "").strip().lower()
        if not epg_id:
            ch_norm = normalize_channel_name(entry.get("name", ""))
            epg_id = self._app.epg_name_map.get(ch_norm, "")
        epg_list = self._app.epg_data.get(epg_id, [])
        if not epg_list:
            return ""
        try:
            now = datetime.now(tz=tz.tzlocal())
            for prog in epg_list:
                start = parser.parse(prog["start_time"])
                stop = parser.parse(prog["stop_time"])
                if start <= now <= stop:
                    start_s = start.astimezone(tz.tzlocal()).strftime("%I:%M %p")
                    stop_s = stop.astimezone(tz.tzlocal()).strftime("%I:%M %p")
                    return f"{prog['title']} ({start_s}-{stop_s})"
        except Exception:
            return ""
        return ""

    def refresh(self):
        self.tree.blockSignals(True)
        self.tree.clear()
        root = self._app._favorites_tree["root"]
        self._populate(self.tree.invisibleRootItem(), root["children"])
        self.tree.expandAll()
        self.tree.blockSignals(False)
        self._on_search(self.search_bar.text())

    def _populate(self, parent_item, nodes):
        for node in nodes:
            it = QTreeWidgetItem(parent_item)
            it.setData(0, ROLE_NODE_ID, node["id"])
            it.setData(0, ROLE_NODE_KIND, node["type"])
            if node["type"] == "group":
                it.setText(0, node["name"])
                it.setIcon(0, self.style().standardIcon(QStyle.SP_DirIcon))
                it.setFlags(it.flags() | Qt.ItemIsDropEnabled | Qt.ItemIsDragEnabled)
                self._populate(it, node.get("children", []))
            else:
                entry = node.get("entry", {})
                name = entry.get("name", "Unnamed")
                src = node.get("source_tab", "")
                # Stale check: only flag for xtream profiles where we know the host
                stale = False
                try:
                    if (self._app.login_type == 'xtream'
                            and self._app.server
                            and entry.get("url")):
                        e_host = urlparse(entry["url"]).netloc
                        s_host = urlparse(self._app.server).netloc
                        if e_host and s_host and e_host != s_host:
                            stale = True
                except Exception:
                    pass
                label = name if not stale else f"{name} (stale)"
                if src:
                    label = f"[{src}] {label}"
                if src == "LIVE":
                    epg_snippet = self._epg_snippet_for(entry)
                    if epg_snippet:
                        label = f"{label}  —  {epg_snippet}"
                it.setText(0, label)
                if src == "LIVE":
                    it.setIcon(0, self._app.live_channel_icon)
                elif src == "Movies":
                    it.setIcon(0, self._app.movies_channel_icon)
                elif src == "Series":
                    it.setIcon(0, self._app.series_channel_icon)
                if stale:
                    it.setForeground(0, QBrush(QColor("#888888")))
                it.setFlags((it.flags() | Qt.ItemIsDragEnabled) & ~Qt.ItemIsDropEnabled)

    # -- search --------------------------------------------------------

    def _on_search(self, text):
        text = (text or "").strip().lower()

        def visit(item):
            kind = item.data(0, ROLE_NODE_KIND)
            if kind == "entry":
                if not text or text in item.text(0).lower():
                    item.setHidden(False)
                    return True
                item.setHidden(True)
                return False
            # group
            any_visible = False
            for i in range(item.childCount()):
                if visit(item.child(i)):
                    any_visible = True
            # Always show empty groups; show non-empty groups if any descendant visible OR no search
            item.setHidden(False if (not text or any_visible or item.childCount() == 0) else True)
            return any_visible or not text

        for i in range(self.tree.topLevelItemCount()):
            visit(self.tree.topLevelItem(i))

    # -- interaction ---------------------------------------------------

    def _on_double_click(self, item, column):
        if item.data(0, ROLE_NODE_KIND) != "entry":
            return
        node_id = item.data(0, ROLE_NODE_ID)
        found = _find_node(self._app._favorites_tree["root"], node_id)
        if found is None:
            return
        node = found[1]
        entry = node.get("entry", {})
        if entry.get("url"):
            self._app.play_channel(entry)

    def _on_new_group_button(self):
        # If a group is selected, create as a subgroup; otherwise under root.
        selected = self.tree.currentItem()
        parent_id = self._app._favorites_tree["root"]["id"]
        if selected is not None and selected.data(0, ROLE_NODE_KIND) == "group":
            parent_id = selected.data(0, ROLE_NODE_ID)
        name, ok = QInputDialog.getText(self, "New Group", "Group name:")
        if ok and name.strip():
            self._app.add_group(parent_id, name.strip())

    def _on_context_menu(self, pos):
        item = self.tree.itemAt(pos)
        menu = QMenu(self.tree)
        if item is None:
            act_new = menu.addAction("New Group")
            chosen = menu.exec_(self.tree.viewport().mapToGlobal(pos))
            if chosen == act_new:
                root_id = self._app._favorites_tree["root"]["id"]
                name, ok = QInputDialog.getText(self, "New Group", "Group name:")
                if ok and name.strip():
                    self._app.add_group(root_id, name.strip())
            return

        kind = item.data(0, ROLE_NODE_KIND)
        node_id = item.data(0, ROLE_NODE_ID)

        if kind == "group":
            act_sub = menu.addAction("New Subgroup")
            act_rename = menu.addAction("Rename")
            act_delete = menu.addAction("Delete Group")
            chosen = menu.exec_(self.tree.viewport().mapToGlobal(pos))
            if chosen == act_sub:
                name, ok = QInputDialog.getText(self, "New Subgroup", "Subgroup name:")
                if ok and name.strip():
                    self._app.add_group(node_id, name.strip())
            elif chosen == act_rename:
                found = _find_node(self._app._favorites_tree["root"], node_id)
                current = found[1]["name"] if found else ""
                name, ok = QInputDialog.getText(self, "Rename Group", "New name:", text=current)
                if ok and name.strip():
                    self._app.rename_node(node_id, name.strip())
            elif chosen == act_delete:
                resp = QMessageBox.question(
                    self, "Delete Group",
                    "Delete this group and all its contents? Favorited items inside will be unstarred.",
                    QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
                if resp == QMessageBox.Yes:
                    self._app.delete_node(node_id)
        else:  # entry
            act_play = menu.addAction("Play")
            act_remove = menu.addAction("Remove from Favorites")
            chosen = menu.exec_(self.tree.viewport().mapToGlobal(pos))
            if chosen == act_play:
                self._on_double_click(item, 0)
            elif chosen == act_remove:
                self._app.remove_favorite(node_id)


class ProfilesDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Profiles")
        self.setMinimumSize(400, 300)
        self.parent = parent

        layout = QtWidgets.QVBoxLayout(self)
        self.credentials_list = QtWidgets.QListWidget()
        layout.addWidget(self.credentials_list)

        button_layout = QHBoxLayout()
        self.add_button = QPushButton("Add")
        self.add_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_FileDialogNewFolder))
        self.select_button = QPushButton("Select")
        self.select_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_DialogYesButton))
        self.delete_button = QPushButton("Delete")
        self.delete_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_DialogCancelButton))
        button_layout.addWidget(self.add_button)
        button_layout.addWidget(self.select_button)
        button_layout.addWidget(self.delete_button)
        layout.addLayout(button_layout)

        self.load_saved_credentials()

        self.add_button.clicked.connect(self.add_credentials)
        self.select_button.clicked.connect(self.select_credentials)
        self.delete_button.clicked.connect(self.delete_credentials)
        self.credentials_list.itemDoubleClicked.connect(self.double_click_credentials)

    def load_saved_credentials(self):
        self.credentials_list.clear()
        config = configparser.ConfigParser()
        config.read('credentials.ini')
        if 'Credentials' in config:
            for key in config['Credentials']:
                self.credentials_list.addItem(key)

    def add_credentials(self):
        dialog = AddCredentialsDialog(self)
        if dialog.exec_() == QtWidgets.QDialog.Accepted:
            method, name, *credentials = dialog.get_credentials()
            if name:
                config = configparser.ConfigParser()
                config.read('credentials.ini')
                if 'Credentials' not in config:
                    config['Credentials'] = {}
                if method == 'manual':
                    server, username, password = credentials
                    config['Credentials'][name] = f"manual|{server}|{username}|{password}"
                elif method == 'm3u_plus':
                    m3u_url, = credentials
                    config['Credentials'][name] = f"m3u_plus|{m3u_url}"
                elif method == 'local_m3u':
                    file_path, = credentials
                    config['Credentials'][name] = f"local_m3u|{file_path}"
                with open('credentials.ini', 'w') as config_file:
                    config.write(config_file)
                self.load_saved_credentials()

    def select_credentials(self):
        selected_item = self.credentials_list.currentItem()
        if selected_item:
            name = selected_item.text()
            if self.parent.load_profile_by_name(name):
                self.accept()

    def double_click_credentials(self, item):
        self.select_credentials()
        self.accept()

    def delete_credentials(self):
        selected_item = self.credentials_list.currentItem()
        if selected_item:
            name = selected_item.text()
            config = configparser.ConfigParser()
            config.read('credentials.ini')
            if 'Credentials' in config and name in config['Credentials']:
                del config['Credentials'][name]
                with open('credentials.ini', 'w') as config_file:
                    config.write(config_file)
                self.load_saved_credentials()

class AddCredentialsDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Add Credentials")
        layout = QtWidgets.QVBoxLayout(self)

        self.method_selector = QtWidgets.QComboBox()
        self.method_selector.addItems(["Manual Entry", "m3u_plus URL Entry", "Local M3U File"])
        layout.addWidget(QtWidgets.QLabel("Select Method:"))
        layout.addWidget(self.method_selector)

        self.stack = QtWidgets.QStackedWidget()
        layout.addWidget(self.stack)

        self.manual_form = QtWidgets.QWidget()
        manual_layout = QFormLayout(self.manual_form)
        self.name_entry_manual = QLineEdit()
        self.server_entry = QLineEdit()
        self.username_entry = QLineEdit()
        self.password_entry = QLineEdit()
        self.password_entry.setEchoMode(QLineEdit.Password)
        manual_layout.addRow("Name:", self.name_entry_manual)
        manual_layout.addRow("Server URL:", self.server_entry)
        manual_layout.addRow("Username:", self.username_entry)
        manual_layout.addRow("Password:", self.password_entry)

        self.m3u_form = QtWidgets.QWidget()
        m3u_layout = QFormLayout(self.m3u_form)
        self.name_entry_m3u = QLineEdit()
        self.m3u_url_entry = QLineEdit()
        m3u_layout.addRow("Name:", self.name_entry_m3u)
        m3u_layout.addRow("m3u_plus URL:", self.m3u_url_entry)

        self.local_form = QtWidgets.QWidget()
        local_layout = QFormLayout(self.local_form)
        self.name_entry_local = QLineEdit()
        path_row = QHBoxLayout()
        self.local_path_entry = QLineEdit()
        self.local_path_entry.setReadOnly(True)
        self.local_path_entry.setPlaceholderText("Choose an .m3u / .m3u8 file...")
        self.local_browse_button = QPushButton("Browse...")
        self.local_browse_button.clicked.connect(self._pick_local_m3u_file)
        path_row.addWidget(self.local_path_entry)
        path_row.addWidget(self.local_browse_button)
        path_row_widget = QWidget()
        path_row_widget.setLayout(path_row)
        local_layout.addRow("Name:", self.name_entry_local)
        local_layout.addRow("M3U File:", path_row_widget)

        self.stack.addWidget(self.manual_form)
        self.stack.addWidget(self.m3u_form)
        self.stack.addWidget(self.local_form)

        self.method_selector.currentIndexChanged.connect(self.stack.setCurrentIndex)

        buttons = QtWidgets.QDialogButtonBox(
            QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel,
            Qt.Horizontal, self)
        layout.addWidget(buttons)
        buttons.accepted.connect(self.validate_and_accept)
        buttons.rejected.connect(self.reject)

    def _pick_local_m3u_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Select M3U Playlist",
            QDir.homePath(),
            "M3U Playlists (*.m3u *.m3u8 *.m3u_plus);;All Files (*)"
        )
        if path:
            self.local_path_entry.setText(path)

    def validate_and_accept(self):
        method = self.method_selector.currentText()
        if method == "Manual Entry":
            name = self.name_entry_manual.text().strip()
            server = self.server_entry.text().strip()
            username = self.username_entry.text().strip()
            password = self.password_entry.text().strip()
            if not name or not server or not username or not password:
                QtWidgets.QMessageBox.warning(self, "Input Error", "Please fill all fields for Manual Entry.")
                return
            self.accept()
        elif method == "m3u_plus URL Entry":
            name = self.name_entry_m3u.text().strip()
            m3u_url = self.m3u_url_entry.text().strip()
            if not name or not m3u_url:
                QtWidgets.QMessageBox.warning(self, "Input Error", "Please fill all fields for m3u_plus URL Entry.")
                return
            self.accept()
        else:  # Local M3U File
            name = self.name_entry_local.text().strip()
            file_path = self.local_path_entry.text().strip()
            if not name or not file_path:
                QtWidgets.QMessageBox.warning(self, "Input Error", "Please provide a name and choose a file.")
                return
            if not os.path.isfile(file_path):
                QtWidgets.QMessageBox.warning(self, "Input Error", "The selected file does not exist or is not readable.")
                return
            self.accept()

    def get_credentials(self):
        method = self.method_selector.currentText()
        if method == "Manual Entry":
            name = self.name_entry_manual.text().strip()
            server = self.server_entry.text().strip()
            username = self.username_entry.text().strip()
            password = self.password_entry.text().strip()
            return ('manual', name, server, username, password)
        elif method == "m3u_plus URL Entry":
            name = self.name_entry_m3u.text().strip()
            m3u_url = self.m3u_url_entry.text().strip()
            return ('m3u_plus', name, m3u_url)
        else:
            name = self.name_entry_local.text().strip()
            file_path = self.local_path_entry.text().strip()
            return ('local_m3u', name, file_path)

class IPTVPlayerApp(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Xtream IPTV Player by MY-1 V4.0")
        self.resize(700, 550)

        self.groups = {}
        self.entries_per_tab = {
            'LIVE': [],
            'Movies': [],
            'Series': []
        }
        self.navigation_stacks = {
            'LIVE': [],
            'Movies': [],
            'Series': []
        }
        self.external_player_command = ""
        self.load_external_player_command()

        self.top_level_scroll_positions = {
            'LIVE': 0,
            'Movies': 0,
            'Series': 0
        }

        self.server = ""
        self.username = ""
        self.password = ""
        self.login_type = None
        self._local_entries_by_category = {}
        self._local_source_path = None
        self.epg_data = {}  
        self.channel_id_to_names = {}  
        self.epg_last_updated = None  
        self.threadpool = QThreadPool()
        self.threadpool.setMaxThreadCount(10)
        self.epg_id_mapping = {}
        self.epg_name_map = {}
        

        self.go_back_icon = self.style().standardIcon(QtWidgets.QStyle.SP_ArrowBack)
        self.live_channel_icon = self.style().standardIcon(QtWidgets.QStyle.SP_MediaVolume)
        self.movies_channel_icon = self.style().standardIcon(QtWidgets.QStyle.SP_ComputerIcon)
        self.series_channel_icon = self.style().standardIcon(QtWidgets.QStyle.SP_DirIcon)

        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(10, 10, 10, 10)
        main_layout.setSpacing(10)

        controls_layout = QVBoxLayout()
        controls_layout.setSpacing(10)

        row1_layout = QHBoxLayout()
        row1_layout.setSpacing(15)

        self.server_label = QLabel("Server URL:")
        self.server_label.setFixedWidth(53)
        self.server_entry = QLineEdit()
        self.server_entry.setPlaceholderText("Enter Server URL...")
        self.server_entry.setClearButtonEnabled(True)

        self.username_label = QLabel("Username:")
        self.username_label.setFixedWidth(50)
        self.username_entry = QLineEdit()
        self.username_entry.setPlaceholderText("Enter Username...")
        self.username_entry.setClearButtonEnabled(True)

        self.password_label = QLabel("Password:")
        self.password_label.setFixedWidth(50)
        self.password_entry = QLineEdit()
        self.password_entry.setPlaceholderText("Enter Password...")
        self.password_entry.setEchoMode(QLineEdit.Password)
        self.password_entry.setClearButtonEnabled(True)

        row1_layout.addWidget(self.server_label)
        row1_layout.addWidget(self.server_entry)
        row1_layout.addWidget(self.username_label)
        row1_layout.addWidget(self.username_entry)
        row1_layout.addWidget(self.password_label)
        row1_layout.addWidget(self.password_entry)

        buttons_layout = QHBoxLayout()
        buttons_layout.setSpacing(15)

        self.login_button = QPushButton("Login")
        self.login_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_DialogApplyButton))
        self.login_button.clicked.connect(self.login)

        self.m3u_plus_button = QPushButton("M3u_plus")
        search_icon = QIcon.fromTheme("edit-find")
        if search_icon.isNull():
            search_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileDialogContentsView)
        self.m3u_plus_button.setIcon(search_icon)
        self.m3u_plus_button.clicked.connect(self.open_m3u_plus_dialog)

        self.profiles_button = QPushButton("Profiles")
        self.profiles_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_DirIcon))
        self.profiles_button.setToolTip("Manage Saved Profiles")
        self.profiles_button.clicked.connect(self.open_profiles)

        self.choose_player_button = QPushButton("Choose Media Player")
        self.choose_player_button.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_MediaPlay))
        self.choose_player_button.clicked.connect(self.choose_external_player)

        buttons_layout.addWidget(self.login_button)
        buttons_layout.addWidget(self.m3u_plus_button)
        buttons_layout.addWidget(self.profiles_button)
        buttons_layout.addWidget(self.choose_player_button)

        checkbox_layout = QHBoxLayout()
        checkbox_layout.setAlignment(Qt.AlignRight)
        checkbox_layout.setSpacing(15)

        self.http_method_checkbox = QCheckBox("Use POST Method")
        self.http_method_checkbox.setToolTip("Check to use POST instead of GET for server requests")
        checkbox_layout.addWidget(self.http_method_checkbox)

        self.keep_on_top_checkbox = QCheckBox("Keep on top")
        self.keep_on_top_checkbox.setToolTip("Keep the application on top of all windows")
        self.keep_on_top_checkbox.stateChanged.connect(self.toggle_keep_on_top)
        checkbox_layout.addWidget(self.keep_on_top_checkbox)

        self.epg_checkbox = QCheckBox("Download EPG")
        self.epg_checkbox.setToolTip(
            "Download EPG data for channels. Preference is remembered across launches; "
            "data refreshes automatically every 60 minutes."
        )
        self.epg_checkbox.stateChanged.connect(self.on_epg_checkbox_toggled)
        checkbox_layout.addWidget(self.epg_checkbox)

        # Periodic EPG background refresh. Started/stopped by the checkbox handler.
        self._epg_refresh_timer = QTimer(self)
        self._epg_refresh_timer.setInterval(EPG_REFRESH_INTERVAL_MS)
        self._epg_refresh_timer.timeout.connect(self._on_epg_refresh_tick)

        # **Add Dark Theme Checkbox**
        self.dark_theme_checkbox = QCheckBox("Dark Theme")
        self.dark_theme_checkbox.setToolTip("Enable or disable dark theme")
        self.dark_theme_checkbox.stateChanged.connect(self.toggle_dark_theme)
        checkbox_layout.addWidget(self.dark_theme_checkbox)

        self.font_size_label = QLabel("Font Size:")
        self.font_size_spinbox = QSpinBox()
        self.font_size_spinbox.setRange(8, 24)
        self.font_size_spinbox.setValue(10)
        self.font_size_spinbox.setToolTip("Set the font size for playlist items")
        self.font_size_spinbox.valueChanged.connect(self.update_font_size)
        self.font_size_spinbox.setFixedWidth(60)

        self.default_font_size = 10
        checkbox_layout.addWidget(self.font_size_label)
        checkbox_layout.addWidget(self.font_size_spinbox)

        controls_layout.addLayout(row1_layout)
        controls_layout.addLayout(buttons_layout)
        controls_layout.addLayout(checkbox_layout)

        main_layout.addLayout(controls_layout)

        content_widget = QWidget()
        content_layout = QVBoxLayout(content_widget)
        content_layout.setSpacing(10)

        self.tab_widget = QTabWidget()
        content_layout.addWidget(self.tab_widget)

        self.tab_icon_size = QSize(24, 24)
        live_icon = self.style().standardIcon(QtWidgets.QStyle.SP_MediaVolume)
        movies_icon = self.style().standardIcon(QtWidgets.QStyle.SP_ComputerIcon)
        series_icon = self.style().standardIcon(QtWidgets.QStyle.SP_DirIcon)

        self.live_tab = QWidget()
        self.movies_tab = QWidget()
        self.series_tab = QWidget()

        self.tab_widget.addTab(self.live_tab, live_icon, "LIVE")
        self.tab_widget.addTab(self.movies_tab, movies_icon, "Movies")
        self.tab_widget.addTab(self.series_tab, series_icon, "Series")

        self.live_layout = QVBoxLayout(self.live_tab)
        self.movies_layout = QVBoxLayout(self.movies_tab)
        self.series_layout = QVBoxLayout(self.series_tab)

        self.search_bar_live = QLineEdit()
        self.search_bar_live.setPlaceholderText("Search Live Channels (Enter for instant)...")
        self.search_bar_live.setClearButtonEnabled(True)
        self.add_search_icon(self.search_bar_live)
        self._install_debounced_search(
            self.search_bar_live,
            lambda text: self.search_in_list('LIVE', text),
        )

        self.search_bar_movies = QLineEdit()
        self.search_bar_movies.setPlaceholderText("Search Movies (Enter for instant)...")
        self.search_bar_movies.setClearButtonEnabled(True)
        self.add_search_icon(self.search_bar_movies)
        self._install_debounced_search(
            self.search_bar_movies,
            lambda text: self.search_in_list('Movies', text),
        )

        self.search_bar_series = QLineEdit()
        self.search_bar_series.setPlaceholderText("Search Series (Enter for instant)...")
        self.search_bar_series.setClearButtonEnabled(True)
        self.add_search_icon(self.search_bar_series)
        self._install_debounced_search(
            self.search_bar_series,
            lambda text: self.search_in_list('Series', text),
        )

        self.add_search_bar(self.live_layout, self.search_bar_live)
        self.add_search_bar(self.movies_layout, self.search_bar_movies)
        self.add_search_bar(self.series_layout, self.search_bar_series)

        self.channel_list_live = QListWidget()
        self.channel_list_movies = QListWidget()
        self.channel_list_series = QListWidget()
        
        
        standard_icon_size = QSize(24, 24)

        # 🟢 Install event filter for tooltip detection
        for widget in [self.channel_list_live, self.channel_list_movies, self.channel_list_series]:
            widget.viewport().installEventFilter(self)
        
        
        for list_widget in [self.channel_list_live, self.channel_list_movies, self.channel_list_series]:
            list_widget.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
            list_widget.setIconSize(standard_icon_size)
            list_widget.setStyleSheet("""
                QListWidget::item {
                    padding-top: 5px;
                    padding-bottom: 5px;
                }
            """)
        
        self.live_layout.addWidget(self.channel_list_live)
        self.movies_layout.addWidget(self.channel_list_movies)
        self.series_layout.addWidget(self.channel_list_series)

        self.list_widgets = {
            'LIVE': self.channel_list_live,
            'Movies': self.channel_list_movies,
            'Series': self.channel_list_series,
        }
        
        self.tab_widget.currentChanged.connect(self.on_tab_change)
        self.channel_list_live.itemDoubleClicked.connect(self.channel_item_double_clicked)
        self.channel_list_movies.itemDoubleClicked.connect(self.channel_item_double_clicked)
        self.channel_list_series.itemDoubleClicked.connect(self.channel_item_double_clicked)

        # Favorites state and per-list star delegates
        self._active_profile_name = None
        self._favorites_tree = _empty_favorites_tree()
        self._fav_url_index = {}
        os.makedirs(FAVORITES_DIR, exist_ok=True)

        # One-shot cache of all leaf entries per tab, used by deep top-level search.
        self._all_entries_cache = {'LIVE': None, 'Movies': None, 'Series': None}

        self._star_delegate_live = FavoritesStarDelegate(self, "LIVE", self.channel_list_live)
        self._star_delegate_movies = FavoritesStarDelegate(self, "Movies", self.channel_list_movies)
        self._star_delegate_series = FavoritesStarDelegate(self, "Series", self.channel_list_series)
        self.channel_list_live.setItemDelegate(self._star_delegate_live)
        self.channel_list_movies.setItemDelegate(self._star_delegate_movies)
        self.channel_list_series.setItemDelegate(self._star_delegate_series)

        # Favorites tab (leftmost)
        self.favorites_tab = FavoritesPanel(self)
        fav_icon = self.style().standardIcon(QtWidgets.QStyle.SP_DialogApplyButton)
        self.tab_widget.insertTab(0, self.favorites_tab, fav_icon, "Favorites")
        self.tab_widget.setCurrentIndex(0)

        self.info_tab = QWidget()
        self.info_tab_layout = QVBoxLayout(self.info_tab)
        self.result_display = QTextEdit(self.info_tab)
        self.result_display.setReadOnly(True)
        default_font = QFont()
        default_font.setPointSize(self.default_font_size)
        self.result_display.setFont(default_font)
        self.info_tab_layout.addWidget(self.result_display)
        info_icon = self.style().standardIcon(QtWidgets.QStyle.SP_MessageBoxInformation)
        self.tab_widget.addTab(self.info_tab, info_icon, "Info")
        self.info_tab_initialized = False

        main_layout.addWidget(content_widget)

        self.progress_bar = QtWidgets.QProgressBar()
        self.progress_bar.setValue(0)
        self.progress_bar.setMaximum(100)
        self.progress_bar.setFixedHeight(25)
        self.progress_bar.setTextVisible(True)
        main_layout.addWidget(self.progress_bar)

        self.playlist_progress_animation = QPropertyAnimation(self.progress_bar, b"value")
        self.playlist_progress_animation.setDuration(1000)  # longer duration for smoother animation
        self.playlist_progress_animation.setEasingCurve(QEasingCurve.InOutQuad)

        self.load_theme_preference()
        # Restore EPG-enabled preference. Setting the checkbox here triggers
        # on_epg_checkbox_toggled, which is a no-op until a profile loads
        # (server/username are still empty). Once autoload_last_profile fires
        # below and the profile loads via load_profile_by_name -> login ->
        # fetch_categories_only, that flow already kicks off EPG loading
        # because epg_checkbox.isChecked() is True.
        if self.load_epg_enabled():
            self.epg_checkbox.setChecked(True)
        self.autoload_last_profile()



    def toggle_dark_theme(self, state):
        """
        Toggle the application's dark theme based on the checkbox state.
        Keeps your existing save_theme_preference calls and simply augments
        the stylesheet with tooltip styles.
        """
        app = QApplication.instance()

        # Try both qdarkstyle loaders for compatibility
        def _load_qdarkstyle():
            try:
                return qdarkstyle.load_stylesheet_pyqt5()
            except Exception:
                try:
                    return qdarkstyle.load_stylesheet(qt_api='pyqt5')
                except Exception:
                    return ""

        if state == Qt.Checked:
            base = _load_qdarkstyle()
            app.setStyleSheet(base + """
            /* Tooltip in dark */
            QToolTip {
                padding: 6px 8px;
                border: 1px solid #1aa3b5;
                background: #1b2332;
                color: #e3f6ff;
                font-size: 12px;
            }
            """)
            self.save_theme_preference(dark=True)
        else:
            # Reset to light but keep a nicer tooltip style
            app.setStyleSheet("""
            QToolTip {
                padding: 6px 8px;
                border: 1px solid #888;
                background: #ffffff;
                color: #222;
                font-size: 12px;
            }
            """)
            self.save_theme_preference(dark=False)

            

    def load_theme_preference(self):
        
        config = configparser.ConfigParser()
        config.read('config.ini')
        dark = False
        if 'Theme' in config:
            dark = config['Theme'].getboolean('Dark', fallback=False)
        if dark:
            self.dark_theme_checkbox.setChecked(True)
            QApplication.instance().setStyleSheet(qdarkstyle.load_stylesheet_pyqt5())
        else:
            self.dark_theme_checkbox.setChecked(False)
            QApplication.instance().setStyleSheet("")

    def save_theme_preference(self, dark):
        """
        Save the theme preference to config.ini.
        """
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'Theme' not in config:
            config['Theme'] = {}
        config['Theme']['Dark'] = str(dark)
        with open('config.ini', 'w') as config_file:
            config.write(config_file)

    def _install_debounced_search(self, line_edit, callback, delay_ms=300):
        """
        Wires a QLineEdit so that the search callback runs once after the user
        pauses typing for `delay_ms` milliseconds, and immediately on Enter.
        """
        timer = QTimer(self)
        timer.setSingleShot(True)
        timer.setInterval(delay_ms)
        pending = {"text": ""}

        def fire():
            callback(pending["text"])

        def on_text_changed(text):
            pending["text"] = text
            timer.start()

        def on_return_pressed():
            timer.stop()
            callback(line_edit.text())

        timer.timeout.connect(fire)
        line_edit.textChanged.connect(on_text_changed)
        line_edit.returnPressed.connect(on_return_pressed)
        return timer

    def add_search_icon(self, search_bar):
        search_icon = QIcon.fromTheme("edit-find")
        if search_icon.isNull():
            search_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileDialogContentsView)
        search_bar.addAction(search_icon, QLineEdit.LeadingPosition)

    def toggle_keep_on_top(self, state):
        flags = self.windowFlags()
        if state == Qt.Checked:
            flags |= Qt.WindowStaysOnTopHint
        else:
            flags &= ~Qt.WindowStaysOnTopHint
        self.setWindowFlags(flags)
        self.show()


    def add_search_bar(self, layout, search_bar):
        layout.addWidget(search_bar)

    def get_http_method(self):
        return 'POST' if self.http_method_checkbox.isChecked() else 'GET'

    def make_request(self, method, url, params=None, timeout=10):
        headers = {'User-Agent': CUSTOM_USER_AGENT}
        if method == 'POST':
            return requests.post(url, data=params, headers=headers, timeout=timeout)
        else:
            return requests.get(url, params=params, headers=headers, timeout=timeout)

    def open_m3u_plus_dialog(self):
        text, ok = QtWidgets.QInputDialog.getText(self, 'M3u_plus Login', 'Enter m3u_plus URL:')
        if ok and text:
            m3u_plus_url = text.strip()
            if self.extract_credentials_from_m3u_plus_url(m3u_plus_url):
                self.login()

    def update_font_size(self, value):
        self.default_font_size = value
        for tab_name, list_widget in self.list_widgets.items():
            for i in range(list_widget.count()):
                item = list_widget.item(i)
                font = item.font()
                font.setPointSize(value)
                item.setFont(font)

        font = QFont()
        font.setPointSize(value)
        self.result_display.setFont(font)

    def extract_credentials_from_m3u_plus_url(self, url):
        try:
            parsed = urlparse((url or "").strip())
            if parsed.scheme not in ('http', 'https') or not parsed.netloc:
                self.animate_progress(0, 100, "Invalid m3u_plus URL")
                return False
            qs = parse_qs(parsed.query)
            username = (qs.get('username') or [''])[0].strip()
            password = (qs.get('password') or [''])[0].strip()
            if not username or not password:
                self.animate_progress(0, 100, "URL missing username or password")
                return False
            server = f"{parsed.scheme}://{parsed.netloc}"
            self.server = server
            self.username = username
            self.password = password
            self.server_entry.setText(server)
            self.username_entry.setText(username)
            self.password_entry.setText(password)
            return True
        except Exception as e:
            print(f"Error extracting credentials: {e}")
            self.animate_progress(0, 100, "Error extracting credentials")
            return False

    def set_progress_text(self, text):
        self.progress_bar.setFormat(text)

    def animate_progress(self, start, end, text):
        self.playlist_progress_animation.stop()
        self.playlist_progress_animation.setStartValue(start)
        self.playlist_progress_animation.setEndValue(end)
        self.set_progress_text(text)
        self.playlist_progress_animation.start()

    def reset_progress_bar(self):
        self.playlist_progress_animation.stop()
        self.progress_bar.setValue(0)
        self.set_progress_text("")

    def login(self):
        # When logging into another server, reset the progress bar
        self.reset_progress_bar()
        self.epg_data = {}
        self.channel_id_to_names = {}
        self.epg_last_updated = None
        for tab_name, list_widget in self.list_widgets.items():
            list_widget.clear()

        # NB: we no longer delete the on-disk EPG cache here. The cache is
        # per-server (keyed by server URL) and managed by EPGWorker, which
        # honors EPG_CACHE_TTL_SECONDS. Forcing a delete here would defeat
        # the cache for legitimate same-server reloads.

        server = self.server_entry.text().strip()
        username = self.username_entry.text().strip()
        password = self.password_entry.text().strip()

        if not server or not username or not password:
            self.animate_progress(0, 100, "Please fill all fields")
            return

        # Start loading playlist from 0 to 100
        self.reset_progress_bar()
        self.animate_progress(0, 30, "Loading playlist...")
        self.fetch_categories_only(server, username, password)

    def fetch_categories_only(self, server, username, password):
        try:
            http_method = self.get_http_method()

            params = {
                'username': username,
                'password': password,
                'action': 'get_live_categories'
            }

            categories_url = f"{server}/player_api.php"
            live_response = self.make_request(http_method, categories_url, params, timeout=10)
            live_response.raise_for_status()

            params['action'] = 'get_vod_categories'
            movies_response = self.make_request(http_method, categories_url, params, timeout=10)
            movies_response.raise_for_status()

            params['action'] = 'get_series_categories'
            series_response = self.make_request(http_method, categories_url, params, timeout=10)
            series_response.raise_for_status()

            self.groups = {
                "LIVE": live_response.json(),
                "Movies": movies_response.json(),
                "Series": series_response.json(),
            }
            self.server = server
            self.username = username
            self.password = password
            self.login_type = 'xtream'
            self._all_entries_cache = {'LIVE': None, 'Movies': None, 'Series': None}
            self.navigation_stacks = {'LIVE': [], 'Movies': [], 'Series': []}
            self.top_level_scroll_positions = {'LIVE': 0, 'Movies': 0, 'Series': 0}
            self.update_category_lists('LIVE')
            self.update_category_lists('Movies')
            self.update_category_lists('Series')
            self.fetch_additional_data(server, username, password)

            # Playlist loading complete
            self.animate_progress(self.progress_bar.value(), 100, "Playlist loaded")

            # After playlist is fully loaded, if EPG is checked and not loaded, load EPG now
            if self.epg_checkbox.isChecked() and not self.epg_data:
                # Reset to 0 before loading EPG
                self.reset_progress_bar()
                self.animate_progress(0, 50, "Loading EPG data...")
                self.load_epg_data_async()

        except requests.exceptions.Timeout:
            print("Request timed out")
            self.animate_progress(self.progress_bar.value(), 100, "Login timed out")
        except requests.RequestException as e:
            print(f"Network error: {e}")
            self.animate_progress(self.progress_bar.value(), 100, "Network Error")
        except ValueError as e:
            print(f"JSON decode error: {e}")
            self.animate_progress(self.progress_bar.value(), 100, "Invalid server response")
        except Exception as e:
            print(f"Error fetching categories: {e}")
            self.animate_progress(self.progress_bar.value(), 100, "Error fetching categories")

    def load_local_m3u(self, file_path):
        try:
            self.reset_progress_bar()
            self.epg_data = {}
            self.channel_id_to_names = {}
            self.epg_last_updated = None
            for lw in self.list_widgets.values():
                lw.clear()

            if not file_path or not os.path.isfile(file_path):
                self.animate_progress(0, 100, "M3U file not found")
                return

            self.animate_progress(0, 50, "Parsing M3U...")
            try:
                parsed = load_or_parse_m3u_with_cache(file_path)
            except Exception as e:
                print(f"Error parsing M3U: {e}")
                self.animate_progress(0, 100, "Error parsing M3U")
                return

            self.groups = parsed['groups']
            entries_by_cat = {}
            for key, value in parsed['entries_by_category'].items():
                tab, _, group_title = key.partition('||')
                entries_by_cat[(tab, group_title)] = value
            self._local_entries_by_category = entries_by_cat
            self._local_source_path = parsed.get('source_path', file_path)

            self.server = ""
            self.username = ""
            self.password = ""
            self.login_type = 'local_m3u'
            self._all_entries_cache = {'LIVE': None, 'Movies': None, 'Series': None}
            self.navigation_stacks = {'LIVE': [], 'Movies': [], 'Series': []}
            self.top_level_scroll_positions = {'LIVE': 0, 'Movies': 0, 'Series': 0}
            self.entries_per_tab = {'LIVE': [], 'Movies': [], 'Series': []}

            for tab in ('LIVE', 'Movies', 'Series'):
                self.update_category_lists(tab)

            total = sum(len(v) for v in entries_by_cat.values())
            self.result_display.setText(
                f"Local playlist loaded\n"
                f"File: {self._local_source_path}\n"
                f"Total entries: {total}\n"
                f"LIVE categories: {len(self.groups['LIVE'])}\n"
                f"Movie categories: {len(self.groups['Movies'])}\n"
                f"Series categories: {len(self.groups['Series'])}\n"
            )
            self.info_tab_initialized = True

            if total == 0:
                self.animate_progress(self.progress_bar.value(), 100, "Empty or invalid M3U")
            else:
                self.animate_progress(self.progress_bar.value(), 100, "Playlist loaded")
        except Exception as e:
            print(f"Error loading local M3U: {e}")
            self.animate_progress(0, 100, "Error loading local M3U")

    def _show_local_category_entries(self, category_name, tab_name):
        entries = self._local_entries_by_category.get((tab_name, category_name), [])
        self.entries_per_tab[tab_name] = entries
        list_widget = self.get_list_widget(tab_name)
        self.navigation_stacks[tab_name].append({
            'level': 'channels',
            'data': {'tab_name': tab_name, 'entries': entries},
            'scroll_position': 0,
        })
        self.show_channels(list_widget, tab_name)

    def fetch_additional_data(self, server, username, password):
        try:
            if not server.startswith("http://") and not server.startswith("https://"):
                server = f"http://{server}"

            headers = {'User-Agent': CUSTOM_USER_AGENT}
            payload = {'username': username, 'password': password}
            url = f"{server}/player_api.php"

            response = requests.post(url, headers=headers, data=payload, timeout=10)
            response.raise_for_status()

            additional_data = response.json()
            user_info = additional_data.get("user_info", {})
            server_info = additional_data.get("server_info", {})

            hostname = server_info.get("url", server.replace("http://", "").replace("https://", ""))
            port = server_info.get("port", 25461)
            host = f"http://{hostname}:{port}"

            username = user_info.get("username", "Unknown")
            password = user_info.get("password", "Unknown")
            max_connections = user_info.get("max_connections", "Unlimited")
            active_connections = user_info.get("active_cons", "0")
            trial = "Yes" if user_info.get("is_trial") == "1" else "No"
            expire_timestamp = user_info.get("exp_date")
            expiry = (
                datetime.fromtimestamp(int(expire_timestamp)).strftime("%B %d, %Y")
                if expire_timestamp else "Unlimited"
            )
            status = user_info.get("status", "Unknown")

            created_at_timestamp = user_info.get("created_at", "Unknown")
            created_at = (
                datetime.fromtimestamp(int(created_at_timestamp)).strftime("%B %d, %Y")
                if created_at_timestamp and created_at_timestamp.isdigit() else "Unknown"
            )
            timezone = server_info.get("timezone", "Unknown")

            formatted_data = (
                f"Host: {host}\n"
                f"Username: {username}\n"
                f"Password: {password}\n"
                f"Max Connections: {max_connections}\n"
                f"Active Connections: {active_connections}\n"
                f"Timezone: {timezone}\n"
                f"Trial: {trial}\n"
                f"Status: {status}\n"
                f"Created At: {created_at}\n"
                f"Expiry: {expiry}\n"
            )

            self.result_display.setText(formatted_data)
            self.info_tab_initialized = True

        except Exception as e:
            print(f"Error fetching additional data: {e}")

    def load_epg_data_async(self):
        if not self.server or not self.username or not self.password:
            # Can't load EPG if not logged in
            return
        http_method = self.get_http_method()
        epg_worker = EPGWorker(
            self.server, self.username, self.password, http_method,
            _epg_cache_file_for(self.server),
        )
        epg_worker.signals.finished.connect(self.on_epg_loaded)
        epg_worker.signals.error.connect(self.on_epg_error)
        self.threadpool.start(epg_worker)
        # Ensure the periodic refresh keeps running while EPG is enabled.
        if (self.epg_checkbox.isChecked()
                and hasattr(self, '_epg_refresh_timer')
                and not self._epg_refresh_timer.isActive()):
            self._epg_refresh_timer.start()

    def on_epg_loaded(self, epg_data, channel_id_to_names):
        self.epg_data = epg_data
        self.channel_id_to_names = channel_id_to_names

        name_to_id = {}
        for cid, names in channel_id_to_names.items():
            for n in names:
                if n not in name_to_id:
                    name_to_id[n] = cid
        self.epg_name_map = name_to_id

        # EPG done
        self.animate_progress(self.progress_bar.value(), 100, "EPG data loaded")

        # If LIVE is currently showing a channel list, rebuild it so each row
        # picks up its on-air EPG snippet (stored on the item at render time).
        live_stack = self.navigation_stacks.get('LIVE', [])
        if live_stack and live_stack[-1].get('level') == 'channels':
            self.show_channels(self.channel_list_live, 'LIVE')

        # Favorites tree needs a rebuild so LIVE entries pick up EPG snippets.
        if hasattr(self, 'favorites_tab'):
            self.favorites_tab.refresh()

    def on_epg_error(self, error_message):
        print(f"Error fetching EPG data: {error_message}")
        self.animate_progress(self.progress_bar.value(), 100, "Error fetching EPG data")

    def channel_item_double_clicked(self, item):
        try:
            sender = self.sender()
            category = {
                self.channel_list_live: 'LIVE',
                self.channel_list_movies: 'Movies',
                self.channel_list_series: 'Series'
            }.get(sender)

            if not category:
                return

            selected_item = sender.currentItem()
            if not selected_item:
                return

            selected_text = selected_item.text()
            list_widget = self.get_list_widget(category)
            current_scroll_position = list_widget.verticalScrollBar().value()
            stack = self.navigation_stacks[category]

            if stack:
                stack[-1]['scroll_position'] = current_scroll_position
            else:
                self.top_level_scroll_positions[category] = current_scroll_position

            self.handle_xtream_double_click(selected_item, selected_text, category, sender)

        except Exception as e:
            print(f"Error occurred while handling double click: {e}")

    def update_category_lists(self, tab_name):
        if tab_name == 'LIVE':
            self.search_bar_live.clear()
        elif tab_name == 'Movies':
            self.search_bar_movies.clear()
        elif tab_name == 'Series':
            self.search_bar_series.clear()

        try:
            list_widget = self.get_list_widget(tab_name)
            list_widget.clear()

            if self.navigation_stacks[tab_name]:
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

            if tab_name == 'LIVE':
                channel_icon = self.live_channel_icon
            elif tab_name == 'Movies':
                channel_icon = self.movies_channel_icon
            elif tab_name == 'Series':
                channel_icon = self.series_channel_icon
            else:
                channel_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileIcon)

            group_list = self.groups[tab_name]
            category_names = sorted(group["category_name"] for group in group_list)
            items = []
            for category_name in category_names:
                item = QListWidgetItem(category_name)
                item.setIcon(channel_icon)
                items.append(item)

            items.sort(key=lambda x: x.text())
            for item in items:
                list_widget.addItem(item)

            scroll_position = self.top_level_scroll_positions.get(tab_name, 0)
            list_widget.verticalScrollBar().setValue(scroll_position)
        except Exception as e:
            print(f"Error updating category lists: {e}")
            self.animate_progress(self.progress_bar.value(), 100, "Error updating lists")

        # ─── inside class IPTVPlayerApp ─────────────────────────────────────────────
    def _get_all_entries(self, tab_name):
        """
        Return a flat list of all leaf entries for `tab_name`, fetching
        once per session for Xtream profiles (no category_id filter pulls
        the whole catalog in a single request). For local M3U profiles,
        aggregates the in-memory groups. For Xtream Series, returns
        series-title entries (clicking drills into seasons).
        """
        cached = self._all_entries_cache.get(tab_name)
        if cached is not None:
            return cached

        entries = []
        if self.login_type == 'local_m3u':
            for (tab, _grp), items in self._local_entries_by_category.items():
                if tab == tab_name:
                    entries.extend(items)
        elif self.login_type == 'xtream' and self.server and self.username:
            try:
                self.animate_progress(0, 60, f"Indexing all {tab_name} for search...")
                params = {
                    "username": self.username,
                    "password": self.password,
                    "action": "",
                }
                if tab_name == "LIVE":
                    params["action"] = "get_live_streams"
                    stream_type = "live"
                elif tab_name == "Movies":
                    params["action"] = "get_vod_streams"
                    stream_type = "movie"
                else:
                    params["action"] = "get_series"
                    stream_type = "series"
                resp = self.make_request(
                    self.get_http_method(),
                    f"{self.server}/player_api.php",
                    params,
                    timeout=20,
                )
                resp.raise_for_status()
                data = resp.json()
                if not isinstance(data, list):
                    data = []
                # Decorate the same way fetch_channels does
                for entry in data:
                    sid = entry.get("stream_id")
                    if sid and tab_name in ("LIVE", "Movies"):
                        ext = "ts" if tab_name == "LIVE" else entry.get("container_extension", "m3u8")
                        entry["url"] = (
                            f"{self.server}/{stream_type}/{self.username}/"
                            f"{self.password}/{sid}.{ext}"
                        )
                    epg_id = (entry.get("epg_channel_id") or "").strip().lower()
                    entry["epg_channel_id"] = epg_id if epg_id else None
                entries = data
                self.animate_progress(self.progress_bar.value(), 100,
                                      f"Indexed {len(entries)} {tab_name} entries")
            except Exception as e:
                print(f"Error indexing {tab_name}: {e}")
                self.animate_progress(self.progress_bar.value(), 100,
                                      f"Error indexing {tab_name}")
                entries = []

        self._all_entries_cache[tab_name] = entries
        return entries

    def fetch_channels(self, category_name, tab_name):
        """
        Retrieve the LIVE / VOD / Series list for the chosen category and show
        it.  No per-movie look-ups are performed here – we only get the list
        itself, add a playback URL, and store it on the navigation stack.
        """
        try:
            # 1. category_id for the clicked name --------------------------------
            category_id = next(
                g["category_id"] for g in self.groups[tab_name]
                if g["category_name"] == category_name
            )

            # remember scroll position before diving one level deeper -----------
            lw          = self.get_list_widget(tab_name)
            curr_scroll = lw.verticalScrollBar().value()
            if self.navigation_stacks[tab_name]:
                self.navigation_stacks[tab_name][-1]["scroll_position"] = curr_scroll
            else:
                self.top_level_scroll_positions[tab_name] = curr_scroll

            # 2. request the list ------------------------------------------------
            params = {
                "username":   self.username,
                "password":   self.password,
                "action":     "",
                "category_id": category_id,
            }
            if tab_name == "LIVE":
                params["action"] = "get_live_streams"
                stream_type      = "live"
            elif tab_name == "Movies":
                params["action"] = "get_vod_streams"
                stream_type      = "movie"
            else:  # Series tab
                params["action"] = "get_series"
                stream_type      = "series"

            response = self.make_request(
                self.get_http_method(),
                f"{self.server}/player_api.php",
                params, timeout=10
            )
            response.raise_for_status()
            data = response.json()
            if not isinstance(data, list):
                raise ValueError("Expected a list of entries")

            # 3. add playback URL and tidy epg_channel_id -----------------------
            for entry in data:
                sid = entry.get("stream_id")
                if sid:
                    if tab_name == "LIVE":
                        ext = "ts"
                    else:
                        ext = entry.get("container_extension", "m3u8")
                    entry["url"] = (f"{self.server}/{stream_type}/{self.username}/"
                                    f"{self.password}/{sid}.{ext}")
                epg_id = (entry.get("epg_channel_id") or "").strip().lower()
                entry["epg_channel_id"] = epg_id if epg_id else None


            # 4. push onto stack & display --------------------------------------
            self.entries_per_tab[tab_name] = data
            self.navigation_stacks[tab_name].append({
                "level": "channels",
                "data":  {"tab_name": tab_name, "entries": data},
                "scroll_position": 0
            })
            self.show_channels(lw, tab_name)

        except Exception as e:
            print("Error fetching channels:", e)
            self.animate_progress(self.progress_bar.value(), 100,
                                  "Error fetching channels")
    # ─────────────────────────────────────────────────────────────────────────────



    def handle_xtream_double_click(self, selected_item, selected_text, tab_name, sender):
        try:
            list_widget = self.get_list_widget(tab_name)
            stack = self.navigation_stacks[tab_name]

            if selected_text == "Go Back":
                if stack:
                    stack.pop()
                    if stack:
                        last_level = stack[-1]
                        level = last_level['level']
                        data = last_level['data']
                        scroll_position = last_level.get('scroll_position', 0)
                        if level == 'channels':
                            self.entries_per_tab[tab_name] = data['entries']
                            self.show_channels(list_widget, tab_name)
                            list_widget.verticalScrollBar().setValue(scroll_position)
                        elif level == 'series_categories':
                            self.show_series_in_category(data['series_list'], restore_scroll_position=True, scroll_position=scroll_position)
                        elif level == 'series':
                            self.show_seasons(data['seasons'], restore_scroll_position=True, scroll_position=scroll_position)
                        elif level == 'season':
                            self.show_episodes(data['episodes'], restore_scroll_position=True, scroll_position=scroll_position)
                    else:
                        self.update_category_lists(tab_name)
                        list_widget.verticalScrollBar().setValue(self.top_level_scroll_positions.get(tab_name, 0))
                else:
                    self.update_category_lists(tab_name)
                    list_widget.verticalScrollBar().setValue(self.top_level_scroll_positions.get(tab_name, 0))
                return

            if tab_name != "Series":
                if selected_text in [group["category_name"] for group in self.groups[tab_name]]:
                    if self.login_type == 'local_m3u':
                        self._show_local_category_entries(selected_text, tab_name)
                    else:
                        self.fetch_channels(selected_text, tab_name)
                else:
                    selected_entry = selected_item.data(Qt.UserRole)
                    if selected_entry and "url" in selected_entry:
                        self.play_channel(selected_entry)
                return

            # Series logic
            if tab_name == "Series":
                if not stack:
                    # If the row is a series entry (e.g. from a deep search result),
                    # drill into its seasons directly.
                    selected_entry = selected_item.data(Qt.UserRole)
                    if isinstance(selected_entry, dict) and selected_entry.get("series_id"):
                        self.fetch_seasons(selected_entry)
                        return
                    if selected_text in [group["category_name"] for group in self.groups["Series"]]:
                        if self.login_type == 'local_m3u':
                            self._show_local_category_entries(selected_text, "Series")
                        else:
                            self.fetch_series_in_category(selected_text)
                        return
                elif stack[-1]['level'] == 'channels':
                    selected_entry = selected_item.data(Qt.UserRole)
                    if selected_entry and "url" in selected_entry:
                        self.play_channel(selected_entry)
                    return
                elif stack[-1]['level'] == 'series_categories':
                    series_entry = selected_item.data(Qt.UserRole)
                    if series_entry and "series_id" in series_entry:
                        self.fetch_seasons(series_entry)
                        return
                elif stack[-1]['level'] == 'series':
                    season_number = selected_item.data(Qt.UserRole)
                    series_entry = stack[-1]['data']['series_entry']
                    self.fetch_episodes(series_entry, season_number)
                    return
                elif stack[-1]['level'] == 'season':
                    selected_entry = selected_item.data(Qt.UserRole)
                    if selected_entry and "url" in selected_entry:
                        self.play_channel(selected_entry)
                    return

        except Exception as e:
            print(f"Error loading channels: {e}")


    def fetch_tmdb_description(self, tmdb_id, media_hint=None):
        """
        Scrape basic info (title / description / rating / year) from TMDb.
        Tries the 'movie' page first; if it 404s, tries the 'tv' page.
        The result – or an empty dict on failure – is cached in self.tmdb_cache.
        """
        import ssl
        if not tmdb_id or not str(tmdb_id).isdigit():
            return {}

        # initialise cache once
        if not hasattr(self, "tmdb_cache"):
            self.tmdb_cache = {}

        # return cached (including cached failures)
        if tmdb_id in self.tmdb_cache:
            return self.tmdb_cache[tmdb_id]

        # decide order to probe
        probe_order = []
        if media_hint == "movie":
            probe_order = ["movie"]
        elif media_hint == "tv":
            probe_order = ["tv"]
        else:
            probe_order = ["movie", "tv"]

        headers  = {"User-Agent": "Mozilla/5.0"}
        context  = ssl._create_unverified_context()
        patterns = {
            "desc":  re.compile(r'<div class="overview">\s*<p[^>]*>(.*?)</p>', re.DOTALL),
            "desc2": re.compile(r'<meta name="description" content="(.*?)"'),
            "title": re.compile(r'<title>(.*?)\s*\|\s*The Movie Database', re.DOTALL),
            "rating":re.compile(r'<span class="user_score_chart"[^>]+data-percent="(\d+)"'),
            "year":  re.compile(r'<span class="release">.*?(\d{4})</span>'),
        }

        for path in probe_order:
            url = f"https://www.themoviedb.org/{path}/{tmdb_id}"
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=10, context=context) as resp:
                    html_data = resp.read().decode("utf-8")

                # --- scrape ---
                desc_match  = patterns["desc"].search(html_data) or patterns["desc2"].search(html_data)
                title_match = patterns["title"].search(html_data)
                rate_match  = patterns["rating"].search(html_data)
                year_match  = patterns["year"].search(html_data)

                result = {
                    "title":       title_match.group(1).strip()  if title_match else "",
                    "description": desc_match.group(1).strip()   if desc_match else "",
                    "rating":      f"{int(rate_match.group(1))/10:.1f}/10" if rate_match else "",
                    "year":        year_match.group(1)           if year_match else "",
                }
                # store & return
                self.tmdb_cache[tmdb_id] = result
                return result

            except urllib.error.HTTPError as http_err:
                if http_err.code == 404:
                    # try next path in order
                    continue
                else:
                    print("TMDb fetch error:", http_err)
                    break
            except Exception as e:
                print("TMDb fetch error:", e)
                break

        # cache the miss so we do not retry every hover
        self.tmdb_cache[tmdb_id] = {}
        return {}




    def _current_epg_description(self, entry):
        """
        Return the description of the programme that is *on-air now* for the
        supplied LIVE entry.  If none is airing, return the first upcoming
        programme’s description.  If the channel is not in the EPG, return ''.
        """
        try:
            if not self.epg_data:
                return ""

            # --- locate the EPG channel id -----------------------------------
            epg_id = (entry.get("epg_channel_id") or "").strip().lower()
            if not epg_id:
                # fall back to fuzzy name-map
                ch_name = normalize_channel_name(entry.get("name", ""))
                epg_id  = self.epg_name_map.get(ch_name, "")

            if not epg_id or epg_id not in self.epg_data:
                return ""

            now      = datetime.now(tz=tz.tzlocal())
            epg_list = self.epg_data[epg_id]

            # --- pick "current" (or very next) programme ---------------------
            current = None
            for p in epg_list:
                start = parser.parse(p["start_time"])
                stop  = parser.parse(p["stop_time"])
                if start <= now <= stop:
                    current = p
                    break
                if start > now and current is None:
                    current = p   # first upcoming show, just in case

            return (current or {}).get("description", "")

        except Exception as err:
            print("EPG helper error:", err)
            return ""



    def _lazy_load_movie_info(self, entry):
        if entry.get("_info_fetched"):
            return

        vod_id = entry.get("stream_id")
        if not vod_id:
            entry["_info_fetched"] = True
            return

        try:
            info = self.make_request(
                self.get_http_method(),
                f"{self.server}/player_api.php",
                {
                    "username": self.username,
                    "password": self.password,
                    "action":   "get_vod_info",
                    "vod_id":   vod_id
                },
                timeout=10
            ).json().get("info", {})

            entry["info"] = info
            entry["plot"]        = info.get("plot", "")
            entry["stream_icon"] = info.get("movie_image", entry.get("stream_icon", ""))
            entry["tmdb_id"]     = (info.get("tmdb_id") or info.get("imdb_id") or "")

        except Exception as err:
            print("Lazy VOD-info fetch failed:", err)

        entry["_info_fetched"] = True



    def _lazy_load_series_info(self, entry):
        if entry.get("_info_fetched"):
            return

        series_id = entry.get("series_id")
        episode_id = entry.get("id")

        try:
            # Fetch for series
            if series_id:
                info = self.make_request(
                    self.get_http_method(),
                    f"{self.server}/player_api.php",
                    {
                        "username": self.username,
                        "password": self.password,
                        "action":   "get_series_info",
                        "series_id": series_id
                    },
                    timeout=10
                ).json().get("info", {})
                entry["info"] = info
            # For episodes, info may be already present (most APIs send it inline)
            elif episode_id:
                if entry.get("info"):
                    entry["_info_fetched"] = True
                    return
                entry["info"] = {}
            else:
                entry["info"] = {}

        except Exception as err:
            print("Lazy Series/Episode-info fetch failed:", err)

        entry["_info_fetched"] = True




    def eventFilter(self, obj, event):
        if event.type() == QtCore.QEvent.ToolTip:
            for widget, tab in [
                (self.channel_list_live,   "LIVE"),
                (self.channel_list_movies, "Movies"),
                (self.channel_list_series, "Series")
            ]:
                if obj is widget.viewport():
                    idx = widget.indexAt(event.pos())
                    if not idx.isValid():
                        break

                    entry = widget.item(idx.row()).data(Qt.UserRole)
                    if not isinstance(entry, dict):
                        return False

                    # ==== MOVIE TOOLTIP ====
                    if tab == "Movies":
                        if not entry.get("_info_fetched"):
                            self._lazy_load_movie_info(entry)
                        info = entry.get("info", {})
                        plot = info.get("plot", "") or entry.get("plot", "")
                        genre = info.get("genre", "")
                        rating = str(info.get("rating", ""))
                        release_date = info.get("releasedate") or info.get("releaseDate", "")
                        duration = info.get("duration", "")
                        cast = info.get("cast", "")
                        director = info.get("director", "")
                        trailer = info.get("youtube_trailer", "")
                        tmdb_id = info.get("tmdb_id", "") or entry.get("tmdb_id", "")

                        if not plot and tmdb_id:
                            plot = self.fetch_tmdb_description(tmdb_id).get("description", "")
                        if not plot:
                            plot = "No description available."

                        details = []
                        if genre: details.append(f"<b>Genre:</b> {html.escape(genre)}")
                        if rating: details.append(f"<b>Rating:</b> {html.escape(rating)}")
                        if release_date: details.append(f"<b>Release:</b> {html.escape(str(release_date))}")
                        if duration: details.append(f"<b>Duration:</b> {html.escape(duration)}")
                        if cast: details.append(f"<b>Cast:</b> {html.escape(cast)}")
                        if director: details.append(f"<b>Director:</b> {html.escape(director)}")
                        if trailer:
                            details.append(f'Trailer: https://youtu.be/{html.escape(trailer)}')

                        details_html = "<br>".join(details)
                        desc_html = html.escape(plot).replace("\n", "<br>")

                        icon_html = ""
                        poster_url = info.get("movie_image") or entry.get("stream_icon") or entry.get("cover", "")
                        local = self.get_cached_icon_path(poster_url)
                        if local:
                            icon_html = f'<img src="{local}" width="160"><br>'

                        movie_title = info.get("name", entry.get("name", "Untitled"))
                        tooltip = (
                            f'<div style="padding:0;margin:0;font-size:13px;max-width:400px;'
                            f'font-family:Arial;white-space:normal;word-wrap:break-word;">'
                            f'{icon_html}<b>{html.escape(movie_title)}</b><br>'
                            f'{details_html}<br><br>{desc_html}</div>'
                        )

                        QToolTip.showText(widget.mapToGlobal(event.pos()), tooltip)
                        return True

                    # ==== SERIES/EPISODE TOOLTIP ====
                    if tab == "Series":
                        if not entry.get("_info_fetched"):
                            self._lazy_load_series_info(entry)
                        info = entry.get("info", {})
                        

                        # Use both 'title' and 'name' in case one is missing
                        item_title = entry.get("title") or info.get("name") or entry.get("name", "Untitled")
                        plot = info.get("plot", "") or entry.get("plot", "")
                        genre = info.get("genre", "")
                        rating = str(info.get("rating", ""))
                        # Handle both 'releasedate' and 'releaseDate'
                        release_date = info.get("releasedate") or info.get("releaseDate", "")
                        duration = info.get("duration", "")
                        cast = info.get("cast", "")
                        director = info.get("director", "")
                        trailer = info.get("youtube_trailer", "")

                        details = []
                        if genre: details.append(f"<b>Genre:</b> {html.escape(genre)}")
                        if rating: details.append(f"<b>Rating:</b> {html.escape(rating)}")
                        if release_date: details.append(f"<b>Release:</b> {html.escape(str(release_date))}")
                        if duration: details.append(f"<b>Duration:</b> {html.escape(duration)}")
                        if cast: details.append(f"<b>Cast:</b> {html.escape(cast)}")
                        if director: details.append(f"<b>Director:</b> {html.escape(director)}")
                        if trailer:
                            details.append(f'Trailer: https://youtu.be/{html.escape(trailer)}')

                        details_html = "<br>".join(details)
                        desc_html = html.escape(plot).replace("\n", "<br>")

                        icon_html = ""
                        poster_url = info.get("movie_image") or entry.get("stream_icon") or entry.get("cover", "")
                        local = self.get_cached_icon_path(poster_url)
                        if local:
                            icon_html = f'<img src="{local}" width="160"><br>'

                        tooltip = (
                            f'<div style="padding:0;margin:0;font-size:13px;max-width:400px;'
                            f'font-family:Arial;white-space:normal;word-wrap:break-word;">'
                            f'{icon_html}<b>{html.escape(str(item_title))}</b><br>'
                            f'{details_html}<br><br>{desc_html}</div>'
                        )

                        QToolTip.showText(widget.mapToGlobal(event.pos()), tooltip)
                        return True

                    # ==== LIVE TOOLTIP (EPG) ====
                    if tab == "LIVE" and self.epg_data:
                        desc = self._current_epg_description(entry) or "No current EPG information available."
                        desc_html = html.escape(desc).replace("\n", "<br>")
                        title_html = html.escape(entry.get("name", "Untitled"))
                        tooltip = (
                            f'<div style="padding:0;margin:0;font-size:13px;max-width:380px;'
                            f'font-family:Arial;white-space:normal;word-wrap:break-word;">'
                            f'<b>{title_html}</b><br>{desc_html}</div>'
                        )
                        if desc.strip():
                            QToolTip.showText(widget.mapToGlobal(event.pos()), tooltip)
                        return True

        return super().eventFilter(obj, event)
















    def get_cached_icon_path(self, url):
        try:
            if not url:
                return ""

            os.makedirs(Path.home() / '.iptv' / 'icons', exist_ok=True)
            ext = os.path.splitext(url)[-1] if '.' in url else '.jpg'
            filename = re.sub(r'\W+', '_', url) + ext
            local_path = Path.home() / '.iptv' / 'icons' / filename

            if not local_path.exists():
                req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})

                # 🔐 Disable SSL cert verification (safe for public image downloads)
                ssl_ctx = ssl._create_unverified_context()
                with urllib.request.urlopen(req, timeout=10, context=ssl_ctx) as response, open(local_path, 'wb') as out_file:
                    out_file.write(response.read())

            return str(local_path)

        except Exception as e:
            print(f"Failed to cache icon: {e}")
            return ""



    def show_channels(self, list_widget, tab_name):
        """
        Populate the QListWidget for LIVE / Movies / Series.

        • LIVE:   – no tooltip at all when EPG is not available
                  – EPG description shown later by eventFilter once EPG is loaded
                  – no poster icon (per your last request)
        • Movies / Series: keep normal icons & placeholder tooltip
        """
        try:
            list_widget.clear()

            # ─── “Go Back” at sub-levels ─────────────────────────────────────────
            if self.navigation_stacks[tab_name]:
                back_item = QListWidgetItem("Go Back")
                back_item.setIcon(self.go_back_icon)
                list_widget.addItem(back_item)

            # choose an icon only for Movies / Series
            if tab_name == "LIVE":
                row_icon = QIcon()                # blank – we don’t want icons
            elif tab_name == "Movies":
                row_icon = self.movies_channel_icon
            elif tab_name == "Series":
                row_icon = self.series_channel_icon
            else:
                row_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileIcon)

            items = []
            now = datetime.now(tz=tz.tzlocal()) if self.epg_data else None

            for entry in self.entries_per_tab[tab_name]:
                display_text = entry.get("name", "Unnamed")
                tooltip_text = ""                 # defaults to nothing
                epg_text = ""                     # rendered in the right column by the delegate

                # ─── LIVE: capture on-air programme (if EPG ready) ──────────────
                if tab_name == "LIVE" and self.epg_data:
                    epg_id = entry.get("epg_channel_id") or ""
                    if not epg_id:
                        ch_norm = normalize_channel_name(entry.get("name", ""))
                        epg_id  = self.epg_name_map.get(ch_norm, "")
                    epg_list = self.epg_data.get(epg_id, [])

                    for prog in epg_list:
                        start = parser.parse(prog["start_time"])
                        stop  = parser.parse(prog["stop_time"])
                        if start <= now <= stop:
                            start_s = start.astimezone(tz.tzlocal()).strftime("%I:%M %p")
                            stop_s  = stop.astimezone(tz.tzlocal()).strftime("%I:%M %p")
                            epg_text = f"{prog['title']} ({start_s}-{stop_s})"
                            tooltip_text = prog["description"]            # may be ""
                            break

                # ─── Movies / Series placeholder (“Loading preview…”) ───────────
                elif tab_name in ("Movies", "Series"):
                    tooltip_text = "Loading preview…"

                # build list row --------------------------------------------------
                itm = QListWidgetItem(display_text)
                itm.setData(Qt.UserRole, entry)
                itm.setData(ROLE_STARRABLE, True)
                if epg_text:
                    itm.setData(ROLE_EPG_TEXT, epg_text)
                itm.setIcon(row_icon)

                # LIVE: show nothing until EPG is ready
                if tab_name == "LIVE" and not self.epg_data:
                    itm.setToolTip("")          # absolutely no hover text
                else:
                    itm.setToolTip(tooltip_text)

                items.append(itm)

            # alphabetical order
            items.sort(key=lambda x: x.text())
            for itm in items:
                list_widget.addItem(itm)

            list_widget.verticalScrollBar().setValue(0)
        except Exception as err:
            print("Error displaying channels:", err)





    def fetch_series_in_category(self, category_name):
        try:
            list_widget = self.get_list_widget('Series')
            curr_scroll = list_widget.verticalScrollBar().value()
            if self.navigation_stacks['Series']:
                self.navigation_stacks['Series'][-1]['scroll_position'] = curr_scroll
            else:
                self.top_level_scroll_positions['Series'] = curr_scroll

            category_id = next(g["category_id"]
                               for g in self.groups["Series"]
                               if g["category_name"] == category_name)

            params = {
                "username": self.username,
                "password": self.password,
                "action":   "get_series",
                "category_id": category_id
            }
            resp = self.make_request(self.get_http_method(),
                                     f"{self.server}/player_api.php",
                                     params)
            resp.raise_for_status()
            series_list = resp.json()

            # 🔑  store for quick lookup (poster / plot / tmdb_id, …)
            self.series_lookup = {s["series_id"]: s for s in series_list}

            self.navigation_stacks['Series'].append({
                "level": "series_categories",
                "data": {"series_list": series_list},
                "scroll_position": 0
            })
            self.show_series_in_category(series_list)

        except Exception as e:
            print("Error fetching series:", e)


    def show_series_in_category(self, series_list, restore_scroll_position=False, scroll_position=0):
        try:
            list_widget = self.channel_list_series

            list_widget.clear()
            if self.navigation_stacks['Series']:
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

            items = []
            for entry in series_list:
                item = QListWidgetItem(entry["name"])
                item.setData(Qt.UserRole, entry)
                item.setIcon(self.series_channel_icon)
                items.append(item)

            items.sort(key=lambda x: x.text())
            for item in items:
                list_widget.addItem(item)

            if restore_scroll_position:
                QTimer.singleShot(0, lambda: list_widget.verticalScrollBar().setValue(scroll_position))
            else:
                list_widget.verticalScrollBar().setValue(0)

            self.current_series_list = series_list
        except Exception as e:
            print(f"Error displaying series: {e}")

    def fetch_seasons(self, series_entry):
        try:
            list_widget = self.get_list_widget('Series')
            current_scroll_position = list_widget.verticalScrollBar().value()
            stack = self.navigation_stacks['Series']
            if stack:
                stack[-1]['scroll_position'] = current_scroll_position

            http_method = self.get_http_method()
            params = {
                'username': self.username,
                'password': self.password,
                'action': 'get_series_info',
                'series_id': series_entry["series_id"]
            }

            episodes_url = f"{self.server}/player_api.php"
            response = self.make_request(http_method, episodes_url, params)
            response.raise_for_status()

            series_info = response.json()
            self.series_info = series_info

            seasons = list(series_info.get("episodes", {}).keys())
            self.navigation_stacks['Series'].append({'level': 'series', 'data': {'series_entry': series_entry, 'seasons': seasons}, 'scroll_position': 0})
            self.show_seasons(seasons)

        except Exception as e:
            print(f"Error fetching seasons: {e}")

    def show_seasons(self, seasons, restore_scroll_position=False, scroll_position=0):
        try:
            list_widget = self.channel_list_series
            list_widget.clear()
            if self.navigation_stacks['Series']:
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

            seasons_int = sorted([int(season) for season in seasons])
            items = []
            for season in seasons_int:
                item = QListWidgetItem(f"Season {season}")
                item.setData(Qt.UserRole, str(season))
                item.setIcon(self.series_channel_icon)
                items.append(item)

            for item in items:
                list_widget.addItem(item)

            if restore_scroll_position:
                QTimer.singleShot(0, lambda: list_widget.verticalScrollBar().setValue(scroll_position))
            else:
                list_widget.verticalScrollBar().setValue(0)

            self.current_seasons = [str(season) for season in seasons_int]
        except Exception as e:
            print(f"Error displaying seasons: {e}")

    def fetch_episodes(self, series_entry, season_number):
        try:
            list_widget = self.get_list_widget('Series')
            current_scroll_position = list_widget.verticalScrollBar().value()
            stack = self.navigation_stacks['Series']
            if stack:
                stack[-1]['scroll_position'] = current_scroll_position

            episodes = self.series_info.get("episodes", {}).get(str(season_number), [])
            self.navigation_stacks['Series'].append({'level': 'season', 'data': {'season_number': season_number, 'episodes': episodes}, 'scroll_position': 0})
            self.show_episodes(episodes)

        except Exception as e:
            print(f"Error fetching episodes: {e}")

    def show_episodes(self, episodes, restore_scroll_position=False, scroll_position=0):
        try:
            lw = self.channel_list_series
            lw.clear()

            # ---- “Go Back” -----------------------------------------------------
            if self.navigation_stacks["Series"]:
                gb = QListWidgetItem("Go Back")
                gb.setIcon(self.go_back_icon)
                lw.addItem(gb)

            # ---- context -------------------------------------------------------
            series_entry   = self.navigation_stacks["Series"][-2]["data"]["series_entry"]
            series_title   = series_entry.get("name", "").strip()
            series_poster  = series_entry.get("cover") or series_entry.get("stream_icon") or ""
            series_tmdb_id = series_entry.get("tmdb_id")

            items = []
            for ep in sorted(episodes, key=lambda x: int(x.get("episode_num", 0))):
                

                # === Attach full info dict from API directly! ===
                ep_entry = dict(ep)  # start with a copy of the whole episode
                ep_info = ep.get("info", {})
                ep_entry["info"] = ep_info  # keep the full info dict

                # Compose display name as before
                season_no   = int(ep.get("season", 1))
                episode_no  = int(ep.get("episode_num", 1))
                code        = f"S{season_no:02d}E{episode_no:02d}"
                raw_title   = ep.get("title", "Untitled Episode").strip()
                clean_title = re.sub(re.escape(series_title), "", raw_title, flags=re.I).strip(" -")
                display_txt = f"{series_title} - {code} - {clean_title}"

                ep_entry["name"] = display_txt
                ep_entry["title"] = raw_title
                ep_entry["url"] = (
                    f"{self.server}/series/{self.username}/{self.password}/"
                    f"{ep['id']}.{ep.get('container_extension', 'm3u8')}"
                )
                ep_entry["plot"] = ep_info.get("plot", "")
                ep_entry["stream_icon"] = ep_info.get("movie_image", series_poster)
                ep_entry["tmdb_id"] = series_tmdb_id

                itm = QListWidgetItem(display_txt)
                itm.setData(Qt.UserRole, ep_entry)
                itm.setData(ROLE_STARRABLE, True)
                itm.setIcon(self.series_channel_icon)
                items.append(itm)

            for itm in items:
                lw.addItem(itm)

            # scroll restore
            if restore_scroll_position:
                QTimer.singleShot(0, lambda:
                    lw.verticalScrollBar().setValue(scroll_position))
            else:
                lw.verticalScrollBar().setValue(0)

            self.current_episodes = episodes

        except Exception as err:
            print("Error displaying episodes:", err)







    def play_channel(self, entry):
        try:
            stream_url = entry.get("url")
            if not stream_url:
                self.animate_progress(0, 100, "Stream URL not found")
                return

            if self.external_player_command:
                user_agent_argument = f":http-user-agent=AppleCoreMedia/1.0.0.20L563 (Apple TV; U; CPU OS 16_5 like Mac OS X; en_us)"
                command = [self.external_player_command, stream_url, user_agent_argument]

                if is_linux:
                    # Ensure the external player command is executable
                    if not os.access(self.external_player_command, os.X_OK):
                        self.animate_progress(0, 100, "Selected player is not executable")
                        return

                subprocess.Popen(command)
            else:
                self.animate_progress(0, 100, "No external player configured")
        except Exception as e:
            print(f"Error playing channel: {e}")
            self.animate_progress(0, 100, "Error playing channel")



    def on_tab_change(self, index):
        try:
            tab_name = self.tab_widget.tabText(index)

            if tab_name == "Info":
                if not self.info_tab_initialized:
                    self.result_display.clear()
                    self.result_display.setText("Ready to fetch and display data.")
                    self.info_tab_initialized = True
                return

            if self.login_type in ('xtream', 'local_m3u'):
                stack = self.navigation_stacks.get(tab_name, [])
                list_widget = self.get_list_widget(tab_name)

                if not stack:
                    self.update_category_lists(tab_name)
                    list_widget.verticalScrollBar().setValue(
                        self.top_level_scroll_positions.get(tab_name, 0)
                    )
                else:
                    last_level = stack[-1]
                    level = last_level['level']
                    data = last_level['data']
                    scroll_position = last_level.get('scroll_position', 0)

                    if level == 'channels':
                        self.entries_per_tab[tab_name] = data['entries']
                        self.show_channels(list_widget, tab_name)
                        list_widget.verticalScrollBar().setValue(scroll_position)
                    elif level == 'series_categories':
                        self.show_series_in_category(
                            data['series_list'],
                            restore_scroll_position=True,
                            scroll_position=scroll_position
                        )
                    elif level == 'series':
                        self.show_seasons(
                            data['seasons'],
                            restore_scroll_position=True,
                            scroll_position=scroll_position
                        )
                    elif level == 'season':
                        self.show_episodes(
                            data['episodes'],
                            restore_scroll_position=True,
                            scroll_position=scroll_position
                        )

        except Exception as e:
            print(f"Error while switching tabs: {e}")

    def choose_external_player(self):
        try:
            file_dialog = QFileDialog()
            file_dialog.setFileMode(QFileDialog.ExistingFile)
            file_dialog.setDirectory(QDir.home())  # Start in the user's home directory

            # Apply appropriate filters based on the OS
            if is_windows:
                file_dialog.setNameFilter("Executable files (*.exe *.bat)")
            elif is_mac:
                file_dialog.setNameFilter("Applications (*.app);;All files (*)")
            elif is_linux:
                file_dialog.setNameFilter("Executable files (*)")

            file_dialog.setWindowTitle("Select External Media Player")

            # Open the file dialog
            if file_dialog.exec_():
                file_paths = file_dialog.selectedFiles()
                if file_paths:
                    selected_path = file_paths[0]
                    
                    # Handle macOS .app bundles
                    if is_mac and selected_path.endswith(".app"):
                        # Extract the actual executable path from the .app bundle
                        executable_path = f"{selected_path}/Contents/MacOS/VLC"
                        if os.path.exists(executable_path):
                            self.external_player_command = executable_path
                        else:
                            print("Error: Executable not found inside .app bundle.")
                            return
                    else:
                        # Use the selected file path directly for other cases
                        self.external_player_command = selected_path

                    # Save the selected external player command
                    self.save_external_player_command()
                    print("External Player selected:", self.external_player_command)
            else:
                print("File dialog canceled.")
        except Exception as e:
            print("Error selecting external player:", str(e))




        





    def show_context_menu(self, position):
        sender = self.sender()
        menu = QMenu()
        sort_action = QAction("Sort Alphabetically", self)
        sort_action.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_ArrowUp))
        sort_action.triggered.connect(lambda: self.sort_channel_list(sender))
        menu.addAction(sort_action)
        menu.exec_(sender.viewport().mapToGlobal(position))

    def sort_channel_list(self, list_widget):
        try:
            items = []
            for i in range(list_widget.count()):
                item = list_widget.item(i)
                if item.text() != "Go Back":
                    items.append(item)

            items.sort(key=lambda x: x.text())
            list_widget.clear()

            current_tab = self.tab_widget.tabText(self.tab_widget.currentIndex())
            if self.navigation_stacks[current_tab]:
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

            for item in items:
                list_widget.addItem(item)
        except Exception as e:
            print(f"Error sorting channel list: {e}")

    def search_in_list(self, tab_name, text):
        """
        When the user types in the search bar for the given tab (LIVE, Movies, Series):
          - If text is empty => revert to the original list in the current level
          - If at top-level => search category names
          - If inside a sub-level => search items in that sub-level (channels/movies/episodes)

        Displays "Not Found" if no results.
        """

        list_widget = self.get_list_widget(tab_name)
        if not list_widget:
            return

        # Trim leading/trailing spaces
        text = text.strip()

        # 1) If the search bar is cleared => revert to original view
        if not text:
            if self.navigation_stacks[tab_name]:
                # We are inside a sub-level
                last_level = self.navigation_stacks[tab_name][-1]
                level = last_level['level']
                data = last_level['data']
                scroll_position = last_level.get('scroll_position', 0)

                list_widget.clear()
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

                if level == 'channels':
                    # Re-show the channels for this category
                    self.entries_per_tab[tab_name] = data['entries']
                    self.show_channels(list_widget, tab_name)
                    list_widget.verticalScrollBar().setValue(scroll_position)

                elif level == 'series_categories':
                    self.show_series_in_category(
                        data['series_list'],
                        restore_scroll_position=True,
                        scroll_position=scroll_position
                    )

                elif level == 'series':
                    self.show_seasons(
                        data['seasons'],
                        restore_scroll_position=True,
                        scroll_position=scroll_position
                    )

                elif level == 'season':
                    self.show_episodes(
                        data['episodes'],
                        restore_scroll_position=True,
                        scroll_position=scroll_position
                    )
            else:
                # No stack => top-level: show the categories again
                self.update_category_lists(tab_name)

            return  # Done reverting on empty text

        # 2) The user typed something => do the search
        list_widget.setUpdatesEnabled(False)
        try:
            list_widget.clear()

            # If inside a sub-level, we add "Go Back" at the top
            if self.navigation_stacks[tab_name]:
                go_back_item = QListWidgetItem("Go Back")
                go_back_item.setIcon(self.go_back_icon)
                list_widget.addItem(go_back_item)

            filtered_items = []
            text_lower = text.lower()

            # 2A) If we are at TOP-LEVEL (stack is empty):
            #     => Search category names AND all leaf entries (deep search).
            if not self.navigation_stacks[tab_name]:
                if tab_name == 'LIVE':
                    cat_icon = self.live_channel_icon
                elif tab_name == 'Movies':
                    cat_icon = self.movies_channel_icon
                elif tab_name == 'Series':
                    cat_icon = self.series_channel_icon
                else:
                    cat_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileIcon)

                for group in self.groups.get(tab_name, []):
                    cat_name = group["category_name"]
                    if text_lower in cat_name.lower():
                        item = QListWidgetItem(cat_name)
                        item.setIcon(cat_icon)
                        filtered_items.append(item)

                # Deep search: also look across every leaf entry
                # (one-time API fetch for Xtream, free for local M3U)
                for entry in self._get_all_entries(tab_name):
                    name = entry.get("name", "")
                    if not name or text_lower not in name.lower():
                        continue
                    item = QListWidgetItem(name)
                    item.setData(Qt.UserRole, entry)
                    if tab_name in ('LIVE', 'Movies'):
                        item.setData(ROLE_STARRABLE, True)
                    item.setIcon(cat_icon)
                    filtered_items.append(item)

            # 2B) If we are INSIDE a sub-level (stack is not empty):
            else:
                last_level = self.navigation_stacks[tab_name][-1]
                level = last_level['level']

                if level == 'channels':
                    if tab_name == 'LIVE':
                        row_icon = self.live_channel_icon
                    elif tab_name == 'Movies':
                        row_icon = self.movies_channel_icon
                    else:
                        row_icon = self.style().standardIcon(QtWidgets.QStyle.SP_FileIcon)
                    for entry in self.entries_per_tab[tab_name]:
                        channel_name = entry.get('name', '')
                        if text_lower in channel_name.lower():
                            item = QListWidgetItem(channel_name)
                            item.setData(Qt.UserRole, entry)
                            item.setData(ROLE_STARRABLE, True)
                            item.setIcon(row_icon)
                            filtered_items.append(item)

                elif level == 'series_categories':
                    for series_info in self.current_series_list:
                        series_name = series_info["name"]
                        if text_lower in series_name.lower():
                            item = QListWidgetItem(series_name)
                            item.setData(Qt.UserRole, series_info)
                            item.setIcon(self.series_channel_icon)
                            filtered_items.append(item)

                elif level == 'series':
                    for season in self.current_seasons:
                        label = f"Season {season}"
                        if text_lower in label.lower():
                            item = QListWidgetItem(label)
                            item.setData(Qt.UserRole, season)
                            item.setIcon(self.series_channel_icon)
                            filtered_items.append(item)

                elif level == 'season':
                    for episode in self.current_episodes:
                        ep_title = episode.get('title', '')
                        if text_lower in ep_title.lower():
                            display_text = f"Episode {episode['episode_num']}: {ep_title}"
                            episode_entry = {
                                "season": episode.get('season'),
                                "episode_num": episode['episode_num'],
                                "name": display_text,
                                "url": f"{self.server}/series/{self.username}/{self.password}/{episode['id']}.{episode.get('container_extension', 'm3u8')}",
                                "title": ep_title
                            }
                            item = QListWidgetItem(display_text)
                            item.setData(Qt.UserRole, episode_entry)
                            item.setData(ROLE_STARRABLE, True)
                            item.setIcon(self.series_channel_icon)
                            filtered_items.append(item)

            # 3) After building 'filtered_items', decide what to show
            if not filtered_items:
                not_found_item = QListWidgetItem("Not Found")
                not_found_item.setFlags(not_found_item.flags() & ~Qt.ItemIsSelectable & ~Qt.ItemIsEnabled)
                list_widget.addItem(not_found_item)
            else:
                filtered_items.sort(key=lambda x: x.text().lower())
                for item in filtered_items:
                    list_widget.addItem(item)
        finally:
            list_widget.setUpdatesEnabled(True)


    def get_list_widget(self, tab_name):
        return self.list_widgets.get(tab_name)

    DEFAULT_PLAYER_PATHS = [
        r"C:\Program Files\VideoLAN\VLC\vlc.exe",
        r"C:\Program Files (x86)\VideoLAN\VLC\vlc.exe",
        "/Applications/VLC.app/Contents/MacOS/VLC",
        "/usr/bin/vlc",
        "/usr/local/bin/vlc",
        "/snap/bin/vlc",
    ]

    def load_external_player_command(self):
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'ExternalPlayer' in config:
            self.external_player_command = config['ExternalPlayer'].get('Command', '')
        if not self.external_player_command:
            for path in self.DEFAULT_PLAYER_PATHS:
                if os.path.isfile(path):
                    self.external_player_command = path
                    break

    def save_external_player_command(self):
        config = configparser.ConfigParser()
        config['ExternalPlayer'] = {'Command': self.external_player_command}
        with open('config.ini', 'w') as config_file:
            config.write(config_file)

    # -- Favorites -----------------------------------------------------

    def _rebuild_fav_index(self):
        self._fav_url_index = {}

        def visit(node):
            if node.get("type") == "entry":
                url = (node.get("entry") or {}).get("url")
                if url:
                    self._fav_url_index[url] = node["id"]

        _walk_tree(self._favorites_tree["root"], visit)

    def is_favorited(self, url):
        return bool(url) and url in self._fav_url_index

    def _repaint_main_lists(self):
        for w in (self.channel_list_live, self.channel_list_movies, self.channel_list_series):
            w.viewport().update()

    def toggle_favorite(self, entry, source_tab):
        if not self._active_profile_name:
            self.animate_progress(0, 100, "Select a profile first")
            return
        url = (entry or {}).get("url")
        if not url:
            return
        existing = self._fav_url_index.get(url)
        if existing:
            _remove_node(self._favorites_tree["root"], existing)
        else:
            node = {
                "id": str(uuid.uuid4()),
                "type": "entry",
                "source_tab": source_tab,
                "entry": dict(entry),
            }
            self._favorites_tree["root"]["children"].append(node)
        self._rebuild_fav_index()
        self.save_favorites()
        self.favorites_tab.refresh()
        self._repaint_main_lists()

    def remove_favorite(self, node_id):
        _remove_node(self._favorites_tree["root"], node_id)
        self._rebuild_fav_index()
        self.save_favorites()
        self.favorites_tab.refresh()
        self._repaint_main_lists()

    def add_group(self, parent_id, name):
        found = _find_node(self._favorites_tree["root"], parent_id)
        if found is None or found[1].get("type") != "group":
            return
        group = {
            "id": str(uuid.uuid4()),
            "type": "group",
            "name": name,
            "children": [],
        }
        found[1]["children"].append(group)
        self.save_favorites()
        self.favorites_tab.refresh()

    def rename_node(self, node_id, new_name):
        found = _find_node(self._favorites_tree["root"], node_id)
        if found is None:
            return
        if found[1].get("type") == "group":
            found[1]["name"] = new_name
        else:
            found[1].setdefault("entry", {})["name"] = new_name
        self.save_favorites()
        self.favorites_tab.refresh()

    def delete_node(self, node_id):
        node = _remove_node(self._favorites_tree["root"], node_id)
        if node is None:
            return
        self._rebuild_fav_index()
        self.save_favorites()
        self.favorites_tab.refresh()
        self._repaint_main_lists()

    def move_node(self, node_id, new_parent_id, new_index):
        node = _remove_node(self._favorites_tree["root"], node_id)
        if node is None:
            return
        target = _find_node(self._favorites_tree["root"], new_parent_id)
        if target is None or target[1].get("type") != "group":
            # Fall back: append to root
            self._favorites_tree["root"]["children"].append(node)
        else:
            children = target[1]["children"]
            new_index = max(0, min(new_index, len(children)))
            children.insert(new_index, node)
        self._rebuild_fav_index()
        self.save_favorites()
        self.favorites_tab.refresh()

    def save_favorites(self):
        if not self._active_profile_name:
            return
        try:
            _atomic_write_json(_favorites_file_for(self._active_profile_name), self._favorites_tree)
        except Exception as e:
            print(f"Error saving favorites: {e}")

    def load_favorites_for_profile(self, name):
        path = _favorites_file_for(name)
        if path.exists():
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    self._favorites_tree = json.load(f)
                if not isinstance(self._favorites_tree, dict) or "root" not in self._favorites_tree:
                    raise ValueError("invalid favorites file")
            except Exception as e:
                print(f"Error loading favorites for '{name}': {e}")
                self._favorites_tree = _empty_favorites_tree()
        else:
            self._favorites_tree = _empty_favorites_tree()
        self._rebuild_fav_index()

    def save_last_profile(self, name):
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'LastProfile' not in config:
            config['LastProfile'] = {}
        config['LastProfile']['Name'] = name
        with open('config.ini', 'w') as config_file:
            config.write(config_file)

    def load_last_profile_name(self):
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'LastProfile' in config:
            return config['LastProfile'].get('Name', '').strip() or None
        return None

    def load_profile_by_name(self, name):
        if not name:
            return False
        config = configparser.ConfigParser()
        config.read('credentials.ini')
        if 'Credentials' not in config or name not in config['Credentials']:
            return False
        data = config['Credentials'][name]
        try:
            if data.startswith('manual|'):
                _, server, username, password = data.split('|')
                self.server_entry.setText(server)
                self.username_entry.setText(username)
                self.password_entry.setText(password)
                self.login()
            elif data.startswith('m3u_plus|'):
                _, m3u_url = data.split('|', 1)
                if not self.extract_credentials_from_m3u_plus_url(m3u_url):
                    return False
                self.login()
            elif data.startswith('local_m3u|'):
                _, file_path = data.split('|', 1)
                self.load_local_m3u(file_path)
            else:
                return False
        except Exception as e:
            print(f"Error loading profile '{name}': {e}")
            return False
        self.save_last_profile(name)
        self._active_profile_name = name
        self.load_favorites_for_profile(name)
        self.favorites_tab.refresh()
        for w in (self.channel_list_live, self.channel_list_movies, self.channel_list_series):
            w.viewport().update()
        return True

    def autoload_last_profile(self):
        name = self.load_last_profile_name()
        if not name:
            return
        QTimer.singleShot(0, lambda: self.load_profile_by_name(name))

    def on_epg_checkbox_toggled(self, state):
        enabled = (state == Qt.Checked)
        # Persist preference so the next launch restores it.
        self.save_epg_enabled(enabled)
        if enabled:
            if self.login_type == 'xtream' and self.server and self.username and self.password:
                if not self.epg_data:
                    self.reset_progress_bar()
                    self.animate_progress(0, 50, "Loading EPG data...")
                    self.load_epg_data_async()
                if hasattr(self, '_epg_refresh_timer') and not self._epg_refresh_timer.isActive():
                    self._epg_refresh_timer.start()
            elif self.login_type == 'local_m3u':
                self.animate_progress(0, 100, "EPG not available for local M3U")
        else:
            if hasattr(self, '_epg_refresh_timer'):
                self._epg_refresh_timer.stop()

    def save_epg_enabled(self, enabled):
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'EPG' not in config:
            config['EPG'] = {}
        config['EPG']['Enabled'] = str(bool(enabled))
        with open('config.ini', 'w') as f:
            config.write(f)

    def load_epg_enabled(self):
        config = configparser.ConfigParser()
        config.read('config.ini')
        if 'EPG' in config:
            return config['EPG'].getboolean('Enabled', fallback=False)
        return False

    def _on_epg_refresh_tick(self):
        # Background refresh: only meaningful for xtream profiles with EPG enabled.
        if not (self.epg_checkbox.isChecked()
                and self.login_type == 'xtream'
                and self.server and self.username and self.password):
            return
        # Worker re-uses the cache if it's still inside EPG_CACHE_TTL_SECONDS,
        # otherwise re-downloads. No status spam on success/no-op.
        self.load_epg_data_async()

    def open_profiles(self):
        dialog = ProfilesDialog(self)
        dialog.exec_()

def main():
    app = QApplication(sys.argv)
    app.setStyle('Fusion')
    player = IPTVPlayerApp()
    player.show()
    sys.exit(app.exec_())

if __name__ == "__main__":
    main()
