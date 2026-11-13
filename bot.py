# -*- coding: utf-8 -*-
from html import escape as html_escape
import telebot
import subprocess
import os
import zipfile
import json
import tempfile
import shutil
from telebot import types
import time
import itertools
from datetime import datetime, timedelta
import psutil
import sqlite3
import logging
import signal
import threading
import re
import ast
import sys
import atexit
import requests
import hashlib
import secrets
import hmac
import io
from urllib.parse import urlsplit, urljoin

# --- Extra imports added by the upgrade ---
from logging.handlers import RotatingFileHandler
from flask import Flask, jsonify
from threading import Thread


# --- Configuration (environment variables) ---------------------------------
def _env_int(name, default):
    raw = os.environ.get(name, '').strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError:
        sys.stderr.write(f"Config warning: {name} must be a whole number; using {default}.\n")
        return default


# Secret: the token is NEVER stored in the code. Set it in your host's environment.
BOT_TOKEN = os.environ.get('BOT_TOKEN', '').strip()
if not BOT_TOKEN:
    sys.stderr.write(
        "\nERROR: BOT_TOKEN is not set.\n"
        "Set the BOT_TOKEN environment variable to your bot token from BotFather and start again.\n"
        "Example (Linux/macOS):  export BOT_TOKEN='your-token-here'\n\n")
    sys.exit(1)

OWNER_ID = _env_int('OWNER_ID', 8597878282)
ADMIN_ID = _env_int('ADMIN_ID', 8432635520)
YOUR_USERNAME = os.environ.get('YOUR_USERNAME', 'U_BOTS_u').strip() or 'U_BOTS_u'
UPDATE_CHANNEL = os.environ.get('UPDATE_CHANNEL', 'U_BOT_CHANNEL').strip() or 'U_BOT_CHANNEL'
FREE_USER_LIMIT = _env_int('FREE_USER_LIMIT', 3)
SUBSCRIBED_USER_LIMIT = _env_int('SUBSCRIBED_USER_LIMIT', 10)
ADMIN_LIMIT = float('inf')
OWNER_LIMIT = float('inf')
MAX_UPLOAD_MB = _env_int('MAX_UPLOAD_MB', 20)
MAX_UNZIPPED_MB = _env_int('MAX_UNZIPPED_MB', 200)       # total size allowed after unzipping
MAX_ZIP_FILES = _env_int('MAX_ZIP_FILES', 2000)          # max number of entries in one zip
MAX_SCRIPT_LOG_MB = _env_int('MAX_SCRIPT_LOG_MB', 10)    # a script log above this is trimmed
INSTALL_TIMEOUT = _env_int('INSTALL_TIMEOUT', 300)       # seconds allowed for pip / npm install
LOG_LEVEL = os.environ.get('LOG_LEVEL', 'INFO').strip().upper() or 'INFO'
HEALTH_PORT = _env_int('PORT', 8080)

# Folder setup
BASE_DIR = os.path.abspath(os.environ.get('BOT_DATA_DIR') or os.path.dirname(os.path.abspath(__file__)))
UPLOAD_BOTS_DIR = os.path.join(BASE_DIR, 'upload_bots')
IROTECH_DIR = os.path.join(BASE_DIR, 'inf')
LOG_DIR = os.path.join(IROTECH_DIR, 'logs')
DATABASE_PATH = os.path.join(IROTECH_DIR, 'bot_data.db')

# Create necessary directories
os.makedirs(UPLOAD_BOTS_DIR, exist_ok=True)
os.makedirs(IROTECH_DIR, exist_ok=True)
os.makedirs(LOG_DIR, exist_ok=True)


# --- Logging setup (console + rotating file, tokens are masked) ------------
_TOKEN_PATTERN = re.compile(r'\d{6,}:[A-Za-z0-9_-]{30,}')


def redact_secrets(text):
    """Mask anything that looks like a bot token (also the exact configured one)."""
    text = _TOKEN_PATTERN.sub('<token hidden>', str(text))
    if BOT_TOKEN:
        text = text.replace(BOT_TOKEN, '<token hidden>')
    return text


class _RedactingFormatter(logging.Formatter):
    def format(self, record):
        return redact_secrets(super().format(record))


def _setup_logging():
    root = logging.getLogger()
    if getattr(root, '_demon_configured', False):
        return
    root.setLevel(getattr(logging, LOG_LEVEL, logging.INFO))
    fmt = _RedactingFormatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console = logging.StreamHandler()
    console.setFormatter(fmt)
    root.addHandler(console)
    try:
        file_handler = RotatingFileHandler(os.path.join(LOG_DIR, 'bot.log'), maxBytes=5 * 1024 * 1024,
                                           backupCount=5, encoding='utf-8')
        file_handler.setFormatter(fmt)
        root.addHandler(file_handler)
    except OSError as exc:
        sys.stderr.write(f"Could not open the log file ({exc}); logging to console only.\n")
    # Libraries that are chatty at INFO level.
    logging.getLogger('werkzeug').setLevel(logging.WARNING)
    logging.getLogger('urllib3').setLevel(logging.WARNING)
    root._demon_configured = True


_setup_logging()
logger = logging.getLogger('demon_hosting')

# --- Database lock (defined early so every function can use it) -------------
DB_LOCK = threading.RLock()

# --- Data structures ---
# Several threads touch these dicts (bot handlers, script runners, watchdog), so every
# structural change goes through STATE_LOCK.
STATE_LOCK = threading.RLock()
bot_scripts = {}
MAX_AUTO_RESTARTS = _env_int('MAX_AUTO_RESTARTS', 5)
WATCHDOG_INTERVAL = 8
LAUNCH_WAIT_SECONDS = 40  # how long a Start/Restart press waits for the script to come up before refreshing the panel
RESTART_BACKOFF = (2, 4, 8, 16, 30)
RESTART_STATE = {}
WATCHDOG_STARTED = False
HOST_START_TIME = time.time()
SHUTDOWN_EVENT = threading.Event()
HEALTH_STATE = {'last_poll_start': None, 'poll_restarts': 0, 'last_error': ''}
user_subscriptions = {}
user_files = {}
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
banned_users = set()
user_limits = {}  # Custom limits per user
bot_locked = False

# --- Manual Modules Installation System ---
pending_modules = {}  # {user_id: {module_name: package_name}}
manual_install_requests = {}  # {admin_id: {user_id: {module_name: package_name}}}

# --- Mandatory Channels/Groups ---
mandatory_channels = {}  # {channel_id: {'username': 'channel_username', 'name': 'Channel Name', 'invite_link': '...'}}
pending_channel_add = {}  # admin_id -> validated private channel metadata awaiting invite link

# Store pending ZIP files for approval (kept in memory; entries expire, see PENDING_ZIP_TTL)
pending_zip_files = {}  # {user_id: {file_name: file_content}}
pending_zip_times = {}  # {(user_id, file_name): time stored}
PENDING_ZIP_TTL = 6 * 3600
PENDING_ZIP_MAX_TOTAL = 10  # never keep more than this many archives waiting in memory


def child_env():
    """Environment given to hosted user scripts: same as ours but WITHOUT the hosting bot's secrets."""
    env = dict(os.environ)
    for name in ('BOT_TOKEN', 'TOKEN'):
        env.pop(name, None)
    env.setdefault('PYTHONUNBUFFERED', '1')
    return env


# --- Flask keep-alive + health endpoint ---
app = Flask('demon_hosting_keepalive')


@app.route('/')
def home():
    return "I am 👿 DEMON 👿 HOSTING BOT"


@app.route('/health')
def health():
    try:
        with STATE_LOCK:
            running = sum(1 for info in bot_scripts.values()
                          if info.get('process') and info['process'].poll() is None)
            tracked = len(bot_scripts)
        return jsonify(status='ok', uptime_seconds=int(time.time() - HOST_START_TIME),
                       scripts_running=running, scripts_tracked=tracked,
                       users=len(active_users), polling_restarts=HEALTH_STATE['poll_restarts'])
    except Exception:  # never let the health page crash
        logger.exception("Health endpoint error")
        return jsonify(status='error'), 500


def run_flask():
    try:
        app.run(host='0.0.0.0', port=HEALTH_PORT, debug=False, use_reloader=False, threaded=True)
    except Exception:
        logger.exception("Keep-alive web server stopped (port %s). The bot itself keeps running.", HEALTH_PORT)


def keep_alive():
    t = Thread(target=run_flask, name="keepalive-web", daemon=True)
    t.start()
    logger.info("Keep-alive web server starting on port %s (health page: /health)", HEALTH_PORT)


# --- Bot with safer Telegram calls -------------------------------------------
_apihelper = telebot.apihelper
# Do not wait forever on the network.
_apihelper.CONNECT_TIMEOUT = 15
_apihelper.READ_TIMEOUT = 45
_apihelper.RETRY_ON_ERROR = True


def _retry_after_seconds(exc, default=5):
    try:
        return int(exc.result_json.get('parameters', {}).get('retry_after', default))
    except Exception:
        match = re.search(r'retry after (\d+)', str(exc).lower())
        return int(match.group(1)) if match else default


# --- Reply-keyboard navigation -------------------------------------------------
# Every screen is a native Telegram reply keyboard that changes with each action. Screens are still
# described with NavMenu/NavButton (same add/row calls the old inline buttons used); SafeTeleBot turns a
# NavMenu into a ReplyKeyboardMarkup when it sends it. Pressing a key sends its label as normal text; the
# text handler below finds the action behind that label for this chat and runs the existing screen code.
# Note: Telegram does not allow custom (premium) emoji inside reply-keyboard button text, so the colours
# come from standard coloured emoji. All of the look is in NAV_THEME below.
NAV_TTL = 6 * 3600           # a keyboard state is forgotten after this many seconds
NAV_MAX_STATES = 5000        # most chats kept in memory
NAV_MAX_BUTTONS = 60         # Telegram allows about 100; keep the keyboard readable
NAV_LABEL_MAX = 46
NAV_BACK_STACK_MAX = 12
NAV_CANCEL = '❌ Cancel'
NAV_HOME = '🏠 Home'
NAV_BACK = '⬅️ Back'
NAV_RESERVED = (NAV_CANCEL, NAV_HOME, NAV_BACK)
NAV_OLD_BUTTON_NOTE = "Ye button purana hai, menu se dobara try karo 👇"

# category -> coloured square, tried in this order against the label text (first match wins)
NAV_THEME = [
    ('danger',  '🟥', r'delete|remove|reject|\bban\b|\bstop|kill|wipe|clear'),
    ('warn',    '🟧', r'restart|refresh|retry|(?<!un)lock|import|restore|expire'),
    ('success', '🟩', r'start|\brun|approve|confirm|\byes\b|unban|unlock|\bdone|accept|\badd\b|join'),
    ('admin',   '🟪', r'admin|user management|broadcast|subscription|approval|channel|setting|health|manage'),
    ('info',    '🟦', r'.'),
]
NAV_NUMBERED_PREFIXES = ('file_', 'rv_', 'remove_channel_')

NAV_STATE = {}
NAV_LOCK = threading.RLock()
_NAV_CALL_COUNTER = itertools.count(1)
_NAV_BACK_RX = re.compile(r'^\W*(?:back|🔙|⬅)', re.I | re.U)
_NAV_LEAD_RX = re.compile(r'^([^\w\s(\[]+)\s*(.*)$', re.S)


class NavButton:
    """One key. Either callback_data (an action) or url (the link is sent when it is tapped)."""
    def __init__(self, text, callback_data=None, url=None, **_ignored):
        self.text = str(text)
        self.callback_data = callback_data
        self.url = url


class NavMenu:
    """Same building calls as InlineKeyboardMarkup: add() and row()."""
    def __init__(self, row_width=3, **_ignored):
        self.row_width = max(1, int(row_width or 3))
        self.rows = []

    def add(self, *buttons, row_width=None):
        width = max(1, int(row_width or self.row_width))
        buttons = [b for b in buttons if b is not None]
        for i in range(0, len(buttons), width):
            self.rows.append(list(buttons[i:i + width]))
        return self

    def row(self, *buttons):
        buttons = [b for b in buttons if b is not None]
        if buttons:
            self.rows.append(list(buttons))
        return self


def _nav_split_label(text):
    """('emoji', 'rest') where emoji is the leading symbol of the label if there is one."""
    m = _NAV_LEAD_RX.match(text.strip())
    if m and not m.group(1).isascii():
        return m.group(1), m.group(2).strip() or text.strip()
    return '', text.strip()


def _nav_category(text):
    low = text.lower()
    for name, square, rx in NAV_THEME:
        if re.search(rx, low):
            return square
    return NAV_THEME[-1][1]


def _nav_label(text, action, number=None):
    emoji, rest = _nav_split_label(text)
    if number is not None:
        square = NAV_THEME[-1][1]
        label = f"{square} {number}. {rest if not emoji else emoji + ' ' + rest}"
    else:
        square = _nav_category(rest)
        label = f"{square} {emoji + ' ' if emoji else ''}{rest}"
    if len(label) > NAV_LABEL_MAX:
        label = label[:NAV_LABEL_MAX - 1].rstrip() + '…'
    return label


def _nav_is_main_menu(buttons):
    acts = {b.callback_data for b in buttons}
    return 'upload' in acts and 'check_files' in acts


def _nav_forget_old():
    now = time.time()
    for key in [k for k, v in NAV_STATE.items() if now - v['time'] > NAV_TTL]:
        NAV_STATE.pop(key, None)
    if len(NAV_STATE) > NAV_MAX_STATES:
        for key, _ in sorted(NAV_STATE.items(), key=lambda kv: kv[1]['time'])[:len(NAV_STATE) - NAV_MAX_STATES + 100]:
            NAV_STATE.pop(key, None)


def _nav_get(chat_id):
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id)
        if st and time.time() - st['time'] > NAV_TTL:
            NAV_STATE.pop(chat_id, None)
            return None
        return st


def _nav_blank():
    return {'map': {}, 'rows': [], 'time': time.time(), 'cur': None, 'stack': [], 'seq': 0, 'await': False}


def _nav_rows_to_markup(rows):
    kb = types.ReplyKeyboardMarkup(row_width=2, resize_keyboard=True, one_time_keyboard=False,
                                   input_field_placeholder="Button dabao...")
    for row in rows:
        kb.row(*[types.KeyboardButton(label) for label in row])
    return kb


def _nav_build(chat_id, menu, cancel_only=False):
    """Turn a NavMenu into a ReplyKeyboardMarkup and remember what each label does for this chat."""
    buttons = [b for row in menu.rows for b in row][:NAV_MAX_BUTTONS]
    main = _nav_is_main_menu(buttons)
    used = set(NAV_RESERVED)
    amap, rows = {}, []
    has_custom_back = False
    counter = 0
    for row in menu.rows:
        out = []
        for b in row:
            if b not in buttons:
                continue
            action = b.callback_data if b.callback_data is not None else ('url:' + str(b.url))
            if not main and action == 'back_to_main':
                continue                                  # the Home key does this
            number = None
            if isinstance(action, str) and action.startswith(NAV_NUMBERED_PREFIXES) and not re.match(r'^\W*\d+\.', b.text):
                counter += 1
                number = counter
            label = _nav_label(b.text, action, number)
            if _NAV_BACK_RX.match(b.text):
                has_custom_back = True
            base, n = label, 2
            while label in used:
                label = f"{base} ({n})"
                n += 1
            used.add(label)
            amap[label] = action
            out.append(label)
        if out:
            rows.append(out)
    if not main:
        tail = []
        if not has_custom_back:
            tail.append(NAV_BACK)
            amap[NAV_BACK] = 'nav_back'
        tail.append(NAV_HOME)
        amap[NAV_HOME] = 'back_to_main'
        rows.append(tail)
    with NAV_LOCK:
        _nav_forget_old()
        st = NAV_STATE.get(chat_id) or _nav_blank()
        st.update({'map': amap, 'rows': rows, 'time': time.time(), 'await': False})
        st['seq'] += 1
        NAV_STATE[chat_id] = st
    return _nav_rows_to_markup(rows)


def _nav_cancel_menu(chat_id):
    """Small keyboard shown while the bot waits for typed text or a file."""
    rows = [[NAV_CANCEL, NAV_HOME]]
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id) or _nav_blank()
        st.update({'map': {NAV_CANCEL: 'nav_cancel', NAV_HOME: 'back_to_main'}, 'rows': rows,
                   'time': time.time(), 'await': True})
        st['seq'] += 1
        NAV_STATE[chat_id] = st
    return _nav_rows_to_markup(rows)


def _nav_convert_markup(chat_id, menu):
    if isinstance(menu, NavMenu):
        if chat_id is None:
            return None
        return _nav_build(chat_id, menu)
    return menu


# --- fake "call" so the existing callback code runs unchanged ----------------------
class _NavMessage:
    def __init__(self, chat, user, text):
        self.chat = chat
        self.from_user = user
        self.message_id = -next(_NAV_CALL_COUNTER)     # negative: not a real Telegram message
        self.text = text
        self.reply_to_message = None
        self.content_type = 'text'
        self.date = int(time.time())


class _NavCall:
    def __init__(self, message, action):
        self.id = f"nav:{message.chat.id}:{next(_NAV_CALL_COUNTER)}"
        self.from_user = message.from_user
        self.data = action
        self.message = _NavMessage(message.chat, message.from_user, message.text)
        self.inline_message_id = None
        self.game_short_name = None


def _nav_run(message, action):
    """Run a callback action as if its button had been pressed (used by commands and keys)."""
    handle_callbacks(_NavCall(message, action))


_NAV_VIEW_PREFIXES = (
    'check_files', 'file_', 'user_account', 'my_running', 'user_help', 'admin_dashboard', 'admin_panel',
    'user_management', 'admin_settings', 'hosting_health', 'subscription', 'stats', 'manual_install',
    'adm_approvals', 'rv_v', 'rv_o', 'manage_mandatory_channels', 'all_users', 'list_admins', 'system_info',
    'bot_performance', 'database_backup', 'speed')


def _nav_lookup(st, text):
    if st is None:
        return None
    action = st['map'].get(text)
    if action is None:
        norm = re.sub(r'\d+', '#', text)
        hits = [a for lab, a in st['map'].items() if re.sub(r'\d+', '#', lab) == norm and not re.match(r'^\W*\d+\.', lab)]
        if len(hits) == 1 and '#' in norm:
            action = hits[0]                      # a live label such as "Approvals (3)" that changed number
    return action


def _nav_is_label(message):
    try:
        if message.chat.type != 'private' or not message.text or message.text.startswith('/'):
            return False
        if message.text in NAV_RESERVED:
            return True
        return _nav_lookup(_nav_get(message.chat.id), message.text) is not None
    except Exception:
        return False


def _nav_show_main(message, note=None):
    uid = message.from_user.id
    if note:
        bot.send_message(message.chat.id, note, reply_markup=create_main_menu_inline(uid))
    else:
        _nav_run(message, 'back_to_main')


def _nav_dispatch(message):
    chat_id = message.chat.id
    text = message.text
    with NAV_LOCK:
        st = _nav_get(chat_id)
    if text == NAV_CANCEL:
        with NAV_LOCK:
            if st:
                st['await'] = False
        _nav_clear_input(message)
        _nav_show_main(message, "❎ Cancel ho gaya.")
        return
    if text in (NAV_HOME,) and _nav_lookup(st, text) is None:
        _nav_show_main(message)
        return
    action = _nav_lookup(st, text)
    if text == NAV_BACK and action is None:
        action = 'nav_back'
    if action is None:
        _nav_stale(message)
        return
    if action == 'nav_cancel':
        _nav_clear_input(message)
        _nav_show_main(message, "❎ Cancel ho gaya.")
        return
    if action.startswith('url:'):
        bot.send_message(chat_id, action[4:], disable_web_page_preview=False)
        return
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id)
        if action == 'nav_back':
            action = st['stack'].pop() if st and st['stack'] else 'back_to_main'
            if st:
                st['cur'] = None
        elif st is not None:
            if action == 'back_to_main':
                st['stack'] = []
                st['cur'] = None
            elif action.startswith(_NAV_VIEW_PREFIXES):
                if st['cur'] and st['cur'] != action:
                    st['stack'].append(st['cur'])
                    del st['stack'][:-NAV_BACK_STACK_MAX]
                st['cur'] = action
    _nav_run(message, action)


def _nav_clear_input(message):
    """Forget a half-finished typed input (Cancel pressed)."""
    try:
        bot.clear_step_handler_by_chat_id(message.chat.id)
    except Exception:
        pass
    try:
        _discard_wait(message.from_user.id)
    except Exception:
        pass
    try:
        _gh_cancel_user(message.from_user.id)
    except Exception:
        pass


def _nav_stale(message):
    """Text that matches no key of the current keyboard: put the keyboard back."""
    chat_id = message.chat.id
    st = _nav_get(chat_id)
    note = "Ye option ab available nahi hai. Neeche ke buttons se chuno 👇"
    if st and st.get('rows'):
        bot.send_message(chat_id, note, reply_markup=_nav_rows_to_markup(st['rows']))
    else:
        bot.send_message(chat_id, note, reply_markup=create_main_menu_inline(message.from_user.id))


def _nav_wrap_next_step(callback):
    """A typed answer normally goes to the waiting step; a key label, Cancel or a /command re-routes."""
    def wrapped(message, *a, **kw):
        text = getattr(message, 'text', None)
        chat_id = message.chat.id
        if text:
            st = _nav_get(chat_id)
            if text == NAV_CANCEL or text == NAV_HOME or text.startswith('/') or _nav_lookup(st, text) is not None:
                try:
                    bot.clear_step_handler_by_chat_id(chat_id)
                except Exception:
                    pass
                if text.startswith('/'):
                    bot.process_new_messages([message])
                else:
                    _nav_dispatch(message)
                return
        before = (_nav_get(chat_id) or {}).get('seq', 0)
        result = callback(message, *a, **kw)
        st = _nav_get(chat_id)
        if st is None or st.get('seq', 0) == before or st.get('await'):
            try:
                bot.send_message(chat_id, "🏠 Menu", reply_markup=create_main_menu_inline(message.from_user.id))
            except Exception:
                logger.exception("Could not restore the menu keyboard")
        return result
    return wrapped


def _nav_offer_cancel(message):
    """Called when a typed answer is awaited: make sure a Cancel key is on screen."""
    chat_id = message.chat.id
    st = _nav_get(chat_id)
    if st and any('cancel' in lab.lower() for lab in st['map']) and not st.get('await'):
        return
    bot.send_message(chat_id, "✍️ Apna jawab bhejo. Rukna ho to ❌ Cancel dabao.", reply_markup=_nav_cancel_menu(chat_id))


def _nav_convert_call(args, kwargs, chat_id):
    kwargs = dict(kwargs)
    args = list(args)
    for i, v in enumerate(args):
        if isinstance(v, NavMenu):
            args[i] = _nav_convert_markup(chat_id, v)
    if isinstance(kwargs.get('reply_markup'), NavMenu):
        kwargs['reply_markup'] = _nav_convert_markup(chat_id, kwargs['reply_markup'])
        if kwargs['reply_markup'] is None:
            kwargs.pop('reply_markup')
    rp = kwargs.get('reply_parameters')
    if rp is not None and (getattr(rp, 'message_id', 1) or 1) < 0:
        kwargs.pop('reply_parameters')
    if isinstance(kwargs.get('reply_to_message_id'), int) and kwargs['reply_to_message_id'] < 0:
        kwargs.pop('reply_to_message_id')
    return tuple(args), kwargs


class SafeTeleBot(telebot.TeleBot):
    """TeleBot whose common calls survive the usual harmless Telegram errors:
    rate limits (429) are waited out, 'message is not modified' is ignored, broken
    Markdown/HTML falls back to plain text and stale button presses do not raise."""

    def _guard(self, parent, args, kwargs, kind):
        for attempt in range(4):
            try:
                return parent(*args, **kwargs)
            except telebot.apihelper.ApiTelegramException as exc:
                desc = str(exc).lower()
                code = getattr(exc, 'error_code', None)
                if code == 429 or 'too many requests' in desc:
                    wait = min(_retry_after_seconds(exc) + 1, 60)
                    logger.warning("Telegram rate limit on %s; waiting %ss (try %s)", kind, wait, attempt + 1)
                    time.sleep(wait)
                    continue
                if 'message is not modified' in desc:
                    return None
                if kind == 'answer_callback_query' and ('query is too old' in desc or 'query id is invalid' in desc):
                    return None
                if kind == 'delete_message' and ('message to delete not found' in desc or "can't be deleted" in desc):
                    return None
                if "can't parse entities" in desc and kwargs.get('parse_mode'):
                    logger.warning("Formatting rejected by Telegram on %s; resending as plain text", kind)
                    kwargs = dict(kwargs)
                    kwargs['parse_mode'] = None
                    continue
                if 'message is too long' in desc and kind in ('send_message', 'edit_message_text'):
                    args, kwargs = _truncate_text_args(args, kwargs)
                    continue
                raise
            except requests.exceptions.RequestException as exc:
                if attempt >= 2:
                    raise
                logger.warning("Network problem on %s (%s); retrying", kind, type(exc).__name__)
                time.sleep(2 * (attempt + 1))
        return None

    def _nav_args(self, args, kwargs, chat_pos=0):
        chat_id = kwargs.get('chat_id', args[chat_pos] if len(args) > chat_pos else None)
        return _nav_convert_call(args, kwargs, chat_id)

    def send_message(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_message, args, kwargs, 'send_message')

    def edit_message_text(self, *args, **kwargs):
        text = kwargs.get('text', args[0] if args else '')
        chat_id = kwargs.get('chat_id', args[1] if len(args) > 1 else None)
        message_id = kwargs.get('message_id', args[2] if len(args) > 2 else None)
        menu = kwargs.get('reply_markup')
        virtual = isinstance(message_id, int) and message_id < 0
        if isinstance(menu, NavMenu) or (virtual and chat_id is not None):
            # A reply keyboard cannot be attached by editing, so the screen is sent as a new message
            # and the old one is removed when it is a real message.
            send_kwargs = {k: kwargs[k] for k in ('parse_mode', 'entities', 'disable_web_page_preview') if k in kwargs}
            if menu is not None:
                send_kwargs['reply_markup'] = menu
            sent = self.send_message(chat_id, text, **send_kwargs)
            if isinstance(menu, NavMenu) and isinstance(message_id, int) and message_id > 0:
                try:
                    self.delete_message(chat_id, message_id)
                except Exception:
                    pass
            return sent
        return self._guard(super().edit_message_text, args, kwargs, 'edit_message_text')

    def edit_message_reply_markup(self, *args, **kwargs):
        chat_id = kwargs.get('chat_id', args[0] if args else None)
        menu = kwargs.get('reply_markup')
        if isinstance(menu, NavMenu):
            if chat_id is None:
                return None
            return self.send_message(chat_id, "🔄 Menu update ho gaya.", reply_markup=menu)
        message_id = kwargs.get('message_id', args[1] if len(args) > 1 else None)
        if isinstance(message_id, int) and message_id < 0:
            return None
        try:
            return self._guard(super().edit_message_reply_markup, args, kwargs, 'edit_message_reply_markup')
        except Exception as exc:
            logger.warning("edit_message_reply_markup skipped: %s", redact_secrets(exc))
            return None

    def answer_callback_query(self, *args, **kwargs):
        qid = kwargs.get('callback_query_id', args[0] if args else '')
        if isinstance(qid, str) and qid.startswith('nav:'):
            text = kwargs.get('text', args[1] if len(args) > 1 else None)
            if text:
                try:
                    self.send_message(int(qid.split(':')[1]), text)
                except Exception:
                    logger.warning("Could not send the notice for a key press")
            return True
        return self._guard(super().answer_callback_query, args, kwargs, 'answer_callback_query')

    def delete_message(self, *args, **kwargs):
        message_id = kwargs.get('message_id', args[1] if len(args) > 1 else None)
        if isinstance(message_id, int) and message_id < 0:
            return True
        return self._guard(super().delete_message, args, kwargs, 'delete_message')

    def register_next_step_handler(self, message, callback, *args, **kwargs):
        try:
            _nav_offer_cancel(message)
        except Exception:
            logger.exception("Could not show the Cancel key")
        return super().register_next_step_handler(message, _nav_wrap_next_step(callback), *args, **kwargs)

    def send_document(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_document, args, kwargs, 'send_document')

    def send_photo(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_photo, args, kwargs, 'send_photo')

    def send_video(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_video, args, kwargs, 'send_video')

    def send_audio(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_audio, args, kwargs, 'send_audio')

    def send_voice(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_voice, args, kwargs, 'send_voice')

    def send_sticker(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_sticker, args, kwargs, 'send_sticker')


def _truncate_text_args(args, kwargs):
    """Cut an over-long text to Telegram's 4096-character limit."""
    notice = "\n...(shortened)"
    kwargs = dict(kwargs)
    if 'text' in kwargs:
        kwargs['text'] = str(kwargs['text'])[:4096 - len(notice)] + notice
        return args, kwargs
    args = list(args)
    # send_message(chat_id, text) / edit_message_text(text, chat_id, message_id)
    for idx, value in enumerate(args):
        if isinstance(value, str) and len(value) > 4000:
            args[idx] = value[:4096 - len(notice)] + notice
            break
    return tuple(args), kwargs


def safe_text(text, limit=4000):
    """Shorten text for a single Telegram message."""
    text = str(text)
    if len(text) <= limit:
        return text
    return text[:limit - 20] + "\n...(shortened)"


class GlobalErrorHandler(telebot.ExceptionHandler):
    """Last line of defence: an error inside any handler is logged, never kills polling."""

    def handle(self, exception):
        HEALTH_STATE['last_error'] = f"{type(exception).__name__}: {redact_secrets(exception)}"[:300]
        logger.error("Unhandled error in a bot handler: %s", redact_secrets(exception),
                     exc_info=(type(exception), exception, exception.__traceback__))
        return True


# Initialize bot
bot = SafeTeleBot(BOT_TOKEN, threaded=True, num_threads=20, skip_pending=True,
                  exception_handler=GlobalErrorHandler())


# --- Command Button Layouts ---
COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["📞 Contact Owner"],
    ["📦 Manual Install", "🆘 Help"]
]

ADMIN_COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["💳 Subscriptions", "📢 Broadcast"],
    ["🔒 Lock Bot", "🟢 Running All Code"],
    ["👑 Admin Panel", "📞 Contact Owner"],
    ["📢 Channel Add", "🛠️ Manual Install"],
    ["👥 User Management", "⚙️ Settings"],
    ["🩺 Hosting Health"]
]

# --- Database Setup ---
def db_connect():
    """Open a SQLite connection that waits for locks instead of failing right away.
    Callers hold DB_LOCK around read/write work, so connections are never shared between threads."""
    conn = sqlite3.connect(DATABASE_PATH, timeout=30, check_same_thread=False)
    conn.execute("PRAGMA busy_timeout=30000")
    return conn


def init_db():
    """Initialize the database with required tables"""
    logger.info(f"Initializing database at: {DATABASE_PATH}")
    try:
        conn = db_connect()
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA busy_timeout=30000")
        c = conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS subscriptions
                     (user_id INTEGER PRIMARY KEY, expiry TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_files
                     (user_id INTEGER, file_name TEXT, file_type TEXT,
                      PRIMARY KEY (user_id, file_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS active_users
                     (user_id INTEGER PRIMARY KEY, join_date TEXT, last_seen TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS admins
                     (user_id INTEGER PRIMARY KEY, added_by INTEGER, added_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS banned_users
                     (user_id INTEGER PRIMARY KEY, reason TEXT, banned_by INTEGER, ban_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_limits
                     (user_id INTEGER PRIMARY KEY, file_limit INTEGER, set_by INTEGER, set_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS mandatory_channels
                     (channel_id TEXT PRIMARY KEY, 
                      channel_username TEXT,
                      channel_name TEXT,
                      invite_link TEXT DEFAULT '',
                      added_by INTEGER,
                      added_date TEXT)''')
        # Migrate databases created by older releases without invite_link.
        c.execute('PRAGMA table_info(mandatory_channels)')
        channel_columns = {row[1] for row in c.fetchall()}
        if 'invite_link' not in channel_columns:
            c.execute("ALTER TABLE mandatory_channels ADD COLUMN invite_link TEXT DEFAULT ''")

        c.execute('''CREATE TABLE IF NOT EXISTS install_logs
                     (id INTEGER PRIMARY KEY AUTOINCREMENT,
                      user_id INTEGER,
                      module_name TEXT,
                      package_name TEXT,
                      status TEXT,
                      log TEXT,
                      install_date TEXT)''')
        
        # Latest upload-scan verdict per hosted file (threat level, score, reasons as JSON).
        c.execute('''CREATE TABLE IF NOT EXISTS file_scans
                     (user_id INTEGER, file_name TEXT, level TEXT, score INTEGER,
                      reasons TEXT, sha256 TEXT, scanned_at TEXT, decision TEXT DEFAULT '',
                      PRIMARY KEY (user_id, file_name))''')
        # Uploads waiting for an admin decision (survive a restart).
        c.execute('''CREATE TABLE IF NOT EXISTS pending_reviews
                     (token TEXT PRIMARY KEY, user_id INTEGER, file_name TEXT, file_type TEXT,
                      level TEXT, score INTEGER, reasons TEXT, sha256 TEXT, created REAL,
                      chat_id INTEGER, msg_id INTEGER, uploader TEXT, admin_msgs TEXT, kind TEXT)''')
        c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                  (OWNER_ID, OWNER_ID, datetime.now().isoformat()))
        if ADMIN_ID != OWNER_ID:
            c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                      (ADMIN_ID, OWNER_ID, datetime.now().isoformat()))
        conn.commit()
        conn.close()
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.critical(f"❌ Database initialization error: {e}", exc_info=True)
        raise

def load_data():
    """Load data from database into memory"""
    logger.info("Loading data from database...")
    conn = None
    try:
        conn = db_connect()
        c = conn.cursor()

        # Load subscriptions
        c.execute('SELECT user_id, expiry FROM subscriptions')
        for user_id, expiry in c.fetchall():
            try:
                user_subscriptions[user_id] = {'expiry': datetime.fromisoformat(expiry)}
            except ValueError:
                logger.warning(f"⚠️ Invalid expiry date format for user {user_id}: {expiry}. Skipping.")

        # Load user files
        c.execute('SELECT user_id, file_name, file_type FROM user_files')
        for user_id, file_name, file_type in c.fetchall():
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((file_name, file_type))

        # Load active users
        c.execute('SELECT user_id FROM active_users')
        active_users.update(user_id for (user_id,) in c.fetchall())

        # Load admins
        c.execute('SELECT user_id FROM admins')
        admin_ids.update(user_id for (user_id,) in c.fetchall())

        # Load banned users
        c.execute('SELECT user_id FROM banned_users')
        banned_users.update(user_id for (user_id,) in c.fetchall())

        # Load user limits
        c.execute('SELECT user_id, file_limit FROM user_limits')
        for user_id, file_limit in c.fetchall():
            user_limits[user_id] = file_limit

        # Load mandatory channels
        c.execute('SELECT channel_id, channel_username, channel_name, invite_link FROM mandatory_channels')
        for channel_id, channel_username, channel_name, invite_link in c.fetchall():
            mandatory_channels[channel_id] = {
                'username': channel_username,
                'name': channel_name,
                'invite_link': invite_link or ''
            }

        logger.info(f"Data loaded: {len(active_users)} users, {len(user_subscriptions)} subscriptions, {len(admin_ids)} admins, {len(banned_users)} banned users, {len(user_limits)} custom limits, {len(mandatory_channels)} mandatory channels.")
    except Exception as e:
        logger.error(f"❌ Error loading data: {e}", exc_info=True)
    finally:
        if conn is not None:
            conn.close()

# Initialize DB and Load Data at startup
try:
    init_db()
except Exception:
    sys.stderr.write("ERROR: the database could not be created. Check that the folder is writable. See the log for details.\n")
    sys.exit(1)
load_data()

# =============================================================================
# Upload scanner: simple, static, honest.
# =============================================================================
# This only READS the code (it never runs it). It is a quick screening step, NOT a sandbox and
# NOT an antivirus: a determined person can still hide things from it.
#   LOW    -> starts automatically
#   MEDIUM -> held until an admin approves or rejects it
#   HIGH   -> rejected (clearly harmful: miner, reverse shell, wiping disks, stealing server
#             secrets, touching this hosting platform's own data, decoding hidden code and running it)
# Ordinary bot code (requests, sockets, subprocess, os.system, files, regex, env vars) is LOW.
# If the scanner itself fails or cannot read a file, the result is LOW and a line is logged.

SCANNER_VERSION = 3
THREAT_LOW, THREAT_MEDIUM, THREAT_HIGH = 'low', 'medium', 'high'
THREAT_RANK = {THREAT_LOW: 0, THREAT_MEDIUM: 1, THREAT_HIGH: 2}
THREAT_BADGE = {THREAT_LOW: '🟢', THREAT_MEDIUM: '🟡', THREAT_HIGH: '🔴'}
THREAT_NAME = {THREAT_LOW: 'LOW', THREAT_MEDIUM: 'MEDIUM', THREAT_HIGH: 'HIGH'}
SCAN_MAX_SOURCE_BYTES = 4 * 1024 * 1024
SCAN_MAX_ZIP_READ_BYTES = 40 * 1024 * 1024
_RX = re.compile

# (level, text shown to people, regex run on text that is NOT a comment)
_SCAN_TEXT_RULES = [
    (THREAT_HIGH, 'Looks like a crypto miner',
     _RX(r'(?i)xmrig|minerd\b|cpuminer|ethminer|nicehash|stratum\+(?:tcp|ssl)|cryptonight|supportxmr|nanopool|hashvault|coinhive')),
    (THREAT_HIGH, 'Opens a reverse shell',
     _RX(r'(?i)/dev/tcp/|\bbash\s+-i\s*>&|\bnc(?:at)?\s+(?:-\w*e\b|[^\n]{0,40}\s-e\s)|\bsocat\b[^\n]*exec:|\bmkfifo\b[^\n]*\bnc\b|pty\.spawn')),
    (THREAT_HIGH, 'Tries to wipe or damage the server',
     _RX(r'(?i)\brm\s+-[a-z]*r[a-z]*\s+(?:--no-preserve-root\s+)?(?:/|~|\$HOME)(?:\s|\*|$|["\'])|\bmkfs(?:\.\w+)?\b|\bdd\s+if=\S+\s+of=/dev/|:\(\)\s*\{\s*:\s*\|\s*:\s*&|>\s*/dev/(?:sd|nvme|vd)|\bchmod\s+-R\s+777\s+/(?:\s|$)')),
    (THREAT_HIGH, 'Reads server secrets (passwords, keys, cloud credentials)',
     _RX(r'(?i)/etc/(?:shadow|gshadow|sudoers)|\.ssh/|\bid_(?:rsa|ed25519|ecdsa)\b|\.aws/credentials|\.git-credentials|\.docker/config|\.kube/config|/proc/(?:self|\d+)/(?:environ|mem)|169\.254\.169\.254|metadata\.google\.internal|docker\.sock')),
    (THREAT_HIGH, 'Downloads a script and pipes it into a shell',
     _RX(r'(?i)\b(?:curl|wget)\b[^|;\n]*\|\s*(?:sudo\s+)?(?:ba|z|da)?sh\b')),
    (THREAT_HIGH, "Touches this hosting platform's own data or other users' folders",
     _RX(r'(?i)bot_data\.db|\bupload_bots\b|demon_hosting')),
    (THREAT_MEDIUM, 'Uses admin / system-level commands (sudo, crontab, service, firewall, kill-all)',
     _RX(r'(?i)(?<![\w.])sudo\s|\bcrontab\s+-|/etc/cron|systemctl\s+(?:enable|start|stop|daemon-reload)|/etc/systemd|\bpkill\b|\bkillall\b|\biptables\b|\bufw\s|\buseradd\b|\badduser\b|\bpasswd\s|(?<![\w.])(?:shutdown|poweroff|reboot)\s+(?:-|now)|authorized_keys|ld\.so\.preload')),
    (THREAT_MEDIUM, 'Sets itself up to survive restarts (shell profile / startup scripts)',
     _RX(r'(?i)\.bashrc\b|\.bash_profile\b|\.zshrc\b|/etc/rc\.local|/etc/init\.d')),
    (THREAT_MEDIUM, 'Sends data to tunnel / log-catcher services',
     _RX(r'(?i)\.onion\b|ngrok\.|serveo\.net|localtunnel|loca\.lt|trycloudflare|webhook\.site|requestbin|pipedream\.net|interact\.sh|grabify|iplogger|discord(?:app)?\.com/api/webhooks')),
]
_SYSPATH_TEXT = 'Touches system folders (/etc, /usr, /bin, /root)'
_SYSPATH_RX = _RX(r'(?<![\w.~/-])/(?:etc|usr|bin|sbin|root|boot)/[\w./*-]+')
_SYSPATH_OK = _RX(r'^/(?:etc/(?:os-release|hostname|localtime|timezone|resolv\.conf|ssl/|ca-certificates|mime\.types|lsb-release)'
                  r'|usr/(?:share/|lib/python|local/bin/(?:env|python[\d.]*|node|npm|pip[\d.]*)$|bin/(?:env|python[\d.]*|node|npm|pip[\d.]*|which)$)'
                  r'|bin/(?:sh|bash|env|ls|cat|echo|python[\d.]*)$)')


def _system_path_hit(text):
    for match in _SYSPATH_RX.finditer(text):
        if not _SYSPATH_OK.match(match.group(0)):
            return match
    return None


_JS_HIGH_RX = _RX(r'(?i)(?:\beval\s*\(|new\s+Function\s*\()[^;]{0,200}?(?:atob\s*\(|Buffer\.from\([^)]*[\'"]base64[\'"]|\bfetch\s*\(|https?\.get\s*\(|axios\.get\s*\()')
_JS_HIGH_TEXT = 'Decodes or downloads hidden code and runs it'
_DECODE_NAMES = ('b64decode', 'b32decode', 'b16decode', 'a85decode', 'b85decode', 'decompress', 'fromhex', 'unhexlify', 'marshal.loads',
                 'codecs.decode', 'requests.get', 'requests.post', 'urlopen', 'httpx.get', 'urllib.request.urlopen')
_COMMAND_CALL_ENDS = ('os.system', 'os.popen', 'subprocess.run', 'subprocess.call', 'subprocess.check_call',
                      'subprocess.check_output', 'subprocess.Popen', 'subprocess.getoutput', 'subprocess.getstatusoutput',
                      'Popen', 'getoutput')
_PY_COMMAND_RULES = [r for r in _SCAN_TEXT_RULES if r[0] == THREAT_MEDIUM and r[1].startswith('Uses admin')]


def _scan_finding(level, text, line=None):
    return {'id': text[:24], 'text': text, 'points': 100 if level == THREAT_HIGH else 40, 'floor': level,
            'lines': [line] if line else [], 'details': []}


def _line_of(text, pos):
    return text.count('\n', 0, pos) + 1


def _dotted(node):
    parts = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
    return '.'.join(reversed(parts))


def _py_strings_and_calls(source):
    """Returns (string constants as (text, line), findings from call analysis) or None when the code does not parse."""
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        return None
    docstrings = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            body = getattr(node, 'body', None)
            if body and isinstance(body[0], ast.Expr) and isinstance(getattr(body[0], 'value', None), ast.Constant) \
                    and isinstance(body[0].value.value, str):
                docstrings.add(id(body[0].value))
    strings, found = [], []
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str) and id(node) not in docstrings:
            strings.append((node.value, getattr(node, 'lineno', 1)))
        elif isinstance(node, ast.Call):
            name = _dotted(node.func)
            if name in ('exec', 'eval') or name.endswith(('.exec', '.eval')):
                inner = [_dotted(sub.func) for sub in ast.walk(node) if isinstance(sub, ast.Call) and sub is not node]
                if any(item.endswith(_DECODE_NAMES) for item in inner):
                    found.append(_scan_finding(THREAT_HIGH, 'Decodes or downloads hidden code and runs it', node.lineno))
            elif name.endswith(_COMMAND_CALL_ENDS):
                for sub in ast.walk(node):
                    if isinstance(sub, ast.Constant) and isinstance(sub.value, str):
                        for level, text, rx in _PY_COMMAND_RULES:
                            if rx.search(sub.value):
                                found.append(_scan_finding(level, text, node.lineno))
            elif name in ('shutil.rmtree', 'rmtree') and node.args and isinstance(node.args[0], ast.Constant) \
                    and node.args[0].value in ('/', '~', '/home', '/root', '/etc', '/usr', '/var'):
                found.append(_scan_finding(THREAT_HIGH, 'Tries to wipe or damage the server', node.lineno))
    return strings, found


def _strip_comments(text, file_type):
    if file_type == 'js':
        text = re.sub(r'/\*.*?\*/', lambda m: '\n' * m.group(0).count('\n'), text, flags=re.S)
        return re.sub(r'(?m)(^|[^:\'"\\])//[^\n]*', r'\1', text)
    return re.sub(r'(?m)^\s*#[^\n]*', '', text)


def _host_path_findings(text):
    """Mentioning the hosting folder's real path is also a platform-data access."""
    base = str(BASE_DIR or '')
    if len(base) > 8 and base in text:
        return [_scan_finding(THREAT_HIGH, "Touches this hosting platform's own data or other users' folders")]
    return []


def scan_source(content, file_type, filename=''):
    """Scan one source file's text. file_type is 'py' or 'js'. Returns the result dict."""
    findings = []
    try:
        if file_type == 'py':
            parsed = _py_strings_and_calls(content)
            if parsed is None:
                logger.info('Scan: %s does not parse as Python, checking it as plain text only', filename)
                chunks = [(_strip_comments(content, 'py'), 1)]
            else:
                strings, calls = parsed
                findings.extend(calls)
                chunks = strings
            for chunk, line in chunks:
                for level, text, rx in _SCAN_TEXT_RULES:
                    if level == THREAT_HIGH and rx.search(chunk):
                        findings.append(_scan_finding(level, text, line if parsed is not None else None))
                    elif level == THREAT_MEDIUM and not text.startswith('Uses admin') and rx.search(chunk):
                        findings.append(_scan_finding(level, text, line if parsed is not None else None))
                if _system_path_hit(chunk):
                    findings.append(_scan_finding(THREAT_MEDIUM, _SYSPATH_TEXT, line if parsed is not None else None))
            if parsed is None:
                for level, text, rx in _SCAN_TEXT_RULES:
                    if text.startswith('Uses admin') and rx.search(chunks[0][0]):
                        findings.append(_scan_finding(level, text))
        else:
            clean = _strip_comments(content, 'js')
            for level, text, rx in _SCAN_TEXT_RULES:
                match = rx.search(clean)
                if match:
                    findings.append(_scan_finding(level, text, _line_of(clean, match.start())))
            hit = _system_path_hit(clean)
            if hit:
                findings.append(_scan_finding(THREAT_MEDIUM, _SYSPATH_TEXT, _line_of(clean, hit.start())))
            match = _JS_HIGH_RX.search(clean)
            if match:
                findings.append(_scan_finding(THREAT_HIGH, _JS_HIGH_TEXT, _line_of(clean, match.start())))
        findings.extend(_host_path_findings(content))
    except Exception as exc:   # a scanner failure is LOW (by design) but is always logged
        logger.warning('Scanner could not analyse %s (treated as LOW): %s', filename, exc)
        findings = []
    return _build_result(findings, filename, file_type, len(content))


def _build_result(findings, filename, file_type, size):
    seen, reasons = set(), []
    for item in sorted(findings, key=lambda f: (-THREAT_RANK[f['floor']], f['lines'] or [0])):
        if item['text'] in seen:
            continue
        seen.add(item['text'])
        reasons.append(item)
    level = THREAT_LOW
    for item in reasons:
        if THREAT_RANK[item['floor']] > THREAT_RANK[level]:
            level = item['floor']
    score = min(100, sum(item['points'] for item in reasons))
    return {'level': level, 'score': score, 'reasons': reasons, 'file': filename, 'type': file_type, 'size': size,
            'scanner': SCANNER_VERSION}


def scan_bytes(data, file_type, filename=''):
    """Scan raw uploaded bytes. Unreadable / binary / oversized content is LOW (logged), as agreed."""
    digest = hashlib.sha256(data).hexdigest()
    try:
        if len(data) > SCAN_MAX_SOURCE_BYTES:
            logger.info('Scan: %s is too big to inspect (%s KB), treated as LOW', filename, len(data) // 1024)
            result = _build_result([], filename, file_type, len(data))
        elif b'\x00' in data[:8192]:
            logger.info('Scan: %s looks binary, treated as LOW', filename)
            result = _build_result([], filename, file_type, len(data))
        else:
            result = scan_source(data.decode('utf-8', 'ignore'), file_type, filename)
    except Exception as exc:
        logger.warning('Scan error on %s (treated as LOW): %s', filename, exc)
        result = _build_result([], filename, file_type, len(data))
    result.update({'file': filename, 'type': file_type, 'size': len(data), 'scanner': SCANNER_VERSION, 'sha256': digest})
    return result


_COMPILED_EXTS = ('.so', '.pyd', '.dll', '.dylib', '.exe', '.node', '.elf', '.msi', '.scr')
_VENDOR_DIRS = ('node_modules/', 'site-packages/', 'venv/', '.venv/', 'env/lib/', '__pycache__/')


def scan_zip_file(zip_path):
    """Scan the source files inside a ZIP without extracting it. Returns one combined result."""
    findings, scanned = [], 0
    read_total = 0
    try:
        with zipfile.ZipFile(zip_path, 'r') as archive:
            for item in archive.infolist():
                if item.is_dir():
                    continue
                name = item.filename.replace('\\', '/')
                low = name.lower()
                if any(('/' + low).find('/' + vendor) != -1 for vendor in _VENDOR_DIRS):
                    continue
                if low.endswith(_COMPILED_EXTS):
                    findings.append(_scan_finding(THREAT_MEDIUM, f'Contains a compiled program ({os.path.basename(low)})'))
                    continue
                ext = os.path.splitext(low)[1]
                if ext not in ('.py', '.js', '.sh', '.bash'):
                    continue
                if item.file_size > SCAN_MAX_SOURCE_BYTES:
                    logger.info('Scan: %s in archive too big, skipped', name)
                    continue
                read_total += item.file_size
                if read_total > SCAN_MAX_ZIP_READ_BYTES:
                    logger.info('Scan: archive source is very large, rest skipped')
                    break
                data = archive.read(item)
                kind = 'js' if ext == '.js' else 'py'
                if ext in ('.sh', '.bash'):
                    sub = scan_source(_strip_comments(data.decode('utf-8', 'ignore'), 'js').replace('//', ' '), 'js', name)
                else:
                    sub = scan_bytes(data, kind, name)
                scanned += 1
                for reason in sub['reasons']:
                    tagged = dict(reason)
                    tagged['text'] = f"{reason['text']} [in {name}]"
                    findings.append(tagged)
    except Exception as exc:
        logger.warning('Could not read archive for scanning (treated as LOW): %s', exc)
        findings = []
    result = _build_result(findings, os.path.basename(zip_path), 'zip', 0)
    result['files_scanned'] = scanned
    return result


def scan_headline(result):
    level = result.get('level', THREAT_LOW)
    return f"{THREAT_BADGE.get(level, '⚪')} {THREAT_NAME.get(level, level)}"


def scan_summary_text(result, max_reasons=3):
    """Short plain bullet lines for people (uploader and admins)."""
    lines = []
    for reason in result.get('reasons', [])[:max_reasons]:
        where = f" (line {reason['lines'][0]})" if reason.get('lines') else ''
        lines.append(f"• {reason['text']}{where}")
    return '\n'.join(lines)


# --- Upload review queue, scan records and launch gate ---------------------
# Everything in this section is static: it stores verdicts, moves bytes around and shows buttons.
# Nothing here ever executes an uploaded file. Execution only happens through run_script /
# run_js_script, and only after a LOW verdict or an explicit admin approval.
QUARANTINE_DIR = os.path.join(IROTECH_DIR, 'quarantine')   # held MEDIUM uploads, named <token>.bin, never executed
REVIEW_LOCK = threading.RLock()     # never take DB_LOCK while holding this lock
PENDING_REVIEWS = {}                # token -> entry dict (see _submit_for_review)
REVIEW_TTL = 3 * 24 * 3600          # an unanswered review expires after 3 days
REVIEW_MAX_TOTAL = 30               # most uploads that may wait for review at the same time
REVIEW_MAX_PER_USER = 3             # most uploads one user may have waiting
_TOKEN_RE = re.compile(r'[0-9a-f]{8}')


class _ChatRef:
    def __init__(self, ident):
        self.id = ident


class _ReplyTarget:
    """Stand-in for a Telegram message when feedback must go to someone else (for example the uploader
    after an admin approved their file). Only .chat.id, .message_id and .from_user.id are used."""
    def __init__(self, chat_id, message_id, user_id):
        self.chat = _ChatRef(chat_id)
        self.message_id = message_id
        self.from_user = _ChatRef(user_id)


def _quarantine_path(token):
    if not _TOKEN_RE.fullmatch(token or ''):
        raise ValueError('bad review token')
    return os.path.join(QUARANTINE_DIR, token + '.bin')


def _remove_quietly(path):
    try:
        if path and os.path.isfile(path):
            os.remove(path)
    except OSError as exc:
        logger.warning('Could not remove %s: %s', path, exc)


def _file_sha256(path):
    """SHA-256 of a file on disk (streamed), or None when it cannot be read."""
    digest = hashlib.sha256()
    try:
        with open(path, 'rb') as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b''):
                digest.update(block)
    except OSError:
        return None
    return digest.hexdigest()


def _safe_send(chat_id, text, **kwargs):
    try:
        return bot.send_message(chat_id, text, parse_mode='HTML', **kwargs)
    except Exception as exc:
        logger.warning('Could not message %s: %s', chat_id, type(exc).__name__)
        return None


# ---- stored verdicts -------------------------------------------------------------------
def save_scan_record(user_id, file_name, result, decision=''):
    """Remember the latest verdict for a hosted file. decision: auto / approved / admin / rescan / rejected / ''."""
    reasons = json.dumps(result.get('reasons', [])[:20])
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('INSERT OR REPLACE INTO file_scans (user_id, file_name, level, score, reasons, sha256, scanned_at, decision) '
                         'VALUES (?, ?, ?, ?, ?, ?, ?, ?)',
                         (user_id, file_name, result.get('level', THREAT_MEDIUM), int(result.get('score', 0)), reasons,
                          result.get('sha256', ''), datetime.now().isoformat(timespec='seconds'), decision))
            conn.commit()
        except sqlite3.Error as exc:
            logger.error('Could not save scan record for %s/%s: %s', user_id, file_name, exc)
        finally:
            conn.close()


def set_scan_decision(user_id, file_name, decision):
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('UPDATE file_scans SET decision = ? WHERE user_id = ? AND file_name = ?', (decision, user_id, file_name))
            conn.commit()
        except sqlite3.Error as exc:
            logger.error('Could not update scan decision: %s', exc)
        finally:
            conn.close()


def get_scan_record(user_id, file_name):
    with DB_LOCK:
        conn = db_connect()
        try:
            row = conn.execute('SELECT level, score, reasons, sha256, scanned_at, decision FROM file_scans '
                               'WHERE user_id = ? AND file_name = ?', (user_id, file_name)).fetchone()
        except sqlite3.Error:
            row = None
        finally:
            conn.close()
    if not row:
        return None
    try:
        reasons = json.loads(row[2] or '[]')
    except ValueError:
        reasons = []
    return {'level': row[0], 'score': row[1], 'reasons': reasons, 'sha256': row[3] or '', 'scanned_at': row[4], 'decision': row[5] or ''}


def get_scan_map(user_id):
    """{file_name: (level, decision)} for one user, in a single query (used by the file list)."""
    with DB_LOCK:
        conn = db_connect()
        try:
            rows = conn.execute('SELECT file_name, level, decision FROM file_scans WHERE user_id = ?', (user_id,)).fetchall()
        except sqlite3.Error:
            rows = []
        finally:
            conn.close()
    return {name: (level, decision or '') for name, level, decision in rows}


def _badge_for(level, decision=''):
    if level not in THREAT_BADGE:
        return '⚪'
    if level == THREAT_MEDIUM and decision in ('approved', 'admin'):
        return '🟡✅'
    return THREAT_BADGE[level]


def _scan_upload(data, ext, name):
    """Static scan of freshly uploaded bytes. Never raises: a scanner problem is logged and counted as LOW."""
    try:
        if ext == '.zip':
            fd, tmp_path = tempfile.mkstemp(prefix='demon_scan_', suffix='.zip')
            os.close(fd)
            try:
                with open(tmp_path, 'wb') as handle:
                    handle.write(data)
                result = scan_zip_file(tmp_path)
            finally:
                _remove_quietly(tmp_path)
            result['file'] = name
            result['size'] = len(data)
            result['sha256'] = hashlib.sha256(data).hexdigest()
            return result
        return scan_bytes(data, ext[1:], name)
    except Exception:
        logger.exception('Scanner failed on %s; treating as LOW', name)
        result = _build_result([], name, ext[1:], len(data))
        result['sha256'] = hashlib.sha256(data).hexdigest()
        return result


def _scan_disk_file(path, file_type):
    """Static scan of a file that is already stored on disk (never executes it)."""
    try:
        with open(path, 'rb') as handle:
            data = handle.read(SCAN_MAX_SOURCE_BYTES + 1)
        result = scan_bytes(data, file_type, os.path.basename(path))
    except Exception:
        logger.exception('Scanner failed on %s; treating as LOW', path)
        result = _build_result([], os.path.basename(path), file_type, 0)
    result['sha256'] = _file_sha256(path) or result.get('sha256', '')
    return result


def _reason_lines_html(result, limit=5, details=False):
    lines = []
    for reason in (result.get('reasons') or [])[:limit]:
        where = f" (line {reason['lines'][0]})" if reason.get('lines') else ''
        lines.append(f"• {html_escape(str(reason.get('text', '')))}{where}")
        if details and reason.get('details'):
            lines.append('   <i>' + html_escape(', '.join(str(x) for x in reason['details'][:3])[:120]) + '</i>')
    extra = len(result.get('reasons') or []) - limit
    if extra > 0:
        lines.append(f'• ...and {extra} more')
    return '\n'.join(lines)


def _user_verdict_text(result, file_name, outcome):
    """What the uploader sees: one or two short lines. outcome: 'auto' (LOW), 'review' (MEDIUM) or 'rejected' (HIGH)."""
    name = html_escape(file_name)
    if outcome == 'auto':
        return f"{THREAT_BADGE[THREAT_LOW]} <code>{name}</code> - safe lagi, start ho raha hai."
    why = _reason_lines_html(result, 2)
    if outcome == 'review':
        return (f"{THREAT_BADGE[THREAT_MEDIUM]} <code>{name}</code> - admin approval chahiye, abhi start nahi hua.\n{why}")
    return f"{THREAT_BADGE[THREAT_HIGH]} <code>{name}</code> - reject ho gaya (khatarnak code mila).\n{why}"


# ---- review registry -----------------------------------------------------------------------
def _review_db_save(entry):
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('INSERT OR REPLACE INTO pending_reviews (token, user_id, file_name, file_type, level, score, reasons, '
                         'sha256, created, chat_id, msg_id, uploader, admin_msgs, kind) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)',
                         (entry['token'], entry['user_id'], entry['file_name'], entry['file_type'], entry['level'], entry['score'],
                          json.dumps(entry['reasons'][:20]), entry['sha256'], entry['created'], entry['chat_id'],
                          entry['msg_id'], entry['uploader'], json.dumps(entry['admin_msgs']), entry['kind']))
            conn.commit()
        except sqlite3.Error as exc:
            logger.error('Could not save review %s: %s', entry.get('token'), exc)
        finally:
            conn.close()


def _review_db_delete(token):
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('DELETE FROM pending_reviews WHERE token = ?', (token,))
            conn.commit()
        except sqlite3.Error as exc:
            logger.error('Could not delete review %s: %s', token, exc)
        finally:
            conn.close()


def _reviews_load():
    """Reload the review queue from the database (startup and after a restore).
    Rows whose held file is gone are dropped, and held files without a row are deleted."""
    loaded = {}
    dropped = []
    with DB_LOCK:
        conn = db_connect()
        try:
            rows = conn.execute('SELECT token, user_id, file_name, file_type, level, score, reasons, sha256, created, chat_id, '
                                'msg_id, uploader, admin_msgs, kind FROM pending_reviews').fetchall()
        except sqlite3.Error as exc:
            logger.error('Could not read pending reviews: %s', exc)
            rows = []
        finally:
            conn.close()
    for row in rows:
        token = row[0]
        if not _TOKEN_RE.fullmatch(token or ''):
            dropped.append(token)
            continue
        try:
            reasons = json.loads(row[6] or '[]')
            admin_msgs = {str(k): v for k, v in json.loads(row[12] or '{}').items()}
        except ValueError:
            reasons, admin_msgs = [], {}
        kind = row[13] or 'upload'
        if kind == 'upload' and not os.path.isfile(_quarantine_path(token)):
            dropped.append(token)
            continue
        loaded[token] = {'token': token, 'user_id': row[1], 'file_name': row[2], 'file_type': row[3], 'level': row[4],
                         'score': row[5], 'reasons': reasons, 'sha256': row[7] or '', 'created': row[8] or time.time(),
                         'chat_id': row[9], 'msg_id': row[10], 'uploader': row[11] or '', 'admin_msgs': admin_msgs,
                         'kind': kind, 'status': 'pending'}
    for token in dropped:
        _review_db_delete(token)
    with REVIEW_LOCK:
        PENDING_REVIEWS.clear()
        PENDING_REVIEWS.update(loaded)
        if os.path.isdir(QUARANTINE_DIR):
            for name in os.listdir(QUARANTINE_DIR):
                if name.endswith('.bin') and _TOKEN_RE.fullmatch(name[:-4]) and name[:-4] not in loaded:
                    _remove_quietly(os.path.join(QUARANTINE_DIR, name))
    if loaded or dropped:
        logger.info('Review queue loaded: %s waiting, %s stale dropped', len(loaded), len(dropped))


def _pending_count():
    with REVIEW_LOCK:
        return sum(1 for item in PENDING_REVIEWS.values() if item['status'] == 'pending')


def _user_pending_count(user_id):
    with REVIEW_LOCK:
        return sum(1 for item in PENDING_REVIEWS.values() if item['user_id'] == user_id)


def _review_text(entry, expanded=False, outcome=None):
    """Admin detail view of one waiting file (short)."""
    level = entry['level']
    created = datetime.fromtimestamp(entry['created']).strftime('%d %b %H:%M')
    reasons = _reason_lines_html(entry, 4) or '• (no details stored)'
    lines = [f"{THREAT_BADGE[level]} <b>Approval chahiye</b>: <code>{html_escape(entry['file_name'])}</code>",
             f"User: {html_escape(entry['uploader'] or 'user')} (<code>{entry['user_id']}</code>) - {created}",
             reasons]
    source = _review_source(entry)
    if source:
        lines.insert(2, source)
    if outcome:
        lines += ['', outcome]
    return '\n'.join(lines)


def _review_markup(entry, expanded=False, in_panel=True):
    token = entry['token']
    kb = NavMenu(row_width=2)
    kb.row(NavButton('✅ Approve & run', callback_data=f'rv_a_{token}'),
           NavButton('❌ Reject', callback_data=f'rv_r_{token}'))
    kb.row(NavButton('📄 Get file to read', callback_data=f'rv_f_{token}'),
           NavButton('⬅️ Back to approvals', callback_data='adm_approvals'))
    return kb


def _review_edit_all(entry, text, markup, skip_message_id=None):
    """Update every admin's copy of a review message so nobody sees stale Approve/Reject buttons."""
    for admin_key, message_id in list(entry.get('admin_msgs', {}).items()):
        if skip_message_id is not None and message_id == skip_message_id and str(admin_key) == str(entry.get('_acting_chat', '')):
            continue
        try:
            bot.edit_message_text(text, int(admin_key), message_id, parse_mode='HTML', reply_markup=markup)
        except Exception as exc:
            logger.debug('Could not update review message for %s: %s', admin_key, type(exc).__name__)


def _submit_for_review(user_id, uploader, chat_id, msg_id, file_name, file_type, data, result, kind='upload'):
    """Hold a MEDIUM upload (or flag an existing hosted file) and ask every admin. Returns (token, error_text)."""
    _expire_reviews()
    token = None
    with REVIEW_LOCK:
        if len(PENDING_REVIEWS) >= REVIEW_MAX_TOTAL:
            return None, 'Too many files are waiting for review right now. Please try again later.'
        if sum(1 for item in PENDING_REVIEWS.values() if item['user_id'] == user_id) >= REVIEW_MAX_PER_USER:
            return None, f'You already have {REVIEW_MAX_PER_USER} files waiting for review. Please wait for a decision first.'
        if any(item['user_id'] == user_id and item['file_name'] == file_name for item in PENDING_REVIEWS.values()):
            return None, 'This file is already waiting for admin review.'
        for _ in range(10):
            candidate = secrets.token_hex(4)
            if candidate not in PENDING_REVIEWS:
                token = candidate
                break
        if token is None:
            return None, 'Could not queue the file. Please try again.'
        entry = {'token': token, 'user_id': user_id, 'file_name': file_name, 'file_type': file_type, 'level': result['level'],
                 'score': result.get('score', 0), 'reasons': list(result.get('reasons', []))[:20], 'sha256': result.get('sha256', ''),
                 'created': time.time(), 'chat_id': chat_id, 'msg_id': msg_id, 'uploader': uploader, 'admin_msgs': {},
                 'kind': kind, 'status': 'pending'}
        if kind == 'upload':
            try:
                os.makedirs(QUARANTINE_DIR, mode=0o700, exist_ok=True)
                fd = os.open(_quarantine_path(token), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                with os.fdopen(fd, 'wb') as handle:
                    handle.write(data)
            except OSError as exc:
                logger.error('Could not hold upload for review: %s', exc)
                return None, 'Could not store the file for review. Please try again later.'
        PENDING_REVIEWS[token] = entry
    _review_db_save(entry)
    # Admins get a plain notice with NO buttons (so their menu keyboard is left alone); they decide in Admin > Approvals.
    notice = (f"{THREAT_BADGE[result['level']]} Naya approval: <code>{html_escape(file_name)}</code> "
              f"(user {html_escape(uploader or str(user_id))}). Admin panel > Approvals mein dekho.")
    if kind == 'upload' and file_type == 'zip':
        source = _gh_source_line(gh_manifest_from_zip_bytes(data))
        if source:
            notice += '\n' + source
    for admin_id in sorted(admin_ids):
        sent = _safe_send(admin_id, notice)
        if sent is not None:
            entry['admin_msgs'][str(admin_id)] = sent.message_id
    _review_db_save(entry)
    logger.info('Review %s queued: user=%s file=%s level=%s kind=%s admins_notified=%s', token, user_id, file_name,
                result['level'], kind, len(entry['admin_msgs']))
    return token, ''


def _expire_reviews():
    """Drop reviews nobody answered for REVIEW_TTL, tell the user and clear the admin buttons."""
    now = time.time()
    expired = []
    with REVIEW_LOCK:
        for token, entry in list(PENDING_REVIEWS.items()):
            if entry['status'] == 'pending' and now - entry['created'] > REVIEW_TTL:
                expired.append(PENDING_REVIEWS.pop(token))
                _remove_quietly(_quarantine_path(token) if entry['kind'] == 'upload' else None)
    for entry in expired:
        _review_db_delete(entry['token'])
        _review_edit_all(entry, _review_text(entry, outcome='⌛ Expired, kisi ne decide nahi kiya.'), None)
        _safe_send(entry['chat_id'], f"⌛ <code>{html_escape(entry['file_name'])}</code> ka review time par nahi hua, hata diya. Zarurat ho to dobara upload karo.")


def _deploy_upload(user_id, file_name, file_type, data, reply_obj, result, decision):
    """Store an accepted upload and start it. Returns (ok, error_text). Only reached after LOW or admin approval."""
    user_folder = get_user_folder(user_id)
    if file_type == 'zip':
        temp_dir = tempfile.mkdtemp(prefix=f'user_{user_id}_zip_')
        try:
            zip_path = os.path.join(temp_dir, file_name)
            with open(zip_path, 'wb') as handle:
                handle.write(data)
            ok = process_zip_file(zip_path, user_id, user_folder, file_name, reply_obj, temp_dir, scan=(result, decision))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)
        return bool(ok), ('' if ok else 'The archive could not be set up. The reason was sent to you.')
    file_path = os.path.join(user_folder, file_name)
    try:
        fd = os.open(file_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    except FileExistsError:
        return False, f'{file_name} already exists in your storage. Rename it or delete the old one first.'
    with os.fdopen(fd, 'wb') as handle:
        handle.write(data)
    record = dict(result)
    record['sha256'] = _file_sha256(file_path) or result.get('sha256', '')
    save_scan_record(user_id, file_name, record, decision)
    if file_type == 'js':
        handle_js_file(file_path, user_id, user_folder, file_name, reply_obj)
    else:
        handle_py_file(file_path, user_id, user_folder, file_name, reply_obj)
    return True, ''


def _start_hosted(owner_id, file_name, file_type, reply_obj):
    user_folder = get_user_folder(owner_id)
    file_path = os.path.join(user_folder, file_name)
    _reset_restart_state(owner_id, file_name)
    target = run_js_script if file_type == 'js' else run_script
    threading.Thread(target=target, args=(file_path, owner_id, user_folder, file_name, reply_obj)).start()


# ---- admin decisions ------------------------------------------------------------------------
def _review_claim(token, new_status='working'):
    """Atomically take a pending review so two admins cannot decide it twice. Returns the entry or None."""
    with REVIEW_LOCK:
        entry = PENDING_REVIEWS.get(token)
        if entry is None or entry['status'] != 'pending':
            return None
        entry['status'] = new_status
        return entry


def _review_release(token):
    with REVIEW_LOCK:
        entry = PENDING_REVIEWS.get(token)
        if entry is not None:
            entry['status'] = 'pending'


def _review_forget(entry):
    with REVIEW_LOCK:
        PENDING_REVIEWS.pop(entry['token'], None)
        if entry['kind'] == 'upload':
            _remove_quietly(_quarantine_path(entry['token']))
    _review_db_delete(entry['token'])


def _review_approve(call, token):
    entry = _review_claim(token)
    if entry is None:
        bot.answer_callback_query(call.id, 'Ye request pehle hi handle ho chuki hai.', show_alert=True)
        _show_approvals(call)
        return
    bot.answer_callback_query(call.id, '✅ Approved. Start ho raha hai...')
    ok, err = False, 'Unknown problem.'
    try:
        user_id, file_name, file_type = entry['user_id'], entry['file_name'], entry['file_type']
        reply_obj = _ReplyTarget(entry['chat_id'], entry['msg_id'], user_id)
        if is_user_banned(user_id):
            err = 'That user is banned.'
        elif entry['kind'] == 'upload':
            with open(_quarantine_path(token), 'rb') as handle:
                data = handle.read()
            if hashlib.sha256(data).hexdigest() != entry['sha256']:
                err = 'The held file no longer matches its fingerprint, so it was not started.'
            elif get_user_file_count(user_id) >= get_user_file_limit(user_id) and not (
                    file_type == 'zip' and (gh_manifest_from_zip_bytes(data) or {}).get('update')):
                err = 'The user has reached their file limit.'
            else:
                ok, err = _deploy_upload(user_id, file_name, file_type, data, reply_obj, entry, 'approved')
        else:
            path = os.path.join(get_user_folder(user_id), file_name)
            current = _file_sha256(path)
            if current is None:
                err = 'The file is no longer in the user storage.'
            elif current != entry['sha256']:
                err = 'The file changed after it was scanned. Ask the user to start it again so it is re-checked.'
            else:
                set_scan_decision(user_id, file_name, 'approved')
                _start_hosted(user_id, file_name, file_type, reply_obj)
                ok = True
    except Exception:
        logger.exception('Approving review %s failed', token)
        ok, err = False, 'Something went wrong while starting the file.'
    if not ok:
        _review_release(token)
        _safe_send(call.message.chat.id, f'⚠️ <code>{html_escape(entry["file_name"])}</code> start nahi ho paya: {html_escape(err)}\nAbhi bhi approvals mein hai.')
        return
    _review_forget(entry)
    logger.info('Review %s approved by %s', token, call.from_user.id)
    admin_name = html_escape(call.from_user.first_name or 'Admin')
    _review_edit_all(entry, _review_text(entry, outcome=f'✅ Approved by {admin_name}.'), None)
    _safe_send(entry['chat_id'], f"✅ Admin ne <code>{html_escape(entry['file_name'])}</code> approve kar diya, start ho raha hai.")
    _show_approvals(call)


def _review_reject(call, token):
    entry = _review_claim(token)
    if entry is None:
        bot.answer_callback_query(call.id, 'Ye request pehle hi handle ho chuki hai.', show_alert=True)
        _show_approvals(call)
        return
    bot.answer_callback_query(call.id, '❌ Rejected.')
    if entry['kind'] == 'existing':
        set_scan_decision(entry['user_id'], entry['file_name'], 'rejected')
    _review_forget(entry)
    logger.info('Review %s rejected by %s', token, call.from_user.id)
    _review_edit_all(entry, _review_text(entry, outcome=f"❌ Rejected by {html_escape(call.from_user.first_name or 'Admin')}."), None)
    _safe_send(entry['chat_id'], f"❌ Admin ne <code>{html_escape(entry['file_name'])}</code> reject kar diya (security). Start nahi hua.")
    _show_approvals(call)


def _approvals_view():
    """Admin list of uploads waiting for a decision: (text, menu)."""
    _expire_reviews()
    with REVIEW_LOCK:
        items = sorted((dict(item) for item in PENDING_REVIEWS.values()), key=lambda item: item['created'])
    kb = NavMenu(row_width=1)
    if items:
        text = f'<b>📥 Approvals ({len(items)})</b>\nKisi ko kholo, reason padho, phir Approve ya Reject.'
        for number, item in enumerate(items[:20], 1):
            who = (item['uploader'] or str(item['user_id']))[:14]
            kb.add(NavButton(f"{number}. {THREAT_BADGE[item['level']]} {item['file_name'][:22]} - {who}",
                                              callback_data=f"rv_o_{item['token']}"))
        if len(items) > 20:
            text += f'\n<i>Pehle 20 dikha raha hoon, total {len(items)}.</i>'
    else:
        text = '<b>📥 Approvals (0)</b>\n✅ Kuch pending nahi hai.'
    kb.add(NavButton('🔄 Refresh', callback_data='adm_approvals'))
    kb.add(NavButton('👑 Admin Panel', callback_data='admin_dashboard'))
    return text, kb


def _show_approvals(call):
    text, kb = _approvals_view()
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)
    except Exception:
        _safe_send(call.message.chat.id, text, reply_markup=kb)


def approvals_callback(call):
    bot.answer_callback_query(call.id)
    _show_approvals(call)


def review_callback(call):
    """Routes rv_a_ / rv_r_ / rv_f_ / rv_o_ buttons (admin only, checked by the caller)."""
    parts = (call.data or '').split('_', 2)
    if len(parts) != 3 or not _TOKEN_RE.fullmatch(parts[2]):
        bot.answer_callback_query(call.id, 'Ye button ab valid nahi hai.', show_alert=True)
        return
    action, token = parts[1], parts[2]
    if action == 'a':
        return _review_approve(call, token)
    if action == 'r':
        return _review_reject(call, token)
    with REVIEW_LOCK:
        entry = PENDING_REVIEWS.get(token)
        entry = dict(entry) if entry else None
    if entry is None:
        bot.answer_callback_query(call.id, 'Ye request handle ho chuki hai ya expire ho gayi.', show_alert=True)
        _show_approvals(call)
        return
    if action in ('d', 's', 'o'):
        bot.answer_callback_query(call.id)
        bot.edit_message_text(_review_text(entry), call.message.chat.id, call.message.message_id,
                              parse_mode='HTML', reply_markup=_review_markup(entry))
        return
    if action == 'f':
        path = _quarantine_path(token) if entry['kind'] == 'upload' else os.path.join(get_user_folder(entry['user_id']), entry['file_name'])
        if not os.path.isfile(path):
            bot.answer_callback_query(call.id, 'File ab available nahi hai.', show_alert=True)
            return
        bot.answer_callback_query(call.id, 'Copy bhej raha hoon...')
        with open(path, 'rb') as handle:
            bot.send_document(call.message.chat.id, types.InputFile(handle, file_name=entry['file_name']),
                              caption='Review copy. Padho, run mat karo.')
        return
    bot.answer_callback_query(call.id, 'Unknown action.')


# ---- launch gate ------------------------------------------------------------------------------
def launch_gate(owner_id, file_name, file_type, actor_id, queue=True, admin_override=True):
    """Decide whether a hosted file may be started. Returns (allowed, note_html).
    Admin-owned files run directly. For everyone else: LOW runs, MEDIUM needs an admin approval, HIGH never runs.
    A stored verdict is only trusted while the file on disk still has the fingerprint that was scanned;
    otherwise (or when there is no record yet, e.g. old files) it is scanned again silently."""
    if owner_id in admin_ids:
        return True, ''
    path = os.path.join(get_user_folder(owner_id), file_name)
    sha = _file_sha256(path)
    if sha is None:
        return True, ''        # missing file: the caller already reports that
    rec = get_scan_record(owner_id, file_name)
    if not rec or rec['sha256'] != sha:
        result = _scan_disk_file(path, file_type)
        save_scan_record(owner_id, file_name, result, 'rescan' if result['level'] == THREAT_LOW else '')
        rec = {'level': result['level'], 'score': result['score'], 'reasons': result['reasons'], 'sha256': sha,
               'decision': 'rescan' if result['level'] == THREAT_LOW else ''}
    level, decision = rec['level'], rec['decision']
    why = _reason_lines_html(rec, 2)
    if decision == 'rejected':
        return False, f"{THREAT_BADGE[THREAT_HIGH]} Admin ne ye file pehle reject ki thi, start nahi hogi."
    if level == THREAT_HIGH:
        return False, f"{THREAT_BADGE[THREAT_HIGH]} Khatarnak code mila, start nahi hoga.\n{why}"
    if level == THREAT_LOW or decision in ('approved', 'admin'):
        return True, ''
    if admin_override and actor_id in admin_ids:
        set_scan_decision(owner_id, file_name, 'admin')
        return True, ''
    if not queue:
        return False, f"{THREAT_BADGE[THREAT_MEDIUM]} Admin approval chahiye.\n{why}"
    token, err = _submit_for_review(owner_id, str(owner_id), owner_id, None, file_name, file_type, None,
                                    dict(rec, file=file_name), kind='existing')
    if token:
        with REVIEW_LOCK:
            item = PENDING_REVIEWS.get(token)
            if item is not None:
                item['msg_id'] = None
        return False, f"{THREAT_BADGE[THREAT_MEDIUM]} Start nahi hua, admin approval ke liye bhej diya.\n{why}"
    return False, f"{THREAT_BADGE[THREAT_MEDIUM]} Start nahi hua. {html_escape(err)}"


def _reset_old_pending_verdicts():
    """Old-scanner MEDIUM/HIGH verdicts that nobody decided are forgotten so the new scanner re-checks them on next launch."""
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute("UPDATE file_scans SET sha256 = '' WHERE level IN ('medium', 'high') "
                         "AND decision NOT IN ('approved', 'admin', 'rejected')")
            conn.commit()
        except sqlite3.Error as exc:
            logger.warning('Could not reset old scan verdicts: %s', exc)
        finally:
            conn.close()


_reset_old_pending_verdicts()
_reviews_load()   # uploads that were waiting for an admin before the last restart


# --- Mandatory Channels Functions ---
_MEMBER_CACHE = {}          # (user_id, channel_id) -> time of last positive answer
_MEMBER_CACHE_TTL = 120     # seconds; avoids asking Telegram on every single button press
_MEMBER_CACHE_MAX = 5000


def is_user_member(user_id, channel_id):
    """Check if user is member of a channel (positive answers are cached for a short time)"""
    cache_key = (user_id, str(channel_id))
    now = time.time()
    cached_at = _MEMBER_CACHE.get(cache_key)
    if cached_at is not None and now - cached_at < _MEMBER_CACHE_TTL:
        return True
    try:
        chat_member = bot.get_chat_member(channel_id, user_id)
        is_member = (chat_member.status in ['member', 'administrator', 'creator'] or (chat_member.status == 'restricted' and bool(getattr(chat_member, 'is_member', False))))
        if is_member:
            if len(_MEMBER_CACHE) >= _MEMBER_CACHE_MAX:
                _MEMBER_CACHE.clear()
            _MEMBER_CACHE[cache_key] = now
        else:
            _MEMBER_CACHE.pop(cache_key, None)
        return is_member
    except Exception as e:
        logger.error(f"Error checking channel membership for {user_id} in {channel_id}: {e}")
        return False

def check_mandatory_subscription(user_id):
    """Check if user is subscribed to all mandatory channels"""
    if not mandatory_channels:
        return True, []  # No mandatory channels exist
    
    not_joined = []
    for channel_id, channel_info in list(mandatory_channels.items()):
        if not is_user_member(user_id, channel_id):
            not_joined.append((channel_id, channel_info))
    
    if not_joined:
        return False, not_joined
    return True, []

def save_mandatory_channel(channel_id, channel_username, channel_name, added_by, invite_link=''):
    """Save mandatory channel to database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            added_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO mandatory_channels (channel_id, channel_username, channel_name, invite_link, added_by, added_date) VALUES (?, ?, ?, ?, ?, ?)',
                      (channel_id, channel_username, channel_name, invite_link or '', added_by, added_date))
            conn.commit()
            mandatory_channels[channel_id] = {
                'username': channel_username,
                'name': channel_name,
                'invite_link': invite_link or ''
            }
            logger.info(f"Saved mandatory channel: {channel_name} ({channel_id})")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error saving channel: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error saving channel: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def remove_mandatory_channel_db(channel_id):
    """Remove mandatory channel from database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM mandatory_channels WHERE channel_id = ?', (channel_id,))
            conn.commit()
            if channel_id in mandatory_channels:
                del mandatory_channels[channel_id]
            logger.info(f"Removed mandatory channel: {channel_id}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error removing channel: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error removing channel: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def create_mandatory_channels_menu():
    """Create mandatory channels management menu"""
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Channel', callback_data='add_mandatory_channel'),
        NavButton('➖ Remove Channel', callback_data='remove_mandatory_channel')
    )
    markup.row(NavButton('📋 List Channels', callback_data='list_mandatory_channels'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_check_message(not_joined_channels):
    """Create subscription verification message"""
    message = "📢 <b>Important: Join Our Channels First:</b>\n\n"
    
    markup = NavMenu()
    
    for channel_id, channel_info in not_joined_channels:
        channel_username = channel_info.get('username', '')
        channel_name = channel_info.get('name', 'Channel')
        
        invite_link = channel_info.get('invite_link', '')
        if channel_username:
            channel_link = f"https://t.me/{channel_username.replace('@', '')}"
        elif invite_link:
            channel_link = invite_link
        else:
            channel_link = None

        message += f"• {html_escape(str(channel_name))}\n"
        if channel_link:
            markup.add(NavButton(f"Join {channel_name}"[:64], url=channel_link))
        else:
            message += "  Private invite link unavailable; contact the bot owner.\n"
    
    markup.add(NavButton("✅ Verify Subscription", callback_data='check_subscription_status'))
    
    return message, markup


# --- User Management Functions ---
def is_user_banned(user_id):
    """Check if user is banned"""
    return user_id in banned_users

def ban_user_db(user_id, reason, banned_by):
    """Ban a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            ban_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO banned_users (user_id, reason, banned_by, ban_date) VALUES (?, ?, ?, ?)',
                      (user_id, reason, banned_by, ban_date))
            conn.commit()
            banned_users.add(user_id)
            logger.warning(f"User {user_id} banned by {banned_by}. Reason: {reason}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error banning user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error banning user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def unban_user_db(user_id):
    """Unban a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM banned_users WHERE user_id = ?', (user_id,))
            conn.commit()
            banned_users.discard(user_id)
            logger.info(f"User {user_id} unbanned")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error unbanning user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error unbanning user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def set_user_limit_db(user_id, limit, set_by):
    """Set custom file limit for a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            set_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO user_limits (user_id, file_limit, set_by, set_date) VALUES (?, ?, ?, ?)',
                      (user_id, limit, set_by, set_date))
            conn.commit()
            user_limits[user_id] = limit
            logger.info(f"Set file limit {limit} for user {user_id} by {set_by}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error setting limit for user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error setting limit for user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def remove_user_limit_db(user_id):
    """Remove custom file limit for a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_limits WHERE user_id = ?', (user_id,))
            conn.commit()
            if user_id in user_limits:
                del user_limits[user_id]
            logger.info(f"Removed custom limit for user {user_id}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error removing limit for user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error removing limit for user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

# --- Modified Helper Functions ---
def get_user_folder(user_id):
    """Get or create user's folder for storing files"""
    user_folder = os.path.join(UPLOAD_BOTS_DIR, str(user_id))
    os.makedirs(user_folder, exist_ok=True)
    return user_folder

def get_user_file_limit(user_id):
    """Get the file upload limit for a user"""
    if user_id == OWNER_ID: return OWNER_LIMIT
    if user_id in admin_ids: return ADMIN_LIMIT
    if user_id in user_limits: return user_limits[user_id]
    if user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now():
        return SUBSCRIBED_USER_LIMIT
    return FREE_USER_LIMIT

def get_user_file_count(user_id):
    """Get the number of files uploaded by a user"""
    return len(user_files.get(user_id, []))

def is_bot_running(script_owner_id, file_name):
    """Return process status; leave dead records for watchdog crash recovery."""
    script_key = f"{script_owner_id}_{file_name}"
    info = bot_scripts.get(script_key)
    if not info or not info.get("process"):
        return False
    try:
        return info["process"].poll() is None
    except Exception as exc:
        logger.warning("Could not inspect process %s: %s", script_key, exc)
        return False

def _close_quietly(handle):
    try:
        if handle is not None and not getattr(handle, 'closed', True):
            handle.close()
    except Exception as exc:
        logger.debug("Could not close a handle: %s", exc)


def release_process_resources(process_info):
    """Close the log file and the pipes of a script process (prevents leaked file handles)."""
    _close_quietly(process_info.get('log_file'))
    proc = process_info.get('process')
    if proc is not None:
        for stream_name in ('stdin', 'stdout', 'stderr'):
            _close_quietly(getattr(proc, stream_name, None))


def _signal_process_group(pid, sig):
    """Send a signal to the whole process group of a script (POSIX only).
    Only done when the script leads its own group, so the hosting bot can never signal itself."""
    if os.name != 'posix':
        return
    try:
        if os.getpgid(pid) == pid:
            os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError, OSError):
        pass


def kill_process_tree(process_info):
    """Stop a script and everything it started, wait for it (no zombies) and close its files."""
    script_key = process_info.get('script_key', 'N/A')
    process = process_info.get('process')
    pid = getattr(process, 'pid', None)
    try:
        if not pid:
            logger.error(f"Process object/PID missing for {script_key}; cannot kill (files are still closed).")
            return
        targets = []
        try:
            parent = psutil.Process(pid)
            targets = parent.children(recursive=True) + [parent]
        except psutil.NoSuchProcess:
            logger.info(f"Process {pid} for {script_key} already gone.")
        logger.info(f"Stopping {script_key} (PID {pid}, {max(len(targets) - 1, 0)} child process(es))")
        _signal_process_group(pid, signal.SIGTERM)
        for proc in targets:
            try:
                proc.terminate()
            except psutil.NoSuchProcess:
                pass
            except Exception as exc:
                logger.warning(f"Could not terminate {proc.pid} for {script_key}: {exc}")
        _gone, alive = psutil.wait_procs(targets, timeout=3)
        if alive:
            logger.warning(f"{len(alive)} process(es) of {script_key} ignored SIGTERM; killing.")
            if hasattr(signal, 'SIGKILL'):
                _signal_process_group(pid, signal.SIGKILL)
            for proc in alive:
                try:
                    proc.kill()
                except psutil.NoSuchProcess:
                    pass
                except Exception as exc:
                    logger.error(f"Failed to kill {proc.pid} for {script_key}: {exc}")
            psutil.wait_procs(alive, timeout=2)
        try:
            process.wait(timeout=2)  # reap the child so no zombie is left behind
        except Exception:
            pass
    except Exception as e:
        logger.error(f"❌ Unexpected error killing process tree for PID {pid or 'N/A'} ({script_key}): {e}", exc_info=True)
    finally:
        release_process_resources(process_info)

# --- Map Telegram import names to actual PyPI package names ---
TELEGRAM_MODULES = {
    # Main Bot Frameworks
    'telebot': 'pyTelegramBotAPI',
    'telegram': 'python-telegram-bot',
    'python_telegram_bot': 'python-telegram-bot',
    'aiogram': 'aiogram',
    'pyrogram': 'pyrogram',
    'telethon': 'telethon',
    'telethon.sync': 'telethon', # Handle specific imports
    'from telethon.sync import telegramclient': 'telethon', # Example

    # Additional Libraries (add more specific mappings if import name differs)
    'telepot': 'telepot',
    'pytg': 'pytg',
    'tgcrypto': 'tgcrypto',
    'telegram_upload': 'telegram-upload',
    'telegram_send': 'telegram-send',
    'telegram_text': 'telegram-text',

    # MTProto & Low-Level
    'mtproto': 'telegram-mtproto', # Example, check actual package name
    'tl': 'telethon',  # Part of Telethon, install 'telethon'

    # Utilities & Helpers (examples, verify package names)
    'telegram_utils': 'telegram-utils',
    'telegram_logger': 'telegram-logger',
    'telegram_handlers': 'python-telegram-handlers',

    # Database Integrations (examples)
    'telegram_redis': 'telegram-redis',
    'telegram_sqlalchemy': 'telegram-sqlalchemy',

    # Payment & E-commerce (examples)
    'telegram_payment': 'telegram-payment',
    'telegram_shop': 'telegram-shop-sdk',

    # Testing & Debugging (examples)
    'pytest_telegram': 'pytest-telegram',
    'telegram_debug': 'telegram-debug',

    # Scraping & Analytics (examples)
    'telegram_scraper': 'telegram-scraper',
    'telegram_analytics': 'telegram-analytics',

    # NLP & AI (examples)
    'telegram_nlp': 'telegram-nlp-toogit',
    'telegram_ai': 'telegram-ai', # Assuming this exists

    # Web & API Integration (examples)
    'telegram_api': 'telegram-api-client',
    'telegram_web': 'telegram-web-integration',

    # Gaming & Interactive (examples)
    'telegram_games': 'telegram-games',
    'telegram_quiz': 'telegram-quiz-bot',

    # File & Media Handling (examples)
    'telegram_ffmpeg': 'telegram-ffmpeg',
    'telegram_media': 'telegram-media-utils',

    # Security & Encryption (examples)
    'telegram_2fa': 'telegram-twofa',
    'telegram_crypto': 'telegram-crypto-bot',

    # Localization & i18n (examples)
    'telegram_i18n': 'telegram-i18n',
    'telegram_translate': 'telegram-translate',

    # Common non-telegram examples
    'bs4': 'beautifulsoup4',
    'requests': 'requests',
    'pillow': 'Pillow', # Note the capitalization difference
    'cv2': 'opencv-python', # Common import name for OpenCV
    'yaml': 'PyYAML',
    'dotenv': 'python-dotenv',
    'dateutil': 'python-dateutil',
    'pandas': 'pandas',
    'numpy': 'numpy',
    'flask': 'Flask',
    'django': 'Django',
    'sqlalchemy': 'SQLAlchemy',
    'asyncio': None, # Core module, should not be installed
    'json': None,    # Core module
    'datetime': None,# Core module
    'os': None,      # Core module
    'sys': None,     # Core module
    're': None,      # Core module
    'time': None,    # Core module
    'math': None,    # Core module
    'random': None,  # Core module
    'logging': None, # Core module
    'threading': None,# Core module
    'subprocess':None,# Core module
    'zipfile':None,  # Core module
    'tempfile':None, # Core module
    'shutil':None,   # Core module
    'sqlite3':None,  # Core module
    'psutil': 'psutil',
    'atexit': None   # Core module
}

# --- Manual Modules Installation System ---
def save_install_log(user_id, module_name, package_name, status, log):
    """Save installation log to database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            install_date = datetime.now().isoformat()
            c.execute('INSERT INTO install_logs (user_id, module_name, package_name, status, log, install_date) VALUES (?, ?, ?, ?, ?, ?)',
                      (user_id, module_name, package_name, status, log, install_date))
            conn.commit()
            logger.info(f"Saved install log for user {user_id}: {module_name} - {status}")
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error saving install log: {e}")
        except Exception as e:
            logger.error(f"❌ Unexpected error saving install log: {e}", exc_info=True)
        finally:
            conn.close()

_SAFE_PACKAGE_RE = re.compile(r'^[A-Za-z0-9@][A-Za-z0-9@._/+=<>!~^*,\[\]-]{0,119}$')


def _is_safe_package_name(name):
    """Reject empty names and anything that could be read as a command-line option (leading dash, spaces)."""
    return bool(name) and bool(_SAFE_PACKAGE_RE.match(name))


def attempt_install_pip(module_name, message, manual_request=False):
    """Install Python package via pip"""
    package_name = TELEGRAM_MODULES.get(module_name.lower(), module_name) 
    if package_name is None: 
        logger.info(f"Module '{module_name}' is core. Skipping pip install.")
        return False, "Core module - no installation needed"
    
    try:
        if manual_request:
            bot.reply_to(message, f"🔄 Manual installation requested for `{module_name}` -> `{package_name}`...", parse_mode='Markdown')
        else:
            bot.reply_to(message, f"🐍 Module `{module_name}` not found. Installing `{package_name}`...", parse_mode='Markdown')
        
        if not _is_safe_package_name(package_name):
            bot.reply_to(message, "❌ That package name is not valid. Send just the package name, for example `requests`.", parse_mode='Markdown')
            return False, "Invalid package name"
        command = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', package_name]
        logger.info(f"Running install: {' '.join(command)}")
        result = subprocess.run(command, capture_output=True, text=True, check=False, encoding='utf-8', errors='ignore',
                                timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=child_env())
        
        if result.returncode == 0:
            log_msg = f"Installed {package_name}. Output:\n{result.stdout}"
            logger.info(log_msg)
            success_msg = f"✅ Package `{package_name}` (for `{module_name}`) installed successfully."
            bot.reply_to(message, success_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "success", log_msg)
            return True, log_msg
        else:
            error_msg = f"❌ Failed to install `{package_name}` for `{module_name}`.\nLog:\n```\n{result.stderr or result.stdout}\n```"
            logger.error(error_msg)
            if len(error_msg) > 4000: error_msg = error_msg[:4000] + "\n... (Log truncated)"
            bot.reply_to(message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "failed", error_msg)
            return False, error_msg
    except subprocess.TimeoutExpired:
        error_msg = f"❌ Installing `{package_name}` took longer than {INSTALL_TIMEOUT} seconds and was stopped. Try again later."
        logger.error(error_msg)
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, package_name, "error", error_msg)
        return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error installing `{package_name}`: {str(e)}"
        logger.error(error_msg, exc_info=True)
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, package_name, "error", error_msg)
        return False, error_msg

def attempt_install_npm(module_name, user_folder, message, manual_request=False):
    """Install Node package via npm"""
    try:
        if manual_request:
            bot.reply_to(message, f"🔄 Manual Node package installation requested for `{module_name}`...", parse_mode='Markdown')
        else:
            bot.reply_to(message, f"🟠 Node package `{module_name}` not found. Installing locally...", parse_mode='Markdown')
        
        if not _is_safe_package_name(module_name):
            bot.reply_to(message, "❌ That package name is not valid. Send just the package name, for example `npm:axios`.", parse_mode='Markdown')
            return False, "Invalid package name"
        command = ['npm', 'install', module_name]
        logger.info(f"Running npm install: {' '.join(command)} in {user_folder}")
        result = subprocess.run(command, capture_output=True, text=True, check=False, cwd=user_folder, encoding='utf-8', errors='ignore',
                                timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=child_env())
        
        if result.returncode == 0:
            log_msg = f"Installed {module_name}. Output:\n{result.stdout}"
            logger.info(log_msg)
            success_msg = f"✅ Node package `{module_name}` installed locally."
            bot.reply_to(message, success_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "success", log_msg)
            return True, log_msg
        else:
            error_msg = f"❌ Failed to install Node package `{module_name}`.\nLog:\n```\n{result.stderr or result.stdout}\n```"
            logger.error(error_msg)
            if len(error_msg) > 4000: error_msg = error_msg[:4000] + "\n... (Log truncated)"
            bot.reply_to(message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "failed", error_msg)
            return False, error_msg
    except subprocess.TimeoutExpired:
        error_msg = f"❌ Installing `{module_name}` took longer than {INSTALL_TIMEOUT} seconds and was stopped. Try again later."
        logger.error(error_msg)
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg
    except FileNotFoundError:
         error_msg = "❌ Error: 'npm' not found. Ensure Node.js/npm are installed and in PATH."
         logger.error(error_msg)
         bot.reply_to(message, error_msg)
         save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
         return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error installing Node package `{module_name}`: {str(e)}"
        logger.error(error_msg, exc_info=True)
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg

def manual_install_module_init(message):
    """Initialize manual module installation"""
    user_id = message.from_user.id
    
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
    
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "⚠️ Bot locked by admin. Try later.")
        return
    
    msg = bot.reply_to(message, "📦 Send module name to install (e.g., `requests` or `pillow`)\nFor Node.js: `npm:module_name`\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_manual_install_module)

def process_manual_install_module(message):
    """Process manual module installation"""
    user_id = message.from_user.id
    
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Installation cancelled.")
        return
    
    if not message.text:
        bot.reply_to(message, "⚠️ Please send the module name as text.")
        return
    module_name = message.text.strip()
    
    # Check if it's a Node.js module
    if module_name.lower().startswith('npm:'):
        module_name = module_name[4:].strip()
        user_folder = get_user_folder(user_id)
        success, log = attempt_install_npm(module_name, user_folder, message, manual_request=True)
    else:
        # Python module
        success, log = attempt_install_pip(module_name, message, manual_request=True)
    
    if success:
        logger.info(f"User {user_id} manually installed module: {module_name}")

# --- Database Operations ---
def save_user_file(user_id, file_name, file_type='py'):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('INSERT OR REPLACE INTO user_files (user_id, file_name, file_type) VALUES (?, ?, ?)',
                      (user_id, file_name, file_type))
            conn.commit()
            if user_id not in user_files: user_files[user_id] = []
            user_files[user_id] = [(fn, ft) for fn, ft in user_files[user_id] if fn != file_name]
            user_files[user_id].append((file_name, file_type))
            logger.info(f"Saved file '{file_name}' ({file_type}) for user {user_id}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error saving file for user {user_id}, {file_name}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error saving file for {user_id}, {file_name}: {e}", exc_info=True)
        finally: conn.close()

def remove_user_file_db(user_id, file_name):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            c.execute('DELETE FROM file_scans WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            conn.commit()
            if user_id in user_files:
                user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
                if not user_files[user_id]: del user_files[user_id]
            logger.info(f"Removed file '{file_name}' for user {user_id} from DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing file for {user_id}, {file_name}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error removing file for {user_id}, {file_name}: {e}", exc_info=True)
        finally: conn.close()

def add_active_user(user_id):
    if user_id in active_users:
        return  # already stored; avoids a database write on every single message
    active_users.add(user_id)
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            join_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO active_users (user_id, join_date, last_seen) VALUES (?, ?, ?)', 
                      (user_id, join_date, join_date))
            conn.commit()
            logger.info(f"Added/Updated active user {user_id} in DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error adding active user {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error adding active user {user_id}: {e}", exc_info=True)
        finally: conn.close()

def save_subscription(user_id, expiry):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            expiry_str = expiry.isoformat()
            c.execute('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)', (user_id, expiry_str))
            conn.commit()
            user_subscriptions[user_id] = {'expiry': expiry}
            logger.info(f"Saved subscription for {user_id}, expiry {expiry_str}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error saving subscription for {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error saving subscription for {user_id}: {e}", exc_info=True)
        finally: conn.close()

def remove_subscription_db(user_id):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM subscriptions WHERE user_id = ?', (user_id,))
            conn.commit()
            if user_id in user_subscriptions: del user_subscriptions[user_id]
            logger.info(f"Removed subscription for {user_id} from DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing subscription for {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error removing subscription for {user_id}: {e}", exc_info=True)
        finally: conn.close()

def add_admin_db(admin_id, added_by):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            added_date = datetime.now().isoformat()
            c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                      (admin_id, added_by, added_date))
            conn.commit()
            admin_ids.add(admin_id) 
            logger.info(f"Added admin {admin_id} to DB by {added_by}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error adding admin {admin_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error adding admin {admin_id}: {e}", exc_info=True)
        finally: conn.close()

def remove_admin_db(admin_id):
    if admin_id == OWNER_ID:
        logger.warning("Attempted to remove OWNER_ID from admins.")
        return False 
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        removed = False
        try:
            c.execute('SELECT 1 FROM admins WHERE user_id = ?', (admin_id,))
            if c.fetchone():
                c.execute('DELETE FROM admins WHERE user_id = ?', (admin_id,))
                conn.commit()
                removed = c.rowcount > 0 
                if removed: admin_ids.discard(admin_id); logger.info(f"Removed admin {admin_id} from DB")
                else: logger.warning(f"Admin {admin_id} found but delete affected 0 rows.")
            else:
                logger.warning(f"Admin {admin_id} not found in DB.")
                admin_ids.discard(admin_id)
            return removed
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing admin {admin_id}: {e}"); return False
        except Exception as e: logger.error(f"❌ Unexpected error removing admin {admin_id}: {e}", exc_info=True); return False
        finally: conn.close()

# --- Menu creation (Inline and ReplyKeyboards) ---
def create_main_menu_inline(user_id):
    """Main menu (a NavMenu, sent as a reply keyboard). Backup export/import is here for every user."""
    markup = NavMenu(row_width=2)
    markup.row(NavButton('📤 Upload Script', callback_data='upload'),
               NavButton('📂 My Files', callback_data='check_files'))
    markup.row(NavButton('👤 My Account', callback_data='user_account'),
               NavButton('🤖 My Running Bots', callback_data='my_running'))
    markup.row(NavButton('📦 Export Backup', callback_data=f'ubk_{user_id}'),
               NavButton('♻️ Import Backup', callback_data=f'ubr_{user_id}'))
    markup.row(NavButton('⚡ Speed Test', callback_data='speed'),
               NavButton('📊 Statistics', callback_data='stats'))
    markup.row(NavButton('📦 Module Install', callback_data='manual_install'),
               NavButton('🆘 Help', callback_data='user_help'))
    markup.row(NavButton('📢 Updates', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'),
               NavButton('📞 Support', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
    if user_id in admin_ids:
        markup.row(NavButton('👑 Admin Center', callback_data='admin_dashboard'),
                   NavButton(f'📥 Approvals ({_pending_count()})', callback_data='adm_approvals'))
        markup.row(NavButton('🩺 Hosting Health', callback_data='hosting_health'),
                   NavButton('⚙️ Admin Settings', callback_data='admin_settings'))
        markup.row(NavButton('👥 User Management', callback_data='user_management'),
                   NavButton('📢 Broadcast', callback_data='broadcast'))
    return markup


def _file_key_text(file_name, file_type, running, badge):
    short = file_name if len(file_name) <= 18 else file_name[:15] + '...'
    return f"{badge} {short} ({file_type}) {'▶️' if running else '⏹️'}"


def _files_view(user_id):
    """(text, NavMenu) for My Files. Export/Import Backup are always on it, even with no files."""
    files = sorted(user_files.get(user_id, []))
    menu = NavMenu(row_width=1)
    scan_map = get_scan_map(user_id)
    for file_name, file_type in files:
        badge = _badge_for(*scan_map[file_name]) if file_name in scan_map else '⚪'
        menu.add(NavButton(_file_key_text(file_name, file_type, is_bot_running(user_id, file_name), badge),
                           callback_data=f'file_{user_id}_{file_name}'))
    menu.row(NavButton('📦 Export Backup', callback_data=f'ubk_{user_id}'),
             NavButton('♻️ Import Backup', callback_data=f'ubr_{user_id}'))
    menu.row(NavButton('📤 Upload Script', callback_data='upload'))
    if files:
        text = "📂 Your files:\nTap a file to manage it, or back up / restore all your bots."
    else:
        text = ("📂 Your files:\n\n(No files uploaded yet)\n"
                "Purana backup hai? Import Backup dabao. Naya hai? Upload Script dabao.")
    return text, menu


# --- Full backup / restore ---------------------------------------------------
# Two scopes, both packed into ONE zip:
#   * Admin "Full Backup": the hosting bot's own source file + the whole hosting database +
#     every user's folder from UPLOAD_BOTS_DIR (scripts and data). Owner / main admin only.
#   * User "My Bots" backup: only that user's own folder (scripts + data) and their script list.
# Every restore is staged first, shown for a Yes/Cancel confirmation, and a backup of the current
# state is written to disk (and sent to the person) before anything is overwritten.
# Zip entries are checked against path traversal (zip-slip), links, duplicates and size limits.
BACKUP_FORMAT_FULL = 'demon-full-backup'
BACKUP_FORMAT_USER = 'demon-user-backup'
BACKUP_VERSION = 1
SQLITE_EXTS = ('.db', '.sqlite', '.sqlite3')
SQLITE_MAGIC = b'SQLite format 3\x00'
BACKUP_SKIP_DIRS = {'node_modules', '__pycache__', 'venv', 'env', 'site-packages', '.git'}
BACKUP_SKIP_SUFFIXES = ('.log', '.pyc', '-wal', '-shm', '-journal')
HOSTING_DB_CORE_TABLES = ('subscriptions', 'user_files', 'active_users', 'admins')
FULL_BACKUP_MAX_MB = _env_int('FULL_BACKUP_MAX_MB', 2048)    # total size of a full backup before compression
USER_BACKUP_MAX_MB = _env_int('USER_BACKUP_MAX_MB', 500)     # same, for one user's backup
BACKUP_MAX_FILES = _env_int('BACKUP_MAX_FILES', 50000)
IMPORT_TTL = 600                                             # seconds a pending upload / confirmation stays valid
# Telegram lets a bot read files up to 20 MB, so bigger backups are sent in parts that fit that limit.
PART_BYTES = max(1, min(MAX_UPLOAD_MB, 19)) * 1024 * 1024
MAX_PARTS = 40
BACKUP_KEEP = 3                                              # automatic pre-restore backups kept per scope
FULL_BACKUP_DIR = os.path.join(IROTECH_DIR, 'full_backups')
USER_BACKUP_DIR = os.path.join(IROTECH_DIR, 'user_backups')
PART_RE = re.compile(r'\.zip\.(\d{1,3})$', re.IGNORECASE)
IMPORT_LOCK = threading.RLock()
BACKUP_OP_LOCK = threading.Lock()   # only one export / restore at a time
PENDING_IMPORT_WAIT = {}      # user_id -> {'kind', 'owner', 'time', 'dir', 'parts'}   waiting for the upload
PENDING_IMPORT_CONFIRM = {}   # token -> staged restore waiting for Yes / Cancel


class BackupTooLarge(Exception):
    """The folder is bigger than the configured backup limit."""


def _now_stamp():
    return datetime.now().strftime('%Y%m%d_%H%M%S')


def _path_inside(root, path):
    """True when path (already resolved) is root or below it."""
    try:
        return os.path.commonpath((root, path)) == root
    except ValueError:
        return False


def _rmtree_quiet(path):
    try:
        if path and os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)
    except OSError:
        pass


def _human_size(num):
    num = float(num)
    for unit in ('B', 'KB', 'MB', 'GB'):
        if num < 1024 or unit == 'GB':
            return f'{num:.0f} {unit}' if unit == 'B' else f'{num:.1f} {unit}'
        num /= 1024


def _safe_zip_rel(rel):
    """A zip entry / relative path that stays inside its folder: no absolute path, no '..', no backslash."""
    if not rel or len(rel) > 400 or any(ord(ch) < 32 for ch in rel):
        return False
    if rel.startswith('/') or '\\' in rel or (len(rel) > 1 and rel[1] == ':'):
        return False
    return all(part not in ('', '.', '..') and len(part) <= 200 for part in rel.split('/'))


def _expire_pending_imports():
    """Forget stale waiting states and delete staged files nobody confirmed."""
    now = time.time()
    with IMPORT_LOCK:
        for uid in [u for u, p in PENDING_IMPORT_WAIT.items() if now - p['time'] > IMPORT_TTL]:
            pend = PENDING_IMPORT_WAIT.pop(uid, None)
            if pend:
                _rmtree_quiet(pend.get('dir'))
        for token in [t for t, e in PENDING_IMPORT_CONFIRM.items() if now - e['time'] > IMPORT_TTL]:
            entry = PENDING_IMPORT_CONFIRM.pop(token, None)
            if entry:
                _rmtree_quiet(entry.get('dir'))


def _prune_backups(folder, prefix, keep=BACKUP_KEEP):
    try:
        names = sorted(n for n in os.listdir(folder) if n.startswith(prefix))
        for old in names[:-keep]:
            try:
                os.remove(os.path.join(folder, old))
            except OSError:
                pass
    except OSError:
        pass


def _sqlite_snapshot(source_path, dest_path):
    """Consistent copy of a SQLite file (works while it is in use). Falls back to a plain copy."""
    try:
        src = sqlite3.connect(f'file:{source_path}?mode=ro', uri=True, timeout=10)
        try:
            dst = sqlite3.connect(dest_path)
            try:
                src.backup(dst)
            finally:
                dst.close()
        finally:
            src.close()
    except sqlite3.Error:
        shutil.copyfile(source_path, dest_path)


def _edit_or_send(call, text, markup=None):
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                              parse_mode='HTML', reply_markup=markup)
    except Exception:
        bot.send_message(call.message.chat.id, text, parse_mode='HTML', reply_markup=markup)


def _download_upload(message, max_mb):
    """Download the document of a message into memory with a size limit."""
    doc = message.document
    limit = max_mb * 1024 * 1024
    if (doc.file_size or 0) > limit:
        raise ValueError(f'That file is too big for me to read (maximum {max_mb} MB per file). '
                         'Big backups are sent as several parts (.zip.001, .zip.002 ...); send those one by one.')
    file_info = bot.get_file(doc.file_id)
    content = bot.download_file(file_info.file_path)
    if len(content) > limit:
        raise ValueError(f'That file is too big for me to read (maximum {max_mb} MB per file).')
    return content


def _confirm_markup(token):
    markup = NavMenu(row_width=2)
    markup.row(NavButton('✅ Yes, restore', callback_data=f'impc_yes_{token}'),
               NavButton('❌ Cancel', callback_data=f'impc_no_{token}'))
    return markup


def _cancel_markup():
    return NavMenu().add(NavButton('❌ Cancel', callback_data='impc_cancel'))


def _parts_markup():
    markup = NavMenu(row_width=2)
    markup.row(NavButton('✅ Done, check backup', callback_data='impc_done'),
               NavButton('❌ Cancel', callback_data='impc_cancel'))
    return markup


def _store_confirm(entry):
    token = os.urandom(6).hex()
    entry['time'] = time.time()
    with IMPORT_LOCK:
        PENDING_IMPORT_CONFIRM[token] = entry
    return token


def _can_backup_global(user_id):
    """The full backup holds every user's code, data and the admin list, so only the configured
    owner / main admin may export or restore it (not admins that were added later)."""
    return user_id in (OWNER_ID, ADMIN_ID) and user_id in admin_ids


def _may_manage_bot_data(user_id, owner_id):
    # Same rule as the existing per-file handlers (start / stop / delete / logs).
    return user_id == owner_id or user_id in admin_ids


# --- Building a backup zip ---------------------------------------------------
def _iter_backup_files(folder):
    """Regular files below folder as (relative path with '/', full path). Never follows links."""
    root = os.path.realpath(folder)
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames
                             if d not in BACKUP_SKIP_DIRS and not os.path.islink(os.path.join(dirpath, d)))
        for name in sorted(filenames):
            if name.endswith(BACKUP_SKIP_SUFFIXES) or (name.startswith('.import_') and name.endswith('.tmp')):
                continue
            full = os.path.join(dirpath, name)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            rel = os.path.relpath(full, root).replace(os.sep, '/')
            if _safe_zip_rel(rel):
                yield rel, full


def _zip_add_folder(archive, folder, prefix, snap_dir, budget):
    """Add every file of folder to the zip under prefix. budget = {'bytes', 'files', 'max_bytes'}.
    SQLite files are written from a consistent snapshot. Returns the number of files added."""
    added = 0
    for rel, full in _iter_backup_files(folder):
        try:
            size = os.path.getsize(full)
        except OSError:
            continue
        budget['bytes'] += size
        budget['files'] += 1
        if budget['files'] > BACKUP_MAX_FILES or (budget['max_bytes'] and budget['bytes'] > budget['max_bytes']):
            raise BackupTooLarge('The data is bigger than the backup size limit.')
        try:
            source = full
            snap = None
            if rel.lower().endswith(SQLITE_EXTS):
                with open(full, 'rb') as handle:
                    is_db = handle.read(16) == SQLITE_MAGIC
                if is_db:
                    snap = os.path.join(snap_dir, f'snap_{os.urandom(4).hex()}.tmp')
                    _sqlite_snapshot(full, snap)
                    source = snap
            archive.write(source, prefix + rel)
            if snap:
                os.remove(snap)
            added += 1
        except OSError as exc:      # a file that vanished or cannot be read must not break the whole backup
            logger.warning("Backup skipped %s: %s", full, redact_secrets(exc))
    return added


def _user_dirs():
    """[(user_id_text, folder)] for every numeric folder in UPLOAD_BOTS_DIR (the folder name is the owner)."""
    found = []
    try:
        names = sorted(os.listdir(UPLOAD_BOTS_DIR))
    except OSError:
        return found
    for name in names:
        folder = os.path.join(UPLOAD_BOTS_DIR, name)
        if name.isdigit() and len(name) <= 19 and os.path.isdir(folder) and not os.path.islink(folder):
            found.append((name, folder))
    return found


def _snapshot_live_database(dest_path):
    with DB_LOCK:
        source = db_connect()
        try:
            target = sqlite3.connect(dest_path)
            try:
                source.backup(target)
            finally:
                target.close()
        finally:
            source.close()


def _db_counts(path):
    """(users, scripts, subscriptions, admins) of a database file."""
    conn = sqlite3.connect(path, timeout=10)
    try:
        return tuple(conn.execute(f'SELECT COUNT(*) FROM {table}').fetchone()[0]
                     for table in ('active_users', 'user_files', 'subscriptions', 'admins'))
    finally:
        conn.close()


def _build_full_backup(zip_path, limit_mb=FULL_BACKUP_MAX_MB):
    """Write the full backup zip (source + database + every user folder). limit_mb=None means no size limit
    (used for the automatic safety backup). Returns a summary dict."""
    work = tempfile.mkdtemp(prefix='demon_fullbk_')
    try:
        db_snap = os.path.join(work, 'bot_data.db')
        _snapshot_live_database(db_snap)
        counts = _db_counts(db_snap)
        source_path = os.path.abspath(__file__)
        budget = {'bytes': 0, 'files': 0, 'max_bytes': limit_mb * 1024 * 1024 if limit_mb else None}
        users = {}
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED, allowZip64=True) as archive:
            archive.write(source_path, 'source/' + os.path.basename(source_path))
            archive.write(db_snap, 'database/bot_data.db')
            for uid_text, folder in _user_dirs():
                added = _zip_add_folder(archive, folder, f'upload_bots/{uid_text}/', work, budget)
                if added:
                    users[uid_text] = added
            manifest = {'format': BACKUP_FORMAT_FULL, 'version': BACKUP_VERSION,
                        'created': datetime.now().isoformat(timespec='seconds'),
                        'source_name': os.path.basename(source_path),
                        'database_counts': {'users': counts[0], 'scripts': counts[1],
                                            'subscriptions': counts[2], 'admins': counts[3]},
                        'users': users}
            archive.writestr('manifest.json', json.dumps(manifest, indent=1))
        return {'counts': counts, 'users': len(users), 'files': sum(users.values()),
                'source_name': os.path.basename(source_path)}
    finally:
        _rmtree_quiet(work)


def _build_user_backup(owner_id, zip_path, limit_mb=USER_BACKUP_MAX_MB):
    """Write one user's backup zip (their folder + script list). Returns a summary dict;
    'files' is 0 when the folder holds nothing to back up."""
    work = tempfile.mkdtemp(prefix=f'demon_userbk_{owner_id}_')
    try:
        folder = get_user_folder(owner_id)
        budget = {'bytes': 0, 'files': 0, 'max_bytes': limit_mb * 1024 * 1024 if limit_mb else None}
        scripts = [{'name': name, 'type': ftype} for name, ftype in sorted(user_files.get(owner_id, []))]
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED, allowZip64=True) as archive:
            added = _zip_add_folder(archive, folder, 'bots/', work, budget)
            manifest = {'format': BACKUP_FORMAT_USER, 'version': BACKUP_VERSION, 'owner': owner_id,
                        'created': datetime.now().isoformat(timespec='seconds'),
                        'scripts': scripts, 'files': added}
            archive.writestr('manifest.json', json.dumps(manifest, indent=1))
        return {'files': added, 'scripts': len(scripts), 'bytes': budget['bytes']}
    finally:
        _rmtree_quiet(work)


def _send_backup_file(chat_id, zip_path, base_name, caption):
    """Send a zip as one document, or as numbered parts (name.zip.001 ...) that fit Telegram's 20 MB read
    limit, so the same file can be sent back for a restore. Returns the number of parts (0 = too big)."""
    size = os.path.getsize(zip_path)
    if size <= PART_BYTES:
        with open(zip_path, 'rb') as handle:
            bot.send_document(chat_id, handle, caption=caption, parse_mode='HTML')
        return 1
    total = -(-size // PART_BYTES)
    if total > MAX_PARTS:
        return 0
    part_dir = tempfile.mkdtemp(prefix='demon_parts_')
    try:
        with open(zip_path, 'rb') as src:
            for index in range(1, total + 1):
                part_path = os.path.join(part_dir, f'{base_name}.zip.{index:03d}')
                with open(part_path, 'wb') as out:
                    out.write(src.read(PART_BYTES))
                text = caption if index == 1 else f'Part {index} of {total}'
                if index == 1:
                    text += (f'\n\nThis backup is big, so it comes in <b>{total} parts</b> '
                             '(.zip.001, .zip.002 ...). Keep all of them; send them back in any order when restoring.')
                with open(part_path, 'rb') as handle:
                    bot.send_document(chat_id, handle, caption=text, parse_mode='HTML')
                os.remove(part_path)
    finally:
        _rmtree_quiet(part_dir)
    return total


# --- Reading a backup zip (shared, zip-slip safe) -----------------------------
def _extract_backup_zip(zip_path, payload_dir, rel_ok, max_bytes):
    """Check every entry, then extract into payload_dir. rel_ok(rel) says which entry names are allowed.
    Returns (manifest_dict, error_text)."""
    try:
        archive = zipfile.ZipFile(zip_path)
    except (zipfile.BadZipFile, OSError):
        return None, 'That file is damaged or is not a zip backup.'
    try:
        with archive:
            items = [i for i in archive.infolist() if not i.is_dir()]
            if not items:
                return None, 'That backup is empty.'
            if len(items) > BACKUP_MAX_FILES:
                return None, f'Too many files in the backup (maximum {BACKUP_MAX_FILES}).'
            seen = set()
            for item in items:
                rel = item.filename
                if not _safe_zip_rel(rel):
                    return None, f'The backup contains an unsafe path: {rel[:60]!r}.'
                if item.flag_bits & 0x1:
                    return None, 'The backup is password protected.'
                if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                    return None, f'The backup contains a link, which is not allowed: {rel[:60]!r}.'
                if rel != 'manifest.json' and not rel_ok(rel):
                    return None, f'The backup contains something that does not belong here: {rel[:60]!r}.'
                if rel.lower() in seen:
                    return None, f'The backup contains the same file twice: {rel[:60]!r}.'
                seen.add(rel.lower())
            if 'manifest.json' not in seen:
                return None, 'This is not a backup made by this bot (manifest missing).'
            if sum(max(0, i.file_size) for i in items) > max_bytes:
                return None, f'The backup is bigger than the {max_bytes // (1024 * 1024)} MB limit.'
            root = os.path.realpath(payload_dir)
            written = 0
            for item in items:
                dest = os.path.realpath(os.path.join(root, item.filename))
                if dest == root or not _path_inside(root, dest):
                    return None, 'The backup contains an unsafe path.'
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                with archive.open(item) as src, open(dest, 'wb') as out:
                    while True:
                        chunk = src.read(1024 * 1024)
                        if not chunk:
                            break
                        written += len(chunk)
                        if written > max_bytes:
                            return None, f'The backup is bigger than the {max_bytes // (1024 * 1024)} MB limit.'
                        out.write(chunk)
    except (zipfile.BadZipFile, OSError, RuntimeError, NotImplementedError):
        return None, 'That backup could not be read (damaged or unsupported zip).'
    try:
        manifest_path = os.path.join(payload_dir, 'manifest.json')
        if os.path.getsize(manifest_path) > 2 * 1024 * 1024:
            return None, 'The backup manifest is too big.'
        with open(manifest_path, 'r', encoding='utf-8') as handle:
            manifest = json.load(handle)
    except (OSError, ValueError):
        return None, 'The backup manifest could not be read.'
    if not isinstance(manifest, dict):
        return None, 'The backup manifest could not be read.'
    try:
        if int(manifest.get('version', 0)) > BACKUP_VERSION:
            return None, 'This backup was made by a newer version of the bot.'
    except (TypeError, ValueError):
        return None, 'The backup manifest could not be read.'
    return manifest, ''


def _inspect_hosting_db(path):
    """Check a file really is a hosting-bot database. Returns (ok, message, counts)."""
    try:
        with open(path, 'rb') as handle:
            if handle.read(16) != SQLITE_MAGIC:
                return False, 'The database inside the backup is not a SQLite database.', None
        conn = sqlite3.connect(path, timeout=10)
        try:
            result = conn.execute('PRAGMA integrity_check').fetchone()
            if not result or result[0] != 'ok':
                return False, 'The database inside the backup is damaged, so I did not restore it.', None
            tables = {row[0] for row in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        finally:
            conn.close()
        missing = [t for t in HOSTING_DB_CORE_TABLES if t not in tables]
        if missing:
            return False, ('The database inside the backup does not look like one from this hosting bot '
                           f'(missing: {", ".join(missing)}). Nothing was changed.'), None
        return True, '', _db_counts(path)
    except sqlite3.Error:
        return False, 'The database inside the backup could not be read. Nothing was changed.', None


def _full_rel_ok(rel):
    parts = rel.split('/')
    if parts[0] == 'source':
        return len(parts) == 2 and parts[1].endswith('.py')
    if parts[0] == 'database':
        return rel == 'database/bot_data.db'
    if parts[0] == 'upload_bots':
        return len(parts) >= 3 and parts[1].isdigit() and len(parts[1]) <= 19
    return False


def _inspect_full_backup(zip_path, payload_dir):
    """Validate + extract a full backup. Returns (ok, error_text, info)."""
    manifest, err = _extract_backup_zip(zip_path, payload_dir, _full_rel_ok, FULL_BACKUP_MAX_MB * 1024 * 1024)
    if err:
        return False, err, None
    if manifest.get('format') != BACKUP_FORMAT_FULL:
        return False, ('This is not a full backup. Use <b>Export Full Backup</b> in the admin panel '
                       'to make one.'), None
    db_path = os.path.join(payload_dir, 'database', 'bot_data.db')
    if not os.path.isfile(db_path):
        return False, 'The backup has no database in it.', None
    ok, problem, counts = _inspect_hosting_db(db_path)
    if not ok:
        return False, problem, None
    source_path = source_name = None
    source_dir = os.path.join(payload_dir, 'source')
    if os.path.isdir(source_dir):
        names = [n for n in os.listdir(source_dir) if n.endswith('.py')]
        if len(names) != 1:
            return False, 'The backup should hold exactly one bot code file.', None
        source_name = names[0]
        source_path = os.path.join(source_dir, source_name)
        try:
            if os.path.getsize(source_path) > 8 * 1024 * 1024:
                return False, 'The bot code file inside the backup is too big.', None
            with open(source_path, 'rb') as handle:
                text = handle.read().decode('utf-8')
            compile(text, source_name, 'exec')     # syntax check only; nothing is executed
        except (UnicodeDecodeError, SyntaxError, ValueError, OSError):
            return False, ('The bot code inside the backup does not compile, so I did not restore it. '
                           'Nothing was changed.'), None
    users = {}
    upload_root = os.path.join(payload_dir, 'upload_bots')
    if os.path.isdir(upload_root):
        for uid_text in sorted(os.listdir(upload_root)):
            count = sum(len(files) for _d, _n, files in os.walk(os.path.join(upload_root, uid_text)))
            users[uid_text] = count
    info = {'counts': counts, 'users': users, 'files': sum(users.values()),
            'source_path': source_path, 'source_name': source_name,
            'created': str(manifest.get('created', ''))[:19]}
    return True, '', info


def _user_rel_ok(rel):
    parts = rel.split('/')
    return parts[0] == 'bots' and len(parts) >= 2


def _inspect_user_backup(zip_path, payload_dir, owner_id, importer_id):
    """Validate + extract a single user's backup for owner_id. Returns (ok, error_text, info)."""
    manifest, err = _extract_backup_zip(zip_path, payload_dir, _user_rel_ok, USER_BACKUP_MAX_MB * 1024 * 1024)
    if err:
        return False, err, None
    if manifest.get('format') != BACKUP_FORMAT_USER:
        return False, ('This is not a "My Bots" backup. Use the <b>Export My Bots</b> button '
                       'in My Files to make one.'), None
    if manifest.get('owner') != owner_id:
        return False, 'This backup belongs to a different account, so I cannot restore it here.', None
    bots_root = os.path.join(payload_dir, 'bots')
    files = []
    for dirpath, _dirs, names in os.walk(bots_root):
        for name in names:
            files.append(os.path.relpath(os.path.join(dirpath, name), bots_root).replace(os.sep, '/'))
    files.sort()
    if not files:
        return False, 'That backup has no files in it.', None
    # Databases must really be databases, so a bad file cannot break the bot.
    for rel in files:
        if rel.lower().endswith(SQLITE_EXTS):
            full = os.path.join(bots_root, rel)
            try:
                with open(full, 'rb') as handle:
                    magic_ok = handle.read(16) == SQLITE_MAGIC
                if not magic_ok:
                    return False, f'"{rel}" is not a valid SQLite database.', None
                conn = sqlite3.connect(full, timeout=10)
                try:
                    result = conn.execute('PRAGMA integrity_check').fetchone()
                finally:
                    conn.close()
                if not result or result[0] != 'ok':
                    return False, f'"{rel}" is a damaged database.', None
            except sqlite3.Error:
                return False, f'"{rel}" could not be read as a database.', None
    scripts = []
    for entry in manifest.get('scripts') or []:
        name = entry.get('name') if isinstance(entry, dict) else None
        ftype = entry.get('type') if isinstance(entry, dict) else None
        if (not isinstance(name, str) or '/' in name or '\\' in name or not _safe_zip_rel(name)
                or ftype not in ('py', 'js') or not name.lower().endswith('.' + ftype)):
            continue
        if name in files:
            scripts.append((name, ftype))
    existing = {item[0] for item in user_files.get(owner_id, [])}
    new_scripts = [s for s in scripts if s[0] not in existing]
    limit = get_user_file_limit(owner_id)
    if len(existing) + len(new_scripts) > limit:
        return False, (f'Restoring would put you over your file limit ({len(existing)} now + {len(new_scripts)} new, '
                       f'limit {limit}). Delete a bot first or ask an admin. Nothing was changed.'), None
    # Only clearly harmful (HIGH) code is refused on import. Anything else is checked again by the launch gate when it is started.
    # Admins are trusted and may restore everything.
    if importer_id not in admin_ids:
        for rel in files:
            ext = os.path.splitext(rel)[1].lower()
            if ext not in ('.py', '.js'):
                continue
            try:
                with open(os.path.join(bots_root, rel), 'rb') as handle:
                    verdict = scan_bytes(handle.read(SCAN_MAX_SOURCE_BYTES + 1), ext[1:], rel)
            except OSError:
                continue
            if verdict['level'] == THREAT_HIGH:
                reasons = [r['text'] for r in verdict['reasons'][:2]]
                return False, (f'"{rel}" mein khatarnak code mila ({"; ".join(reasons)}). '
                               'Nothing was changed.'), None
    info = {'files': files, 'scripts': scripts, 'new_scripts': len(new_scripts), 'bots_root': bots_root,
            'existing_files': sum(1 for rel in files if os.path.isfile(os.path.join(get_user_folder(owner_id), rel))),
            'created': str(manifest.get('created', ''))[:19]}
    return True, '', info


# --- Stopping scripts before a restore -----------------------------------------
def _stop_scripts(owner_id=None):
    """Stop running scripts (all, or one user's) without letting the watchdog bring them back."""
    with STATE_LOCK:
        items = [(key, info) for key, info in bot_scripts.items()
                 if owner_id is None or key.startswith(f'{owner_id}_')]
    for key, info in items:
        RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        try:
            kill_process_tree(info)
        except Exception:
            logger.exception("Could not stop %s before restore", key)
        _forget_script(key)
    return len(items)


# --- Admin: full backup ----------------------------------------------------------
def _reload_memory_state():
    """After a database restore: reload the in-memory copies from the new database."""
    with STATE_LOCK:
        user_subscriptions.clear()
        user_files.clear()
        active_users.clear()
        admin_ids.clear()
        admin_ids.update({ADMIN_ID, OWNER_ID})
        banned_users.clear()
        user_limits.clear()
        mandatory_channels.clear()
        load_data()
    _reviews_load()


def _replace_live_database(source_path):
    """Overwrite the live database with source_path (SQLite backup API, safe while in use) and reload memory."""
    with DB_LOCK:
        source = sqlite3.connect(source_path, timeout=30)
        try:
            dest = db_connect()
            try:
                try:
                    dest.execute('PRAGMA journal_mode=DELETE')
                except sqlite3.Error:
                    pass
                source.backup(dest)
            finally:
                dest.close()
        finally:
            source.close()
        init_db()            # missing tables are created and the owner / main admin are always kept
        _reload_memory_state()


def full_backup_callback(call):
    """Send ONE zip: bot source code + database + every user's uploaded bots and data."""
    if not _can_backup_global(call.from_user.id):
        bot.answer_callback_query(call.id, '⚠️ Only the owner can export the full backup.', show_alert=True)
        return
    if not BACKUP_OP_LOCK.acquire(blocking=False):
        bot.answer_callback_query(call.id, '⏳ Another backup or restore is running. Try again in a minute.', show_alert=True)
        return
    tmp_dir = tempfile.mkdtemp(prefix='demon_fullexport_')
    try:
        bot.answer_callback_query(call.id, 'Preparing the full backup...')
        bot.send_message(call.message.chat.id, '⏳ Building the full backup (code + database + all users\' bots and data)...')
        base = f'demon_full_backup_{_now_stamp()}'
        zip_path = os.path.join(tmp_dir, base + '.zip')
        try:
            summary = _build_full_backup(zip_path)
        except BackupTooLarge:
            bot.send_message(call.message.chat.id,
                             f'⚠️ The data is bigger than the backup limit ({FULL_BACKUP_MAX_MB} MB). '
                             'The limit can be raised with FULL_BACKUP_MAX_MB.')
            return
        counts = summary['counts']
        caption = ('<b>📦 Full Backup</b>\n'
                   f'Bot code: <code>{html_escape(summary["source_name"])}</code>\n'
                   f'Database: {counts[0]} users, {counts[1]} scripts, {counts[2]} subscriptions, {counts[3]} admins\n'
                   f'Users\' bots and data: {summary["users"]} users, {summary["files"]} files\n'
                   f'Size: {_human_size(os.path.getsize(zip_path))}\n\n'
                   'Keep it safe (it holds everyone\'s code and data). Use <b>Import Full Backup</b> to restore it.')
        sent = _send_backup_file(call.message.chat.id, zip_path, base, caption)
        if not sent:
            bot.send_message(call.message.chat.id,
                             '⚠️ The backup is too big to send through Telegram, even in parts. '
                             'Copy the data folder from the server instead.')
        logger.info("Full backup exported by admin %s (%s users, %s files, %s part(s))",
                    call.from_user.id, summary['users'], summary['files'], sent)
    except Exception as exc:
        logger.exception('Full backup export failed')
        bot.send_message(call.message.chat.id,
                         f'⚠️ Full backup failed: <code>{html_escape(str(exc)[:300])}</code>', parse_mode='HTML')
    finally:
        BACKUP_OP_LOCK.release()
        _rmtree_quiet(tmp_dir)


def _start_waiting(call, kind, owner_id, title, body):
    bot.answer_callback_query(call.id)
    _expire_pending_imports()
    with IMPORT_LOCK:
        old = PENDING_IMPORT_WAIT.pop(call.from_user.id, None)
        PENDING_IMPORT_WAIT[call.from_user.id] = {'kind': kind, 'owner': owner_id, 'time': time.time(),
                                                  'dir': None, 'parts': {}}
    if old:
        _rmtree_quiet(old.get('dir'))
    bot.send_message(call.message.chat.id, f'<b>{title}</b>\n{body}\nThe request expires in {IMPORT_TTL // 60} minutes.',
                     parse_mode='HTML', reply_markup=_cancel_markup())


def full_restore_callback(call):
    if not _can_backup_global(call.from_user.id):
        bot.answer_callback_query(call.id, '⚠️ Only the owner can import the full backup.', show_alert=True)
        return
    _start_waiting(
        call, 'full', None, '♻️ Import Full Backup',
        'Send me the full backup <code>.zip</code> you exported earlier (as a file). If it came in parts '
        '(<code>.zip.001</code>, <code>.zip.002</code> ...), send every part, then tap <b>Done</b>.\n\n'
        '⚠️ This restores <b>everything</b>: the database, every user\'s bots and data (back into each user\'s '
        'own folder), and the bot code file. I will show you a summary and ask you to confirm first. '
        'A backup of the current state is saved automatically before anything is overwritten.')


# --- User: My Bots backup -------------------------------------------------------
def _user_target(call):
    """Parse 'ubk_<owner>' / 'ubr_<owner>' and check the requester may manage that folder."""
    try:
        owner_id = int(call.data.split('_', 1)[1])
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, 'Error: invalid action data.', show_alert=True)
        return None
    if not _may_manage_bot_data(call.from_user.id, owner_id):
        logger.warning("User %s tried a bot backup for user %s", call.from_user.id, owner_id)
        bot.answer_callback_query(call.id, '⚠️ You can only export or import your own bots.', show_alert=True)
        return None
    return owner_id


def user_backup_callback(call):
    """Send ONE zip with this user's own bots (scripts) and their data."""
    owner_id = _user_target(call)
    if owner_id is None:
        return
    if not BACKUP_OP_LOCK.acquire(blocking=False):
        bot.answer_callback_query(call.id, '⏳ Another backup is running. Try again in a minute.', show_alert=True)
        return
    tmp_dir = tempfile.mkdtemp(prefix=f'demon_userexport_{owner_id}_')
    try:
        bot.answer_callback_query(call.id, 'Preparing your backup...')
        base = f'my_bots_backup_{owner_id}_{_now_stamp()}'
        zip_path = os.path.join(tmp_dir, base + '.zip')
        try:
            summary = _build_user_backup(owner_id, zip_path)
        except BackupTooLarge:
            bot.send_message(call.message.chat.id,
                             f'⚠️ Your bots and data are bigger than the backup limit ({USER_BACKUP_MAX_MB} MB).')
            return
        if not summary['files']:
            bot.send_message(call.message.chat.id, '⚠️ You have no bots or data to export yet.')
            return
        caption = ('<b>📦 My Bots backup</b>\n'
                   f'{summary["scripts"]} bot(s), {summary["files"]} file(s) (your bot code and its data), '
                   f'{_human_size(os.path.getsize(zip_path))}\n\n'
                   'Use <b>Import My Bots</b> in My Files to restore it.')
        sent = _send_backup_file(call.message.chat.id, zip_path, base, caption)
        if not sent:
            bot.send_message(call.message.chat.id, '⚠️ Your backup is too big to send through Telegram.')
        logger.info("User backup exported: owner=%s by=%s files=%s", owner_id, call.from_user.id, summary['files'])
    except Exception as exc:
        logger.exception('User backup export failed')
        bot.send_message(call.message.chat.id,
                         f'⚠️ Export failed: <code>{html_escape(str(exc)[:300])}</code>', parse_mode='HTML')
    finally:
        BACKUP_OP_LOCK.release()
        _rmtree_quiet(tmp_dir)


def user_restore_callback(call):
    owner_id = _user_target(call)
    if owner_id is None:
        return
    _start_waiting(
        call, 'user', owner_id, '♻️ Import My Bots',
        'Send me the <code>.zip</code> you exported with <b>Export My Bots</b> (as a file). If it came in parts '
        '(<code>.zip.001</code>, <code>.zip.002</code> ...), send every part, then tap <b>Done</b>.\n\n'
        '⚠️ Your bots and data go back into your own folder only; files with the same name are replaced. '
        'Your running bots are stopped for the restore. I will show you a summary and ask you to confirm first, '
        'and your current files are backed up automatically (and sent to you).')


# --- Receiving the uploaded backup (single zip or parts) --------------------------
def _say(chat_id, text, markup=None):
    return bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=markup)


def _wait_permission_ok(uid, pend):
    if pend['kind'] == 'full':
        return _can_backup_global(uid)
    return _may_manage_bot_data(uid, pend['owner'])


def _discard_wait(uid):
    with IMPORT_LOCK:
        pend = PENDING_IMPORT_WAIT.pop(uid, None)
    if pend:
        _rmtree_quiet(pend.get('dir'))
    return pend


def _receive_backup_upload(message, pend):
    uid = message.from_user.id
    chat_id = message.chat.id
    if not _wait_permission_ok(uid, pend):
        _discard_wait(uid)
        _say(chat_id, '⚠️ You are not allowed to do this restore. Nothing was changed.')
        return
    name = message.document.file_name or ''
    part = PART_RE.search(name)
    if not part and not name.lower().endswith('.zip'):
        _say(chat_id, '⚠️ Please send the backup <code>.zip</code> (or its <code>.zip.001</code>, '
                      '<code>.zip.002</code> parts). Nothing was changed.', _cancel_markup())
        return
    try:
        content = _download_upload(message, MAX_UPLOAD_MB)
    except ValueError as exc:
        _say(chat_id, f'⚠️ {html_escape(str(exc))}', _cancel_markup())
        return
    except Exception as exc:
        logger.warning("Backup download failed: %s", redact_secrets(exc))
        _say(chat_id, '⚠️ I could not download that file. Please try again.', _cancel_markup())
        return
    with IMPORT_LOCK:
        if not pend.get('dir'):
            pend['dir'] = tempfile.mkdtemp(prefix='demon_restore_')
        work = pend['dir']
        pend['time'] = time.time()
    if part:
        number = int(part.group(1))
        if number < 1 or number > MAX_PARTS:
            _say(chat_id, '⚠️ That part number is not valid.', _cancel_markup())
            return
        part_path = os.path.join(work, f'part_{number:03d}')
        with open(part_path, 'wb') as handle:
            handle.write(content)
        pend['parts'][number] = part_path
        have = ', '.join(str(n) for n in sorted(pend['parts']))
        _say(chat_id, f'✅ Part {number} received. Parts so far: {have}.\n'
                      'Send the next part, or tap <b>Done</b> when you have sent all of them.', _parts_markup())
        return
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT.pop(uid, None)
    zip_path = os.path.join(work, 'upload.zip')
    with open(zip_path, 'wb') as handle:
        handle.write(content)
    _stage_backup(chat_id, uid, pend, zip_path)


def _assemble_parts(pend):
    """Join the received parts into one zip. Returns (zip_path, error_text)."""
    numbers = sorted(pend['parts'])
    if numbers != list(range(1, numbers[-1] + 1)):
        missing = [str(n) for n in range(1, numbers[-1] + 1) if n not in pend['parts']]
        return None, f'Part(s) missing: {", ".join(missing)}. Send them, then tap Done again.'
    limit = (FULL_BACKUP_MAX_MB if pend['kind'] == 'full' else USER_BACKUP_MAX_MB) * 1024 * 1024
    zip_path = os.path.join(pend['dir'], 'upload.zip')
    total = 0
    with open(zip_path, 'wb') as out:
        for number in numbers:
            with open(pend['parts'][number], 'rb') as src:
                while True:
                    chunk = src.read(1024 * 1024)
                    if not chunk:
                        break
                    total += len(chunk)
                    if total > limit:
                        return None, 'The parts together are bigger than the backup size limit.'
                    out.write(chunk)
            os.remove(pend['parts'][number])
    return zip_path, ''


def _stage_backup(chat_id, uid, pend, zip_path):
    """Validate the uploaded zip and ask for confirmation. Owns pend['dir'] from here on."""
    work = pend['dir']
    keep = False
    try:
        payload = os.path.join(work, 'payload')
        os.makedirs(payload, exist_ok=True)
        if pend['kind'] == 'full':
            ok, problem, info = _inspect_full_backup(zip_path, payload)
        else:
            ok, problem, info = _inspect_user_backup(zip_path, payload, pend['owner'], uid)
        if not ok:
            _say(chat_id, f'⚠️ {problem} Nothing was changed.')
            return
        try:
            os.remove(zip_path)
        except OSError:
            pass
        if pend['kind'] == 'full':
            counts = info['counts']
            now = _db_counts(DATABASE_PATH)
            code_line = (f'• Bot code: <code>{html_escape(info["source_name"])}</code> (replaced on disk; the old '
                         'file is kept next to it as a .bak copy and the new code is used after the next restart)'
                         if info['source_path'] else '• Bot code: not in this backup, stays as it is')
            text = ('<b>⚠️ Confirm full restore</b>'
                    + (f' (backup from {html_escape(info["created"])})' if info['created'] else '') + '\n\n'
                    f'<b>In the backup:</b> {counts[0]} users, {counts[1]} scripts, {counts[2]} subscriptions, '
                    f'{counts[3]} admins; {len(info["users"])} user folder(s) with {info["files"]} files\n'
                    f'<b>Live now:</b> {now[0]} users, {now[1]} scripts, {now[2]} subscriptions, {now[3]} admins\n\n'
                    'This will replace:\n'
                    '• The whole database\n'
                    f'• Each of the {len(info["users"])} user folders (every user\'s bots and data go back to that same user)\n'
                    f'{code_line}\n\n'
                    'All running bots are stopped. A full backup of the current state is saved first and sent to you. Continue?')
            entry = {'kind': 'full', 'user_id': uid, 'dir': work, 'payload': payload, 'info': info}
        else:
            text = ('<b>⚠️ Confirm restore of your bots</b>'
                    + (f' (backup from {html_escape(info["created"])})' if info['created'] else '') + '\n\n'
                    f'{len(info["files"])} file(s), {len(info["scripts"])} bot(s) '
                    f'({info["new_scripts"]} not in your list yet). '
                    f'{info["existing_files"]} existing file(s) with the same name will be replaced.\n'
                    'Your running bots will be stopped. Your current files are backed up first and sent to you. Continue?')
            entry = {'kind': 'user', 'user_id': uid, 'owner': pend['owner'], 'dir': work, 'payload': payload,
                     'info': info}
        token = _store_confirm(entry)
        keep = True
        _say(chat_id, text, _confirm_markup(token))
    except Exception:
        logger.exception('Restore staging failed')
        _say(chat_id, '⚠️ Something went wrong while checking that backup. Nothing was changed.')
    finally:
        if not keep:
            _rmtree_quiet(work)


def _handle_pending_import_upload(message):
    """Called first by the document handler. True when the document belonged to a waiting restore."""
    uid = message.from_user.id
    with IMPORT_LOCK:
        _expire_pending_imports()
        pend = PENDING_IMPORT_WAIT.get(uid)
    if not pend:
        return False
    try:
        _receive_backup_upload(message, pend)
    except Exception:
        logger.exception('Restore upload failed')
        _discard_wait(uid)
        bot.reply_to(message, '⚠️ Something went wrong while checking that file. Nothing was changed.')
    return True


# --- Applying a restore -----------------------------------------------------------
def _install_restored_source(source_path):
    """Put the restored bot code on disk for the next start. The running process keeps its already loaded
    code, so nothing breaks now. The old file is kept as a .bak copy. Returns (status, name)."""
    if not source_path:
        return 'none', ''
    live = os.path.abspath(__file__)
    with open(source_path, 'rb') as handle:
        new_bytes = handle.read()
    try:
        with open(live, 'rb') as handle:
            if handle.read() == new_bytes:
                return 'same', os.path.basename(live)
    except OSError:
        pass
    stamp = _now_stamp()
    try:
        if os.path.isfile(live):
            shutil.copy2(live, f'{live}.bak_{stamp}')
        tmp_path = f'{live}.new_{os.urandom(4).hex()}'
        try:
            with open(tmp_path, 'wb') as handle:
                handle.write(new_bytes)
            os.replace(tmp_path, live)
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        _prune_backups(os.path.dirname(live), os.path.basename(live) + '.bak_')
        return 'replaced', os.path.basename(live)
    except OSError as exc:
        logger.warning("Could not overwrite the bot code file (%s); saving it next to it instead", exc)
        stem = os.path.splitext(os.path.basename(live))[0]
        aside = os.path.join(os.path.dirname(live), f'{stem}_restored_{stamp}.py')
        with open(aside, 'wb') as handle:
            handle.write(new_bytes)
        return 'saved_aside', os.path.basename(aside)


def _apply_full_restore(entry):
    """Safety backup -> database -> user folders -> bot code. Returns a result dict."""
    info = entry['info']
    payload = entry['payload']
    os.makedirs(FULL_BACKUP_DIR, exist_ok=True)
    stopped = _stop_scripts()
    pre_path = os.path.join(FULL_BACKUP_DIR, f'full_backup_before_restore_{_now_stamp()}.zip')
    _build_full_backup(pre_path, limit_mb=None)       # nothing is touched if this fails
    _prune_backups(FULL_BACKUP_DIR, 'full_backup_before_restore_')
    prev_db = os.path.join(entry['dir'], 'previous_bot_data.db')
    _snapshot_live_database(prev_db)
    incoming = tempfile.mkdtemp(prefix='.restore_in_', dir=UPLOAD_BOTS_DIR)
    old_dir = tempfile.mkdtemp(prefix='.restore_old_', dir=UPLOAD_BOTS_DIR)
    swapped = []
    db_replaced = False
    try:
        upload_root = os.path.join(payload, 'upload_bots')
        for uid_text in sorted(info['users']):
            shutil.move(os.path.join(upload_root, uid_text), os.path.join(incoming, uid_text))
        _replace_live_database(os.path.join(payload, 'database', 'bot_data.db'))
        db_replaced = True
        for uid_text in sorted(info['users']):
            target = os.path.join(UPLOAD_BOTS_DIR, uid_text)
            if os.path.lexists(target):
                os.rename(target, os.path.join(old_dir, uid_text))
            swapped.append(uid_text)
            os.rename(os.path.join(incoming, uid_text), target)
    except Exception:
        rollback_ok = True
        for uid_text in reversed(swapped):          # put every folder back the way it was
            target = os.path.join(UPLOAD_BOTS_DIR, uid_text)
            saved = os.path.join(old_dir, uid_text)
            try:
                if os.path.lexists(saved):
                    _rmtree_quiet(target)
                    os.rename(saved, target)
            except OSError:
                rollback_ok = False
                logger.exception("Could not roll back folder %s (original kept in %s)", uid_text, old_dir)
        if db_replaced:
            try:
                _replace_live_database(prev_db)
            except Exception:
                logger.exception("Could not roll back the database")
        _rmtree_quiet(incoming)
        if rollback_ok:
            _rmtree_quiet(old_dir)
        raise
    _rmtree_quiet(incoming)
    _rmtree_quiet(old_dir)
    try:
        source_status, source_name = _install_restored_source(info['source_path'])
    except Exception:
        logger.exception("Bot code could not be restored")
        source_status, source_name = 'failed', ''
    missing = 0
    for owner_id, items in list(user_files.items()):
        for file_name, _ftype in list(items):
            if not os.path.isfile(os.path.join(UPLOAD_BOTS_DIR, str(owner_id), file_name)):
                missing += 1
    return {'pre_path': pre_path, 'stopped': stopped, 'source_status': source_status,
            'source_name': source_name, 'missing': missing}


def _apply_user_restore(entry):
    """Back up the user's current folder, then write the staged files into their own folder only."""
    owner_id = entry['owner']
    info = entry['info']
    root = os.path.realpath(get_user_folder(owner_id))
    upload_root = os.path.realpath(UPLOAD_BOTS_DIR)
    if root == upload_root or not _path_inside(upload_root, root) or os.path.basename(root) != str(owner_id):
        raise RuntimeError('Your folder could not be verified.')
    stopped = _stop_scripts(owner_id)
    pre_path = None
    backup_dir = os.path.join(USER_BACKUP_DIR, str(owner_id))
    os.makedirs(backup_dir, exist_ok=True)
    candidate = os.path.join(backup_dir, f'my_bots_before_restore_{_now_stamp()}.zip')
    if _build_user_backup(owner_id, candidate, limit_mb=None)['files']:
        pre_path = candidate
        _prune_backups(backup_dir, 'my_bots_before_restore_')
    else:
        os.remove(candidate)
    written = 0
    for rel in info['files']:
        src = os.path.join(info['bots_root'], rel)
        dest = os.path.join(root, rel)
        dest_dir = os.path.dirname(dest)
        os.makedirs(dest_dir, exist_ok=True)
        if not _path_inside(root, os.path.realpath(dest_dir)):
            raise RuntimeError('Unsafe target folder.')
        tmp_target = os.path.join(dest_dir, f'.import_{os.urandom(4).hex()}.tmp')
        try:
            shutil.copyfile(src, tmp_target)
            os.replace(tmp_target, dest)
        finally:
            if os.path.exists(tmp_target):
                try:
                    os.remove(tmp_target)
                except OSError:
                    pass
        if rel.lower().endswith(SQLITE_EXTS):
            for suffix in ('-wal', '-shm', '-journal'):   # stale side files would corrupt the restored database
                try:
                    os.remove(dest + suffix)
                except OSError:
                    pass
        written += 1
    for name, ftype in info['scripts']:
        save_user_file(owner_id, name, ftype)
    return {'pre_path': pre_path, 'stopped': stopped, 'written': written}


def import_confirm_callback(call):
    uid = call.from_user.id
    if call.data == 'impc_cancel':
        _discard_wait(uid)
        bot.answer_callback_query(call.id, 'Cancelled.')
        _edit_or_send(call, '❌ Cancelled. Nothing was changed.')
        return
    if call.data == 'impc_done':
        _finish_parts(call)
        return
    try:
        _, action, token = call.data.split('_', 2)
    except ValueError:
        bot.answer_callback_query(call.id, 'Invalid action.', show_alert=True)
        return
    with IMPORT_LOCK:
        _expire_pending_imports()
        entry = PENDING_IMPORT_CONFIRM.get(token)
        if not entry:
            bot.answer_callback_query(call.id, '⚠️ This request expired. Start the restore again.', show_alert=True)
            return
        if entry['user_id'] != uid:
            bot.answer_callback_query(call.id, '⚠️ This is not your request.', show_alert=True)
            return
        PENDING_IMPORT_CONFIRM.pop(token, None)      # one use only
    try:
        if action != 'yes':
            bot.answer_callback_query(call.id, 'Cancelled.')
            _edit_or_send(call, '❌ Cancelled. Nothing was changed.')
            return
        if not BACKUP_OP_LOCK.acquire(blocking=False):
            with IMPORT_LOCK:                 # keep the staged restore so the same button can be tapped again
                PENDING_IMPORT_CONFIRM[token] = entry
            entry = {}
            bot.answer_callback_query(call.id, '⏳ Another backup or restore is running. Tap Yes again in a minute.', show_alert=True)
            return
        try:
            bot.answer_callback_query(call.id, 'Restoring...')
            _edit_or_send(call, '⏳ Restoring... please wait, this can take a minute.')
            if entry['kind'] == 'full':
                _confirm_full_restore(call, entry)
            else:
                _confirm_user_restore(call, entry)
        finally:
            BACKUP_OP_LOCK.release()
    finally:
        _rmtree_quiet(entry.get('dir'))


def _finish_parts(call):
    uid = call.from_user.id
    with IMPORT_LOCK:
        pend = PENDING_IMPORT_WAIT.get(uid)
    if not pend or not pend.get('parts'):
        bot.answer_callback_query(call.id, '⚠️ No parts received yet. Send the backup file(s) first.', show_alert=True)
        return
    if not _wait_permission_ok(uid, pend):
        _discard_wait(uid)
        bot.answer_callback_query(call.id, '⚠️ You are not allowed to do this restore.', show_alert=True)
        return
    try:
        zip_path, problem = _assemble_parts(pend)
    except OSError:
        zip_path, problem = None, 'I could not join the parts.'
    if not zip_path:
        bot.answer_callback_query(call.id, f'⚠️ {problem}', show_alert=True)
        return
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT.pop(uid, None)
    bot.answer_callback_query(call.id, 'Checking the backup...')
    _stage_backup(call.message.chat.id, uid, pend, zip_path)


def _send_safety_backup(chat_id, pre_path, caption):
    if not pre_path:
        return
    try:
        base = os.path.splitext(os.path.basename(pre_path))[0]
        sent = _send_backup_file(chat_id, pre_path, base, caption)
        if not sent:
            _say(chat_id, 'The safety backup is too big for Telegram; it is kept on the server '
                          f'(<code>{html_escape(os.path.relpath(pre_path, BASE_DIR))}</code>).')
    except Exception:
        logger.exception('Could not send the safety backup')


def _confirm_full_restore(call, entry):
    uid = call.from_user.id
    if not _can_backup_global(uid):
        _edit_or_send(call, '⚠️ Only the owner can restore the full backup. Nothing was changed.')
        return
    try:
        result = _apply_full_restore(entry)
    except Exception as exc:
        logger.exception('Full restore failed')
        _edit_or_send(call, ('❌ Restore failed. The database and user folders were put back the way they were.\n'
                             f'<code>{html_escape(str(exc)[:300])}</code>'))
        return
    logger.warning("Full backup restored by admin %s; safety backup at %s", uid, result['pre_path'])
    info = entry['info']
    lines = ['✅ <b>Full backup restored.</b>',
             f'• Database: {len(active_users)} users, {sum(len(v) for v in user_files.values())} scripts, '
             f'{len(user_subscriptions)} subscriptions, {len(admin_ids)} admins',
             f'• Bots and data: {len(info["users"])} user folder(s), {info["files"]} files, each back in its own user\'s folder']
    status = result['source_status']
    if status == 'replaced':
        lines.append(f'• Bot code: <code>{html_escape(result["source_name"])}</code> replaced on disk '
                     '(old copy kept as .bak). <b>Restart the bot to start using it.</b>')
    elif status == 'same':
        lines.append('• Bot code: identical to the running one, nothing to change.')
    elif status == 'saved_aside':
        lines.append(f'• Bot code: could not overwrite the running file, so it was saved as '
                     f'<code>{html_escape(result["source_name"])}</code> next to it. Swap it in and restart when you are ready.')
    elif status == 'failed':
        lines.append('• Bot code: could not be restored (the data parts are fine).')
    else:
        lines.append('• Bot code: not in this backup.')
    if result['stopped']:
        lines.append(f'• {result["stopped"]} running bot(s) were stopped; start them again from My Files or Run All.')
    if result['missing']:
        lines.append(f'• {result["missing"]} script(s) in the list have no file on disk.')
    lines.append('The state from before the restore was saved and is attached below.')
    _edit_or_send(call, '\n'.join(lines))
    _send_safety_backup(call.message.chat.id, result['pre_path'], 'Backup of everything as it was before this restore.')


def _confirm_user_restore(call, entry):
    uid = call.from_user.id
    owner_id = entry['owner']
    if not _may_manage_bot_data(uid, owner_id):
        _edit_or_send(call, '⚠️ You can only restore your own bots. Nothing was changed.')
        return
    try:
        result = _apply_user_restore(entry)
    except Exception as exc:
        logger.exception('User restore failed')
        _edit_or_send(call, ('❌ Restore failed. Some files may not have been replaced; your previous files '
                             'are in the backup that was made first.\n'
                             f'<code>{html_escape(str(exc)[:300])}</code>'))
        return
    logger.info("User backup restored: owner=%s by=%s files=%s", owner_id, uid, result['written'])
    text = (f'✅ <b>Your bots were restored</b>: {result["written"]} file(s) are back in your folder '
            f'and {len(user_files.get(owner_id, []))} bot(s) are listed in My Files.\nStart your bots again to use them.')
    if result['pre_path']:
        text += '\nYour previous files were backed up and are attached below.'
    _edit_or_send(call, text)
    _send_safety_backup(call.message.chat.id, result['pre_path'], 'Backup of your files as they were before this restore.')


def create_control_buttons(script_owner_id, file_name, is_running=True):
    markup = NavMenu(row_width=2)
    if is_running:
        markup.row(
            NavButton("🔴 Stop", callback_data=f'stop_{script_owner_id}_{file_name}'),
            NavButton("🔄 Restart", callback_data=f'restart_{script_owner_id}_{file_name}')
        )
        markup.row(
            NavButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}'),
            NavButton("📜 Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    else:
        markup.row(
            NavButton("🟢 Start", callback_data=f'start_{script_owner_id}_{file_name}'),
            NavButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}')
        )
        markup.row(
            NavButton("📜 View Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    try:
        if gh_read_sidecar(get_user_folder(script_owner_id), file_name)[0] is not None:
            markup.row(NavButton("🔄 Update from GitHub", callback_data=f'ghu_{script_owner_id}_{file_name}'))
    except Exception:
        pass
    markup.row(NavButton("🔑 Environment (.env)", callback_data=f'envm_{script_owner_id}_{file_name}'))
    markup.row(
        NavButton("📦 Export My Bots", callback_data=f'ubk_{script_owner_id}'),
        NavButton("♻️ Import My Bots", callback_data=f'ubr_{script_owner_id}')
    )
    markup.add(NavButton("🔙 Back to Files", callback_data='check_files'))
    return markup

def create_admin_panel():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Admin', callback_data='add_admin'),
        NavButton('➖ Remove Admin', callback_data='remove_admin')
    )
    markup.row(NavButton('📋 List Admins', callback_data='list_admins'),
               NavButton(f'📥 Approvals ({_pending_count()})', callback_data='adm_approvals'))
    markup.row(NavButton('🗄 Database Backup', callback_data='database_backup'),
               NavButton('📤 Export Users', callback_data='export_users'))
    markup.row(NavButton('📦 Export Full Backup', callback_data='export_database'),
               NavButton('♻️ Import Full Backup', callback_data='import_database'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_user_management_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('🚫 Ban User', callback_data='ban_user'),
        NavButton('✅ Unban User', callback_data='unban_user')
    )
    markup.row(
        NavButton('📊 User Info', callback_data='user_info'),
        NavButton('👥 All Users', callback_data='all_users')
    )
    markup.row(
        NavButton('🔧 Set User Limit', callback_data='set_user_limit'),
        NavButton('🗑️ Remove User Limit', callback_data='remove_user_limit')
    )
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Subscription', callback_data='add_subscription'),
        NavButton('➖ Remove Subscription', callback_data='remove_subscription')
    )
    markup.row(NavButton('🔍 Check Subscription', callback_data='check_subscription'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_admin_settings_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('📊 System Info', callback_data='system_info'),
        NavButton('📈 Bot Performance', callback_data='bot_performance')
    )
    markup.row(
        NavButton('🧹 Cleanup Files', callback_data='cleanup_files'),
        NavButton('📋 Installation Logs', callback_data='install_logs')
    )
    markup.row(
        NavButton('🩺 Hosting Health', callback_data='hosting_health'),
        NavButton('🔄 Retry Failed Bots', callback_data='retry_failed_bots')
    )
    markup.row(NavButton('👑 Admin Dashboard', callback_data='admin_dashboard'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

# --- File Handling ---
# =====================================================================================
# Deploy from GitHub (public repositories only)
# The repo is cloned into a NEW temp folder, only the important files are picked, packed into a zip
# (plus a signed manifest) and handed to the SAME scan / approval / zip-deploy code as a manual zip upload.
# Nothing from the repo is ever run before the scan and the start gate have passed.
# =====================================================================================
GH_CLONE_TIMEOUT = _env_int('GITHUB_CLONE_TIMEOUT', 120)      # seconds for clone / archive download
GH_MAX_REPO_MB = _env_int('GITHUB_MAX_REPO_MB', 100)          # size of the fresh clone (all of it, .git included)
GH_MAX_SELECTED_MB = _env_int('GITHUB_MAX_SELECTED_MB', 40)   # total size of the files that are kept
GH_MAX_FILES = _env_int('GITHUB_MAX_FILES', 600)              # number of files that are kept
GH_MAX_DATA_KB = 2048                                          # one json / yaml / txt / csv file
GH_MAX_ASSET_KB = 512                                          # one image / font
GH_PICK_TTL = 600                                              # seconds a "which file is the main one?" list waits
GH_GLOBAL_LIMIT = 2                                            # deploys running at the same time (all users)
GH_MANIFEST_NAME = '.demon_github.json'
GH_SIDECAR_SUFFIX = '.github.json'

GH_OWNER_RE = re.compile(r'^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$')
GH_REPO_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_BRANCH_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_SEG_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_CODE_EXTS = ('.py', '.js', '.mjs', '.cjs')
GH_DATA_EXTS = ('.json', '.yaml', '.yml', '.toml', '.ini', '.cfg', '.txt', '.csv', '.html', '.htm', '.css', '.jinja', '.j2')
GH_ASSET_EXTS = ('.png', '.jpg', '.jpeg', '.gif', '.svg', '.ico', '.webp', '.ttf', '.otf', '.woff', '.woff2')
GH_INFO_NAMES = ('package.json', 'package-lock.json', 'requirements.txt', 'runtime.txt', 'procfile',
                 '.env.example', '.env.sample', '.env.template')
GH_SKIP_DIRS = frozenset({'.git', '.github', '.gitlab', 'node_modules', 'venv', '.venv', 'env', '__pycache__', 'site-packages',
                          'tests', 'test', '__tests__', 'docs', 'doc', '.idea', '.vscode', '.pytest_cache', '.mypy_cache',
                          '.tox', '.cache', 'dist', 'build', '.next', 'coverage'})
GH_PROTECTED_SUFFIXES = ('.env', '.db', '.sqlite', '.sqlite3')
GH_UPDATE_CODE_EXTS = ('.py', '.js', '.mjs', '.cjs', '.html', '.htm', '.css', '.jinja', '.j2')
GH_UPDATE_CODE_NAMES = ('package.json', 'package-lock.json', 'requirements.txt', 'runtime.txt', 'procfile',
                        '.env.example', '.env.sample', '.env.template')

GH_LOCK = threading.Lock()
GH_ACTIVE_USERS = set()          # users with a deploy running or a picker waiting
GH_PENDING = {}                  # token -> picker context
GH_SLOTS = threading.BoundedSemaphore(GH_GLOBAL_LIMIT)


class GithubError(Exception):
    """A problem with a repo link or its content. .text is safe to show to the user."""
    def __init__(self, code, text):
        super().__init__(text)
        self.code = code
        self.text = text


def parse_github_url(text):
    """Strict check of a pasted GitHub link. Returns {'owner','repo','branch','subdir','url','clone_url'} or raises GithubError.
    Only https://github.com/<owner>/<repo>[.git][/tree/<branch>[/<subfolder>]] is accepted. The clone address is REBUILT from the
    validated owner and repo, the pasted text itself is never used for anything else."""
    bad = GithubError('url', 'Ye valid GitHub repo link nahi lag raha. Aisa bhejo: https://github.com/owner/repo '
                             '(sirf github.com, https, public repo).')
    raw = (text or '').strip()
    if raw.startswith('<') and raw.endswith('>'):
        raw = raw[1:-1].strip()
    if not raw or len(raw) > 300:
        raise bad
    if any(ch.isspace() or ord(ch) < 33 or ord(ch) > 126 for ch in raw):
        raise bad
    if '\\' in raw or '%' in raw or '@' in raw.split('github.com', 1)[0]:
        raise bad
    lowered = raw.lower()
    if lowered.startswith('http://'):
        raise GithubError('url', 'Sirf https link chalega (http nahi). Aisa bhejo: https://github.com/owner/repo')
    if lowered.startswith('github.com/') or lowered.startswith('www.github.com/'):
        raw = 'https://' + raw
    try:
        parts = urlsplit(raw)
    except ValueError:
        raise bad
    if parts.scheme.lower() != 'https' or (parts.hostname or '').lower() not in ('github.com', 'www.github.com'):
        raise bad
    try:
        port = parts.port
    except ValueError:
        raise bad
    if parts.username or parts.password or port:
        raise bad
    segs = [s for s in parts.path.split('/') if s != '']
    if len(segs) < 2:
        raise bad
    owner, repo = segs[0], segs[1]
    if repo.lower().endswith('.git'):
        repo = repo[:-4]
    if not GH_OWNER_RE.fullmatch(owner) or not GH_REPO_RE.fullmatch(repo) or repo in ('.', '..') or '..' in repo:
        raise bad
    branch, subdir = None, None
    rest = segs[2:]
    if rest:
        if rest[0] != 'tree' or len(rest) < 2 or len(rest) > 9:
            raise GithubError('url', 'Sirf repo ka link do (ya /tree/branch/folder wala link). Issues/blob/pull links nahi chalte.')
        branch = rest[1]
        if not GH_BRANCH_RE.fullmatch(branch) or '..' in branch or branch.endswith('.lock') or branch.endswith('.'):
            raise bad
        sub = rest[2:]
        for seg in sub:
            if not GH_SEG_RE.fullmatch(seg) or seg in ('.', '..') or '..' in seg:
                raise bad
        subdir = '/'.join(sub) or None
    base = f'https://github.com/{owner}/{repo}'
    return {'owner': owner, 'repo': repo, 'branch': branch, 'subdir': subdir, 'url': base, 'clone_url': base + '.git'}


def _gh_dir_size(path):
    total = 0
    for base, dirs, files in os.walk(path):
        for name in files:
            try:
                total += os.lstat(os.path.join(base, name)).st_size
            except OSError:
                pass
    return total


def _gh_git_env(home_dir):
    env = child_env()
    env.update({'GIT_TERMINAL_PROMPT': '0', 'GIT_ASKPASS': 'true', 'SSH_ASKPASS': 'true', 'GCM_INTERACTIVE': 'never',
                'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': os.devnull, 'GIT_LFS_SKIP_SMUDGE': '1',
                'GIT_OPTIONAL_LOCKS': '0', 'HOME': home_dir, 'XDG_CONFIG_HOME': home_dir, 'LC_ALL': 'C'})
    for name in list(env):
        if name.startswith('GIT_') and name not in ('GIT_TERMINAL_PROMPT', 'GIT_ASKPASS', 'GIT_CONFIG_NOSYSTEM', 'GIT_CONFIG_GLOBAL',
                                                    'GIT_LFS_SKIP_SMUDGE', 'GIT_OPTIONAL_LOCKS'):
            env.pop(name, None)
    return env


def gh_clone_command(url, dest, branch=None, local_test=False):
    """Argument list for the shallow clone (never a shell string). `--` keeps the address from being read as an option.
    local_test=True is only used by the tests to clone a file:// repo; users can never reach it."""
    protocol = ['-c', 'protocol.allow=never', '-c', 'protocol.https.allow=always']
    if local_test:
        protocol = ['-c', 'protocol.allow=never', '-c', 'protocol.file.allow=always']
    cmd = ['git', '-c', 'credential.helper=', '-c', 'core.hooksPath=' + os.devnull, '-c', 'core.symlinks=false',
           '-c', 'core.fsmonitor=false', '-c', 'submodule.recurse=false', '-c', 'http.followRedirects=false'] + protocol
    cmd += ['clone', '--depth', '1', '--single-branch', '--no-tags', '--no-recurse-submodules', '--quiet']
    if branch:
        cmd += ['--branch', branch]
    cmd += ['--', url, dest]
    return cmd


def _gh_stderr_code(text):
    low = (text or '').lower()
    if 'remote branch' in low and 'not found' in low:
        return 'branch'
    if any(key in low for key in ('not found', 'authentication', 'could not read username', 'terminal prompts disabled',
                                  'repository access', 'permission denied', 'invalid username')):
        return 'notfound'
    return 'fail'


def gh_clone(url, dest, branch=None, timeout=None, max_mb=None, local_test=False, home_dir=None):
    """Shallow clone into `dest` (must not exist). Returns None on success, else one of
    'nogit', 'notfound', 'branch', 'timeout', 'toobig', 'fail'. The partial folder is removed on any failure."""
    timeout = GH_CLONE_TIMEOUT if timeout is None else timeout
    max_bytes = (GH_MAX_REPO_MB if max_mb is None else max_mb) * 1024 * 1024
    home = home_dir or tempfile.mkdtemp(prefix='demon_ghhome_')
    code = 'fail'
    try:
        try:
            proc = subprocess.Popen(gh_clone_command(url, dest, branch, local_test), stdin=subprocess.DEVNULL,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, env=_gh_git_env(home),
                                    cwd=home, text=True, errors='ignore')
        except FileNotFoundError:
            return 'nogit'
        except OSError:
            return 'nogit'
        started = time.time()
        stderr_text = ''
        while True:
            try:
                _, stderr_text = proc.communicate(timeout=1)
                break
            except subprocess.TimeoutExpired:
                if time.time() - started > timeout:
                    code = 'timeout'
                elif os.path.isdir(dest) and _gh_dir_size(dest) > max_bytes:
                    code = 'toobig'
                else:
                    continue
                try:
                    proc.kill()
                    proc.communicate(timeout=10)
                except Exception:
                    pass
                _rmtree_quiet(dest)
                return code
        if proc.returncode == 0 and os.path.isdir(dest):
            if _gh_dir_size(dest) > max_bytes:
                _rmtree_quiet(dest)
                return 'toobig'
            return None
        code = _gh_stderr_code(stderr_text)
        logger.info('git clone failed (%s)', code)
        _rmtree_quiet(dest)
        return code
    finally:
        if home_dir is None:
            _rmtree_quiet(home)


def gh_extract_archive(zip_path, dest):
    """Safely unpack a GitHub source archive into `dest`, dropping the single top-level folder. Same limits as a zip upload."""
    os.makedirs(dest, exist_ok=True)
    root_dir = os.path.realpath(dest)
    with zipfile.ZipFile(zip_path, 'r') as archive:
        items = archive.infolist()
        if len(items) > MAX_ZIP_FILES:
            raise GithubError('toobig', 'Repo mein files bahut zyada hain.')
        if sum(max(0, i.file_size) for i in items) > GH_MAX_REPO_MB * 1024 * 1024:
            raise GithubError('toobig', f'Repo {GH_MAX_REPO_MB} MB se bada hai.')
        for item in items:
            name = item.filename.replace('\\', '/')
            parts = [p for p in name.split('/') if p]
            if name.startswith('/') or '..' in parts or (len(name) > 1 and name[1] == ':'):
                raise GithubError('fail', 'Archive mein unsafe path mila.')
            if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                continue                                           # symlinks are simply not created
            rel = '/'.join(parts[1:])                              # drop "<repo>-<branch>/"
            if not rel or item.is_dir():
                continue
            target = os.path.realpath(os.path.join(root_dir, rel))
            if os.path.commonpath((root_dir, target)) != root_dir:
                raise GithubError('fail', 'Archive mein unsafe path mila.')
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with archive.open(item) as src, open(target, 'wb') as out:
                shutil.copyfileobj(src, out, 1024 * 1024)


def gh_fetch_archive(info, zip_path, timeout=None):
    """Fallback when git is not installed: download the repo as a zip from GitHub's code archive host (https only, redirects
    only to github.com / codeload.github.com, size and time limited). Raises GithubError. Needs the network, so never run in tests."""
    timeout = GH_CLONE_TIMEOUT if timeout is None else timeout
    if info.get('branch'):
        url = f"https://github.com/{info['owner']}/{info['repo']}/archive/refs/heads/{info['branch']}.zip"
    else:
        url = f"https://github.com/{info['owner']}/{info['repo']}/archive/HEAD.zip"
    deadline = time.time() + timeout
    limit = GH_MAX_REPO_MB * 1024 * 1024
    for _ in range(4):
        parts = urlsplit(url)
        if parts.scheme != 'https' or parts.hostname not in ('github.com', 'codeload.github.com'):
            raise GithubError('fail', 'Download ka raasta safe nahi tha, roka gaya.')
        try:
            resp = requests.get(url, stream=True, allow_redirects=False, timeout=(10, 20), headers={'User-Agent': 'demon-hosting-bot'})
        except requests.exceptions.RequestException:
            raise GithubError('fail', 'GitHub se connect nahi ho paya.')
        try:
            if resp.status_code in (301, 302, 303, 307, 308):
                url = urljoin(url, resp.headers.get('Location', ''))
                continue
            if resp.status_code in (404, 401, 403):
                raise GithubError('notfound', '')
            if resp.status_code != 200:
                raise GithubError('fail', 'GitHub ne download nahi diya.')
            size = 0
            with open(zip_path, 'wb') as handle:
                for block in resp.iter_content(1024 * 256):
                    size += len(block)
                    if size > limit:
                        raise GithubError('toobig', '')
                    if time.time() > deadline:
                        raise GithubError('timeout', '')
                    handle.write(block)
            return
        except requests.exceptions.RequestException:
            raise GithubError('fail', 'Download beech mein ruk gaya.')
        finally:
            resp.close()
    raise GithubError('fail', 'Bahut zyada redirect.')


# ---- picking the important files ----------------------------------------------------------
def _gh_rel_ok(rel):
    parts = rel.split('/')
    if len(parts) > 8:
        return False
    return all(GH_SEG_RE.fullmatch(p) or p in ('.env.example', '.env.sample', '.env.template') for p in parts)


def gh_collect_files(root, subdir=None):
    """Walk a cloned repo and pick the files worth hosting. Returns {'files': [(rel, abs, size)], 'skipped': {reason: count}}.
    Raises GithubError for a symlink that points outside the repo, a source file the scanner could not read in full,
    or a selection that is too big. Nothing is copied here."""
    base = os.path.realpath(root)
    if subdir:
        base = os.path.realpath(os.path.join(base, *subdir.split('/')))
        if os.path.commonpath((os.path.realpath(root), base)) != os.path.realpath(root) or not os.path.isdir(base):
            raise GithubError('subdir', 'Ye folder repo mein nahi mila. Link ka /tree/branch/folder part check karo.')
    skipped = {}
    picked = []
    total = 0
    code_total = 0

    def skip(reason):
        skipped[reason] = skipped.get(reason, 0) + 1

    for current, dirs, names in os.walk(base, followlinks=False):
        keep_dirs = []
        for d in sorted(dirs):
            full = os.path.join(current, d)
            if os.path.islink(full):
                if os.path.commonpath((base, os.path.realpath(full))) != base:
                    raise GithubError('symlink', 'Repo mein aisa shortcut (symlink) hai jo repo ke bahar jaata hai. Safety ke liye roka gaya.')
                skip('symlink')
                continue
            if d.lower() in GH_SKIP_DIRS:
                skip('junk folder')
                continue
            keep_dirs.append(d)
        dirs[:] = keep_dirs
        for name in sorted(names):
            full = os.path.join(current, name)
            rel = os.path.relpath(full, base).replace(os.sep, '/')
            if os.path.islink(full):
                if os.path.commonpath((base, os.path.realpath(full))) != base:
                    raise GithubError('symlink', 'Repo mein aisa shortcut (symlink) hai jo repo ke bahar jaata hai. Safety ke liye roka gaya.')
                skip('symlink')
                continue
            try:
                size = os.lstat(full).st_size
            except OSError:
                continue
            low = name.lower()
            ext = os.path.splitext(low)[1]
            if low.endswith(GH_PROTECTED_SUFFIXES) and low not in GH_INFO_NAMES:
                skip('env/db file')
                continue
            if low in GH_INFO_NAMES:
                kind = 'info'
            elif ext in GH_CODE_EXTS:
                kind = 'code'
            elif ext in GH_DATA_EXTS:
                kind = 'data'
            elif ext in GH_ASSET_EXTS:
                kind = 'asset'
            else:
                skip('other')
                continue
            if not _gh_rel_ok(rel):
                skip('odd name')
                continue
            if kind == 'code':
                if size > SCAN_MAX_SOURCE_BYTES:
                    raise GithubError('bigcode', f'Code file `{rel}` bahut badi hai ({_human_size(size)}), scan nahi ho sakti.')
                code_total += size
            elif kind == 'data' and size > GH_MAX_DATA_KB * 1024:
                skip('big data file')
                continue
            elif kind == 'asset' and size > GH_MAX_ASSET_KB * 1024:
                skip('big image')
                continue
            elif kind == 'info' and size > GH_MAX_DATA_KB * 1024:
                skip('big data file')
                continue
            total += size
            picked.append((rel, full, size))
            if len(picked) > GH_MAX_FILES:
                raise GithubError('toobig', f'Zyada files hain (max {GH_MAX_FILES} important files).')
            if total > GH_MAX_SELECTED_MB * 1024 * 1024:
                raise GithubError('toobig', f'Important files ka total {GH_MAX_SELECTED_MB} MB se bada hai.')
    if code_total > SCAN_MAX_ZIP_READ_BYTES - 1024 * 1024:
        raise GithubError('bigcode', 'Code bahut bada hai, poora scan nahi ho sakta.')
    return {'files': picked, 'skipped': skipped}


GH_MAIN_ORDER = ('bot.py', 'main.py', 'app.py', 'index.js', 'bot.js', 'main.js')


def gh_detect_main(files):
    """files: list of (rel, abs, size). Returns an ordered list of runnable candidates found at the top level
    (bot.py, main.py, app.py, index.js, bot.js, main.js, package.json start/main, Procfile worker:/web:)."""
    rels = {rel for rel, _, _ in files}
    top_code = {r for r in rels if '/' not in r and r.lower().endswith(GH_CODE_EXTS) and not r.lower().endswith(('.mjs', '.cjs'))}
    found = []

    def add(name):
        name = (name or '').strip().lstrip('./')
        if name in top_code and name not in found:
            found.append(name)

    for name in GH_MAIN_ORDER:
        add(name)
    by_rel = {rel: path for rel, path, _ in files}
    if 'package.json' in by_rel:
        try:
            with open(by_rel['package.json'], 'r', encoding='utf-8', errors='ignore') as handle:
                pkg = json.load(handle)
            start = (pkg.get('scripts') or {}).get('start') if isinstance(pkg, dict) else None
            if isinstance(start, str):
                m = re.match(r'^\s*node\s+([A-Za-z0-9_./-]+\.js)\s*$', start)
                if m:
                    add(m.group(1))
            main = pkg.get('main') if isinstance(pkg, dict) else None
            if isinstance(main, str):
                add(main)
        except (OSError, ValueError):
            pass
    proc_key = next((r for r in rels if r.lower() == 'procfile'), None)
    if proc_key:
        try:
            with open(by_rel[proc_key], 'r', encoding='utf-8', errors='ignore') as handle:
                for line in handle.read(20000).splitlines():
                    m = re.match(r'^\s*(?:worker|web)\s*:\s*(?:python3?|node)\s+([A-Za-z0-9_./-]+\.(?:py|js))\b', line)
                    if m:
                        add(m.group(1))
        except OSError:
            pass
    return found


def gh_main_choices(files):
    """(candidates, fallback_used). Falls back to every top-level .py/.js when none of the usual names exists."""
    found = gh_detect_main(files)
    if found:
        return found, False
    others = sorted(r for r, _, _ in files if '/' not in r and r.lower().endswith(('.py', '.js')))
    return others, True


# ---- dependency files: only plain package names, no links, no install scripts --------------
GH_REQ_LINE_RE = re.compile(r'^[A-Za-z0-9][A-Za-z0-9._-]*(\[[A-Za-z0-9._,-]+\])?\s*((==|>=|<=|~=|!=|<|>|===)\s*[A-Za-z0-9*.+!_-]+\s*(,\s*(==|>=|<=|~=|!=|<|>)\s*[A-Za-z0-9*.+!_-]+\s*)*)?'
                            r'(;\s*[A-Za-z0-9_.\s\'"<>=!~()]+)?$')


def gh_clean_requirements(text):
    """Keep only plain 'name [version]' lines. Options (-r, -e, --index-url ...), links, VCS and path requirements are dropped,
    because they could pull code from anywhere. Returns (clean_text, dropped_count)."""
    kept, dropped = [], 0
    for line in text.splitlines():
        stripped = line.split(' #', 1)[0].strip()
        if not stripped or stripped.startswith('#'):
            continue
        if GH_REQ_LINE_RE.fullmatch(stripped) and '://' not in stripped and '@' not in stripped:
            kept.append(stripped)
        else:
            dropped += 1
    return '\n'.join(kept) + ('\n' if kept else ''), dropped


def gh_clean_package_json(raw):
    """Drop dependencies that point at a link, git repo or local path (npm would fetch code from there). Returns (bytes, dropped_names)."""
    try:
        pkg = json.loads(raw.decode('utf-8-sig'))
    except (ValueError, UnicodeDecodeError):
        return raw, []
    if not isinstance(pkg, dict):
        return raw, []
    dropped = []
    for section in ('dependencies', 'optionalDependencies', 'devDependencies', 'peerDependencies'):
        deps = pkg.get(section)
        if not isinstance(deps, dict):
            continue
        for name in list(deps):
            spec = str(deps[name]).strip().lower()
            if (not re.fullmatch(r'[a-z0-9@/._~^<>=*|\s-]*', spec) or '/' in spec or spec.startswith(('git', 'file', 'link', 'http', 'github', 'npm:'))
                    or not re.fullmatch(r'(@[a-z0-9._~-]+/)?[a-z0-9._~-]+', name.lower())):
                dropped.append(name)
                del deps[name]
    if dropped:
        return json.dumps(pkg, indent=2).encode('utf-8'), dropped
    return raw, []


def gh_lock_is_safe(raw):
    """A package-lock.json is kept only when every download address in it is the normal npm registry."""
    try:
        for url in re.findall(rb'"resolved"\s*:\s*"([^"]*)"', raw):
            if not url.startswith(b'https://registry.npmjs.org/'):
                return False
        return b'"git+' not in raw and b'"file:' not in raw
    except Exception:
        return False


# ---- manifest + zip -------------------------------------------------------------------------
def _gh_sign_key():
    return hashlib.sha256(('github-manifest:' + BOT_TOKEN).encode()).digest()


def gh_sign_manifest(manifest):
    body = {k: v for k, v in manifest.items() if k != 'sig'}
    data = json.dumps(body, sort_keys=True, separators=(',', ':')).encode()
    return hmac.new(_gh_sign_key(), data, hashlib.sha256).hexdigest()


def gh_manifest_valid(manifest):
    """True only for a manifest made by this bot (a user's own zip cannot fake it)."""
    try:
        return (isinstance(manifest, dict) and isinstance(manifest.get('sig'), str)
                and hmac.compare_digest(manifest['sig'], gh_sign_manifest(manifest))
                and isinstance(manifest.get('repo'), str) and isinstance(manifest.get('main'), str))
    except Exception:
        return False


def gh_build_zip(files, out_path, info, main_name, update=False, notes=None):
    """Write the picked files (+ cleaned dependency files + signed manifest) into one zip. Returns the list of kept relative names."""
    notes = notes if notes is not None else {}
    kept = []
    with zipfile.ZipFile(out_path, 'w', zipfile.ZIP_DEFLATED) as archive:
        for rel, path, _ in files:
            low = rel.lower()
            with open(path, 'rb') as handle:
                raw = handle.read()
            if low == 'requirements.txt':
                clean, dropped = gh_clean_requirements(raw.decode('utf-8', 'ignore'))
                if dropped:
                    notes['req_dropped'] = dropped
                raw = clean.encode()
                if not raw.strip():
                    continue
            elif low == 'package.json':
                raw, dropped_pkgs = gh_clean_package_json(raw)
                if dropped_pkgs:
                    notes['pkg_dropped'] = dropped_pkgs
            elif low == 'package-lock.json' and not gh_lock_is_safe(raw):
                notes['lock_dropped'] = True
                continue
            archive.writestr(rel, raw)
            kept.append(rel)
        manifest = {'v': 1, 'repo': info['url'], 'branch': info.get('branch') or '', 'subdir': info.get('subdir') or '',
                    'main': main_name, 'update': bool(update), 'files': kept[:GH_MAX_FILES]}
        manifest['sig'] = gh_sign_manifest(manifest)
        archive.writestr(GH_MANIFEST_NAME, json.dumps(manifest))
    return kept


def gh_manifest_from_zip_bytes(data):
    """The verified manifest of a zip held in memory / on disk, or None."""
    try:
        with zipfile.ZipFile(io.BytesIO(data) if isinstance(data, (bytes, bytearray)) else data) as archive:
            info = archive.getinfo(GH_MANIFEST_NAME)
            if info.file_size > 200000:
                return None
            manifest = json.loads(archive.read(info).decode('utf-8'))
        return manifest if gh_manifest_valid(manifest) else None
    except Exception:
        return None


def gh_take_manifest(extract_dir):
    """Read and REMOVE the manifest from an extracted archive. Returns it only when the signature is ours."""
    path = os.path.join(extract_dir, GH_MANIFEST_NAME)
    if not os.path.isfile(path) or os.path.islink(path):
        return None
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            manifest = json.loads(handle.read(300000))
    except (OSError, ValueError):
        manifest = None
    _remove_quietly(path)          # never left behind in the user's storage, valid or not
    if manifest is not None and gh_manifest_valid(manifest):
        return manifest
    return None


# ---- sidecar (<bot file>.github.json inside the user's folder: travels with every backup) --------
def gh_sidecar_path(user_folder, file_name):
    base = bot_env_path(user_folder, file_name)
    return None if base is None else os.path.join(user_folder, file_name + GH_SIDECAR_SUFFIX)


def gh_write_sidecar(user_folder, file_name, manifest):
    path = gh_sidecar_path(user_folder, file_name)
    if path is None:
        return False
    body = {'repo': manifest['repo'], 'branch': manifest.get('branch', ''), 'subdir': manifest.get('subdir', ''),
            'main': file_name, 'files': list(manifest.get('files', []))[:GH_MAX_FILES], 'updated': int(time.time())}
    tmp = path + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as handle:
            json.dump(body, handle)
        os.replace(tmp, path)
        return True
    except OSError as exc:
        logger.warning('Could not write GitHub info for %s: %s', file_name, exc)
        _remove_quietly(tmp)
        return False


def gh_read_sidecar(user_folder, file_name):
    """Stored source of a bot, re-validated (a restored backup could carry anything). Returns (info, data) or (None, None)."""
    path = gh_sidecar_path(user_folder, file_name)
    if path is None or not os.path.isfile(path) or os.path.islink(path):
        return None, None
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            data = json.loads(handle.read(400000))
        link = data['repo'] + ('/tree/' + data['branch'] + ('/' + data['subdir'] if data.get('subdir') else '') if data.get('branch') else '')
        info = parse_github_url(link)
        if not isinstance(data.get('files', []), list):
            data['files'] = []
        data['files'] = [f for f in data['files'] if isinstance(f, str)][:GH_MAX_FILES]
        return info, data
    except Exception:
        return None, None


# ---- running a deploy (clone -> pick files -> pack -> SAME scan / approval / zip deploy as a manual zip) -----------------
def gh_begin(user_id):
    """One GitHub deploy at a time per user. True when this user may start one."""
    with GH_LOCK:
        if user_id in GH_ACTIVE_USERS:
            return False
        GH_ACTIVE_USERS.add(user_id)
        return True


def gh_end(user_id):
    with GH_LOCK:
        GH_ACTIVE_USERS.discard(user_id)


def _gh_say(ctx, text):
    """Progress line: edit the status message (never raises)."""
    try:
        bot.edit_message_text(text, ctx['chat_id'], ctx['status_id'], parse_mode='HTML')
    except Exception as exc:
        logger.debug('GitHub status edit failed: %s', type(exc).__name__)


def _gh_head(ctx):
    kind = 'Update' if ctx.get('update') else 'Deploy'
    return f"🐙 <b>GitHub {kind}</b> - <code>{html_escape(ctx['info']['owner'])}/{html_escape(ctx['info']['repo'])}</code>"


def _gh_error_text(err):
    """User-facing text for a GithubError (plain next step, no raw errors)."""
    code = getattr(err, 'code', 'fail')
    if code == 'notfound':
        return ('Repo nahi mila, ya woh private hai. Abhi sirf PUBLIC repos chalte hain (token/password main nahi leta). '
                'Link check karo, ya repo ko Public karke dobara try karo.')
    if code == 'branch':
        return 'Ye branch repo mein nahi mili. Link ka /tree/<branch> part check karo, ya branch ke bina sirf repo ka link do.'
    if code == 'timeout':
        return f'Download {GH_CLONE_TIMEOUT} second se zyada lag raha tha, isliye roka gaya. Thodi der baad dobara try karo.'
    if code == 'toobig':
        return f'Repo bahut bada hai (limit {GH_MAX_REPO_MB} MB). Chhota repo ya /tree/branch/folder wala link try karo.'
    if code == 'nogit':
        return 'Server par git nahi mila aur backup tareeka bhi nahi chala. Admin ko batao.'
    if code == 'fail':
        return 'GitHub se repo nahi aa paya (network ya link ki problem). Thodi der baad dobara try karo.'
    return getattr(err, 'text', '') or 'Kuch gadbad ho gayi. Dobara try karo.'


def gh_prepare(info, work_dir):
    """Clone the repo into <work_dir>/repo (git first, GitHub's zip archive when git is not installed). Returns the folder
    with the .git data removed. Raises GithubError."""
    dest = os.path.join(work_dir, 'repo')
    code = gh_clone(info['clone_url'], dest, info.get('branch'))
    if code == 'nogit':
        archive = os.path.join(work_dir, 'repo_archive.zip')
        try:
            gh_fetch_archive(info, archive)
            gh_extract_archive(archive, dest)
        finally:
            _remove_quietly(archive)
    elif code:
        raise GithubError(code, '')
    _rmtree_quiet(os.path.join(dest, '.git'))
    return dest


def _gh_top_clashes(user_id, files):
    """Top-level names of the picked files that already exist in the user's storage."""
    folder = get_user_folder(user_id)
    known = {item[0] for item in user_files.get(user_id, [])}
    tops = sorted({rel.split('/')[0] for rel, _, _ in files})
    return [name for name in tops if name in known or os.path.lexists(os.path.join(folder, name))]


def _gh_skip_summary(skipped):
    if not skipped:
        return ''
    return ', '.join(f'{count} {reason}' for reason, count in sorted(skipped.items(), key=lambda kv: -kv[1])[:4])


def _gh_cleanup(ctx):
    _rmtree_quiet(ctx.get('work'))
    gh_end(ctx['user_id'])


def _gh_run(ctx):
    """Whole deploy in a background thread. Cleans its temp folder in every case except while a picker is waiting."""
    picking = False
    slot = False
    try:
        if not GH_SLOTS.acquire(blocking=False):
            _gh_say(ctx, f"{_gh_head(ctx)}\n⏳ Abhi {GH_GLOBAL_LIMIT} deploy chal rahe hain, server busy hai. 1-2 minute baad dobara try karo.")
            return
        slot = True
        ctx['work'] = tempfile.mkdtemp(prefix=f"user_{ctx['user_id']}_gh_")
        _gh_say(ctx, f"{_gh_head(ctx)}\n⏳ Repo clone ho raha hai (public repo, sirf padhne ke liye)...")
        try:
            repo_dir = gh_prepare(ctx['info'], ctx['work'])
            _gh_say(ctx, f"{_gh_head(ctx)}\n📂 Important files chun raha hoon...")
            picked = gh_collect_files(repo_dir, ctx['info'].get('subdir'))
        except GithubError as err:
            _gh_say(ctx, f"{_gh_head(ctx)}\n❌ {html_escape(_gh_error_text(err))}")
            return
        files = picked['files']
        ctx['files'] = files
        ctx['skipped'] = picked['skipped']
        if not any(rel.lower().endswith(('.py', '.js')) for rel, _, _ in files):
            _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Is repo (ya folder) mein koi .py ya .js file nahi mili, to chalane layak kuch nahi hai.")
            return
        if ctx.get('update'):
            if ctx['main'] not in {rel for rel, _, _ in files}:
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Update nahi hua: <code>{html_escape(ctx['main'])}</code> ab repo ke top par nahi mili. Purana version waise hi hai.")
                return
            main = ctx['main']
        else:
            candidates, fallback = gh_main_choices(files)
            if not candidates:
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Main file nahi mili. Repo ke top par bot.py, main.py, app.py, index.js ya bot.js honi chahiye "
                             "(ya /tree/branch/folder wala link do jahan wo file ho).")
                return
            clashes = _gh_top_clashes(ctx['user_id'], files)
            if clashes:
                shown = ', '.join(html_escape(c) for c in clashes[:6])
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Tumhari storage mein ye naam pehle se hain: <code>{shown}</code>. "
                             "Pehle wali file delete ya rename karo, phir dobara try karo (kuch overwrite nahi kiya).")
                return
            if len(candidates) > 1:
                picking = _gh_offer_pick(ctx, candidates[:9], fallback)
                if picking:
                    return
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Main file ki list nahi dikha paya. Dobara try karo.")
                return
            main = candidates[0]
        _gh_finish(ctx, main)
    except Exception:
        logger.exception('GitHub deploy crashed for user %s', ctx.get('user_id'))
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Kuch gadbad ho gayi, kuch save nahi hua. Thodi der baad dobara try karo.")
    finally:
        if slot:
            GH_SLOTS.release()
        if not picking:
            _gh_cleanup(ctx)


def _gh_offer_pick(ctx, candidates, fallback):
    """Several possible main files: ask which one runs. The clone stays in a temp folder until the user answers (or GH_PICK_TTL)."""
    token = secrets.token_hex(4)
    ctx['candidates'] = list(candidates)
    ctx['created'] = time.time()
    ctx['token'] = token
    with GH_LOCK:
        GH_PENDING[token] = ctx
    keycaps = ['1️⃣', '2️⃣', '3️⃣', '4️⃣', '5️⃣', '6️⃣', '7️⃣', '8️⃣', '9️⃣']
    menu = NavMenu(row_width=1)
    for index, name in enumerate(candidates):
        menu.row(NavButton(f'{keycaps[index]} {name}', callback_data=f'ghp_{token}_{index}'))
    menu.row(NavButton('❌ Cancel', callback_data=f'ghx_{token}'))
    why = 'Usual naam nahi mila, ye .py/.js files top par hain' if fallback else 'Kai main file mil gayi'
    text = f"{_gh_head(ctx)}\n🤔 {why}. Kaun si file chalani hai? Number dabao:"
    try:
        bot.edit_message_text(text, ctx['chat_id'], ctx['status_id'], parse_mode='HTML')
    except Exception as exc:
        logger.debug('GitHub picker edit failed: %s', type(exc).__name__)
    sent = _safe_send(ctx['chat_id'], f'Main file chuno (ye {GH_PICK_TTL // 60} minute tak rukega) 👇', reply_markup=menu)
    if sent is None:
        with GH_LOCK:
            GH_PENDING.pop(token, None)
        return False
    timer = threading.Timer(GH_PICK_TTL + 5, _gh_expire_token, args=(token,))
    timer.daemon = True
    timer.start()
    return True


def _gh_expire_token(token):
    with GH_LOCK:
        ctx = GH_PENDING.pop(token, None)
    if ctx is not None:
        _gh_say(ctx, f"{_gh_head(ctx)}\n⌛ Main file chuni nahi gayi, isliye deploy cancel ho gaya. Dobara Upload se shuru karo.")
        _gh_cleanup(ctx)


def _gh_cancel_user(user_id):
    """Cancel pressed: drop any 'pick the main file' list this user left open."""
    with GH_LOCK:
        tokens = [t for t, c in GH_PENDING.items() if c['user_id'] == user_id or c['actor_id'] == user_id]
        dropped = [GH_PENDING.pop(t) for t in tokens]
    for ctx in dropped:
        _gh_say(ctx, f"{_gh_head(ctx)}\n❎ Cancel ho gaya, kuch save nahi hua.")
        _gh_cleanup(ctx)


def _gh_resume(ctx, main):
    """After the user picked the main file."""
    slot = False
    try:
        slot = GH_SLOTS.acquire(timeout=60)
        if not slot:
            _gh_say(ctx, f"{_gh_head(ctx)}\n⏳ Server busy hai, kuch save nahi hua. Thodi der baad dobara try karo.")
            return
        _gh_finish(ctx, main)
    except Exception:
        logger.exception('GitHub deploy (after pick) crashed for user %s', ctx.get('user_id'))
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Kuch gadbad ho gayi, kuch save nahi hua. Thodi der baad dobara try karo.")
    finally:
        if slot:
            GH_SLOTS.release()
        _gh_cleanup(ctx)


def _gh_finish(ctx, main):
    """Pack the picked files, then hand the zip to the same scan / approval / deploy path as a manual zip upload."""
    user_id, chat_id, info = ctx['user_id'], ctx['chat_id'], ctx['info']
    files = ctx['files']
    label = f"{info['owner']}/{info['repo']}"
    zip_name = f"{info['repo']}-update.zip" if ctx.get('update') else f"{info['repo']}.zip"
    zip_path = os.path.join(ctx['work'], 'pack.zip')
    notes = {}
    try:
        kept = gh_build_zip(files, zip_path, info, main, update=bool(ctx.get('update')), notes=notes)
        with open(zip_path, 'rb') as handle:
            data = handle.read()
    except GithubError as err:
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ {html_escape(_gh_error_text(err))}")
        return
    total = sum(size for _, _, size in files)
    lines = [_gh_head(ctx), f"✅ {len(kept)} important files li ({_human_size(total)}). Main: <code>{html_escape(main)}</code>"]
    skip_text = _gh_skip_summary(ctx.get('skipped'))
    if skip_text:
        lines.append(f"↪️ Skip: {html_escape(skip_text)}")
    if notes.get('req_dropped'):
        lines.append(f"⚠️ requirements.txt ki {notes['req_dropped']} line(s) hatayi (link/option wali, safety ke liye).")
    if notes.get('pkg_dropped'):
        lines.append(f"⚠️ package.json ki ye dependencies hatayi (link/git wali): {html_escape(', '.join(notes['pkg_dropped'][:5]))}")
    if notes.get('lock_dropped'):
        lines.append('⚠️ package-lock.json hata di (registry ke bahar ke links the).')
    lines.append('🛡 Security scan chal raha hai...')
    _gh_say(ctx, '\n'.join(lines))

    is_admin = user_id in admin_ids      # an admin pressing Update on someone else's bot does NOT skip that owner's scan
    reply_obj = _ReplyTarget(chat_id, ctx['status_id'], user_id)
    if is_admin:
        result = _build_result([], zip_name, 'zip', len(data))
        result['sha256'] = hashlib.sha256(data).hexdigest()
        decision = 'admin'
    else:
        result = _scan_upload(data, '.zip', zip_name)
        decision = 'auto'
    level = result['level']
    logger.info('GitHub scan: user=%s repo=%s level=%s update=%s', user_id, label, level, bool(ctx.get('update')))
    head = '\n'.join(lines[:-1])

    def verdict(outcome):
        text = _user_verdict_text(result, label, outcome)
        if outcome == 'rejected':
            text += '\nKuch save ya start nahi hua.'
        elif outcome == 'review' and ctx.get('update'):
            text += '\nPurana version waise hi chalta rahega.'
        _gh_say(ctx, f"{head}\n{text}")

    if not is_admin and level == THREAT_HIGH:
        verdict('rejected')
        notice = (f"🔴 GitHub deploy reject hua: <code>{html_escape(info['url'])}</code> from {html_escape(ctx['uploader'])} "
                  f"(<code>{user_id}</code>)\n{_reason_lines_html(result, 2)}")
        for admin_id in sorted(admin_ids):
            _safe_send(admin_id, notice)
        return
    if not is_admin and level == THREAT_MEDIUM:
        token, err = _submit_for_review(user_id, ctx['uploader'], chat_id, ctx['status_id'], zip_name, 'zip', data, result)
        if token:
            verdict('review')
        else:
            _gh_say(ctx, f"{head}\n{THREAT_BADGE[level]} Start nahi hua. {html_escape(err)}")
        return
    if is_admin:
        _gh_say(ctx, f"{head}\n🛡 Admin deploy - seedha chal raha hai (scan record ke saath).")
    else:
        verdict('auto')
    ok, err = _deploy_upload(user_id, zip_name, 'zip', data, reply_obj, result, decision)
    if not ok and err:
        _safe_send(chat_id, f'⚠️ {html_escape(err)}')


# ---- link prompt, picker answers, update button ------------------------------------------------------------------------
def _gh_upload_menu():
    menu = NavMenu(row_width=1)
    menu.row(NavButton('🐙 Deploy from GitHub', callback_data='gh_start'))
    menu.row(NavButton('📤 Manual Upload', callback_data='gh_manual'))
    menu.row(NavButton('❌ Cancel', callback_data='nav_cancel'))
    return menu


UPLOAD_CHOICE_TEXT = ("📤 <b>Upload kaise karna hai?</b>\n\n"
                      "🐙 <b>Deploy from GitHub</b> - apne public GitHub repo ka link do, main important files clone karke chala dunga.\n"
                      "📤 <b>Manual Upload</b> - apni .py, .js ya .zip file khud bhejo.")


def _send_upload_choice(chat_id):
    bot.send_message(chat_id, UPLOAD_CHOICE_TEXT, parse_mode='HTML', reply_markup=_gh_upload_menu())


def _upload_limit_ok(user_id, chat_id):
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else 'Unlimited'
        bot.send_message(chat_id, f"⚠️ File limit ({current_files}/{limit_str}) reached. Purani file delete karo, ya backup export/import karo.",
                         reply_markup=_files_view(user_id)[1])
        return False
    return True


def gh_manual_callback(call):
    bot.answer_callback_query(call.id)
    if _upload_limit_ok(call.from_user.id, call.message.chat.id):
        bot.send_message(call.message.chat.id, "📤 Send your Python (`.py`), JS (`.js`), or ZIP (`.zip`) file.")


def gh_start_callback(call):
    bot.answer_callback_query(call.id)
    user_id, chat_id = call.from_user.id, call.message.chat.id
    if not _upload_limit_ok(user_id, chat_id):
        return
    with GH_LOCK:
        busy = user_id in GH_ACTIVE_USERS
    if busy:
        bot.send_message(chat_id, '⏳ Tumhara ek GitHub deploy abhi chal raha hai (ya main file ka intezaar hai). Pehle use khatam hone do.')
        return
    prompt = ("🐙 <b>Deploy from GitHub</b>\n\nApne <b>public</b> repo ka link bhejo, jaise:\n"
              "<code>https://github.com/owner/repo</code>\n"
              "Branch/folder ke liye: <code>https://github.com/owner/repo/tree/main/folder</code>\n\n"
              "Private repo abhi support nahi hai, aur main koi token/password nahi maangta.")
    sent = bot.send_message(chat_id, prompt, parse_mode='HTML', reply_markup=NavMenu().add(NavButton('❌ Cancel', callback_data='nav_cancel')))
    bot.register_next_step_handler(sent, _gh_receive_link, user_id)


def _gh_receive_link(message, actor_id):
    chat_id = message.chat.id
    user_id = message.from_user.id
    text = getattr(message, 'text', None)
    if user_id != actor_id or not text:
        sent = bot.send_message(chat_id, '⚠️ Link text mein bhejo, jaise https://github.com/owner/repo')
        bot.register_next_step_handler(sent, _gh_receive_link, actor_id)
        return
    try:
        info = parse_github_url(text)
    except GithubError as err:
        sent = bot.send_message(chat_id, f"⚠️ {err.text}\nDobara link bhejo, ya Cancel dabao.")
        bot.register_next_step_handler(sent, _gh_receive_link, actor_id)
        return
    if is_user_banned(user_id) or (bot_locked and user_id not in admin_ids):
        bot.send_message(chat_id, '⚠️ Abhi deploy nahi ho sakta.')
        return
    if not _upload_limit_ok(user_id, chat_id):
        return
    if not gh_begin(user_id):
        bot.send_message(chat_id, '⏳ Tumhara ek GitHub deploy abhi chal raha hai. Pehle use khatam hone do.')
        return
    try:
        status = bot.send_message(chat_id, f"🐙 <b>GitHub Deploy</b> - <code>{html_escape(info['owner'])}/{html_escape(info['repo'])}</code>\n⏳ Shuru ho raha hai...",
                                  parse_mode='HTML')
    except Exception:
        gh_end(user_id)
        raise
    uploader = message.from_user.first_name or message.from_user.username or str(user_id)
    ctx = {'user_id': user_id, 'actor_id': user_id, 'chat_id': chat_id, 'status_id': status.message_id, 'info': info,
           'update': False, 'uploader': uploader, 'work': None}
    threading.Thread(target=_gh_run, args=(ctx,), daemon=True).start()


def gh_pick_callback(call):
    """ghp_<token>_<index> = chosen main file, ghx_<token> = cancel."""
    parts = call.data.split('_')
    token = parts[1] if len(parts) > 1 else ''
    with GH_LOCK:
        ctx = GH_PENDING.get(token)
        allowed = ctx is not None and call.from_user.id in (ctx['actor_id'], ctx['user_id'])
        if allowed:
            GH_PENDING.pop(token, None)
    if ctx is None or not allowed:
        bot.answer_callback_query(call.id, 'Ye list purani ho gayi. Upload se dobara shuru karo.', show_alert=True)
        return
    if parts[0] == 'ghx':
        bot.answer_callback_query(call.id, 'Cancel ho gaya.')
        _gh_say(ctx, f"{_gh_head(ctx)}\n❎ Cancel ho gaya, kuch save nahi hua.")
        _gh_cleanup(ctx)
        return
    try:
        main = ctx['candidates'][int(parts[2])]
    except (IndexError, ValueError):
        bot.answer_callback_query(call.id, 'Galat choice.', show_alert=True)
        _gh_cleanup(ctx)
        return
    bot.answer_callback_query(call.id, f'{main} chuni.')
    threading.Thread(target=_gh_resume, args=(ctx, main), daemon=True).start()


def gh_update_callback(call):
    """ghu_<ownerid>_<file>: pull the repo again; restart only if the scan passes."""
    try:
        _, owner_str, file_name = call.data.split('_', 2)
        owner_id = int(owner_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, 'Galat button.', show_alert=True)
        return
    actor = call.from_user.id
    if not (actor == owner_id or actor in admin_ids):
        bot.answer_callback_query(call.id, '⚠️ Permission denied.', show_alert=True)
        return
    if not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.answer_callback_query(call.id, '⚠️ File not found.', show_alert=True)
        return
    info, side = gh_read_sidecar(get_user_folder(owner_id), file_name)
    if info is None:
        bot.answer_callback_query(call.id, 'Is bot ka GitHub source yaad nahi hai.', show_alert=True)
        return
    if not gh_begin(owner_id):
        bot.answer_callback_query(call.id, 'Ek GitHub deploy pehle se chal raha hai.', show_alert=True)
        return
    bot.answer_callback_query(call.id, 'Update shuru...')
    chat_id = call.message.chat.id
    try:
        status = bot.send_message(chat_id, f"🐙 <b>GitHub Update</b> - <code>{html_escape(info['owner'])}/{html_escape(info['repo'])}</code>\n⏳ Shuru ho raha hai...",
                                  parse_mode='HTML')
    except Exception:
        gh_end(owner_id)
        raise
    uploader = call.from_user.first_name or call.from_user.username or str(actor)
    ctx = {'user_id': owner_id, 'actor_id': actor, 'chat_id': chat_id, 'status_id': status.message_id, 'info': info,
           'update': True, 'main': file_name, 'uploader': uploader, 'work': None}
    threading.Thread(target=_gh_run, args=(ctx,), daemon=True).start()


# ---- applying an update to an already hosted bot ------------------------------------------------------------------------
def _gh_apply_update(extract_dir, manifest, user_id, user_folder, message, scan, state):
    """Update branch of the zip deploy. Only code files the earlier GitHub deploy put there are overwritten;
    .env / .db / .sqlite files, data files and anything else of the user stay untouched. If anything fails the old files
    are put back. The bot is restarted only after everything worked (the scan already passed to get here)."""
    main = manifest['main']
    info, side = gh_read_sidecar(user_folder, main)
    entry = next((item for item in user_files.get(user_id, []) if item[0] == main), None)
    if info is None or info['url'] != manifest.get('repo') or entry is None or not os.path.isfile(os.path.join(user_folder, main)):
        bot.reply_to(message, '❌ Update nahi hua: is bot ka GitHub source ya file ab maujood nahi hai. Purana version waise hi hai.')
        return
    file_type = entry[1]
    known = set(side.get('files') or [])
    root_real = os.path.realpath(user_folder)
    plan, kept_count = [], 0
    for base, dirs, names in os.walk(extract_dir):
        for name in names:
            src = os.path.join(base, name)
            rel = os.path.relpath(src, extract_dir).replace(os.sep, '/')
            low = rel.lower()
            leaf = os.path.basename(low)
            if os.path.islink(src) or not _gh_rel_ok(rel):
                continue
            if low.endswith(GH_PROTECTED_SUFFIXES) and leaf not in GH_INFO_NAMES:
                kept_count += 1
                continue
            dest = os.path.join(user_folder, *rel.split('/'))
            real = os.path.realpath(dest)
            if os.path.commonpath((root_real, real)) != root_real or real != os.path.join(os.path.realpath(os.path.dirname(dest)), os.path.basename(dest)):
                continue
            if os.path.lexists(dest):
                is_code = low.endswith(GH_UPDATE_CODE_EXTS) or leaf in GH_UPDATE_CODE_NAMES
                if os.path.isfile(dest) and not os.path.islink(dest) and rel in known and is_code:
                    plan.append((rel, src, dest, 'update'))
                else:
                    kept_count += 1
            else:
                plan.append((rel, src, dest, 'new'))
    if main not in {rel for rel, _, _, _ in plan}:
        bot.reply_to(message, '❌ Update nahi hua: main file update list mein nahi aayi. Purana version waise hi hai.')
        return
    if os.path.isfile(os.path.join(extract_dir, 'requirements.txt')):
        if not _install_zip_deps(extract_dir, message, user_id, safe=True, do_npm=False):
            return
    backup_dir = os.path.join(os.path.dirname(extract_dir), 'update_backup')
    os.makedirs(backup_dir, exist_ok=True)
    touched = []          # (rel, dest, action)

    def rollback():
        for rel, dest, action in reversed(touched):
            try:
                if action == 'new':
                    _remove_quietly(dest)
                else:
                    shutil.copyfile(os.path.join(backup_dir, *rel.split('/')), dest)
            except OSError as exc:
                logger.error('GitHub update rollback failed for %s: %s', rel, exc)

    try:
        for rel, src, dest, action in plan:
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            if action == 'update':
                backup = os.path.join(backup_dir, *rel.split('/'))
                os.makedirs(os.path.dirname(backup), exist_ok=True)
                shutil.copyfile(dest, backup)
            tmp = dest + '.ghtmp'
            shutil.copyfile(src, tmp)
            os.replace(tmp, dest)
            touched.append((rel, dest, action))
    except OSError as exc:
        logger.error('GitHub update copy failed: %s', exc)
        rollback()
        bot.reply_to(message, '❌ Update ke beech file likhne mein dikkat aayi. Purani files wapas rakh di, kuch nahi badla.')
        return
    if any(rel == 'package.json' for rel, _, _ in touched):
        if not _install_zip_deps(user_folder, message, user_id, safe=True, do_pip=False):
            rollback()
            bot.reply_to(message, '↩️ Update wapas le liya, purani files waise hi hain.')
            return

    script_key = _script_key(user_id, main)
    RESTART_STATE.setdefault(script_key, {'attempts': 0, 'manual_stop': False})['manual_stop'] = True
    if is_bot_running(user_id, main):
        process_info = bot_scripts.get(script_key)
        if process_info:
            kill_process_tree(process_info)
        _forget_script(script_key)
        time.sleep(1.5)
    _reset_restart_state(user_id, main)
    main_path = os.path.join(user_folder, main)
    if scan:
        record = dict(scan[0])
        record['sha256'] = _file_sha256(main_path) or record.get('sha256', '')
        save_scan_record(user_id, main, record, scan[1])
    gh_write_sidecar(user_folder, main, manifest)
    state['ok'] = True
    updated = sum(1 for _, _, _, action in plan if action == 'update')
    added = len(plan) - updated
    bot.reply_to(message, f"✅ Update ho gaya: {updated} file badli, {added} nayi, {kept_count} waise hi chhodi (.env/data/db). "
                          f"Ab <code>{html_escape(main)}</code> restart ho raha hai...", parse_mode='HTML')
    target = run_js_script if file_type == 'js' else run_script
    threading.Thread(target=target, args=(main_path, user_id, user_folder, main, message)).start()


# ---- what the admin sees for a held GitHub deploy ---------------------------------------------------------------------
def _gh_source_line(manifest):
    if not manifest:
        return ''
    kind = 'update' if manifest.get('update') else 'deploy'
    return f"🐙 GitHub {kind}: <code>{html_escape(str(manifest.get('repo', '')))}</code>"


def _review_source(entry):
    """Source line for a held upload that came from GitHub (read from the signed manifest inside the held zip)."""
    try:
        if entry.get('kind') != 'upload' or entry.get('file_type') != 'zip':
            return ''
        return _gh_source_line(gh_manifest_from_zip_bytes(_quarantine_path(entry['token'])))
    except Exception:
        return ''



def _install_zip_deps(folder, message, user_id, safe=False, do_pip=True, do_npm=True):
    """Install requirements.txt / package.json found in `folder` (same behaviour as before for manual zips).
    safe=True (GitHub deploys): npm runs with --ignore-scripts so no repo install hook is executed.
    Returns False when something failed (the user was told why)."""
    req_path = os.path.join(folder, 'requirements.txt')
    if do_pip and os.path.isfile(req_path):
        req_file = 'requirements.txt'
        logger.info(f"requirements.txt found, installing: {req_path}")
        bot.reply_to(message, f"🔄 Installing Python deps from `{req_file}`...")
        try:
            command = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', '-r', req_path]
            result = subprocess.run(command, capture_output=True, text=True, check=True, encoding='utf-8', errors='ignore',
                                    timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=child_env())
            logger.info(f"pip install from requirements.txt OK. Output:\n{result.stdout}")
            bot.reply_to(message, f"✅ Python deps from `{req_file}` installed.")
        except subprocess.CalledProcessError as e:
            log_tail = _short_code_block((e.stderr or e.stdout or '')[-2500:], 2500)
            error_msg = f"❌ Failed to install Python deps from `{req_file}`.\nLog:\n```\n{log_tail}\n```"
            logger.error(error_msg)
            bot.reply_to(message, error_msg, parse_mode='Markdown'); return False
        except subprocess.TimeoutExpired:
            logger.error(f"pip install -r timed out for user {user_id}")
            bot.reply_to(message, f"❌ Installing the Python deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return False
        except Exception as e:
            error_msg = f"❌ Unexpected error installing Python deps: {e}"
            logger.error(error_msg, exc_info=True); bot.reply_to(message, error_msg); return False

    pkg_json = 'package.json'
    if do_npm and os.path.isfile(os.path.join(folder, pkg_json)):
        logger.info(f"package.json found, npm install in: {folder}")
        bot.reply_to(message, f"🔄 Installing Node deps from `{pkg_json}`...")
        try:
            command = ['npm', 'install', '--ignore-scripts'] if safe else ['npm', 'install']
            result = subprocess.run(command, capture_output=True, text=True, check=True, cwd=folder, encoding='utf-8', errors='ignore',
                                    timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=child_env())
            logger.info(f"npm install OK. Output:\n{result.stdout}")
            bot.reply_to(message, f"✅ Node deps from `{pkg_json}` installed.")
        except FileNotFoundError:
            bot.reply_to(message, "❌ 'npm' not found. Cannot install Node deps."); return False
        except subprocess.CalledProcessError as e:
            log_tail = _short_code_block((e.stderr or e.stdout or '')[-2500:], 2500)
            error_msg = f"❌ Failed to install Node deps from `{pkg_json}`.\nLog:\n```\n{log_tail}\n```"
            logger.error(error_msg)
            bot.reply_to(message, error_msg, parse_mode='Markdown'); return False
        except subprocess.TimeoutExpired:
            logger.error(f"npm install timed out for user {user_id}")
            bot.reply_to(message, f"❌ Installing the Node deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return False
        except Exception as e:
            error_msg = f"❌ Unexpected error installing Node deps: {e}"
            logger.error(error_msg, exc_info=True); bot.reply_to(message, error_msg); return False
    return True


def process_zip_file(zip_path, user_id, user_folder, file_name_zip, message, temp_dir=None, scan=None):
    """Process ZIP file extraction and setup. Returns True when the archive was set up and its main script started.
    scan = (scan_result, decision) from the upload security scan, stored for the main script."""
    state = {'ok': False}
    _process_zip_file_impl(zip_path, user_id, user_folder, file_name_zip, message, temp_dir, scan, state)
    return state['ok']


def _process_zip_file_impl(zip_path, user_id, user_folder, file_name_zip, message, temp_dir, scan, state):
    cleanup_temp = False
    if temp_dir is None:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_")
        cleanup_temp = True
        
    try:
        # Extract into a sub folder so the uploaded .zip itself is never copied into the user's storage.
        extract_dir = os.path.join(temp_dir, 'extracted')
        os.makedirs(extract_dir, exist_ok=True)
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            # Validate archive paths and expansion limits before extracting.
            archive_items = zip_ref.infolist()
            if len(archive_items) > MAX_ZIP_FILES:
                raise zipfile.BadZipFile(f'Archive contains too many entries (maximum {MAX_ZIP_FILES}).')
            total_uncompressed = sum(max(0, item.file_size) for item in archive_items)
            if total_uncompressed > MAX_UNZIPPED_MB * 1024 * 1024:
                raise zipfile.BadZipFile(f'Archive expands beyond the {MAX_UNZIPPED_MB} MB extraction limit.')
            root_dir = os.path.realpath(extract_dir)
            for member in archive_items:
                _norm_name = member.filename.replace(chr(92), '/')
                if _norm_name.startswith('/') or '..' in _norm_name.split('/') or (len(_norm_name) > 1 and _norm_name[1] == ':'):
                    raise zipfile.BadZipFile(f"Zip has unsafe path: {member.filename}")
                member_path = os.path.realpath(os.path.join(root_dir, member.filename))
                if os.path.commonpath((root_dir, member_path)) != root_dir:
                    raise zipfile.BadZipFile(f"Zip has unsafe path: {member.filename}")
                # Reject symlink entries; they can redirect extracted paths.
                unix_mode = (member.external_attr >> 16) & 0o170000
                if unix_mode == 0o120000:
                    raise zipfile.BadZipFile(f"Zip contains a symbolic link: {member.filename}")
            zip_ref.extractall(extract_dir)
            logger.info(f"Extracted zip to {extract_dir}")

        # A zip packed by the GitHub deploy carries a signed manifest (a manual zip cannot fake it; it is removed here).
        manifest = gh_take_manifest(extract_dir)
        if manifest and manifest.get('update'):
            _gh_apply_update(extract_dir, manifest, user_id, user_folder, message, scan, state)
            return

        extracted_items = os.listdir(extract_dir)
        py_files = [f for f in extracted_items if f.endswith('.py')]
        js_files = [f for f in extracted_items if f.endswith('.js')]
        req_file = 'requirements.txt' if 'requirements.txt' in extracted_items else None
        pkg_json = 'package.json' if 'package.json' in extracted_items else None

        if not _install_zip_deps(extract_dir, message, user_id, safe=bool(manifest)):
            return

        main_script_name = None; file_type = None
        preferred_py = ['main.py', 'bot.py', 'app.py']; preferred_js = ['index.js', 'main.js', 'bot.js', 'app.js']
        for p in preferred_py:
            if p in py_files: main_script_name = p; file_type = 'py'; break
        if not main_script_name:
             for p in preferred_js:
                 if p in js_files: main_script_name = p; file_type = 'js'; break
        if not main_script_name:
            if py_files: main_script_name = py_files[0]; file_type = 'py'
            elif js_files: main_script_name = js_files[0]; file_type = 'js'
        if manifest:
            wanted = str(manifest.get('main', ''))
            if wanted in extracted_items and wanted.endswith(('.py', '.js')):
                main_script_name = wanted; file_type = 'js' if wanted.endswith('.js') else 'py'
        if not main_script_name:
            bot.reply_to(message, "❌ No `.py` or `.js` script found in archive!"); return

        logger.info(f"Moving extracted files from {extract_dir} to {user_folder}")
        moved_count = 0
        for item_name in os.listdir(extract_dir):
            dest_path = os.path.join(user_folder, item_name)
            if os.path.exists(dest_path):
                raise FileExistsError(f"Archive item already exists in your storage: {item_name}")
        for item_name in os.listdir(extract_dir):
            src_path = os.path.join(extract_dir, item_name)
            dest_path = os.path.join(user_folder, item_name)
            shutil.move(src_path, dest_path); moved_count += 1
        logger.info(f"Moved {moved_count} items to {user_folder}")

        save_user_file(user_id, main_script_name, file_type)
        _reset_restart_state(user_id, main_script_name)
        logger.info(f"Saved main script '{main_script_name}' ({file_type}) for {user_id} from zip.")
        main_script_path = os.path.join(user_folder, main_script_name)
        if scan:
            # Remember the archive's verdict for its main script (fingerprint = the file now on disk).
            scan_record = dict(scan[0])
            scan_record['sha256'] = _file_sha256(main_script_path) or scan_record.get('sha256', '')
            save_scan_record(user_id, main_script_name, scan_record, scan[1])
        state['ok'] = True
        if manifest:
            gh_write_sidecar(user_folder, main_script_name, manifest)
            bot.reply_to(message, f"✅ GitHub repo se files lag gayi. Starting main script: `{main_script_name}`...\n🐙 Source: {manifest.get('repo', '')}")
        else:
            bot.reply_to(message, f"✅ Files extracted. Starting main script: `{main_script_name}`...", parse_mode='Markdown')

        # Use user_id as script_owner_id for script key context
        if file_type == 'py':
             threading.Thread(target=run_script, args=(main_script_path, user_id, user_folder, main_script_name, message)).start()
        elif file_type == 'js':
             threading.Thread(target=run_js_script, args=(main_script_path, user_id, user_folder, main_script_name, message)).start()
             
    except Exception as e:
        logger.error(f"Error processing zip file: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error processing zip: {str(e)}")
    finally:
        if cleanup_temp and temp_dir and os.path.exists(temp_dir):
            try: shutil.rmtree(temp_dir); logger.info(f"Cleaned temp dir: {temp_dir}")
            except Exception as e: logger.error(f"Failed to clean temp dir {temp_dir}: {e}", exc_info=True)

# --- Per-bot environment variables (.env style) -------------------------------------
# Each bot keeps its variables in "<bot file name>.env" next to the script, inside the user's own folder
# (for example bot.py.env). The file is a normal part of that folder, so My Bots export / import and full
# backups carry it along. It is read every time the bot is launched (first start, Restart button, watchdog).
ENV_KEY_RE = re.compile(r'^[A-Za-z_][A-Za-z0-9_]{0,39}$')
ENV_MAX_VARS = 40
ENV_MAX_VALUE_CHARS = 2000
ENV_MAX_FILE_BYTES = 128 * 1024
# Names that change how the interpreter / loader itself behaves; they could be used to get around the upload review.
ENV_RESERVED_KEYS = frozenset({
    'PATH', 'HOME', 'USER', 'SHELL', 'IFS', 'ENV', 'BASH_ENV', 'PWD', 'TMPDIR',
    'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONINSPECT', 'PYTHONSAFEPATH', 'PYTHONUSERBASE',
    'PYTHONBREAKPOINT', 'PYTHONEXECUTABLE', 'NODE_OPTIONS', 'NODE_PATH', 'NODE_EXTRA_CA_CERTS',
    'NPM_CONFIG_PREFIX', 'SSL_CERT_FILE', 'REQUESTS_CA_BUNDLE',
})
ENV_RESERVED_PREFIXES = ('LD_', 'DYLD_')
ENV_LOCK = threading.RLock()
_ENV_SENSITIVE_RE = re.compile(r'TOKEN|SECRET|PASS|KEY|HASH|AUTH|CRED|PRIVATE|SESSION|DSN|URL|URI|COOKIE', re.IGNORECASE)


def _env_key_reserved(key):
    upper = key.upper()
    return upper in ENV_RESERVED_KEYS or upper.startswith(ENV_RESERVED_PREFIXES)


def _env_safe_label(text, limit=30):
    """A piece of user input that is safe to show back (printable ASCII only, shortened, no values)."""
    return re.sub(r'[^\x21-\x7e]', '?', str(text))[:limit]


def bot_env_path(user_folder, file_name):
    """Where the variables of one bot live; None when the name is not a plain file name."""
    if not file_name or file_name != os.path.basename(file_name) or file_name in ('.', '..') or '\\' in file_name:
        return None
    return os.path.join(user_folder, file_name + '.env')


def _parse_env_value(raw):
    """Value part of a KEY=VALUE line -> (value, error). Understands "double", 'single' and unquoted values."""
    raw = raw.strip()
    if not raw:
        return '', None
    quote = raw[0]
    if quote in ('"', "'"):
        out = []
        i = 1
        escapes = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\'}
        while i < len(raw):
            ch = raw[i]
            if quote == '"' and ch == '\\' and i + 1 < len(raw):
                nxt = raw[i + 1]
                out.append(escapes.get(nxt, '\\' + nxt))
                i += 2
                continue
            if ch == quote:
                rest = raw[i + 1:].strip()
                if rest and not rest.startswith('#'):
                    return None, 'there is text after the closing quote'
                return ''.join(out), None
            out.append(ch)
            i += 1
        return None, 'the quote is not closed'
    match = re.search(r'\s#', raw)       # unquoted values may end with a " # comment"
    if match:
        raw = raw[:match.start()]
    return raw.strip(), None


def parse_env_text(text):
    """Parse .env style text. Returns (pairs, problems): pairs is {KEY: value}; problems is a list of
    (line number, key label or None, reason). Values are never put into problems."""
    pairs = {}
    problems = []
    text = (text or '').lstrip('\ufeff')
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            continue
        if re.match(r'export\s', stripped):
            stripped = stripped[6:].lstrip()
        if '=' not in stripped:
            problems.append((number, None, 'needs the form KEY=VALUE'))
            continue
        key, _, raw_value = stripped.partition('=')
        key = key.strip()
        label = _env_safe_label(key)
        if not ENV_KEY_RE.match(key):
            problems.append((number, label, 'name can only use letters, digits and _ (not starting with a digit, max 40 characters)'))
            continue
        if _env_key_reserved(key):
            problems.append((number, key, 'this name is reserved by the host and cannot be changed'))
            continue
        value, error = _parse_env_value(raw_value)
        if error:
            problems.append((number, key, error))
            continue
        if len(value) > ENV_MAX_VALUE_CHARS:
            problems.append((number, key, f'value is longer than {ENV_MAX_VALUE_CHARS} characters'))
            continue
        if any((ord(ch) < 32 and ch not in '\t\n\r') or ch == '\x7f' for ch in value):
            problems.append((number, key, 'value has unsupported control characters'))
            continue
        pairs[key] = value
    return pairs, problems


def _format_env_value(value):
    if re.fullmatch(r'[A-Za-z0-9_@%+=:,./-]*', value):
        return value
    escaped = value.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '\\r')
    return f'"{escaped}"'


def serialize_env(env):
    return ''.join(f'{key}={_format_env_value(value)}\n' for key, value in sorted(env.items()))


def load_bot_env(user_folder, file_name):
    """Saved variables of one bot as a plain dict. Never raises: a missing or broken file simply gives {}.
    Anything that is not a valid, allowed name is dropped here as well, so a hand-made file or a restored
    backup cannot smuggle in reserved names."""
    try:
        path = bot_env_path(user_folder, file_name)
        if not path or os.path.islink(path) or not os.path.isfile(path):
            return {}
        if os.path.getsize(path) > ENV_MAX_FILE_BYTES:
            logger.warning("Environment file for %s is too large and was ignored.", file_name)
            return {}
        with open(path, 'r', encoding='utf-8', errors='replace') as handle:
            pairs, problems = parse_env_text(handle.read())
        if problems:
            logger.warning("Environment file for %s: %d line(s) ignored.", file_name, len(problems))
        return dict(list(pairs.items())[:ENV_MAX_VARS])
    except Exception as exc:
        logger.warning("Could not read the environment of %s: %s", file_name, redact_secrets(exc))
        return {}


def _write_bot_env(path, env):
    """Atomic write (owner-only permissions). An empty set removes the file."""
    if not env:
        try:
            os.remove(path)
        except FileNotFoundError:
            pass
        return
    data = serialize_env(env)
    if len(data.encode('utf-8')) > ENV_MAX_FILE_BYTES:
        raise ValueError('The environment is too large.')
    tmp_path = f'{path}.{os.urandom(4).hex()}.tmp'
    try:
        fd = os.open(tmp_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as handle:
            handle.write(data)
        os.replace(tmp_path, path)
    finally:
        if os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass


def update_bot_env(user_folder, file_name, new_pairs):
    """Add or update variables. Returns (added keys, updated keys, unchanged keys). Raises ValueError with a
    plain message when the result would be too big or the name is unusable."""
    path = bot_env_path(user_folder, file_name)
    if not path:
        raise ValueError('That bot name cannot have variables.')
    with ENV_LOCK:
        current = load_bot_env(user_folder, file_name)
        merged = dict(current)
        added, updated, unchanged = [], [], []
        for key, value in new_pairs.items():
            if key not in current:
                added.append(key)
            elif current[key] != value:
                updated.append(key)
            else:
                unchanged.append(key)
            merged[key] = value
        if len(merged) > ENV_MAX_VARS:
            raise ValueError(f'A bot can have at most {ENV_MAX_VARS} variables '
                             f'(you have {len(current)}, this would make {len(merged)}). Delete some first.')
        _write_bot_env(path, merged)
    return added, updated, unchanged


def delete_bot_env_key(user_folder, file_name, key):
    path = bot_env_path(user_folder, file_name)
    if not path:
        return False
    with ENV_LOCK:
        current = load_bot_env(user_folder, file_name)
        if key not in current:
            return False
        del current[key]
        _write_bot_env(path, current)
    return True


def clear_bot_env(user_folder, file_name):
    """Remove every saved variable of one bot. Returns how many were set."""
    path = bot_env_path(user_folder, file_name)
    if not path:
        return 0
    with ENV_LOCK:
        count = len(load_bot_env(user_folder, file_name))
        _write_bot_env(path, {})
    return count


def _env_key_tag(key):
    return hashlib.sha1(key.encode('utf-8')).hexdigest()[:6]


def _env_display_value(key, value, reveal):
    shown = value.replace('\r', ' ').replace('\n', ' ')
    if not reveal and _ENV_SENSITIVE_RE.search(key):
        return (shown[:3] + '••••') if len(shown) > 8 else '••••'
    return shown if len(shown) <= 24 else shown[:24] + '…'


def _prepare_log_file(log_file_path):
    """Open a script log for appending; start a fresh file if the old one is already too big."""
    try:
        if os.path.exists(log_file_path) and os.path.getsize(log_file_path) > MAX_SCRIPT_LOG_MB * 1024 * 1024:
            os.replace(log_file_path, log_file_path + '.old')
    except OSError as exc:
        logger.warning(f"Could not rotate log {log_file_path}: {exc}")
    return open(log_file_path, 'a', encoding='utf-8', errors='ignore')


def _popen_kwargs(user_folder=None, file_name=None):
    """Extra Popen arguments: own process group on POSIX (so children can be stopped too) and a clean environment.
    With user_folder + file_name, the variables saved for that one bot (Environment button) are merged in.
    Only the dict handed to this one child is changed; the hosting bot's own os.environ is never touched."""
    env = child_env()
    if user_folder and file_name:
        env.update(load_bot_env(user_folder, file_name))
    kwargs = {'env': env}
    if os.name == 'posix':
        kwargs['start_new_session'] = True
    return kwargs


def _kill_check_process(check_proc):
    """Stop a pre-check process (and anything it started) and reap it."""
    if check_proc is None:
        return
    try:
        if check_proc.poll() is None:
            if os.name == 'posix':
                try:
                    os.killpg(check_proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    check_proc.kill()
            else:
                check_proc.kill()
        check_proc.communicate(timeout=5)
    except Exception as exc:
        logger.debug(f"Pre-check cleanup problem: {exc}")


def _register_script(script_key, info):
    """Store a running script; if an older one with the same key is still alive, stop it first (no leaked processes)."""
    with STATE_LOCK:
        old = bot_scripts.get(script_key)
        bot_scripts[script_key] = info
    if old and old.get('process') is not None and old['process'] is not info['process']:
        try:
            if old['process'].poll() is None:
                logger.warning(f"Replacing a still-running process for {script_key}; stopping the old one.")
                kill_process_tree(old)
            else:
                release_process_resources(old)
        except Exception as exc:
            logger.error(f"Could not clean up the old process for {script_key}: {exc}")


def _forget_script(script_key):
    with STATE_LOCK:
        return bot_scripts.pop(script_key, None)


def _short_code_block(text, limit=500):
    """Shorten text for use inside a Markdown code block (a stray triple backtick would break the message)."""
    return (text or '')[:limit].replace('```', "'" * 3)


def handle_js_file(file_path, script_owner_id, user_folder, file_name, message):
    try:
        save_user_file(script_owner_id, file_name, 'js')
        _reset_restart_state(script_owner_id, file_name)
        threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, message)).start()
    except Exception as e:
        logger.error(f"❌ Error processing JS file {file_name} for {script_owner_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error processing JS file: {str(e)}")

def handle_py_file(file_path, script_owner_id, user_folder, file_name, message):
    try:
        save_user_file(script_owner_id, file_name, 'py')
        _reset_restart_state(script_owner_id, file_name)
        threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, message)).start()
    except Exception as e:
        logger.error(f"❌ Error processing Python file {file_name} for {script_owner_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error processing Python file: {str(e)}")

# --- Automatic Package Installation & Script Running ---
def run_script(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    """Run Python script. script_owner_id is used for the script_key. message_obj_for_reply is for sending feedback."""
    max_attempts = 2 
    if attempt > max_attempts:
        bot.reply_to(message_obj_for_reply, f"❌ Failed to run '{file_name}' after {max_attempts} attempts. Check logs.")
        return

    script_key = f"{script_owner_id}_{file_name}"
    logger.info(f"Attempt {attempt} to run Python script: {script_path} (Key: {script_key}) for user {script_owner_id}")

    try:
        if not os.path.exists(script_path):
             bot.reply_to(message_obj_for_reply, f"❌ Error: Script '{file_name}' not found at '{script_path}'!")
             logger.error(f"Script not found: {script_path} for user {script_owner_id}")
             if script_owner_id in user_files:
                 user_files[script_owner_id] = [f for f in user_files.get(script_owner_id, []) if f[0] != file_name]
             remove_user_file_db(script_owner_id, file_name)
             return

        if attempt == 1:
            # Last line of defence for every start path (watchdog, Run All, imports). This runs BEFORE the
            # test run below: HIGH never runs, MEDIUM only after an admin approved it.
            allowed, gate_note = launch_gate(script_owner_id, file_name, 'py', 0, queue=False, admin_override=False)
            if not allowed:
                logger.warning("Security gate stopped %s for user %s", file_name, script_owner_id)
                bot.send_message(message_obj_for_reply.chat.id, gate_note, parse_mode='HTML')
                return

        if attempt == 1:
            check_command = [sys.executable, script_path]
            logger.info(f"Running Python pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **_popen_kwargs(user_folder, file_name))
                stdout, stderr = check_proc.communicate(timeout=5)
                return_code = check_proc.returncode
                logger.info(f"Python Pre-check early. RC: {return_code}. Stderr: {stderr[:200]}...")
                if return_code != 0 and stderr:
                    match_py = re.search(r"ModuleNotFoundError: No module named '(.+?)'", stderr)
                    if match_py:
                        module_name = match_py.group(1).strip().strip("'\"")
                        logger.info(f"Detected missing Python module: {module_name}")
                        success, _ = attempt_install_pip(module_name, message_obj_for_reply)
                        if success:
                            logger.info(f"Install OK for {module_name}. Retrying run_script...")
                            bot.reply_to(message_obj_for_reply, f"🔄 Install successful. Retrying '{file_name}'...")
                            time.sleep(2)
                            threading.Thread(target=run_script, args=(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt + 1)).start()
                            return
                        else:
                            bot.reply_to(message_obj_for_reply, f"❌ Install failed. Cannot run '{file_name}'.")
                            return
                    else:
                         error_summary = _short_code_block(stderr)
                         bot.reply_to(message_obj_for_reply, f"❌ Error in script pre-check for '{file_name}':\n```\n{error_summary}\n```\nFix the script.", parse_mode='Markdown')
                         return
            except subprocess.TimeoutExpired:
                logger.info("Python Pre-check timed out (>5s), imports likely OK. Killing check process.")
                _kill_check_process(check_proc)
                logger.info("Python Check process killed. Proceeding to long run.")
            except FileNotFoundError:
                 logger.error(f"Python interpreter not found: {sys.executable}")
                 bot.reply_to(message_obj_for_reply, f"❌ Error: Python interpreter '{sys.executable}' not found.")
                 return
            except Exception as e:
                 logger.error(f"Error in Python pre-check for {script_key}: {e}", exc_info=True)
                 bot.reply_to(message_obj_for_reply, f"❌ Unexpected error in script pre-check for '{file_name}': {e}")
                 return
            finally:
                 if check_proc and check_proc.poll() is None:
                     logger.warning(f"Python Check process {check_proc.pid} still running. Killing.")
                     _kill_check_process(check_proc)

        logger.info(f"Starting long-running Python process for {script_key}")
        log_file_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        log_file = None; process = None
        try: log_file = _prepare_log_file(log_file_path)
        except Exception as e:
             logger.error(f"Failed to open log file '{log_file_path}' for {script_key}: {e}", exc_info=True)
             bot.reply_to(message_obj_for_reply, f"❌ Failed to open log file '{log_file_path}': {e}")
             return
        try:
            process = subprocess.Popen(
                [sys.executable, '-u', script_path], cwd=user_folder, stdout=log_file, stderr=log_file,
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **_popen_kwargs(user_folder, file_name)
            )
            logger.info(f"Started Python process {process.pid} for {script_key}")
            _register_script(script_key, {
                'process': process, 'log_file': log_file, 'file_name': file_name,
                'chat_id': message_obj_for_reply.chat.id, # Chat ID for potential future direct replies from script, defaults to admin/triggering user
                'script_owner_id': script_owner_id, # Actual owner of the script
                'start_time': datetime.now(), 'user_folder': user_folder, 'type': 'py', 'script_key': script_key, 'reply_target': message_obj_for_reply
            })
            bot.reply_to(message_obj_for_reply, f"✅ Python script '{file_name}' started! (PID: {process.pid}) (For User: {script_owner_id})")
        except FileNotFoundError:
             logger.error(f"Python interpreter {sys.executable} not found for long run {script_key}")
             bot.reply_to(message_obj_for_reply, f"❌ Error: Python interpreter '{sys.executable}' not found.")
             if log_file and not log_file.closed: log_file.close()
             _forget_script(script_key)
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            error_msg = f"❌ Error starting Python script '{file_name}': {str(e)}"
            logger.error(error_msg, exc_info=True)
            bot.reply_to(message_obj_for_reply, error_msg)
            if process and process.poll() is None:
                 logger.warning(f"Killing potentially started Python process {process.pid} for {script_key}")
                 kill_process_tree({'process': process, 'log_file': log_file, 'script_key': script_key})
            _forget_script(script_key)
    except Exception as e:
        error_msg = f"❌ Unexpected error running Python script '{file_name}': {str(e)}"
        logger.error(error_msg, exc_info=True)
        bot.reply_to(message_obj_for_reply, error_msg)
        stale = _forget_script(script_key)
        if stale:
             logger.warning(f"Cleaning up {script_key} due to error in run_script.")
             kill_process_tree(stale)

def run_js_script(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    """Run JS script. script_owner_id is used for the script_key. message_obj_for_reply is for sending feedback."""
    max_attempts = 2
    if attempt > max_attempts:
        bot.reply_to(message_obj_for_reply, f"❌ Failed to run '{file_name}' after {max_attempts} attempts. Check logs.")
        return

    script_key = f"{script_owner_id}_{file_name}"
    logger.info(f"Attempt {attempt} to run JS script: {script_path} (Key: {script_key}) for user {script_owner_id}")

    try:
        if not os.path.exists(script_path):
             bot.reply_to(message_obj_for_reply, f"❌ Error: Script '{file_name}' not found at '{script_path}'!")
             logger.error(f"JS Script not found: {script_path} for user {script_owner_id}")
             if script_owner_id in user_files:
                 user_files[script_owner_id] = [f for f in user_files.get(script_owner_id, []) if f[0] != file_name]
             remove_user_file_db(script_owner_id, file_name)
             return

        if attempt == 1:
            # Last line of defence for every start path (watchdog, Run All, imports). This runs BEFORE the
            # test run below: HIGH never runs, MEDIUM only after an admin approved it.
            allowed, gate_note = launch_gate(script_owner_id, file_name, 'js', 0, queue=False, admin_override=False)
            if not allowed:
                logger.warning("Security gate stopped %s for user %s", file_name, script_owner_id)
                bot.send_message(message_obj_for_reply.chat.id, gate_note, parse_mode='HTML')
                return

        if attempt == 1:
            check_command = ['node', script_path]
            logger.info(f"Running JS pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **_popen_kwargs(user_folder, file_name))
                stdout, stderr = check_proc.communicate(timeout=5)
                return_code = check_proc.returncode
                logger.info(f"JS Pre-check early. RC: {return_code}. Stderr: {stderr[:200]}...")
                if return_code != 0 and stderr:
                    match_js = re.search(r"Cannot find module '(.+?)'", stderr)
                    if match_js:
                        module_name = match_js.group(1).strip().strip("'\"")
                        if not module_name.startswith('.') and not module_name.startswith('/'):
                             logger.info(f"Detected missing Node module: {module_name}")
                             success, _ = attempt_install_npm(module_name, user_folder, message_obj_for_reply)
                             if success:
                                 logger.info(f"NPM Install OK for {module_name}. Retrying run_js_script...")
                                 bot.reply_to(message_obj_for_reply, f"🔄 NPM Install successful. Retrying '{file_name}'...")
                                 time.sleep(2)
                                 threading.Thread(target=run_js_script, args=(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt + 1)).start()
                                 return
                             else:
                                 bot.reply_to(message_obj_for_reply, f"❌ NPM Install failed. Cannot run '{file_name}'.")
                                 return
                        else: logger.info(f"Skipping npm install for relative/core: {module_name}")
                    error_summary = _short_code_block(stderr)
                    bot.reply_to(message_obj_for_reply, f"❌ Error in JS script pre-check for '{file_name}':\n```\n{error_summary}\n```\nFix script or install manually.", parse_mode='Markdown')
                    return
            except subprocess.TimeoutExpired:
                logger.info("JS Pre-check timed out (>5s), imports likely OK. Killing check process.")
                _kill_check_process(check_proc)
                logger.info("JS Check process killed. Proceeding to long run.")
            except FileNotFoundError:
                 error_msg = "❌ Error: 'node' not found. Ensure Node.js is installed for JS files."
                 logger.error(error_msg)
                 bot.reply_to(message_obj_for_reply, error_msg)
                 return
            except Exception as e:
                 logger.error(f"Error in JS pre-check for {script_key}: {e}", exc_info=True)
                 bot.reply_to(message_obj_for_reply, f"❌ Unexpected error in JS pre-check for '{file_name}': {e}")
                 return
            finally:
                 if check_proc and check_proc.poll() is None:
                     logger.warning(f"JS Check process {check_proc.pid} still running. Killing.")
                     _kill_check_process(check_proc)

        logger.info(f"Starting long-running JS process for {script_key}")
        log_file_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        log_file = None; process = None
        try: log_file = _prepare_log_file(log_file_path)
        except Exception as e:
            logger.error(f"Failed to open log file '{log_file_path}' for JS script {script_key}: {e}", exc_info=True)
            bot.reply_to(message_obj_for_reply, f"❌ Failed to open log file '{log_file_path}': {e}")
            return
        try:
            process = subprocess.Popen(
                ['node', script_path], cwd=user_folder, stdout=log_file, stderr=log_file,
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **_popen_kwargs(user_folder, file_name)
            )
            logger.info(f"Started JS process {process.pid} for {script_key}")
            _register_script(script_key, {
                'process': process, 'log_file': log_file, 'file_name': file_name,
                'chat_id': message_obj_for_reply.chat.id, # Chat ID for potential future direct replies
                'script_owner_id': script_owner_id, # Actual owner of the script
                'start_time': datetime.now(), 'user_folder': user_folder, 'type': 'js', 'script_key': script_key, 'reply_target': message_obj_for_reply
            })
            bot.reply_to(message_obj_for_reply, f"✅ JS script '{file_name}' started! (PID: {process.pid}) (For User: {script_owner_id})")
        except FileNotFoundError:
             error_msg = "❌ Error: 'node' not found for long run. Ensure Node.js is installed."
             logger.error(error_msg)
             if log_file and not log_file.closed: log_file.close()
             bot.reply_to(message_obj_for_reply, error_msg)
             _forget_script(script_key)
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            error_msg = f"❌ Error starting JS script '{file_name}': {str(e)}"
            logger.error(error_msg, exc_info=True)
            bot.reply_to(message_obj_for_reply, error_msg)
            if process and process.poll() is None:
                 logger.warning(f"Killing potentially started JS process {process.pid} for {script_key}")
                 kill_process_tree({'process': process, 'log_file': log_file, 'script_key': script_key})
            _forget_script(script_key)
    except Exception as e:
        error_msg = f"❌ Unexpected error running JS script '{file_name}': {str(e)}"
        logger.error(error_msg, exc_info=True)
        bot.reply_to(message_obj_for_reply, error_msg)
        stale = _forget_script(script_key)
        if stale:
             logger.warning(f"Cleaning up {script_key} due to error in run_js_script.")
             kill_process_tree(stale)

# --- Logic Functions (called by commands and text handlers) ---
def _logic_send_welcome(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    user_name = message.from_user.first_name

    logger.info(f"Welcome request from user_id: {user_id}")

    # Check if user is banned
    if is_user_banned(user_id):
        bot.send_message(chat_id, "❌ You are banned from using this bot.")
        return

    # Check mandatory subscription FIRST - before anything else
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return

    if bot_locked and user_id not in admin_ids:
        bot.send_message(chat_id, "⚠️ Bot locked by admin. Try later.")
        return

    if user_id not in active_users:
        add_active_user(user_id)
        try:
            owner_notification = (f"🎉 New user!\n👤 Name: {user_name}\n🆔 ID: `{user_id}`")
            bot.send_message(OWNER_ID, owner_notification, parse_mode='Markdown')
        except Exception as e: 
            logger.error(f"⚠️ Failed to notify owner about new user {user_id}: {e}")

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    expiry_info = ""
    
    if user_id == OWNER_ID: 
        user_status = "👑 Owner"
    elif user_id in admin_ids: 
        user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"
            days_left = (expiry_date - datetime.now()).days
            expiry_info = f"\n⏳ Subscription expires in: {days_left} days"
        else: 
            user_status = "🆓 Free User (Expired Sub)"
            remove_subscription_db(user_id)
    else: 
        user_status = "🆓 Free User"

    welcome_msg_text = (f"<b>〽️ DEMON HOSTING</b>\n"
                        f"━━━━━━━━━━━━━━━━━━\n"
                        f"Welcome, <b>{html_escape(user_name)}</b>!\n\n"
                        f"🆔 <b>User ID:</b> <code>{user_id}</code>\n"
                        f"🔰 <b>Plan:</b> {user_status}{expiry_info}\n"
                        f"📁 <b>Storage:</b> {current_files} / {limit_str} files\n\n"
                        f"🚀 Host Python and JavaScript scripts, manage processes, inspect logs, and monitor your bots.\n\n"
                        f"<i>Select an option from the control panel below.</i>")
    try:
        bot.send_message(chat_id, welcome_msg_text, reply_markup=create_main_menu_inline(user_id), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error sending welcome to {user_id}: {e}", exc_info=True)

def _logic_updates_channel(message):
    markup = NavMenu()
    markup.add(NavButton('📢 Updates Channel', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'))
    bot.reply_to(message, "Visit our Updates Channel:", reply_markup=markup)

def _logic_upload_file(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "⚠️ Bot locked by admin, cannot accept files.")
        return

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.reply_to(message, f"⚠️ File limit ({current_files}/{limit_str}) reached. Purani file delete karo, ya backup export/import karo.", reply_markup=_files_view(user_id)[1])
        return
    _send_upload_choice(message.chat.id)

def _logic_check_files(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    text, menu = _files_view(user_id)
    bot.reply_to(message, text, reply_markup=menu)

def _logic_bot_speed(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_time_ping = time.time()
    wait_msg = bot.reply_to(message, "🏃 Testing speed...")
    try:
        bot.send_chat_action(chat_id, 'typing')
        response_time = round((time.time() - start_time_ping) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now(): user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        speed_msg = (f"⚡ Bot Speed & Status:\n\n⏱️ API Response Time: {response_time} ms\n"
                     f"🚦 Bot Status: {status}\n"
                     f"👤 Your Level: {user_level}")
        bot.edit_message_text(speed_msg, chat_id, wait_msg.message_id)
    except Exception as e:
        logger.error(f"Error during speed test (cmd): {e}", exc_info=True)
        bot.edit_message_text("❌ Error during speed test.", chat_id, wait_msg.message_id)

def _logic_contact_owner(message):
    markup = NavMenu()
    markup.add(NavButton('📞 Contact Owner', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
    bot.reply_to(message, "Click to contact Owner:", reply_markup=markup)

def _logic_manual_install(message):
    """Handle manual installation request from user"""
    manual_install_module_init(message)

def _logic_help(message):
    help_text = """
🤖 <b>DEMON Hosting Bot Help Guide</b>

<b>📌 Basic Commands:</b>
• /start - Start the bot
• /help - Show this help message
• /status - Show bot statistics

<b>📁 File Management:</b>
• Upload <code>.py</code> or <code>.js</code> files directly
• Upload <code>.zip</code> archives with multiple files
• Auto-installs dependencies from <code>requirements.txt</code> or <code>package.json</code>

<b>📦 Module Installation:</b>
• Auto-install missing Python/Node modules
• Manual install via "📦 Manual Install" button
• Admin can install modules for users

<b>👑 Admin Features:</b>
• User management (ban/unban)
• Set custom file limits
• Manage mandatory channels
• Broadcast messages
• Run all user scripts

<b>⚙️ Tips:</b>
1. Make sure your scripts don't contain dangerous commands
2. Join all required channels
3. Contact owner for subscription upgrades

<b>Support:</b> @DEMON_HOSTING_GROUP
<b>Updates:</b> @DEMON_HOSTING_GROUP
"""
    bot.reply_to(message, help_text, parse_mode='HTML')

# --- Admin Logic Functions ---
def _logic_subscriptions_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "💳 Subscription Management\nUse inline buttons from /start or admin command menu.", reply_markup=create_subscription_menu())

def _logic_statistics(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    total_users = len(active_users)
    total_files_records = sum(len(files) for files in user_files.values())

    running_bots_count = 0
    user_running_bots = 0

    for script_key_iter, script_info_iter in list(bot_scripts.items()):
        s_owner_id, _ = script_key_iter.split('_', 1) # Extract owner_id from key
        if is_bot_running(int(s_owner_id), script_info_iter['file_name']):
            running_bots_count += 1
            if int(s_owner_id) == user_id:
                user_running_bots +=1

    stats_msg_base = (f"📊 Bot Statistics:\n\n"
                      f"👥 Total Users: {total_users}\n"
                      f"🚫 Banned Users: {len(banned_users)}\n"
                      f"📂 Total File Records: {total_files_records}\n"
                      f"🟢 Total Active Bots: {running_bots_count}\n")

    if user_id in admin_ids:
        stats_msg_admin = (f"🔒 Bot Status: {'🔴 Locked' if bot_locked else '🟢 Unlocked'}\n"
                           f"📢 Mandatory Channels: {len(mandatory_channels)}\n"
                           f"⚙️ Custom Limits: {len(user_limits)}\n"
                           f"🤖 Your Running Bots: {user_running_bots}")
        stats_msg = stats_msg_base + stats_msg_admin
    else:
        stats_msg = stats_msg_base + f"🤖 Your Running Bots: {user_running_bots}"

    bot.reply_to(message, stats_msg)

def _logic_broadcast_init(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    msg = bot.reply_to(message, "📢 Send message to broadcast to all active users.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_broadcast_message)

def _logic_toggle_lock_bot(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    global bot_locked
    bot_locked = not bot_locked
    status = "locked" if bot_locked else "unlocked"
    logger.warning(f"Bot {status} by Admin {message.from_user.id} via command/button.")
    bot.reply_to(message, f"🔒 Bot has been {status}.")

def _logic_admin_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "👑 Admin Panel\nManage admins. Use inline buttons from /start or admin menu.",
                 reply_markup=create_admin_panel())

def _logic_user_management(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "👥 User Management\nManage users, set limits, ban/unban.", 
                 reply_markup=create_user_management_menu())

def _logic_admin_settings(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "⚙️ Admin Settings\nSystem information and management.", 
                 reply_markup=create_admin_settings_menu())

def _logic_hosting_health(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, build_hosting_health_report(), parse_mode="HTML")


def _logic_run_all_scripts(message_or_call):
    if isinstance(message_or_call, telebot.types.Message):
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.chat.id
        reply_func = lambda text, **kwargs: bot.reply_to(message_or_call, text, **kwargs)
        admin_message_obj_for_script_runner = message_or_call
    elif isinstance(message_or_call, telebot.types.CallbackQuery):
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.message.chat.id
        bot.answer_callback_query(message_or_call.id)
        reply_func = lambda text, **kwargs: bot.send_message(admin_chat_id, text, **kwargs)
        admin_message_obj_for_script_runner = message_or_call.message 
    else:
        logger.error("Invalid argument for _logic_run_all_scripts")
        return

    if admin_user_id not in admin_ids:
        reply_func("⚠️ Admin permissions required.")
        return

    reply_func("⏳ Starting process to run all user scripts. This may take a while...")
    logger.info(f"Admin {admin_user_id} initiated 'run all scripts' from chat {admin_chat_id}.")

    started_count = 0; attempted_users = 0; skipped_files = 0; error_files_details = []

    # Use a copy of user_files keys and values to avoid modification issues during iteration
    all_user_files_snapshot = dict(user_files)

    for target_user_id, files_for_user in all_user_files_snapshot.items():
        if not files_for_user: continue
        attempted_users += 1
        logger.info(f"Processing scripts for user {target_user_id}...")
        user_folder = get_user_folder(target_user_id)

        for file_name, file_type in files_for_user:
            # script_owner_id for key context is target_user_id
            if not is_bot_running(target_user_id, file_name):
                file_path = os.path.join(user_folder, file_name)
                if os.path.exists(file_path):
                    logger.info(f"Admin {admin_user_id} attempting to start '{file_name}' ({file_type}) for user {target_user_id}.")
                    try:
                        gate_ok, _gate_note = launch_gate(target_user_id, file_name, file_type, admin_user_id, queue=False, admin_override=False)
                        if not gate_ok:
                            error_files_details.append(f"`{file_name}` (User {target_user_id}) - held by security scan")
                            skipped_files += 1
                            continue
                        _reset_restart_state(target_user_id, file_name)
                        if file_type == 'py':
                            threading.Thread(target=run_script, args=(file_path, target_user_id, user_folder, file_name, admin_message_obj_for_script_runner)).start()
                            started_count += 1
                        elif file_type == 'js':
                            threading.Thread(target=run_js_script, args=(file_path, target_user_id, user_folder, file_name, admin_message_obj_for_script_runner)).start()
                            started_count += 1
                        else:
                            logger.warning(f"Unknown file type '{file_type}' for {file_name} (user {target_user_id}). Skipping.")
                            error_files_details.append(f"`{file_name}` (User {target_user_id}) - Unknown type")
                            skipped_files += 1
                        time.sleep(0.7) # Increased delay slightly
                    except Exception as e:
                        logger.error(f"Error queueing start for '{file_name}' (user {target_user_id}): {e}")
                        error_files_details.append(f"`{file_name}` (User {target_user_id}) - Start error")
                        skipped_files += 1
                else:
                    logger.warning(f"File '{file_name}' for user {target_user_id} not found at '{file_path}'. Skipping.")
                    error_files_details.append(f"`{file_name}` (User {target_user_id}) - File not found")
                    skipped_files += 1
            # else: logger.info(f"Script '{file_name}' for user {target_user_id} already running.")

    summary_msg = (f"✅ All Users' Scripts - Processing Complete:\n\n"
                   f"▶️ Attempted to start: {started_count} scripts.\n"
                   f"👥 Users processed: {attempted_users}.\n")
    if skipped_files > 0:
        summary_msg += f"⚠️ Skipped/Error files: {skipped_files}\n"
        if error_files_details:
             summary_msg += "Details (first 5):\n" + "\n".join([f"  - {err}" for err in error_files_details[:5]])
             if len(error_files_details) > 5: summary_msg += "\n  ... and more (check logs)."

    reply_func(summary_msg, parse_mode='Markdown')
    logger.info(f"Run all scripts finished. Admin: {admin_user_id}. Started: {started_count}. Skipped/Errors: {skipped_files}")

# --- New Admin Functions for Channel Management ---
def _logic_manage_mandatory_channels(message):
    """Manage mandatory channels - for admin only"""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "📢 Manage Mandatory Channels\nUse the buttons below:", reply_markup=create_mandatory_channels_menu())

def _logic_admin_install(message):
    """Admin manual installation for users"""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    msg = bot.reply_to(message, "🛠️ Admin Module Installation\nSend user ID and module name (e.g., `12345678 requests`)\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_admin_install)

def process_admin_install(message):
    """Process admin installation request"""
    admin_id = message.from_user.id
    if admin_id not in admin_ids:
        bot.reply_to(message, "⚠️ Not authorized.")
        return
        
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Installation cancelled.")
        return
    
    try:
        parts = message.text.split()
        if len(parts) < 2:
            bot.reply_to(message, "⚠️ Format: `user_id module_name`\nExample: `12345678 requests`")
            return
            
        user_id = int(parts[0])
        module_name = ' '.join(parts[1:])
        
        # Check if it's a Node.js module
        if module_name.lower().startswith('npm:'):
            module_name = module_name[4:].strip()
            user_folder = get_user_folder(user_id)
            success, log = attempt_install_npm(module_name, user_folder, message, manual_request=True)
        else:
            # Python module
            success, log = attempt_install_pip(module_name, message, manual_request=True)
        
        if success:
            logger.info(f"Admin {admin_id} installed module {module_name} for user {user_id}")
            # Notify user
            try:
                bot.send_message(user_id, f"📦 Admin installed module `{module_name}` for you.")
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error in admin install: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

# --- Command Handlers & Text Handlers for ReplyKeyboard ---
@bot.message_handler(commands=['start', 'help'])
def command_send_welcome(message): 
    if message.text == '/help':
        _logic_help(message)
    else:
        _logic_send_welcome(message)

@bot.message_handler(commands=['account'])
def command_account(message):
    _nav_run(message, 'user_account')

@bot.message_handler(commands=['mybots'])
def command_mybots(message):
    _nav_run(message, 'my_running')

@bot.message_handler(commands=['admindashboard'])
def command_admindashboard(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, 'Admin permissions required.'); return
    _nav_run(message, 'admin_dashboard')

@bot.message_handler(commands=['status']) # Kept for direct command
def command_show_status(message): _logic_statistics(message)

@bot.message_handler(commands=['hosthealth'])
def command_hosthealth(message):
    _logic_hosting_health(message)

@bot.message_handler(commands=['retryfailed'])
def command_retryfailed(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required."); return
    threading.Thread(target=retry_failed_scripts,
                     args=(message.from_user.id, message.chat.id), daemon=True).start()

BUTTON_TEXT_TO_LOGIC = {
    "🏠 Main Menu": _logic_send_welcome,
    "👤 Account": lambda message: _nav_run(message, 'user_account'),
    "🤖 My Bots": lambda message: _nav_run(message, 'my_running'),
    "📢 Updates Channel": _logic_updates_channel,
    "📤 Upload File": _logic_upload_file,
    "📂 Check Files": _logic_check_files,
    "⚡ Bot Speed": _logic_bot_speed,
    "📞 Contact Owner": _logic_contact_owner,
    "📊 Statistics": _logic_statistics, 
    "💳 Subscriptions": _logic_subscriptions_panel,
    "📢 Broadcast": _logic_broadcast_init,
    "🔒 Lock Bot": _logic_toggle_lock_bot, 
    "🟢 Running All Code": _logic_run_all_scripts,
    "👑 Admin Panel": _logic_admin_panel,
    "📢 Channel Add": _logic_manage_mandatory_channels,
    "👥 User Management": _logic_user_management,
    "🛠️ Manual Install": _logic_manual_install,
    "⚙️ Settings": _logic_admin_settings,
    "🩺 Hosting Health": _logic_hosting_health,
    "📦 Manual Install": _logic_manual_install,
    "🆘 Help": _logic_help
}

@bot.message_handler(func=_nav_is_label, content_types=['text'])
def handle_nav_key(message):
    _nav_dispatch(message)


@bot.message_handler(func=lambda message: message.text in BUTTON_TEXT_TO_LOGIC)
def handle_button_text(message):
    logic_func = BUTTON_TEXT_TO_LOGIC.get(message.text)
    if logic_func: logic_func(message)
    else: logger.warning(f"Button text '{message.text}' matched but no logic func.")

@bot.message_handler(commands=['updateschannel'])
def command_updates_channel(message): _logic_updates_channel(message)
@bot.message_handler(commands=['uploadfile'])
def command_upload_file(message): _logic_upload_file(message)
@bot.message_handler(commands=['checkfiles'])
def command_check_files(message): _logic_check_files(message)
@bot.message_handler(commands=['botspeed'])
def command_bot_speed(message): _logic_bot_speed(message)
@bot.message_handler(commands=['contactowner'])
def command_contact_owner(message): _logic_contact_owner(message)
@bot.message_handler(commands=['subscriptions'])
def command_subscriptions(message): _logic_subscriptions_panel(message)
@bot.message_handler(commands=['statistics']) # Alias for /status
def command_statistics(message): _logic_statistics(message)
@bot.message_handler(commands=['broadcast'])
def command_broadcast(message): _logic_broadcast_init(message)
@bot.message_handler(commands=['lockbot']) 
def command_lock_bot(message): _logic_toggle_lock_bot(message)
@bot.message_handler(commands=['adminpanel'])
def command_admin_panel(message): _logic_admin_panel(message)
@bot.message_handler(commands=['runningallcode']) # Added
def command_run_all_code(message): _logic_run_all_scripts(message)
@bot.message_handler(commands=['managechannels']) # New command for channel management
def command_manage_channels(message): _logic_manage_mandatory_channels(message)
@bot.message_handler(commands=['usermanagement'])
def command_user_management(message): _logic_user_management(message)
@bot.message_handler(commands=['manualinstall'])
def command_manual_install(message): _logic_manual_install(message)
@bot.message_handler(commands=['admininstall'])
def command_admin_install(message): _logic_admin_install(message)

@bot.message_handler(commands=['ping'])
def ping(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_ping_time = time.time() 
    msg = bot.reply_to(message, "Pong!")
    latency = round((time.time() - start_ping_time) * 1000, 2)
    bot.edit_message_text(f"Pong! Latency: {latency} ms", message.chat.id, msg.message_id)

def _sanitize_upload_filename(raw_name, max_stem=32):
    """Return a safe short filename suitable for filesystem paths and Telegram callbacks."""
    raw_name = (raw_name or '').replace('\\', '/')
    base = os.path.basename(raw_name).strip()
    stem, ext = os.path.splitext(base)
    ext = ext.lower()
    if ext not in ('.py', '.js', '.zip'):
        raise ValueError('Only .py, .js and .zip files are supported.')
    stem = re.sub(r'[^A-Za-z0-9_-]+', '_', stem).strip('._-')
    if not stem:
        stem = 'uploaded_script'
    stem = stem[:max_stem]
    return f'{stem}{ext}'


# --- Document (File) Handler ---
def _show_verdict(message, wait_msg, text):
    """Show the uploader their verdict: edit the 'Processing' message in place, or reply if that fails."""
    try:
        bot.edit_message_text(text, message.chat.id, wait_msg.message_id, parse_mode='HTML')
    except Exception as exc:
        logger.debug('Could not edit verdict message: %s', type(exc).__name__)
        _safe_send(message.chat.id, text)


def _handle_scanned_upload(message, user_id, chat_id, file_name, file_ext, data, wait_msg):
    """Static scan of an upload (the file is never run by the scan). Admin uploads run directly.
    LOW -> start it, MEDIUM -> hold it for an admin, HIGH -> reject and drop it."""
    file_type = file_ext[1:]
    if user_id in admin_ids:
        result = _build_result([], file_name, file_type, len(data))
        result['sha256'] = hashlib.sha256(data).hexdigest()
        ok, err = _deploy_upload(user_id, file_name, file_type, data, message, result, 'admin')
        if not ok and err:
            _safe_send(chat_id, f'⚠️ {html_escape(err)}')
        return
    result = _scan_upload(data, file_ext, file_name)
    level = result['level']
    uploader = message.from_user.first_name or message.from_user.username or str(user_id)
    logger.info('Upload scan: user=%s file=%s level=%s', user_id, file_name, level)
    if level == THREAT_HIGH:
        _show_verdict(message, wait_msg, _user_verdict_text(result, file_name, 'rejected'))
        notice = (f"🔴 High-threat upload reject hua: <code>{html_escape(file_name)}</code> from "
                  f"{html_escape(uploader)} (<code>{user_id}</code>)\n{_reason_lines_html(result, 2)}")
        for admin_id in sorted(admin_ids):
            _safe_send(admin_id, notice)
        return
    if level == THREAT_MEDIUM:
        token, err = _submit_for_review(user_id, uploader, chat_id, message.message_id, file_name, file_type, data, result)
        if token:
            _show_verdict(message, wait_msg, _user_verdict_text(result, file_name, 'review'))
        else:
            _show_verdict(message, wait_msg, f"{THREAT_BADGE[level]} Start nahi hua. {html_escape(err)}")
        return
    _show_verdict(message, wait_msg, _user_verdict_text(result, file_name, 'auto'))
    ok, err = _deploy_upload(user_id, file_name, file_type, data, message, result, 'auto')
    if not ok and err:
        _safe_send(chat_id, f'⚠️ {html_escape(err)}')


@bot.message_handler(content_types=['document'])
def handle_file_upload_doc(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot.")
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return

    # A database / bot-data import that is waiting for its file takes this upload.
    if _handle_pending_import_upload(message):
        return

    doc = message.document
    logger.info(f"Doc from {user_id}: {doc.file_name} ({doc.mime_type}), Size: {doc.file_size}")

    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "⚠️ Bot locked, cannot accept files.")
        return

    # File limit check (relies on FREE_USER_LIMIT being > 0 for free users)
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.reply_to(message, f"⚠️ File limit ({current_files}/{limit_str}) reached. Purani file delete karo, ya backup export/import karo.", reply_markup=_files_view(user_id)[1])
        return

    if not doc.file_name: bot.reply_to(message, "⚠️ No file name. Ensure file has a name."); return
    try:
        file_name = _sanitize_upload_filename(doc.file_name)
    except ValueError as name_error:
        bot.reply_to(message, f"⚠️ {name_error}"); return
    file_ext = os.path.splitext(file_name)[1].lower()
    if file_ext not in ['.py', '.js', '.zip']:
        bot.reply_to(message, "⚠️ Unsupported type! Only `.py`, `.js`, `.zip` allowed.")
        return
    max_file_size = MAX_UPLOAD_MB * 1024 * 1024
    if (doc.file_size or 0) > max_file_size:
        bot.reply_to(message, f"⚠️ File too large (Max: {max_file_size // 1024 // 1024} MB)."); return

    try:
        try:
            bot.forward_message(OWNER_ID, chat_id, message.message_id)
            bot.send_message(OWNER_ID, f"⬆️ File '{file_name}' from {message.from_user.first_name} (`{user_id}`)", parse_mode='Markdown')
        except Exception as e: logger.error(f"Failed to forward uploaded file to OWNER_ID {OWNER_ID}: {e}")

        download_wait_msg = bot.reply_to(message, f"⏳ Downloading `{file_name}`...")
        file_info_tg_doc = bot.get_file(doc.file_id)
        downloaded_file_content = bot.download_file(file_info_tg_doc.file_path)
        bot.edit_message_text(f"✅ Downloaded `{file_name}`. Processing...", chat_id, download_wait_msg.message_id)
        logger.info(f"Downloaded {file_name} for user {user_id}")
        user_folder = get_user_folder(user_id)

        # Never silently overwrite an existing script after filename normalization.
        existing_names = {item[0] for item in user_files.get(user_id, [])}
        if file_name in existing_names or os.path.exists(os.path.join(user_folder, file_name)):
            bot.reply_to(message, f"⚠️ <code>{html_escape(file_name)}</code> already exists. Rename the upload before sending it again.", parse_mode='HTML')
            return

        # --- Security scan (static, never runs the file). LOW runs, MEDIUM waits for an admin, HIGH is rejected. ---
        _handle_scanned_upload(message, user_id, chat_id, file_name, file_ext, downloaded_file_content, download_wait_msg)
    except telebot.apihelper.ApiTelegramException as e:
         logger.error(f"Telegram API Error handling file for {user_id}: {e}", exc_info=True)
         if "file is too big" in str(e).lower():
              bot.reply_to(message, "❌ Telegram API Error: File too large to download (~20MB limit).")
         else: bot.reply_to(message, f"❌ Telegram API Error: {str(e)}. Try later.")
    except Exception as e:
        logger.error(f"❌ General error handling file for {user_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Unexpected error: {str(e)}")

# --- Callback Query Handlers (for Inline Buttons) ---
@bot.callback_query_handler(func=lambda call: True)
def legacy_inline_callback(call):
    """Inline buttons in messages sent before the keyboard upgrade: tell the person and show the menu."""
    try:
        bot.answer_callback_query(call.id, "Ye button purana hai, menu se dobara try karo.")
    except Exception:
        pass
    try:
        bot.send_message(call.message.chat.id, NAV_OLD_BUTTON_NOTE, reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception:
        logger.exception("Could not answer an old inline button")


def handle_callbacks(call):
    user_id = call.from_user.id
    data = call.data
    logger.info(f"Callback: User={user_id}, Data='{data}'")

    # Check if user is banned
    if is_user_banned(user_id) and data not in ['back_to_main']:
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return

    # Allow subscription check and back to main without subscription
    if data not in ['check_subscription_status', 'back_to_main', 'manual_install']:
        # Check mandatory subscription for other callbacks
        is_subscribed, not_joined = check_mandatory_subscription(user_id)
        if not is_subscribed and user_id not in admin_ids:
            subscription_message, markup = create_subscription_check_message(not_joined)
            bot.answer_callback_query(call.id)
            try:
                bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
            except Exception:
                bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
            return

    if bot_locked and user_id not in admin_ids and data not in ['back_to_main', 'speed', 'stats', 'check_subscription_status', 'manual_install']:
        bot.answer_callback_query(call.id, "⚠️ Bot locked by admin.", show_alert=True)
        return
        
    try:
        if data == 'upload': upload_callback(call)
        elif data == 'gh_start': gh_start_callback(call)
        elif data == 'gh_manual': gh_manual_callback(call)
        elif data.startswith(('ghp_', 'ghx_')): gh_pick_callback(call)
        elif data.startswith('ghu_'): gh_update_callback(call)
        elif data == 'check_files': check_files_callback(call)
        elif data.startswith('file_'): file_control_callback(call)
        elif data.startswith('start_'): start_bot_callback(call)
        elif data.startswith('stop_'): stop_bot_callback(call)
        elif data.startswith('restart_'): restart_bot_callback(call)
        elif data.startswith('delete_'): delete_bot_callback(call)
        elif data.startswith('logs_'): logs_bot_callback(call)
        elif data.startswith(('envm_', 'envv_', 'enva_', 'envd_', 'envk_', 'envc_', 'envy_')): env_callback(call)
        elif data == 'speed': speed_callback(call)
        elif data == 'user_account': user_account_callback(call)
        elif data == 'my_running': my_running_callback(call)
        elif data == 'user_help': user_help_callback(call)
        elif data == 'admin_dashboard': admin_required_callback(call, admin_dashboard_callback)
        elif data == 'database_backup': admin_required_callback(call, database_backup_callback)
        elif data == 'export_users': admin_required_callback(call, export_users_callback)
        elif data == 'export_database': admin_required_callback(call, full_backup_callback)
        elif data == 'import_database': admin_required_callback(call, full_restore_callback)
        elif data.startswith('impc_'): import_confirm_callback(call)
        elif data.startswith('ubk_'): user_backup_callback(call)
        elif data.startswith('ubr_'): user_restore_callback(call)
        elif data == 'back_to_main': back_to_main_callback(call)
        elif data.startswith('confirm_broadcast_'): handle_confirm_broadcast(call)
        elif data == 'cancel_broadcast': handle_cancel_broadcast(call)
        elif data == 'manual_install': manual_install_callback(call)
        # --- Admin Callbacks ---
        elif data == 'subscription': admin_required_callback(call, subscription_management_callback)
        elif data == 'stats': stats_callback(call) # No admin check here, handled in func
        elif data == 'lock_bot': admin_required_callback(call, lock_bot_callback)
        elif data == 'unlock_bot': admin_required_callback(call, unlock_bot_callback)
        elif data == 'run_all_scripts': admin_required_callback(call, run_all_scripts_callback)
        elif data == 'broadcast': admin_required_callback(call, broadcast_init_callback) 
        elif data == 'admin_panel': admin_required_callback(call, admin_panel_callback)
        elif data == 'add_admin': owner_required_callback(call, add_admin_init_callback) 
        elif data == 'remove_admin': owner_required_callback(call, remove_admin_init_callback) 
        elif data == 'list_admins': admin_required_callback(call, list_admins_callback)
        elif data == 'add_subscription': admin_required_callback(call, add_subscription_init_callback) 
        elif data == 'remove_subscription': admin_required_callback(call, remove_subscription_init_callback) 
        elif data == 'check_subscription': admin_required_callback(call, check_subscription_init_callback)
        elif data == 'user_management': admin_required_callback(call, user_management_callback)
        elif data == 'ban_user': admin_required_callback(call, ban_user_callback)
        elif data == 'unban_user': admin_required_callback(call, unban_user_callback)
        elif data == 'user_info': admin_required_callback(call, user_info_callback)
        elif data == 'all_users': admin_required_callback(call, all_users_callback)
        elif data == 'set_user_limit': admin_required_callback(call, set_user_limit_callback)
        elif data == 'remove_user_limit': admin_required_callback(call, remove_user_limit_callback)
        elif data == 'admin_settings': admin_required_callback(call, admin_settings_callback)
        elif data == 'system_info': admin_required_callback(call, system_info_callback)
        elif data == 'bot_performance': admin_required_callback(call, bot_performance_callback)
        elif data == 'hosting_health': admin_required_callback(call, hosting_health_callback)
        elif data == 'retry_failed_bots': admin_required_callback(call, retry_failed_callback)
        elif data == 'cleanup_files': admin_required_callback(call, cleanup_files_callback)
        elif data == 'install_logs': admin_required_callback(call, install_logs_callback)
        elif data == 'admin_install': admin_required_callback(call, admin_install_callback)
        # --- Mandatory Channels Callbacks ---
        elif data == 'manage_mandatory_channels': admin_required_callback(call, manage_mandatory_channels_callback)
        elif data == 'add_mandatory_channel': admin_required_callback(call, add_mandatory_channel_callback)
        elif data == 'remove_mandatory_channel': admin_required_callback(call, remove_mandatory_channel_callback)
        elif data == 'list_mandatory_channels': admin_required_callback(call, list_mandatory_channels_callback)
        elif data.startswith('remove_channel_'): admin_required_callback(call, process_remove_channel)
        elif data == 'check_subscription_status': check_subscription_status_callback(call)
        # --- Upload approvals (admins only) ---
        elif data.startswith('rv_'): admin_required_callback(call, review_callback)
        elif data in ('adm_approvals', 'sec_center', 'sec_queue'): admin_required_callback(call, approvals_callback)
        # --- Security Approval Callbacks (older approval buttons that may still be in chats) ---
        elif data.startswith('approve_file_'): admin_required_callback(call, process_approve_file)
        elif data.startswith('reject_file_'): admin_required_callback(call, process_reject_file)
        elif data.startswith('approve_zip_'): admin_required_callback(call, process_approve_zip)
        elif data.startswith('reject_zip_'): admin_required_callback(call, process_reject_zip)
        # --- Users list paging ---
        elif data.startswith('users_page_'): handle_users_page(call)
        elif data == 'noop': bot.answer_callback_query(call.id)
        else:
            bot.answer_callback_query(call.id, "Unknown action.")
            logger.warning(f"Unhandled callback data: {data} from user {user_id}")
    except Exception as e:
        logger.error(f"Error handling callback '{data}' for {user_id}: {e}", exc_info=True)
        try: bot.answer_callback_query(call.id, "Error processing request.", show_alert=True)
        except Exception as e_ans: logger.error(f"Failed to answer callback after error: {e_ans}")

def _user_plan_label(user_id):
    if user_id == OWNER_ID:
        return "👑 Owner"
    if user_id in admin_ids:
        return "🛡️ Administrator"
    sub = user_subscriptions.get(user_id)
    if sub:
        expiry = sub.get('expiry')
        if expiry and expiry > datetime.now():
            return "⭐ Premium"
    return "🆓 Free"


def user_account_callback(call):
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    limit = get_user_file_limit(user_id)
    limit_text = "Unlimited" if limit == float('inf') else str(limit)
    files_count = get_user_file_count(user_id)
    running_count = 0
    for key, info in list(bot_scripts.items()):
        try:
            if int(info.get('script_owner_id', -1)) == user_id and info.get('process') and info['process'].poll() is None:
                running_count += 1
        except Exception:
            continue
    sub = user_subscriptions.get(user_id, {})
    expiry = sub.get('expiry')
    expiry_text = expiry.strftime('%d %b %Y, %H:%M') if expiry and expiry > datetime.now() else 'Not active'
    text = (
        "<b>👤 MY ACCOUNT</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🆔 <b>ID:</b> <code>{user_id}</code>\n"
        f"🏷️ <b>Plan:</b> {_user_plan_label(user_id)}\n"
        f"📁 <b>Files:</b> {files_count} / {limit_text}\n"
        f"🟢 <b>Running scripts:</b> {running_count}\n"
        f"⭐ <b>Premium expiry:</b> {expiry_text}\n\n"
        "<i>Your account and hosting usage at a glance.</i>"
    )
    kb = NavMenu(row_width=2)
    kb.row(NavButton('📂 Manage Files', callback_data='check_files'),
           NavButton('🤖 Running Bots', callback_data='my_running'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def my_running_callback(call):
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    rows = []
    for key, info in list(bot_scripts.items()):
        try:
            if int(info.get('script_owner_id', -1)) != user_id:
                continue
            proc = info.get('process')
            if proc and proc.poll() is None:
                rows.append((info.get('file_name', 'Unknown'), key))
        except Exception:
            continue
    kb = NavMenu(row_width=1)
    if rows:
        for name, key in rows[:40]:
            owner_part, file_part = key.split('_', 1)
            kb.add(NavButton(f'🟢 {name}', callback_data=f'file_{owner_part}_{file_part}'))
        body = f"<b>🤖 YOUR RUNNING SCRIPTS</b>\n━━━━━━━━━━━━━━━━━━\n🟢 Active processes: <b>{len(rows)}</b>\n\nSelect a script to open its controls."
    else:
        body = "<b>🤖 YOUR RUNNING SCRIPTS</b>\n━━━━━━━━━━━━━━━━━━\nNo scripts are running right now.\n\nUpload a script or start one from My Files."
    kb.add(NavButton('📂 My Files', callback_data='check_files'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(body, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def user_help_callback(call):
    bot.answer_callback_query(call.id)
    text = (
        "<b>🆘 HOSTING HELP CENTER</b>\n━━━━━━━━━━━━━━━━━━\n"
        "<b>1.</b> Upload a <code>.py</code>, <code>.js</code>, or supported <code>.zip</code> file.\n"
        "<b>2.</b> Open <b>My Files</b> and select your script.\n"
        "<b>3.</b> Use Start, Stop, Restart, or Logs.\n"
        "<b>4.</b> If a dependency is missing, use Module Install.\n\n"
        "<b>Useful commands</b>\n/start — Main menu\n/status — Statistics\n/ping — Response test\n/cancel — Cancel supported pending actions\n\n"
        "For account or hosting issues, contact the owner."
    )
    kb = NavMenu(row_width=2)
    kb.row(NavButton('📂 My Files', callback_data='check_files'),
           NavButton('📞 Contact Support', url='https://t.me/' + YOUR_USERNAME.replace('@', '')))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def admin_dashboard_callback(call):
    bot.answer_callback_query(call.id)
    running = 0
    for info in list(bot_scripts.values()):
        try:
            if info.get('process') and info['process'].poll() is None:
                running += 1
        except Exception:
            pass
    total_files = sum(len(items) for items in user_files.values())
    total_users = len(active_users)
    premium = sum(1 for item in user_subscriptions.values()
                  if item.get('expiry') and item['expiry'] > datetime.now())
    exhausted = sum(1 for state in RESTART_STATE.values() if state.get('attempts', 0) >= MAX_AUTO_RESTARTS)
    body = (
        "<b>👑 ADMIN CONTROL CENTER</b>\n━━━━━━━━━━━━━━━━━━\n"
        f"👥 <b>Users:</b> {total_users}\n"
        f"⭐ <b>Active premium:</b> {premium}\n"
        f"📦 <b>Stored scripts:</b> {total_files}\n"
        f"🟢 <b>Running processes:</b> {running}\n"
        f"🔁 <b>Restart limit reached:</b> {exhausted}\n"
        f"🔐 <b>Service mode:</b> {'Maintenance' if bot_locked else 'Online'}\n\n"
        "<i>Administrative tools and quick operations.</i>"
    )
    kb = NavMenu(row_width=2)
    kb.row(NavButton('🩺 Hosting Health', callback_data='hosting_health'),
           NavButton('👥 Users', callback_data='user_management'))
    kb.row(NavButton('📢 Broadcast', callback_data='broadcast'),
           NavButton('💳 Subscriptions', callback_data='subscription'))
    kb.row(NavButton('🗄 Database Backup', callback_data='database_backup'),
           NavButton('📤 Export Users', callback_data='export_users'))
    kb.row(NavButton('📦 Export Full Backup', callback_data='export_database'),
           NavButton('♻️ Import Full Backup', callback_data='import_database'))
    kb.row(NavButton('⚙️ Settings', callback_data='admin_settings'),
           NavButton('👑 Admins', callback_data='admin_panel'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(body, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def database_backup_callback(call):
    bot.answer_callback_query(call.id, 'Preparing a consistent SQLite backup…')
    _fd, backup_path = tempfile.mkstemp(prefix='demon_backup_', suffix='.db'); os.close(_fd)
    try:
        with DB_LOCK:
            source = db_connect()
            target = sqlite3.connect(backup_path)
            try:
                source.backup(target)
            finally:
                target.close()
                source.close()
        with open(backup_path, 'rb') as backup_file:
            bot.send_document(call.message.chat.id, backup_file,
                              caption='<b>🗄 Database Backup</b>\nConsistent SQLite snapshot.',
                              parse_mode='HTML')
    except Exception as exc:
        logger.exception('Database backup failed')
        bot.send_message(call.message.chat.id, f'⚠️ Backup failed: <code>{html_escape(str(exc))}</code>', parse_mode='HTML')
    finally:
        try:
            if os.path.exists(backup_path):
                os.remove(backup_path)
        except OSError:
            pass


def export_users_callback(call):
    bot.answer_callback_query(call.id, 'Preparing user export…')
    _fd, export_path = tempfile.mkstemp(prefix='demon_users_', suffix='.csv'); os.close(_fd)
    try:
        with DB_LOCK:
            conn = db_connect()
            try:
                rows = conn.execute('SELECT user_id, join_date, last_seen FROM active_users ORDER BY join_date DESC').fetchall()
            finally:
                conn.close()
        import csv
        with open(export_path, 'w', newline='', encoding='utf-8-sig') as handle:
            writer = csv.writer(handle)
            writer.writerow(['user_id', 'join_date', 'last_seen', 'plan', 'banned'])
            for uid, joined, seen in rows:
                writer.writerow([uid, joined, seen, _user_plan_label(uid), 'yes' if uid in banned_users else 'no'])
        with open(export_path, 'rb') as export_file:
            bot.send_document(call.message.chat.id, export_file,
                              caption=f'<b>📤 User Export</b>\nRecords: <b>{len(rows)}</b>', parse_mode='HTML')
    except Exception as exc:
        logger.exception('User export failed')
        bot.send_message(call.message.chat.id, f'⚠️ Export failed: <code>{html_escape(str(exc))}</code>', parse_mode='HTML')
    finally:
        try:
            if os.path.exists(export_path):
                os.remove(export_path)
        except OSError:
            pass


def admin_required_callback(call, func_to_run):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "⚠️ Admin permissions required.", show_alert=True)
        return
    func_to_run(call) 

def owner_required_callback(call, func_to_run):
    if call.from_user.id != OWNER_ID:
        bot.answer_callback_query(call.id, "⚠️ Owner permissions required.", show_alert=True)
        return
    func_to_run(call)

# --- User Callbacks ---
def manual_install_callback(call):
    bot.answer_callback_query(call.id)
    manual_install_module_init(call.message)

def upload_callback(call):
    user_id = call.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception:
            bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, f"⚠️ File limit ({current_files}/{limit_str}) reached. Purani file delete karo, ya backup export/import karo.",
                         reply_markup=_files_view(user_id)[1])
        return
    bot.answer_callback_query(call.id) 
    _send_upload_choice(call.message.chat.id)

def check_files_callback(call):
    user_id = call.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception:
            bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    bot.answer_callback_query(call.id)
    text, menu = _files_view(user_id)
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, reply_markup=menu)

def file_control_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id

        # Allow owner/admin to control any file, or user to control their own
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            logger.warning(f"User {requesting_user_id} tried to access file '{file_name}' of user {script_owner_id} without permission.")
            bot.answer_callback_query(call.id, "⚠️ You can only manage your own files.", show_alert=True)
            check_files_callback(call) # Show their own files
            return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            logger.warning(f"File '{file_name}' not found for user {script_owner_id} during control.")
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True)
            # If admin was viewing, this might be confusing. For now, just show their own.
            check_files_callback(call) 
            return

        bot.answer_callback_query(call.id) 
        is_running = is_bot_running(script_owner_id, file_name)
        status_text = '🟢 Running' if is_running else '🔴 Stopped'
        file_type = next((f[1] for f in user_files_list if f[0] == file_name), '?') 
        try:
            source_info = gh_read_sidecar(get_user_folder(script_owner_id), file_name)[0]
            source_line = f"\n🐙 Source: `{source_info['url']}`" if source_info else ''
            bot.edit_message_text(
                f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: {status_text}{source_line}",
                call.message.chat.id, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_running),
                parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified (controls for {file_name})")
             else: raise 
    except (ValueError, IndexError) as ve:
        logger.error(f"Error parsing file control callback: {ve}. Data: '{call.data}'")
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in file_control_callback for data '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)

def _gate_button_start(call, owner_id, file_name, file_type):
    """Security check for the Start / Restart buttons. Returns True when the file may start. Otherwise the
    panel is edited in place to show the threat level and what happens next (a running bot is left alone)."""
    allowed, note = launch_gate(owner_id, file_name, file_type, call.from_user.id)
    if allowed:
        return True
    try:
        bot.answer_callback_query(call.id, '🛡 Not started - security check')
    except Exception as exc:
        logger.debug('answer_callback_query: %s', type(exc).__name__)
    running = is_bot_running(owner_id, file_name)
    try:
        bot.edit_message_text(f"{note}\n\n📄 <code>{html_escape(file_name)}</code>", call.message.chat.id, call.message.message_id,
                              parse_mode='HTML', reply_markup=create_control_buttons(owner_id, file_name, running))
    except Exception as exc:
        logger.debug('Could not edit gate note: %s', type(exc).__name__)
        _safe_send(call.message.chat.id, note, parse_mode='HTML')
    return False


def start_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id # Where the admin/user gets the reply

        logger.info(f"Start request: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")

        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied to start this script.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1]
        user_folder = get_user_folder(script_owner_id)
        file_path = os.path.join(user_folder, file_name)

        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ Error: File `{file_name}` missing! Re-upload.", show_alert=True)
            remove_user_file_db(script_owner_id, file_name); check_files_callback(call); return

        if is_bot_running(script_owner_id, file_name):
            bot.answer_callback_query(call.id, f"⚠️ Script '{file_name}' already running.", show_alert=True)
            try: bot.edit_message_reply_markup(chat_id_for_reply, call.message.message_id, reply_markup=create_control_buttons(script_owner_id, file_name, True))
            except Exception as e: logger.error(f"Error updating buttons (already running): {e}")
            return

        if not _gate_button_start(call, script_owner_id, file_name, file_type):
            return

        RESTART_STATE[_script_key(script_owner_id, file_name)] = {"attempts": 0, "manual_stop": False}
        bot.answer_callback_query(call.id, f"⏳ Attempting to start {file_name} for user {script_owner_id}...")

        # Pass call.message as message_obj_for_reply so feedback goes to the person who clicked
        if file_type == 'py':
            launcher = threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        elif file_type == 'js':
            launcher = threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        else:
             bot.send_message(chat_id_for_reply, f"❌ Error: Unknown file type '{file_type}' for '{file_name}'."); return 
        launcher.start()

        # The launcher first test-runs the script for about 5 seconds, so wait for it to finish.
        # Otherwise the panel keeps showing "Starting" with a Start button after the script is already up.
        launcher.join(timeout=LAUNCH_WAIT_SECONDS)
        time.sleep(0.5)
        is_now_running = is_bot_running(script_owner_id, file_name) 
        if is_now_running:
            status_text = '🟢 Running'
        elif launcher.is_alive():
            status_text = '🟡 Still starting (installing modules?). Open Check Files again in a moment'
        else:
            status_text = '🔴 Not running. See the message above or the logs'
        try:
            bot.edit_message_text(
                f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: {status_text}",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_now_running), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified after starting {file_name}")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing start callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid start command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in start_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error starting script.", show_alert=True)
        try: # Attempt to reset buttons to 'stopped' state on error
            _, script_owner_id_err_str, file_name_err = call.data.split('_', 2)
            script_owner_id_err = int(script_owner_id_err_str)
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_control_buttons(script_owner_id_err, file_name_err, False))
        except Exception as e_btn: logger.error(f"Failed to update buttons after start error: {e_btn}")

def stop_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Stop request: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1] 
        script_key = f"{script_owner_id}_{file_name}"
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True

        if not is_bot_running(script_owner_id, file_name): 
            bot.answer_callback_query(call.id, f"⚠️ Script '{file_name}' already stopped.", show_alert=True)
            try:
                 bot.edit_message_text(
                     f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: 🔴 Stopped",
                     chat_id_for_reply, call.message.message_id,
                     reply_markup=create_control_buttons(script_owner_id, file_name, False), parse_mode='Markdown')
            except Exception as e: logger.error(f"Error updating buttons (already stopped): {e}")
            return

        bot.answer_callback_query(call.id, f"⏳ Stopping {file_name} for user {script_owner_id}...")
        process_info = bot_scripts.get(script_key)
        if process_info:
            kill_process_tree(process_info)
            _forget_script(script_key); logger.info(f"Removed {script_key} from running after stop.")
        else: logger.warning(f"Script {script_key} running by psutil but not in bot_scripts dict.")

        try:
            bot.edit_message_text(
                f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: 🔴 Stopped",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, False), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified after stopping {file_name}")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing stop callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid stop command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in stop_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error stopping script.", show_alert=True)

def restart_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Restart: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1]; user_folder = get_user_folder(script_owner_id)
        file_path = os.path.join(user_folder, file_name); script_key = f"{script_owner_id}_{file_name}"

        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ Error: File `{file_name}` missing! Re-upload.", show_alert=True)
            remove_user_file_db(script_owner_id, file_name)
            _forget_script(script_key)
            check_files_callback(call); return

        if not _gate_button_start(call, script_owner_id, file_name, file_type):
            return

        bot.answer_callback_query(call.id, f"⏳ Restarting {file_name} for user {script_owner_id}...")
        # Mark it as manually stopped while the old process is killed, so the watchdog does not see the
        # kill as a crash (extra "stopped unexpectedly" message, possible second launch).
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        if is_bot_running(script_owner_id, file_name):
            logger.info(f"Restart: Stopping existing {script_key}...")
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            _forget_script(script_key)
            time.sleep(1.5) 
        _reset_restart_state(script_owner_id, file_name)

        logger.info(f"Restart: Starting script {script_key}...")
        if file_type == 'py':
            launcher = threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        elif file_type == 'js':
            launcher = threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        else:
             bot.send_message(chat_id_for_reply, f"❌ Unknown type '{file_type}' for '{file_name}'."); return
        launcher.start()

        launcher.join(timeout=LAUNCH_WAIT_SECONDS)
        time.sleep(0.5)
        is_now_running = is_bot_running(script_owner_id, file_name) 
        if is_now_running:
            status_text = '🟢 Running'
        elif launcher.is_alive():
            status_text = '🟡 Still starting (installing modules?). Open Check Files again in a moment'
        else:
            status_text = '🔴 Not running. See the message above or the logs'
        try:
            bot.edit_message_text(
                f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: {status_text}",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_now_running), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified (restart {file_name})")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing restart callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid restart command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in restart_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error restarting.", show_alert=True)
        try:
            _, script_owner_id_err_str, file_name_err = call.data.split('_', 2)
            script_owner_id_err = int(script_owner_id_err_str)
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_control_buttons(script_owner_id_err, file_name_err, False))
        except Exception as e_btn: logger.error(f"Failed to update buttons after restart error: {e_btn}")

def delete_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Delete: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        bot.answer_callback_query(call.id, f"🗑️ Deleting {file_name} for user {script_owner_id}...")
        script_key = f"{script_owner_id}_{file_name}"
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        if is_bot_running(script_owner_id, file_name):
            logger.info(f"Delete: Stopping {script_key}...")
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            _forget_script(script_key)
            time.sleep(0.5) 

        user_folder = get_user_folder(script_owner_id)
        file_path = os.path.join(user_folder, file_name)
        log_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        env_path = bot_env_path(user_folder, file_name)
        deleted_disk = []
        if os.path.exists(file_path):
            try: os.remove(file_path); deleted_disk.append(file_name); logger.info(f"Deleted file: {file_path}")
            except OSError as e: logger.error(f"Error deleting {file_path}: {e}")
        if os.path.exists(log_path):
            try: os.remove(log_path); deleted_disk.append(os.path.basename(log_path)); logger.info(f"Deleted log: {log_path}")
            except OSError as e: logger.error(f"Error deleting log {log_path}: {e}")

        if env_path and os.path.isfile(env_path):
            try: os.remove(env_path); deleted_disk.append(os.path.basename(env_path)); logger.info(f"Deleted environment file: {env_path}")
            except OSError as e: logger.error(f"Error deleting {env_path}: {e}")

        side_path = gh_sidecar_path(user_folder, file_name)
        if side_path and os.path.isfile(side_path):
            _remove_quietly(side_path)
        remove_user_file_db(script_owner_id, file_name)
        deleted_str = ", ".join(f"`{f}`" for f in deleted_disk) if deleted_disk else "associated files"
        try:
            bot.edit_message_text(
                f"🗑️ Record `{file_name}` (User `{script_owner_id}`) and {deleted_str} deleted!",
                chat_id_for_reply, call.message.message_id, reply_markup=None, parse_mode='Markdown'
            )
        except Exception as e:
            logger.error(f"Error editing msg after delete: {e}")
            bot.send_message(chat_id_for_reply, f"🗑️ Record `{file_name}` deleted.", parse_mode='Markdown')
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing delete callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid delete command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in delete_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error deleting.", show_alert=True)

def logs_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Logs: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        user_folder = get_user_folder(script_owner_id)
        log_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        if not os.path.exists(log_path):
            bot.answer_callback_query(call.id, f"⚠️ No logs for '{file_name}'.", show_alert=True); return

        bot.answer_callback_query(call.id) 
        try:
            log_content = ""; file_size = os.path.getsize(log_path)
            max_log_kb = 100; max_tg_msg = 3500
            if file_size == 0: log_content = "(Log empty)"
            elif file_size > max_log_kb * 1024:
                 with open(log_path, 'rb') as f: f.seek(-max_log_kb * 1024, os.SEEK_END); log_bytes = f.read()
                 log_content = log_bytes.decode('utf-8', errors='ignore')
                 log_content = f"(Last {max_log_kb} KB)\n...\n" + log_content
            else:
                 with open(log_path, 'r', encoding='utf-8', errors='ignore') as f: log_content = f.read()

            if len(log_content) > max_tg_msg:
                log_content = log_content[-max_tg_msg:]
                first_nl = log_content.find('\n')
                if first_nl != -1: log_content = "...\n" + log_content[first_nl+1:]
                else: log_content = "...\n" + log_content 
            if not log_content.strip(): log_content = "(No visible content)"

            log_content = log_content.replace('```', "'" * 3)
            bot.send_message(chat_id_for_reply, f"📜 Logs for `{file_name}` (User `{script_owner_id}`):\n```\n{log_content}\n```", parse_mode='Markdown')
        except Exception as e:
            logger.error(f"Error reading/sending log {log_path}: {e}", exc_info=True)
            bot.send_message(chat_id_for_reply, f"❌ Error reading log for `{file_name}`.")
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing logs callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid logs command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in logs_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error fetching logs.", show_alert=True)

# --- Environment (.env) button: per-bot control panel ----------------------------
def _env_panel(owner_id, file_name, reveal=False):
    """Text + buttons of the Environment panel for one bot."""
    user_folder = get_user_folder(owner_id)
    env = load_bot_env(user_folder, file_name)
    lines = [f"🔑 <b>Environment</b> for <code>{html_escape(file_name)}</code> (User <code>{owner_id}</code>)",
             f"Saved variables: {len(env)}/{ENV_MAX_VARS}", ""]
    if env:
        shown = []
        for key in sorted(env):
            shown.append(f"<code>{html_escape(key)}</code> = <code>{html_escape(_env_display_value(key, env[key], reveal))}</code>")
        text_tail = ("\n\nValues that look secret are partly hidden. Tap <b>Show Values</b> to see everything."
                     if not reveal else "\n\nShowing full values. Do not forward this message.")
        footer = text_tail + "\nChanges are used the next time this bot starts or restarts."
        body = "\n".join(shown)
        limit = 3800 - len("\n".join(lines)) - len(footer)
        if len(body) > limit:
            cut = body[:limit].rsplit("\n", 1)[0]
            body = cut + "\n…(more not shown)"
        lines.append(body)
        lines.append(footer)
    else:
        lines.append("No variables yet. Tap <b>Add / Update</b> and send them like a .env file, for example <code>BOT_TOKEN=123:abc</code>.")
    markup = NavMenu(row_width=2)
    markup.row(NavButton("➕ Add / Update", callback_data=f'enva_{owner_id}_{file_name}'),
               NavButton("🗑 Delete One", callback_data=f'envd_{owner_id}_{file_name}') if env else
               NavButton("🔄 Refresh", callback_data=f'envm_{owner_id}_{file_name}'))
    if env:
        view_btn = (NavButton("🙈 Hide Values", callback_data=f'envm_{owner_id}_{file_name}') if reveal
                    else NavButton("👁 Show Values", callback_data=f'envv_{owner_id}_{file_name}'))
        markup.row(view_btn, NavButton("🧹 Clear All", callback_data=f'envc_{owner_id}_{file_name}'))
    if is_bot_running(owner_id, file_name):
        markup.row(NavButton("🔄 Restart Now (apply changes)", callback_data=f'restart_{owner_id}_{file_name}'))
    markup.row(NavButton("🔙 Back to Controls", callback_data=f'file_{owner_id}_{file_name}'))
    return "\n".join(lines), markup


def _env_show_panel(call, owner_id, file_name, reveal=False):
    text, markup = _env_panel(owner_id, file_name, reveal)
    _edit_or_send(call, text, markup)


def _env_access_ok(call, owner_id, file_name):
    """Same rule as the other per-bot buttons: the bot's owner or an admin, and the bot must exist."""
    uid = call.from_user.id
    if not (uid == owner_id or uid in admin_ids):
        bot.answer_callback_query(call.id, "⚠️ You can only manage the environment of your own bots.", show_alert=True)
        return False
    if not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True)
        return False
    if getattr(call.message.chat, 'type', 'private') != 'private':
        bot.answer_callback_query(call.id, "🔒 Open this in a private chat with me, so your secrets stay private.", show_alert=True)
        return False
    return True


def env_callback(call):
    """All buttons of the Environment panel (callback prefixes envm_ envv_ enva_ envd_ envk_ envc_ envy_)."""
    try:
        action = call.data.split('_', 1)[0]
        key_tag = None
        if action == 'envk':
            _, owner_str, key_tag, file_name = call.data.split('_', 3)
        else:
            _, owner_str, file_name = call.data.split('_', 2)
        owner_id = int(owner_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
        return
    try:
        if not _env_access_ok(call, owner_id, file_name):
            return
        chat_id = call.message.chat.id
        user_folder = get_user_folder(owner_id)
        bot.clear_step_handler_by_chat_id(chat_id)   # leaving a half-finished "send variables" step
        if action in ('envm', 'envv'):
            bot.answer_callback_query(call.id)
            _env_show_panel(call, owner_id, file_name, reveal=(action == 'envv'))
        elif action == 'enva':
            bot.answer_callback_query(call.id)
            prompt = (f"➕ <b>Add / update variables</b> for <code>{html_escape(file_name)}</code>\n\n"
                      "Send me one line:\n<pre>KEY=VALUE</pre>"
                      "or several lines, like the inside of a .env file (you can also upload the .env file itself):\n"
                      "<pre>BOT_TOKEN=123456:abcdef\nADMIN_ID=12345\nDEBUG=true</pre>"
                      "A name that already exists is updated, new names are added. Lines starting with # are ignored. "
                      "If a value has spaces, put it in quotes.\n"
                      "I delete your message after saving so the secrets do not stay in the chat.")
            markup = NavMenu().add(
                NavButton("❌ Cancel", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, prompt, markup)
            bot.register_next_step_handler(call.message, _env_receive_input, owner_id, file_name, call.from_user.id)
        elif action == 'envd':
            env = load_bot_env(user_folder, file_name)
            bot.answer_callback_query(call.id)
            if not env:
                _env_show_panel(call, owner_id, file_name)
                return
            markup = NavMenu(row_width=2)
            markup.add(*[NavButton(f"🗑 {key}", callback_data=f'envk_{owner_id}_{_env_key_tag(key)}_{file_name}')
                         for key in sorted(env)])
            markup.row(NavButton("🔙 Back", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, f"🗑 Which variable of <code>{html_escape(file_name)}</code> should be deleted?", markup)
        elif action == 'envk':
            env = load_bot_env(user_folder, file_name)
            key = next((k for k in env if _env_key_tag(k) == key_tag), None)
            if key and delete_bot_env_key(user_folder, file_name, key):
                bot.answer_callback_query(call.id, f"🗑 {key} deleted.")
            else:
                bot.answer_callback_query(call.id, "That variable is already gone.")
            _env_show_panel(call, owner_id, file_name)
        elif action == 'envc':
            bot.answer_callback_query(call.id)
            markup = NavMenu()
            markup.row(NavButton("✅ Yes, delete all", callback_data=f'envy_{owner_id}_{file_name}'),
                       NavButton("❌ No", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, f"🧹 Delete <b>all</b> variables of <code>{html_escape(file_name)}</code>?", markup)
        elif action == 'envy':
            count = clear_bot_env(user_folder, file_name)
            bot.answer_callback_query(call.id, f"🧹 {count} variable(s) deleted.")
            _env_show_panel(call, owner_id, file_name)
        else:
            bot.answer_callback_query(call.id, "Unknown action.")
    except Exception as exc:
        logger.error("Error in env_callback for '%s': %s", call.data, redact_secrets(exc), exc_info=True)
        try:
            bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)
        except Exception:
            pass


def _env_forget_message(message):
    """Best effort: remove the message that carried the secrets (works in private chats)."""
    try:
        bot.delete_message(message.chat.id, message.message_id)
        return True
    except Exception:
        return False


def _env_receive_input(message, owner_id, file_name, expected_uid):
    """Next message after Add / Update: text lines, or an uploaded .env file."""
    chat_id = message.chat.id
    uid = message.from_user.id if message.from_user else None
    try:
        if uid != expected_uid:
            return
        text = message.text if message.content_type == 'text' else None
        # A command or a menu button means the user moved on: hand it back to the normal handlers.
        if text and (text.startswith('/') or text in BUTTON_TEXT_TO_LOGIC):
            bot.process_new_messages([message])
            return
        if is_user_banned(uid) or not (uid == owner_id or uid in admin_ids) \
                or not any(item[0] == file_name for item in user_files.get(owner_id, [])):
            bot.send_message(chat_id, "⚠️ That bot is not available for you any more. Nothing was changed.")
            return
        if message.content_type == 'document':
            doc = message.document
            if (doc.file_size or 0) > ENV_MAX_FILE_BYTES:
                bot.send_message(chat_id, f"❌ That file is too big for an environment file (max {ENV_MAX_FILE_BYTES // 1024} KB). Nothing was changed.")
                return
            raw = bot.download_file(bot.get_file(doc.file_id).file_path)
            if len(raw) > ENV_MAX_FILE_BYTES:
                bot.send_message(chat_id, "❌ That file is too big for an environment file. Nothing was changed.")
                return
            try:
                text = raw.decode('utf-8-sig')
            except UnicodeDecodeError:
                bot.send_message(chat_id, "❌ I could not read that file as text. Send a plain text .env file. Nothing was changed.")
                return
        elif text is None:
            bot.send_message(chat_id, "❌ Please send text like KEY=VALUE, or a .env file. Nothing was changed.")
            return
        if len(text) > ENV_MAX_FILE_BYTES:
            bot.send_message(chat_id, "❌ That is too much text. Nothing was changed.")
            return

        pairs, problems = parse_env_text(text)
        result = []
        if pairs:
            try:
                added, updated, unchanged = update_bot_env(get_user_folder(owner_id), file_name, pairs)
            except ValueError as exc:
                bot.send_message(chat_id, f"❌ {html_escape(str(exc))} Nothing was changed.", parse_mode='HTML',
                                 reply_markup=_env_back_markup(owner_id, file_name))
                _env_forget_message(message)
                return
            if added:
                result.append("Added: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in added))
            if updated:
                result.append("Updated: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in updated))
            if unchanged:
                result.append("Already the same: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in unchanged))
            head = f"✅ Saved {len(added) + len(updated)} change(s) for <code>{html_escape(file_name)}</code>."
        else:
            head = "❌ I found no valid KEY=VALUE line, so nothing was changed."
        if problems:
            result.append("Skipped lines:")
            for number, label, reason in problems[:10]:
                who = f" (<code>{html_escape(label)}</code>)" if label else ""
                result.append(f"• line {number}{who}: {html_escape(reason)}")
            if len(problems) > 10:
                result.append(f"• …and {len(problems) - 10} more")
        removed = _env_forget_message(message)
        tail = "\nYour message was deleted so the secrets do not stay in the chat." if removed else \
               "\nTip: delete your message yourself so the secrets do not stay in the chat."
        if pairs:
            tail += "\nRestart the bot to use the new values."
        bot.send_message(chat_id, head + ("\n" + "\n".join(result) if result else "") + tail, parse_mode='HTML',
                         reply_markup=_env_back_markup(owner_id, file_name))
    except Exception as exc:
        logger.error("Error saving environment for %s: %s", file_name, redact_secrets(exc), exc_info=True)
        try:
            bot.send_message(chat_id, "⚠️ Something went wrong while saving. Please try again.")
        except Exception:
            pass


def _env_back_markup(owner_id, file_name):
    return NavMenu().add(
        NavButton("🔑 Open Environment", callback_data=f'envm_{owner_id}_{file_name}'))


def speed_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, chat_id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception:
            bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_cb_ping_time = time.time() 
    try:
        bot.edit_message_text("🏃 Testing speed...", chat_id, call.message.message_id)
        bot.send_chat_action(chat_id, 'typing') 
        response_time = round((time.time() - start_cb_ping_time) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now(): user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        speed_msg = (f"⚡ Bot Speed & Status:\n\n⏱️ API Response Time: {response_time} ms\n"
                     f"🚦 Bot Status: {status}\n"
                     f"👤 Your Level: {user_level}")
        bot.answer_callback_query(call.id) 
        bot.edit_message_text(speed_msg, chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id))
    except Exception as e:
         logger.error(f"Error during speed test (cb): {e}", exc_info=True)
         bot.answer_callback_query(call.id, "Error in speed test.", show_alert=True)
         try: bot.edit_message_text("〽️ Main Menu", chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id))
         except Exception: pass

def back_to_main_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, chat_id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception:
            bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    expiry_info = ""
    if user_id == OWNER_ID: user_status = "👑 Owner"
    elif user_id in admin_ids: user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"; days_left = (expiry_date - datetime.now()).days
            expiry_info = f"\n⏳ Subscription expires in: {days_left} days"
        else: user_status = "🆓 Free User (Expired Sub)" # Will be cleaned up by welcome if not already
    else: user_status = "🆓 Free User"
    main_menu_text = (f"〽️ Welcome back, {call.from_user.first_name}!\n\n🆔 ID: `{user_id}`\n"
                      f"🔰 Status: {user_status}{expiry_info}\n📁 Files: {current_files} / {limit_str}\n\n"
                      f"👇 Use buttons or type commands.")
    try:
        bot.answer_callback_query(call.id)
        bot.edit_message_text(main_menu_text, chat_id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
         if "message is not modified" in str(e): logger.warning("Msg not modified (back_to_main).")
         else: logger.error(f"API error on back_to_main: {e}")
    except Exception as e: logger.error(f"Error handling back_to_main: {e}", exc_info=True)

# --- Admin Callback Implementations (for Inline Buttons) ---
def subscription_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("💳 Subscription Management\nSelect action:",
                              call.message.chat.id, call.message.message_id, reply_markup=create_subscription_menu())
    except Exception as e: logger.error(f"Error showing sub menu: {e}")

def stats_callback(call): # Called by user and admin
    bot.answer_callback_query(call.id)
    _logic_statistics(call.message) 
    try:
        bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                      reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception as e:
        logger.error(f"Error updating menu after stats_callback: {e}")

def lock_bot_callback(call):
    global bot_locked; bot_locked = True
    logger.warning(f"Bot locked by Admin {call.from_user.id}")
    bot.answer_callback_query(call.id, "🔒 Bot locked.")
    try: bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception as e: logger.error(f"Error updating menu (lock): {e}")

def unlock_bot_callback(call):
    global bot_locked; bot_locked = False
    logger.warning(f"Bot unlocked by Admin {call.from_user.id}")
    bot.answer_callback_query(call.id, "🔓 Bot unlocked.")
    try: bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception as e: logger.error(f"Error updating menu (unlock): {e}")

def run_all_scripts_callback(call): # Added
    _logic_run_all_scripts(call) # Pass the call object

def broadcast_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "📢 Send message to broadcast.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_broadcast_message)

def process_broadcast_message(message):
    user_id = message.from_user.id
    if user_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Broadcast cancelled."); return

    broadcast_content = message.text # Can also handle photos, videos etc. if message.content_type is checked
    if not broadcast_content and not (message.photo or message.video or message.document or message.sticker or message.voice or message.audio): # If no text and no other media
         bot.reply_to(message, "⚠️ Cannot broadcast empty message. Send text or media, or /cancel.")
         msg = bot.send_message(message.chat.id, "📢 Send broadcast message or /cancel.")
         bot.register_next_step_handler(msg, process_broadcast_message)
         return

    target_count = len(active_users)
    markup = NavMenu()
    markup.row(NavButton("✅ Confirm & Send", callback_data=f"confirm_broadcast_{message.message_id}"),
               NavButton("❌ Cancel", callback_data="cancel_broadcast"))

    preview_text = broadcast_content[:1000].strip().replace('`' * 3, "'" * 3) if broadcast_content else "(Media message)"
    bot.reply_to(message, f"⚠️ Confirm Broadcast:\n\n```\n{preview_text}\n```\n" 
                          f"To **{target_count}** users. Sure?", reply_markup=markup, parse_mode='Markdown')

def handle_confirm_broadcast(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    if user_id not in admin_ids: bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True); return
    try:
        original_message = call.message.reply_to_message
        if not original_message: raise ValueError("Could not retrieve original message.")

        # Check content type and get content
        broadcast_text = None
        broadcast_photo_id = None
        broadcast_video_id = None
        broadcast_document_id = None
        broadcast_audio_id = None
        broadcast_voice_id = None
        broadcast_sticker_id = None

        if original_message.text:
            broadcast_text = original_message.text
        elif original_message.photo:
            broadcast_photo_id = original_message.photo[-1].file_id # Get highest quality
        elif original_message.video:
            broadcast_video_id = original_message.video.file_id
        elif original_message.document:
            broadcast_document_id = original_message.document.file_id
        elif original_message.audio:
            broadcast_audio_id = original_message.audio.file_id
        elif original_message.voice:
            broadcast_voice_id = original_message.voice.file_id
        elif original_message.sticker:
            broadcast_sticker_id = original_message.sticker.file_id
        else:
            raise ValueError("Message has no text or supported media for broadcast.")

        bot.answer_callback_query(call.id, "🚀 Starting broadcast...")
        bot.edit_message_text(f"📢 Broadcasting to {len(active_users)} users...",
                              chat_id, call.message.message_id, reply_markup=None)
        # Pass all potential content types to execute_broadcast
        thread = threading.Thread(name='broadcast', daemon=True, target=execute_broadcast, args=(
            broadcast_text, broadcast_photo_id, broadcast_video_id,
            original_message.caption if (broadcast_photo_id or broadcast_video_id or broadcast_document_id or broadcast_audio_id or broadcast_voice_id) else None,
            chat_id, broadcast_document_id, broadcast_audio_id, broadcast_voice_id, broadcast_sticker_id))
        thread.start()
    except ValueError as ve: 
        logger.error(f"Error retrieving msg for broadcast confirm: {ve}")
        bot.edit_message_text(f"❌ Error starting broadcast: {ve}", chat_id, call.message.message_id, reply_markup=None)
    except Exception as e:
        logger.error(f"Error in handle_confirm_broadcast: {e}", exc_info=True)
        bot.edit_message_text("❌ Unexpected error during broadcast confirm.", chat_id, call.message.message_id, reply_markup=None)

def handle_cancel_broadcast(call):
    bot.answer_callback_query(call.id, "Broadcast cancelled.")
    bot.delete_message(call.message.chat.id, call.message.message_id)
    # Optionally delete the original message too if call.message.reply_to_message exists
    if call.message.reply_to_message:
        try: bot.delete_message(call.message.chat.id, call.message.reply_to_message.message_id)
        except Exception as exc: logger.debug(f"Could not delete the original message: {exc}")

def _broadcast_send_one(user_id_bc, broadcast_text, photo_id, video_id, caption, document_id, audio_id, voice_id, sticker_id):
    """Send one broadcast item. Rate limits and bad formatting are handled inside SafeTeleBot."""
    cap = caption[:1024] if caption else None  # Telegram caption limit
    pm = 'Markdown' if cap else None
    if broadcast_text:
        bot.send_message(user_id_bc, broadcast_text[:4096], parse_mode='Markdown')
    elif photo_id:
        bot.send_photo(user_id_bc, photo_id, caption=cap, parse_mode=pm)
    elif video_id:
        bot.send_video(user_id_bc, video_id, caption=cap, parse_mode=pm)
    elif document_id:
        bot.send_document(user_id_bc, document_id, caption=cap, parse_mode=pm)
    elif audio_id:
        bot.send_audio(user_id_bc, audio_id, caption=cap, parse_mode=pm)
    elif voice_id:
        bot.send_voice(user_id_bc, voice_id, caption=cap, parse_mode=pm)
    elif sticker_id:
        bot.send_sticker(user_id_bc, sticker_id)
    else:
        raise ValueError("Nothing to broadcast")


def execute_broadcast(broadcast_text, photo_id, video_id, caption, admin_chat_id, document_id=None, audio_id=None, voice_id=None, sticker_id=None):
    sent_count = 0; failed_count = 0; blocked_count = 0
    start_exec_time = time.time()
    with STATE_LOCK:
        users_to_broadcast = list(active_users)
    total_users = len(users_to_broadcast)
    logger.info("Executing broadcast to %s users.", total_users)
    batch_size = 25; delay_batches = 1.5
    blocked_markers = ("bot was blocked", "user is deactivated", "chat not found", "kicked from", "restricted",
                       "have no rights", "forbidden")

    for i, user_id_bc in enumerate(users_to_broadcast):
        if SHUTDOWN_EVENT.is_set():
            logger.warning("Broadcast interrupted by shutdown at %s/%s", i, total_users)
            break
        try:
            _broadcast_send_one(user_id_bc, broadcast_text, photo_id, video_id, caption,
                                document_id, audio_id, voice_id, sticker_id)
            sent_count += 1
        except telebot.apihelper.ApiTelegramException as e:
            err_desc = str(e).lower()
            if any(m in err_desc for m in blocked_markers):
                logger.warning("Broadcast failed to %s: user blocked/inactive.", user_id_bc)
                blocked_count += 1
            else:
                logger.error("Broadcast failed to %s: %s", user_id_bc, e)
                failed_count += 1
        except Exception as e:
            logger.error("Unexpected error broadcasting to %s: %s", user_id_bc, e)
            failed_count += 1

        if (i + 1) % batch_size == 0 and i < total_users - 1:
            logger.info("Broadcast batch %s sent. Sleeping %ss...", i // batch_size + 1, delay_batches)
            SHUTDOWN_EVENT.wait(delay_batches)
        elif i % 5 == 0:
            SHUTDOWN_EVENT.wait(0.2)

    duration = round(time.time() - start_exec_time, 2)
    result_msg = (f"📢 Broadcast Complete!\n\n✅ Sent: {sent_count}\n❌ Failed: {failed_count}\n"
                  f"🚫 Blocked/Inactive: {blocked_count}\n👥 Targets: {total_users}\n⏱️ Duration: {duration}s")
    logger.info(result_msg.replace("\n", " | "))
    try:
        bot.send_message(admin_chat_id, result_msg)
    except Exception as e:
        logger.error("Failed to send broadcast result to admin %s: %s", admin_chat_id, e)

def admin_panel_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("👑 Admin Panel\nManage admins (Owner actions may be restricted).",
                              call.message.chat.id, call.message.message_id, reply_markup=create_admin_panel())
    except Exception as e: logger.error(f"Error showing admin panel: {e}")

def add_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👑 Enter User ID to promote to Admin.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_add_admin_id)

def process_add_admin_id(message):
    owner_id_check = message.from_user.id 
    if owner_id_check != OWNER_ID: bot.reply_to(message, "⚠️ Owner only."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Admin promotion cancelled."); return
    try:
        new_admin_id = int(message.text.strip())
        if new_admin_id <= 0: raise ValueError("ID must be positive")
        if new_admin_id == OWNER_ID: bot.reply_to(message, "⚠️ Owner is already Owner."); return
        if new_admin_id in admin_ids: bot.reply_to(message, f"⚠️ User `{new_admin_id}` already Admin."); return
        add_admin_db(new_admin_id, owner_id_check) 
        logger.warning(f"Admin {new_admin_id} added by Owner {owner_id_check}.")
        bot.reply_to(message, f"✅ User `{new_admin_id}` promoted to Admin.")
        try: bot.send_message(new_admin_id, "🎉 Congrats! You are now an Admin.")
        except Exception as e: logger.error(f"Failed to notify new admin {new_admin_id}: {e}")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "👑 Enter User ID to promote or /cancel.")
        bot.register_next_step_handler(msg, process_add_admin_id)
    except Exception as e: logger.error(f"Error processing add admin: {e}", exc_info=True); bot.reply_to(message, "Error.")

def remove_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👑 Enter User ID of Admin to remove.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_admin_id)

def process_remove_admin_id(message):
    owner_id_check = message.from_user.id
    if owner_id_check != OWNER_ID: bot.reply_to(message, "⚠️ Owner only."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Admin removal cancelled."); return
    try:
        admin_id_remove = int(message.text.strip()) # Renamed
        if admin_id_remove <= 0: raise ValueError("ID must be positive")
        if admin_id_remove == OWNER_ID: bot.reply_to(message, "⚠️ Owner cannot remove self."); return
        if admin_id_remove not in admin_ids: bot.reply_to(message, f"⚠️ User `{admin_id_remove}` not Admin."); return
        if remove_admin_db(admin_id_remove): 
            logger.warning(f"Admin {admin_id_remove} removed by Owner {owner_id_check}.")
            bot.reply_to(message, f"✅ Admin `{admin_id_remove}` removed.")
            try: bot.send_message(admin_id_remove, "ℹ️ You are no longer an Admin.")
            except Exception as e: logger.error(f"Failed to notify removed admin {admin_id_remove}: {e}")
        else: bot.reply_to(message, f"❌ Failed to remove admin `{admin_id_remove}`. Check logs.")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "👑 Enter Admin ID to remove or /cancel.")
        bot.register_next_step_handler(msg, process_remove_admin_id)
    except Exception as e: logger.error(f"Error processing remove admin: {e}", exc_info=True); bot.reply_to(message, "Error.")

def list_admins_callback(call):
    bot.answer_callback_query(call.id)
    try:
        admin_list_str = "\n".join(f"- `{aid}` {'(Owner)' if aid == OWNER_ID else ''}" for aid in sorted(list(admin_ids)))
        if not admin_list_str: admin_list_str = "(No Owner/Admins configured!)"
        bot.edit_message_text(f"👑 Current Admins:\n\n{admin_list_str}", call.message.chat.id,
                              call.message.message_id, reply_markup=create_admin_panel(), parse_mode='Markdown')
    except Exception as e: logger.error(f"Error listing admins: {e}")

def add_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID & days (e.g., `12345678 30`).\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_add_subscription_details)

def process_add_subscription_details(message):
    admin_id_check = message.from_user.id 
    if admin_id_check not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Sub add cancelled."); return
    try:
        parts = message.text.split();
        if len(parts) != 2: raise ValueError("Incorrect format")
        sub_user_id = int(parts[0].strip()); days = int(parts[1].strip())
        if sub_user_id <= 0 or days <= 0: raise ValueError("User ID/days must be positive")

        current_expiry = user_subscriptions.get(sub_user_id, {}).get('expiry')
        start_date_new_sub = datetime.now() # Renamed
        if current_expiry and current_expiry > start_date_new_sub: start_date_new_sub = current_expiry
        new_expiry = start_date_new_sub + timedelta(days=days)
        save_subscription(sub_user_id, new_expiry)

        logger.info(f"Sub for {sub_user_id} by admin {admin_id_check}. Expiry: {new_expiry:%Y-%m-%d}")
        bot.reply_to(message, f"✅ Sub for `{sub_user_id}` by {days} days.\nNew expiry: {new_expiry:%Y-%m-%d}")
        try: bot.send_message(sub_user_id, f"🎉 Sub activated/extended by {days} days! Expires: {new_expiry:%Y-%m-%d}.")
        except Exception as e: logger.error(f"Failed to notify {sub_user_id} of new sub: {e}")
    except ValueError as e:
        bot.reply_to(message, f"⚠️ Invalid: {e}. Format: `ID days` or /cancel.")
        msg = bot.send_message(message.chat.id, "💳 Enter User ID & days, or /cancel.")
        bot.register_next_step_handler(msg, process_add_subscription_details)
    except Exception as e: logger.error(f"Error processing add sub: {e}", exc_info=True); bot.reply_to(message, "Error.")

def remove_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to remove sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_subscription_id)

def process_remove_subscription_id(message):
    admin_id_check = message.from_user.id
    if admin_id_check not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Sub removal cancelled."); return
    try:
        sub_user_id_remove = int(message.text.strip()) # Renamed
        if sub_user_id_remove <= 0: raise ValueError("ID must be positive")
        if sub_user_id_remove not in user_subscriptions:
            bot.reply_to(message, f"⚠️ User `{sub_user_id_remove}` no active sub in memory."); return
        remove_subscription_db(sub_user_id_remove) 
        logger.warning(f"Sub removed for {sub_user_id_remove} by admin {admin_id_check}.")
        bot.reply_to(message, f"✅ Sub for `{sub_user_id_remove}` removed.")
        try: bot.send_message(sub_user_id_remove, "ℹ️ Your subscription removed by admin.")
        except Exception as e: logger.error(f"Failed to notify {sub_user_id_remove} of sub removal: {e}")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to remove sub from, or /cancel.")
        bot.register_next_step_handler(msg, process_remove_subscription_id)
    except Exception as e: logger.error(f"Error processing remove sub: {e}", exc_info=True); bot.reply_to(message, "Error.")

def check_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to check sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_check_subscription_id)

def process_check_subscription_id(message):
    admin_id_check = message.from_user.id
    if admin_id_check not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "Sub check cancelled."); return
    try:
        sub_user_id_check = int(message.text.strip()) # Renamed
        if sub_user_id_check <= 0: raise ValueError("ID must be positive")
        if sub_user_id_check in user_subscriptions:
            expiry_dt = user_subscriptions[sub_user_id_check].get('expiry')
            if expiry_dt:
                if expiry_dt > datetime.now():
                    days_left = (expiry_dt - datetime.now()).days
                    bot.reply_to(message, f"✅ User `{sub_user_id_check}` active sub.\nExpires: {expiry_dt:%Y-%m-%d %H:%M:%S} ({days_left} days left).")
                else:
                    bot.reply_to(message, f"⚠️ User `{sub_user_id_check}` expired sub (On: {expiry_dt:%Y-%m-%d %H:%M:%S}).")
                    remove_subscription_db(sub_user_id_check) # Clean up
            else: bot.reply_to(message, f"⚠️ User `{sub_user_id_check}` in sub list, but expiry missing. Re-add if needed.")
        else: bot.reply_to(message, f"ℹ️ User `{sub_user_id_check}` no active sub record.")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to check, or /cancel.")
        bot.register_next_step_handler(msg, process_check_subscription_id)
    except Exception as e: logger.error(f"Error processing check sub: {e}", exc_info=True); bot.reply_to(message, "Error.")

# --- User Management Callbacks ---
def user_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("👥 User Management\nSelect action:", call.message.chat.id, 
                              call.message.message_id, reply_markup=create_user_management_menu())
    except Exception as e: logger.error(f"Error showing user management menu: {e}")

def ban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🚫 Enter User ID to ban and reason (e.g., `12345678 Spamming`)\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_ban_user)

def process_ban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Ban cancelled.")
        return
    
    try:
        parts = message.text.split()
        if len(parts) < 2:
            bot.reply_to(message, "⚠️ Format: `user_id reason`\nExample: `12345678 Spamming`")
            return
        
        user_id = int(parts[0])
        reason = ' '.join(parts[1:])
        
        if user_id <= 0: raise ValueError("ID must be positive")
        if user_id == OWNER_ID: bot.reply_to(message, "⚠️ Cannot ban owner."); return
        if user_id in admin_ids: bot.reply_to(message, "⚠️ Cannot ban admin."); return
        
        if ban_user_db(user_id, reason, admin_id):
            bot.reply_to(message, f"✅ User `{user_id}` banned.\nReason: {reason}")
            # Stop all scripts for banned user
            for file_name, _ in user_files.get(user_id, []):
                script_key = f"{user_id}_{file_name}"
                stopped_info = _forget_script(script_key)
                if stopped_info:
                    kill_process_tree(stopped_info)
            
            try:
                bot.send_message(user_id, f"🚫 You have been banned from using this bot.\nReason: {reason}")
            except Exception as e:
                logger.error(f"Failed to notify banned user {user_id}: {e}")
        else:
            bot.reply_to(message, "❌ Failed to ban user.")
            
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error banning user: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

def unban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "✅ Enter User ID to unban\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_unban_user)

def process_unban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Unban cancelled.")
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        if user_id not in banned_users:
            bot.reply_to(message, f"ℹ️ User `{user_id}` is not banned.")
            return
        
        if unban_user_db(user_id):
            bot.reply_to(message, f"✅ User `{user_id}` unbanned.")
            try:
                bot.send_message(user_id, "✅ Your ban has been lifted. You can now use the bot again.")
            except Exception as e:
                logger.error(f"Failed to notify unbanned user {user_id}: {e}")
        else:
            bot.reply_to(message, "❌ Failed to unban user.")
            
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error unbanning user: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

def user_info_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👤 Enter User ID to get info\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_user_info)

def process_user_info(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Info request cancelled.")
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        # Gather user information
        info_parts = []
        
        # Basic info
        info_parts.append(f"👤 **User ID:** `{user_id}`")
        
        # Status
        if user_id == OWNER_ID:
            info_parts.append("👑 **Status:** Owner")
        elif user_id in admin_ids:
            info_parts.append("🛡️ **Status:** Admin")
        elif user_id in banned_users:
            info_parts.append("🚫 **Status:** Banned")
        elif user_id in user_subscriptions:
            expiry = user_subscriptions[user_id].get('expiry')
            if expiry and expiry > datetime.now():
                days_left = (expiry - datetime.now()).days
                info_parts.append(f"⭐ **Status:** Premium (Expires in {days_left} days)")
            else:
                info_parts.append("🆓 **Status:** Free User (Expired subscription)")
        else:
            info_parts.append("🆓 **Status:** Free User")
        
        # Files
        file_count = get_user_file_count(user_id)
        file_limit = get_user_file_limit(user_id)
        info_parts.append(f"📁 **Files:** {file_count}/{file_limit if file_limit != float('inf') else 'Unlimited'}")
        
        # Custom limit
        if user_id in user_limits:
            info_parts.append(f"⚙️ **Custom Limit:** {user_limits[user_id]}")
        
        # Active scripts
        running_scripts = 0
        for file_name, _ in user_files.get(user_id, []):
            if is_bot_running(user_id, file_name):
                running_scripts += 1
        info_parts.append(f"🤖 **Running Scripts:** {running_scripts}")
        
        # Last seen (if in active users)
        if user_id in active_users:
            info_parts.append("🟢 **Status:** Active")
        
        info_text = "\n".join(info_parts)
        bot.reply_to(message, info_text, parse_mode='Markdown')
        
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error getting user info: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

def all_users_callback(call):
    bot.answer_callback_query(call.id)
    try:
        if not active_users:
            bot.edit_message_text("👥 No active users yet.", call.message.chat.id, call.message.message_id)
            return
        
        users_list = sorted(active_users)
        chunk_size = 20
        total_pages = (len(users_list) + chunk_size - 1) // chunk_size
        
        # Create pagination
        current_page = 0
        display_users_list(call.message.chat.id, call.message.message_id, users_list, current_page, total_pages, chunk_size)
        
    except Exception as e:
        logger.error(f"Error displaying all users: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error displaying users.", show_alert=True)

def display_users_list(chat_id, message_id, users_list, page, total_pages, chunk_size):
    start_idx = page * chunk_size
    end_idx = min(start_idx + chunk_size, len(users_list))
    
    user_chunk = users_list[start_idx:end_idx]
    
    message_text = f"👥 **Active Users** (Page {page + 1}/{total_pages})\n\n"
    for i, user_id in enumerate(user_chunk, start=start_idx + 1):
        status = ""
        if user_id == OWNER_ID: status = "👑"
        elif user_id in admin_ids: status = "🛡️"
        elif user_id in banned_users: status = "🚫"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now():
            status = "⭐"
        else: status = "🆓"
        
        message_text += f"{i}. `{user_id}` {status}\n"
    
    markup = NavMenu(row_width=3)
    
    if total_pages > 1:
        page_buttons = []
        if page > 0:
            page_buttons.append(NavButton("⬅️ Previous", callback_data=f"users_page_{page-1}"))
        
        page_buttons.append(NavButton(f"{page+1}/{total_pages}", callback_data="noop"))
        
        if page < total_pages - 1:
            page_buttons.append(NavButton("Next ➡️", callback_data=f"users_page_{page+1}"))
        
        markup.row(*page_buttons)
    
    markup.row(NavButton("🔙 Back to User Management", callback_data='user_management'))
    
    try:
        bot.edit_message_text(message_text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error editing users list: {e}")

def handle_users_page(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True)
        return
    
    try:
        page = int(call.data.split('_')[2])
        users_list = sorted(active_users)
        chunk_size = 20
        total_pages = (len(users_list) + chunk_size - 1) // chunk_size
        
        bot.answer_callback_query(call.id)
        if 0 <= page < total_pages:
            display_users_list(call.message.chat.id, call.message.message_id, users_list, page, total_pages, chunk_size)
    except Exception as e:
        logger.error(f"Error handling users page: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error.", show_alert=True)

def set_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🔧 Enter User ID and new limit (e.g., `12345678 50`)\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_set_user_limit)

def process_set_user_limit(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Limit set cancelled.")
        return
    
    try:
        parts = message.text.split()
        if len(parts) != 2: raise ValueError("Format: user_id limit")
        
        user_id = int(parts[0])
        limit = int(parts[1])
        
        if user_id <= 0 or limit <= 0: raise ValueError("ID and limit must be positive")
        
        if set_user_limit_db(user_id, limit, admin_id):
            bot.reply_to(message, f"✅ Set file limit {limit} for user `{user_id}`")
            try:
                bot.send_message(user_id, f"⚙️ Your file upload limit has been set to {limit}")
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
        else:
            bot.reply_to(message, "❌ Failed to set limit.")
            
    except ValueError as e:
        bot.reply_to(message, f"⚠️ Invalid input: {e}\nFormat: `user_id limit`")
    except Exception as e:
        logger.error(f"Error setting user limit: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

def remove_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🗑️ Enter User ID to remove custom limit\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_remove_user_limit)

def process_remove_user_limit(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Limit removal cancelled.")
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        if user_id not in user_limits:
            bot.reply_to(message, f"ℹ️ User `{user_id}` has no custom limit.")
            return
        
        if remove_user_limit_db(user_id):
            bot.reply_to(message, f"✅ Removed custom limit for user `{user_id}`")
            try:
                bot.send_message(user_id, "⚙️ Your custom file limit has been removed")
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
        else:
            bot.reply_to(message, "❌ Failed to remove limit.")
            
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error removing user limit: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")


# --- Hosting Health & Crash Recovery ---
def _script_key(owner_id, file_name):
    return f"{int(owner_id)}_{file_name}"

def _reset_restart_state(owner_id, file_name):
    """A fresh user-initiated launch clears an old manual stop / used-up retries, so auto-restart works again."""
    RESTART_STATE[_script_key(owner_id, file_name)] = {"attempts": 0, "manual_stop": False}

def _read_cgroup_value(paths):
    """Read the first available cgroup metric without touching /proc."""
    for path in paths:
        try:
            with open(path, "r", encoding="utf-8") as handle:
                value = handle.read().strip()
            if value:
                return value
        except (OSError, ValueError):
            continue
    return None

def _safe_cpu_health():
    # Many container hosts deny /proc/stat. Use cgroup v2 accounting first.
    stat_text = _read_cgroup_value(("/sys/fs/cgroup/cpu.stat",))
    if stat_text and "usage_usec" in stat_text:
        try:
            usage1 = next(int(line.split()[1]) for line in stat_text.splitlines() if line.startswith("usage_usec "))
            time.sleep(0.12)
            later = _read_cgroup_value(("/sys/fs/cgroup/cpu.stat",))
            usage2 = next(int(line.split()[1]) for line in later.splitlines() if line.startswith("usage_usec "))
            quota_text = _read_cgroup_value(("/sys/fs/cgroup/cpu.max",))
            parts = quota_text.split() if quota_text else []
            cores = (float(parts[0]) / float(parts[1])) if len(parts) == 2 and parts[0] != "max" else float(os.cpu_count() or 1)
            pct = max(0.0, (usage2 - usage1) / 1200.0 / max(cores, 0.01))
            return f"{pct:.1f}% (container)"
        except Exception:
            pass
    try:
        return f"Load {os.getloadavg()[0]:.2f} (CPU % restricted)"
    except (AttributeError, OSError):
        return "Unavailable (host restricts CPU metrics)"

def _safe_memory_health():
    current = _read_cgroup_value(("/sys/fs/cgroup/memory.current", "/sys/fs/cgroup/memory/memory.usage_in_bytes"))
    limit = _read_cgroup_value(("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"))
    try:
        if current and limit and limit != "max":
            used, total = int(current), int(limit)
            if 0 < total < (1 << 60):
                return f"{used / total * 100:.1f}% ({used // 1048576}/{total // 1048576} MB, container)"
    except (TypeError, ValueError):
        pass
    try:
        mem = psutil.virtual_memory()
        return f"{mem.percent:.1f}% ({mem.used // 1048576}/{mem.total // 1048576} MB)"
    except Exception:
        return "Unavailable (host restricts memory metrics)"

def build_hosting_health_report():
    # Isolate each metric so a restricted /proc mount cannot break the report.
    try:
        try:
            disk = shutil.disk_usage(BASE_DIR)
            disk_text = f"{disk.used / disk.total * 100:.1f}% ({disk.used // 1048576}/{disk.total // 1048576} MB)"
        except Exception:
            disk_text = "Unavailable"
        try:
            running = sum(1 for info in list(bot_scripts.values())
                          if info.get("process") and info["process"].poll() is None)
        except Exception:
            running = "Unknown"
        exhausted = sum(1 for st in RESTART_STATE.values()
                        if st.get("attempts", 0) >= MAX_AUTO_RESTARTS)
        up = max(0, int(time.time() - HOST_START_TIME))
        return ("🩺 <b>HOSTING HEALTH</b>\n\n"
                f"🟢 Hosting bot: Online\n⚙️ Managed scripts running: {running}\n"
                f"🔁 Restart-exhausted scripts: {exhausted}\n"
                f"👥 Registered users: {len(active_users)}\n"
                f"📦 Stored scripts: {sum(len(v) for v in user_files.values())}\n"
                f"🧠 CPU: {_safe_cpu_health()}\n💾 RAM: {_safe_memory_health()}\n"
                f"💿 Disk: {disk_text}\n"
                f"⏱️ Host uptime: {up // 3600}h {(up % 3600) // 60}m\n"
                f"🛡️ Auto-restart: maximum {MAX_AUTO_RESTARTS} attempts")
    except Exception as exc:
        logger.exception("Health report failed")
        return f"⚠️ Health report partial error: {type(exc).__name__}: {exc}"

def _watchdog_restart(info, script_key, attempt_no):
    try:
        owner_id = int(info["script_owner_id"])
        file_name = info["file_name"]
        folder = info["user_folder"]
        path = os.path.join(folder, file_name)
        state = RESTART_STATE.get(script_key, {})
        if state.get("manual_stop"):
            logger.info("Watchdog restart for %s cancelled: stopped manually.", script_key)
            return
        if is_bot_running(owner_id, file_name):
            logger.info("Watchdog restart for %s skipped: already running again.", script_key)
            return
        if not os.path.isfile(path):
            logger.error("Watchdog cannot restart missing script: %s", script_key)
            return
        target = info.get("reply_target")
        if target is None:
            logger.error("No Telegram reply target stored for %s", script_key)
            return
        runner = run_js_script if info.get("type") == "js" else run_script
        runner(path, owner_id, folder, file_name, target)
    except Exception:
        logger.exception("Watchdog restart worker failed: %s", script_key)


def _trim_script_log(info):
    """Keep a running script's log file from growing without limit (the script keeps appending to the same file)."""
    try:
        log_path = os.path.join(info["user_folder"], f"{os.path.splitext(info['file_name'])[0]}.log")
        if os.path.exists(log_path) and os.path.getsize(log_path) > MAX_SCRIPT_LOG_MB * 1024 * 1024:
            os.truncate(log_path, 0)
            logger.info("Log %s passed %s MB and was cleared.", log_path, MAX_SCRIPT_LOG_MB)
    except Exception as exc:
        logger.debug("Could not trim log for %s: %s", info.get("script_key"), exc)


def _notify_owner(info, text):
    try:
        bot.send_message(int(info["script_owner_id"]), text, parse_mode="HTML")
    except Exception as exc:
        logger.warning("Could not notify user %s: %s", info.get("script_owner_id"), exc)


def watchdog_loop():
    """Checks running scripts. A script that exits is restarted after a growing delay (RESTART_BACKOFF).
    The wait is tracked per script, so one failing script never delays the checks for the others."""
    logger.info("Crash watchdog started (max %s retries)", MAX_AUTO_RESTARTS)
    scheduled = {}  # script_key -> (time when the restart is due, info, attempt number)
    loops = 0
    while not SHUTDOWN_EVENT.is_set():
        try:
            loops += 1
            now = time.time()
            with STATE_LOCK:
                snapshot = list(bot_scripts.items())
            for key, info in snapshot:
                proc = info.get("process")
                if proc is None:
                    continue
                try:
                    rc = proc.poll()
                except Exception:
                    logger.exception("Could not inspect child process %s", key)
                    continue
                if rc is None:
                    started = info.get("start_time")
                    if started and (datetime.now() - started).total_seconds() >= 120:
                        RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})["attempts"] = 0
                    if loops % 8 == 0:
                        _trim_script_log(info)
                    continue
                state = RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})
                with STATE_LOCK:
                    if bot_scripts.get(key) is not info:
                        continue
                    bot_scripts.pop(key, None)
                release_process_resources(info)  # close the log file and pipes of the finished process
                if state.get("manual_stop"):
                    continue
                attempts = int(state.get("attempts", 0))
                if attempts >= MAX_AUTO_RESTARTS:
                    state["last_error"] = f"exit={rc}; retry limit reached"
                    logger.error("Restart limit reached for %s (exit=%s)", key, rc)
                    _notify_owner(info, f"❌ <code>{html_escape(str(info['file_name']))}</code> stopped. "
                                        f"Auto-restart limit ({MAX_AUTO_RESTARTS}) reached. Check logs.")
                    continue
                attempts += 1
                state["attempts"] = attempts
                state["last_error"] = f"exit={rc}"
                delay = RESTART_BACKOFF[min(attempts - 1, len(RESTART_BACKOFF) - 1)]
                logger.warning("%s exited (%s); retry %s/%s in %ss", key, rc, attempts, MAX_AUTO_RESTARTS, delay)
                _notify_owner(info, f"⚠️ <code>{html_escape(str(info['file_name']))}</code> stopped unexpectedly. "
                                    f"Auto-restart {attempts}/{MAX_AUTO_RESTARTS} in {delay}s.")
                scheduled[key] = (now + delay, info, attempts)

            for key, (due, info, attempts) in list(scheduled.items()):
                if due > time.time():
                    continue
                del scheduled[key]
                if RESTART_STATE.get(key, {}).get("manual_stop"):
                    continue
                threading.Thread(target=_watchdog_restart, args=(info, key, attempts),
                                 name=f"watchdog-{key}", daemon=True).start()
        except Exception:
            logger.exception("Watchdog loop error; continuing")
        SHUTDOWN_EVENT.wait(1 if scheduled else WATCHDOG_INTERVAL)
    logger.info("Crash watchdog stopped.")

def start_watchdog():
    global WATCHDOG_STARTED
    if WATCHDOG_STARTED: return
    WATCHDOG_STARTED = True
    threading.Thread(target=watchdog_loop, name="script-watchdog", daemon=True).start()

def retry_failed_scripts(admin_id, chat_id):
    if admin_id not in admin_ids:
        bot.send_message(chat_id, "⚠️ Admin permissions required.")
        return
    retryable = []
    for owner_id, files_list in list(user_files.items()):
        folder = get_user_folder(owner_id)
        for file_name, file_type in list(files_list):
            key = _script_key(owner_id, file_name)
            state = RESTART_STATE.get(key, {})
            if state.get("attempts", 0) >= MAX_AUTO_RESTARTS and os.path.isfile(os.path.join(folder, file_name)):
                retryable.append((owner_id, file_name, file_type, folder))
    if not retryable:
        bot.send_message(chat_id, "✅ No failed scripts are waiting for retry.")
        return
    for owner_id, file_name, file_type, folder in retryable:
        key = _script_key(owner_id, file_name)
        RESTART_STATE[key] = {"attempts": 0, "manual_stop": False}
        msg = bot.send_message(chat_id, f"🔄 Retrying <code>{file_name}</code> for <code>{owner_id}</code>...")
        runner = run_js_script if file_type == "js" else run_script
        threading.Thread(target=runner, args=(os.path.join(folder, file_name), owner_id,
                         folder, file_name, msg), daemon=True).start()
        time.sleep(0.2)
    bot.send_message(chat_id, f"✅ Manual retry queued for {len(retryable)} script(s).")

def hosting_health_callback(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True); return
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(build_hosting_health_report(), call.message.chat.id,
                              call.message.message_id, parse_mode="HTML",
                              reply_markup=create_admin_settings_menu())
    except Exception: logger.exception("Unable to show hosting health")

def retry_failed_callback(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True); return
    bot.answer_callback_query(call.id, "Retry queue started")
    threading.Thread(target=retry_failed_scripts,
                     args=(call.from_user.id, call.message.chat.id), daemon=True).start()


# --- Admin Settings Callbacks ---
def admin_settings_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("⚙️ Admin Settings\nSelect action:", call.message.chat.id, 
                              call.message.message_id, reply_markup=create_admin_settings_menu())
    except Exception as e: logger.error(f"Error showing admin settings: {e}")

def system_info_callback(call):
    bot.answer_callback_query(call.id)
    try:
        # Get system information
        import platform
        
        info_parts = []
        
        # Bot info
        info_parts.append("🤖 **Bot Information:**")
        info_parts.append(f"• Python: {platform.python_version()}")
        info_parts.append(f"• Platform: {platform.platform()}")
        info_parts.append(f"• Bot Uptime: {time.strftime('%H:%M:%S', time.gmtime(max(0, time.time() - HOST_START_TIME)))}")
        
        # System info
        info_parts.append("\n💻 **System Information:**")
        try:
            info_parts.append(f"• CPU: {_safe_cpu_health()}")
            info_parts.append(f"• Memory: {_safe_memory_health()}")
            disk = shutil.disk_usage(BASE_DIR)
            info_parts.append(f"• Disk: {disk.used / disk.total * 100:.1f}% used ({disk.used//1024//1024}MB/{disk.total//1024//1024}MB)")
        except Exception as e:
            info_parts.append(f"• System stats error: {str(e)}")
        
        # Bot stats
        info_parts.append("\n📊 **Bot Statistics:**")
        info_parts.append(f"• Active Users: {len(active_users)}")
        info_parts.append(f"• Running Scripts: {len(bot_scripts)}")
        info_parts.append(f"• Total Files: {sum(len(files) for files in user_files.values())}")
        info_parts.append(f"• Bot Status: {'🔒 Locked' if bot_locked else '🔓 Unlocked'}")
        
        info_text = "\n".join(info_parts)
        
        bot.edit_message_text(info_text, call.message.chat.id, call.message.message_id, 
                              reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error showing system info: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error showing system info.", show_alert=True)

def bot_performance_callback(call):
    bot.answer_callback_query(call.id)
    try:
        # Calculate performance metrics
        performance_parts = []
        
        # Script performance
        running_scripts = len(bot_scripts)
        total_files = sum(len(files) for files in user_files.values())
        
        performance_parts.append("📈 **Bot Performance Metrics:**")
        performance_parts.append(f"• Running Scripts: {running_scripts}")
        performance_parts.append(f"• Total Scripts: {total_files}")
        performance_parts.append(f"• Running Ratio: {running_scripts}/{total_files} ({(running_scripts / total_files * 100):.1f}%)" if total_files else '• Running Ratio: 0/0 (N/A)')
        
        # Resource usage
        try:
            bot_process = psutil.Process()
            memory_usage = bot_process.memory_info().rss / 1024 / 1024  # MB
            cpu_usage = bot_process.cpu_percent(interval=0.5)
            
            performance_parts.append("\n💾 **Resource Usage:**")
            performance_parts.append(f"• Memory: {memory_usage:.1f} MB")
            performance_parts.append(f"• CPU: {cpu_usage:.1f}%")
        except Exception as e:
            performance_parts.append(f"\n⚠️ Resource stats error: {str(e)}")
        
        # Database stats
        performance_parts.append("\n🗄️ **Database:**")
        performance_parts.append(f"• Active Users: {len(active_users)}")
        performance_parts.append(f"• Subscriptions: {len(user_subscriptions)}")
        performance_parts.append(f"• Banned Users: {len(banned_users)}")
        performance_parts.append(f"• Custom Limits: {len(user_limits)}")
        
        performance_text = "\n".join(performance_parts)
        
        bot.edit_message_text(performance_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error showing performance: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error showing performance.", show_alert=True)

def cleanup_files_callback(call):
    bot.answer_callback_query(call.id, "🧹 Cleaning up temporary files...")
    
    try:
        # Clean up empty user directories
        cleaned_dirs = 0
        cleaned_files = 0
        
        for user_dir in os.listdir(UPLOAD_BOTS_DIR):
            if user_dir.startswith('.'):
                continue  # temporary restore folders (.restore_in_*, .restore_old_*) must not be touched
            user_path = os.path.join(UPLOAD_BOTS_DIR, user_dir)
            if os.path.isdir(user_path):
                # Check if directory is empty
                if not os.listdir(user_path):
                    try:
                        os.rmdir(user_path)
                        cleaned_dirs += 1
                    except Exception as e:
                        logger.error(f"Error removing empty dir {user_path}: {e}")
                
                # Clean old log files (older than 7 days)
                else:
                    for file_name in os.listdir(user_path):
                        if file_name.endswith('.log'):
                            file_path = os.path.join(user_path, file_name)
                            try:
                                file_age = time.time() - os.path.getmtime(file_path)
                                if file_age > 7 * 24 * 3600:  # 7 days
                                    os.remove(file_path)
                                    cleaned_files += 1
                            except Exception as e:
                                logger.error(f"Error cleaning log file {file_path}: {e}")
        
        result_msg = f"🧹 **Cleanup Complete:**\n• Removed empty directories: {cleaned_dirs}\n• Cleared old log files: {cleaned_files}"
        
        bot.edit_message_text(result_msg, call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
        
    except Exception as e:
        logger.error(f"Error during cleanup: {e}", exc_info=True)
        bot.edit_message_text(f"❌ Cleanup error: {str(e)}", call.message.chat.id, call.message.message_id)

def install_logs_callback(call):
    bot.answer_callback_query(call.id)
    try:
        with DB_LOCK:
            conn = db_connect()
            c = conn.cursor()
            c.execute('SELECT user_id, module_name, package_name, status, install_date FROM install_logs ORDER BY install_date DESC LIMIT 20')
            logs = c.fetchall()
            conn.close()
        
        if not logs:
            bot.edit_message_text("📋 **No installation logs found**", call.message.chat.id, 
                                  call.message.message_id, reply_markup=create_admin_settings_menu())
            return
        
        log_text = "📋 **Recent Installation Logs (Last 20):**\n\n"
        for user_id, module_name, package_name, status, install_date in logs:
            status_icon = "✅" if status == "success" else "❌" if status == "failed" else "⚠️"
            log_text += f"{status_icon} `{user_id}`: {module_name} -> {package_name}\n"
            log_text += f"   📅 {install_date[:19]}\n\n"
        
        bot.edit_message_text(log_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
        
    except Exception as e:
        logger.error(f"Error showing install logs: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error showing logs.", show_alert=True)

def admin_install_callback(call):
    bot.answer_callback_query(call.id)
    _logic_admin_install(call.message)

# --- Mandatory Channels Callbacks ---
def manage_mandatory_channels_callback(call):
    """Handle mandatory channels management request"""
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("📢 Manage Mandatory Channels\nChoose desired action:",
                              call.message.chat.id, call.message.message_id, 
                              reply_markup=create_mandatory_channels_menu())
    except Exception as e:
        logger.error(f"Error showing channel management menu: {e}")

def add_mandatory_channel_callback(call):
    """Start the mandatory-channel setup flow."""
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin permissions required.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    prompt = (
        "📢 <b>Add Force-Join Channel</b>\n\n"
        "Send one of these: <code>@public_channel</code>, "
        "<code>https://t.me/public_channel</code>, or numeric channel ID "
        "such as <code>-1001234567890</code>.\n\n"
        "<b>Important:</b> Add this bot as an administrator in the channel first.\n"
        "Private channels require their numeric ID; send the invite link separately to users if needed.\n\n"
        "Send /cancel to stop."
    )
    msg = bot.send_message(call.message.chat.id, prompt, parse_mode='HTML')
    bot.register_next_step_handler(msg, process_add_channel)

def _normalize_channel_identifier(raw_value):
    """Normalize common Telegram channel username/link/ID formats."""
    value = (raw_value or '').strip()
    if not value:
        raise ValueError('Channel ID or username is empty.')
    value = value.split('?')[0].rstrip('/')
    value = re.sub(r'^https?://(?:www\.)?(?:t\.me|telegram\.me)/', '', value, flags=re.I)
    if value.startswith('s/'):
        value = value[2:]
    # A t.me/c/<internal-id>/<message-id> link maps to a -100 channel ID.
    private_match = re.match(r'^c/(\d+)(?:/\d+)?$', value)
    if private_match:
        return '-100' + private_match.group(1)
    if value.startswith('@'):
        return value
    if re.fullmatch(r'-?\d+', value):
        return value
    if re.fullmatch(r'[A-Za-z0-9_]{5,}', value):
        return '@' + value
    raise ValueError('Invalid format. Send @username, a t.me channel link, or a numeric -100 channel ID.')

def process_add_channel(message):
    """Validate bot permissions and save a force-join channel."""
    admin_id = message.from_user.id
    if admin_id not in admin_ids:
        bot.reply_to(message, "⚠️ Not authorized.")
        return
    if not message.text:
        bot.reply_to(message, "❌ Please send channel username, link, or numeric ID as text.\n/cancel to cancel")
        return
    if message.text.strip().lower() == '/cancel':
        bot.reply_to(message, "❌ Channel addition cancelled.")
        return

    try:
        channel_identifier = _normalize_channel_identifier(message.text)
        chat = bot.get_chat(channel_identifier)
        if getattr(chat, 'type', None) not in ('channel', 'supergroup'):
            bot.reply_to(message, "❌ This is not a Telegram channel/supergroup. Send a channel username or channel ID.")
            return

        channel_id = str(chat.id)
        channel_username = f"@{chat.username}" if getattr(chat, 'username', None) else ""
        channel_name = getattr(chat, 'title', None) or channel_username or channel_id

        try:
            bot_member = bot.get_chat_member(channel_id, bot.get_me().id)
        except Exception as permission_error:
            logger.warning('Cannot inspect bot membership in channel %s: %s', channel_id, permission_error, exc_info=True)
            bot.reply_to(
                message,
                "❌ <b>Bot cannot access this channel.</b>\n\n"
                "1. Add the bot to the channel.\n"
                "2. Promote it to administrator.\n"
                "3. Retry using the channel's @username or -100 channel ID.\n\n"
                f"<i>Telegram says:</i> <code>{html_escape(str(permission_error)[:350])}</code>",
                parse_mode='HTML'
            )
            return

        if getattr(bot_member, 'status', None) not in ('administrator', 'creator'):
            bot.reply_to(message, "❌ Bot is not an administrator in this channel. Promote the bot and try again.")
            return

        if not channel_username:
            # Private channels have no public t.me/username URL. Ask for a real invite link.
            pending_channel_add[admin_id] = {
                'channel_id': channel_id,
                'username': '',
                'name': channel_name,
                'added_by': admin_id
            }
            prompt = bot.reply_to(
                message,
                "🔗 <b>Private channel detected.</b> Send its invite link now "
                "(<code>https://t.me/+...</code> or <code>https://t.me/joinchat/...</code>).\n"
                "Send /cancel to abort.",
                parse_mode='HTML'
            )
            bot.register_next_step_handler(prompt, process_private_channel_invite)
            return

        if save_mandatory_channel(channel_id, channel_username, channel_name, admin_id):
            bot.reply_to(
                message,
                f"✅ <b>Force-join channel added successfully!</b>\n\n"
                f"📢 <b>{html_escape(channel_name)}</b>\n"
                f"🆔 <code>{channel_id}</code>\n"
                f"🔗 {html_escape(channel_username)}",
                parse_mode='HTML',
                reply_markup=create_mandatory_channels_menu()
            )
        else:
            bot.reply_to(message, "❌ Database could not save this channel. Check hosting logs and database write permissions.")
    except ValueError as exc:
        bot.reply_to(message, f"❌ {html_escape(str(exc))}", parse_mode='HTML')
    except Exception as exc:
        logger.error('Error adding mandatory channel: %s', exc, exc_info=True)
        error_text = str(exc)
        if 'chat not found' in error_text.lower():
            hint = 'Channel not found. Check the username/ID and make sure the bot is already added to the channel.'
        elif 'not enough rights' in error_text.lower() or 'administrator' in error_text.lower():
            hint = 'Bot needs administrator access in that channel.'
        else:
            hint = 'Could not add this channel. Verify the channel ID/username and bot admin permissions.'
        bot.reply_to(message, f"❌ <b>{html_escape(hint)}</b>\n<code>{html_escape(error_text[:350])}</code>", parse_mode='HTML')

def process_private_channel_invite(message):
    admin_id = message.from_user.id
    pending = pending_channel_add.get(admin_id)
    if admin_id not in admin_ids or not pending:
        bot.reply_to(message, '⚠️ This channel setup has expired. Start again from Channel Add.')
        return
    if not message.text:
        bot.reply_to(message, '❌ Send the private invite URL as text, or /cancel.')
        bot.register_next_step_handler(message, process_private_channel_invite)
        return
    value = message.text.strip()
    if value.lower() == '/cancel':
        pending_channel_add.pop(admin_id, None)
        bot.reply_to(message, '❌ Private channel setup cancelled.')
        return
    if not re.match(r'^https?://(?:www\.)?t\.me/(?:\+[^/\s]+|joinchat/[^/\s]+)(?:\?.*)?$', value, re.I):
        bot.reply_to(message, '❌ Invalid invite link. Use https://t.me/+... or https://t.me/joinchat/....')
        bot.register_next_step_handler(message, process_private_channel_invite)
        return
    pending_channel_add.pop(admin_id, None)
    if save_mandatory_channel(pending['channel_id'], '', pending['name'], admin_id, invite_link=value):
        bot.reply_to(
            message,
            f"✅ <b>Private force-join channel added!</b>\n\n"
            f"📢 <b>{html_escape(pending['name'])}</b>\n"
            f"🆔 <code>{pending['channel_id']}</code>\n"
            f"🔗 {html_escape(value)}",
            parse_mode='HTML', reply_markup=create_mandatory_channels_menu()
        )
    else:
        bot.reply_to(message, '❌ Database could not save this channel. Check hosting logs.')


def remove_mandatory_channel_callback(call):
    """Remove mandatory channel"""
    if not mandatory_channels:
        bot.answer_callback_query(call.id, "❌ No mandatory channels.", show_alert=True)
        return
        
    bot.answer_callback_query(call.id)
    
    markup = NavMenu()
    for channel_id, channel_info in list(mandatory_channels.items()):
        channel_name = channel_info.get('name', 'Unknown')
        button_text = f"🗑️ {channel_name}"
        markup.add(NavButton(button_text, callback_data=f'remove_channel_{channel_id}'))
    
    markup.add(NavButton("🔙 Back", callback_data='manage_mandatory_channels'))
    
    try:
        bot.edit_message_text("📢 Choose channel to delete:",
                              call.message.chat.id, call.message.message_id, 
                              reply_markup=markup)
    except Exception as e:
        logger.error(f"Error showing remove channel menu: {e}")

def process_remove_channel(call):
    """Process channel removal"""
    channel_id = call.data.replace('remove_channel_', '')
    
    if channel_id in mandatory_channels:
        channel_name = mandatory_channels[channel_id].get('name', 'Unknown')
        if remove_mandatory_channel_db(channel_id):
            bot.answer_callback_query(call.id, f"✅ Channel deleted: {channel_name}")
            try:
                bot.edit_message_text(f"✅ Mandatory channel deleted: **{channel_name}**",
                                      call.message.chat.id, call.message.message_id,
                                      reply_markup=create_mandatory_channels_menu(), parse_mode='Markdown')
            except Exception as e:
                logger.error(f"Error updating message after channel removal: {e}")
        else:
            bot.answer_callback_query(call.id, "❌ Failed to delete channel.", show_alert=True)
    else:
        bot.answer_callback_query(call.id, "❌ Channel not found.", show_alert=True)

def list_mandatory_channels_callback(call):
    """Show list of mandatory channels"""
    bot.answer_callback_query(call.id)
    
    if not mandatory_channels:
        message_text = "📢 **No mandatory channels currently**"
    else:
        message_text = "📢 **Mandatory Channels:**\n\n"
        for channel_id, channel_info in list(mandatory_channels.items()):
            channel_name = channel_info.get('name', 'Unknown')
            channel_username = channel_info.get('username', 'No username')
            message_text += f"• **{channel_name}**\n  {channel_username or channel_id}\n\n"
    
    try:
        bot.edit_message_text(message_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_mandatory_channels_menu(), parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error listing channels: {e}")

def check_subscription_status_callback(call):
    """Check subscription status"""
    user_id = call.from_user.id
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    
    if is_subscribed or user_id in admin_ids:
        bot.answer_callback_query(call.id, "✅ You are subscribed to all required channels!", show_alert=True)
        # Show main menu
        try:
            _logic_send_welcome(call.message)
        except Exception:
            back_to_main_callback(call)
    else:
        bot.answer_callback_query(call.id, "❌ You haven't joined all required channels yet!", show_alert=True)
        # Update the subscription message
        subscription_message, markup = create_subscription_check_message(not_joined)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, 
                                  call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception as e:
            logger.error(f"Error updating subscription message: {e}")

# --- Security Approval Callbacks ---
def _parse_review_data(call):
    """Read (user_id, file_name) from approve/reject button data. Returns None and answers the admin if invalid."""
    data_parts = (call.data or '').split('_')
    if len(data_parts) < 4:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True)
        return None
    try:
        user_id = int(data_parts[2])
    except ValueError:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True)
        return None
    # Only a plain file name is allowed; never a path.
    file_name = os.path.basename('_'.join(data_parts[3:]).replace('\\', '/'))
    if not file_name or file_name in ('.', '..'):
        bot.answer_callback_query(call.id, "❌ Invalid file name.", show_alert=True)
        return None
    return user_id, file_name


def _pop_pending_zip(user_id, file_name):
    """Remove and return a stored zip (or None). Keeps the time-tracking dict in step."""
    with STATE_LOCK:
        content = pending_zip_files.get(user_id, {}).pop(file_name, None)
        pending_zip_times.pop((user_id, file_name), None)
        if user_id in pending_zip_files and not pending_zip_files[user_id]:
            del pending_zip_files[user_id]
    return content


def process_approve_file(call):
    """Process admin approval for file"""
    parsed = _parse_review_data(call)
    if not parsed:
        return
    user_id, file_name = parsed
    safe_name = html_escape(file_name)

    user_folder = get_user_folder(user_id)
    file_path = os.path.join(user_folder, file_name)

    if not os.path.exists(file_path):
        bot.answer_callback_query(call.id, "❌ File not found.", show_alert=True)
        return

    file_ext = os.path.splitext(file_name)[1].lower()

    try:
        if file_ext == '.js':
            handle_js_file(file_path, user_id, user_folder, file_name, call.message)
        elif file_ext == '.py':
            handle_py_file(file_path, user_id, user_folder, file_name, call.message)

        bot.answer_callback_query(call.id, "✅ File approved!")
        bot.edit_message_text(f"✅ File <code>{safe_name}</code> approved for user <code>{user_id}</code>",
                              call.message.chat.id, call.message.message_id, parse_mode='HTML')
        try:
            bot.send_message(user_id, f"✅ Your file <code>{safe_name}</code> has been approved and started.",
                             parse_mode='HTML')
        except Exception as e:
            logger.error("Failed to notify user %s: %s", user_id, e)
    except Exception as e:
        logger.error("Error processing approved file: %s", e, exc_info=True)
        bot.answer_callback_query(call.id, "❌ Error processing file.", show_alert=True)


def process_reject_file(call):
    """Process admin rejection for file"""
    parsed = _parse_review_data(call)
    if not parsed:
        return
    user_id, file_name = parsed
    safe_name = html_escape(file_name)

    file_path = os.path.join(get_user_folder(user_id), file_name)
    if os.path.exists(file_path):
        try:
            os.remove(file_path)
        except Exception as e:
            logger.error("Error deleting rejected file: %s", e)

    bot.answer_callback_query(call.id, "❌ File rejected!")
    bot.edit_message_text(f"❌ File <code>{safe_name}</code> rejected for user <code>{user_id}</code>",
                          call.message.chat.id, call.message.message_id, parse_mode='HTML')
    try:
        bot.send_message(user_id, f"❌ Your file <code>{safe_name}</code> has been rejected for security reasons.",
                         parse_mode='HTML')
    except Exception as e:
        logger.error("Failed to notify user %s: %s", user_id, e)


def process_approve_zip(call):
    """Process admin approval for ZIP file"""
    parsed = _parse_review_data(call)
    if not parsed:
        return
    user_id, file_name = parsed
    safe_name = html_escape(file_name)

    file_content = _pop_pending_zip(user_id, file_name)
    if file_content is None:
        bot.answer_callback_query(call.id, "❌ File content not found or expired. Ask user to re-upload.", show_alert=True)
        return

    user_folder = get_user_folder(user_id)
    temp_dir = None
    try:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_approve_")
        zip_path = os.path.join(temp_dir, file_name)
        with open(zip_path, 'wb') as f:
            f.write(file_content)
        file_content = None  # free the memory

        process_zip_file(zip_path, user_id, user_folder, file_name, call.message, temp_dir)

        bot.answer_callback_query(call.id, "✅ Archive approved!")
        bot.edit_message_text(f"✅ Archive <code>{safe_name}</code> approved for user <code>{user_id}</code>",
                              call.message.chat.id, call.message.message_id, parse_mode='HTML')
        try:
            bot.send_message(user_id, f"✅ Your archive <code>{safe_name}</code> has been approved and processed.",
                             parse_mode='HTML')
        except Exception as e:
            logger.error("Failed to notify user %s: %s", user_id, e)
    except Exception as e:
        logger.error("Error processing approved zip: %s", e, exc_info=True)
        bot.answer_callback_query(call.id, "❌ Error processing archive.", show_alert=True)
    finally:
        if temp_dir and os.path.exists(temp_dir):
            shutil.rmtree(temp_dir, ignore_errors=True)


def process_reject_zip(call):
    """Process admin rejection for ZIP file"""
    parsed = _parse_review_data(call)
    if not parsed:
        return
    user_id, file_name = parsed
    safe_name = html_escape(file_name)
    _pop_pending_zip(user_id, file_name)

    bot.answer_callback_query(call.id, "❌ Archive rejected!")
    bot.edit_message_text(f"❌ Archive <code>{safe_name}</code> rejected for user <code>{user_id}</code>",
                          call.message.chat.id, call.message.message_id, parse_mode='HTML')
    try:
        bot.send_message(user_id, f"❌ Your archive <code>{safe_name}</code> has been rejected for security reasons.",
                         parse_mode='HTML')
    except Exception as e:
        logger.error("Failed to notify user %s: %s", user_id, e)

# --- Cleanup Function ---
_CLEANUP_DONE = False

def cleanup():
    """Stop every hosted script. Safe to call more than once."""
    global _CLEANUP_DONE
    if _CLEANUP_DONE:
        return
    _CLEANUP_DONE = True
    SHUTDOWN_EVENT.set()
    logger.warning("Shutdown. Cleaning up processes...")
    with STATE_LOCK:
        infos = list(bot_scripts.items())
    if not infos:
        logger.info("No scripts running. Exiting.")
        return
    logger.info("Stopping %s scripts...", len(infos))
    for key, info in infos:
        try:
            logger.info("Stopping: %s", key)
            kill_process_tree(info)
        except Exception:
            logger.exception("Could not stop %s", key)
    logger.warning("Cleanup finished.")
atexit.register(cleanup)


def _handle_signal(signum, _frame):
    logger.warning("Received signal %s; shutting down gracefully.", signum)
    SHUTDOWN_EVENT.set()
    try:
        bot.stop_polling()
    except Exception as exc:
        logger.debug("stop_polling: %s", exc)


def run_polling_forever():
    """Run polling; if it ever stops or fails, restart with a growing delay (max 60s)."""
    delay = 3
    while not SHUTDOWN_EVENT.is_set():
        started = time.time()
        HEALTH_STATE['last_poll_start'] = datetime.now().isoformat(timespec='seconds')
        try:
            bot.infinity_polling(logger_level=logging.INFO, timeout=60, long_polling_timeout=30,
                                 skip_pending=True)
        except requests.exceptions.ReadTimeout:
            logger.warning("Polling read timeout.")
        except requests.exceptions.ConnectionError as ce:
            logger.error("Polling connection error: %s", ce)
            HEALTH_STATE['last_error'] = 'connection error'
        except Exception as exc:
            logger.exception("Polling crashed: %s", exc)
            HEALTH_STATE['last_error'] = str(exc)[:200]
        if SHUTDOWN_EVENT.is_set():
            break
        HEALTH_STATE['poll_restarts'] += 1
        # A run that lasted a while means the network was fine: start the backoff over.
        delay = 3 if time.time() - started > 120 else min(delay * 2, 60)
        logger.warning("Polling stopped. Restarting in %ss (restart #%s).", delay, HEALTH_STATE['poll_restarts'])
        SHUTDOWN_EVENT.wait(delay)


# --- Main Execution ---
@bot.message_handler(func=lambda m: m.chat.type == 'private' and bool(m.text) and not m.text.startswith('/'),
                     content_types=['text'])
def handle_stale_text(message):
    """Registered last: any other text brings the current keyboard back."""
    _nav_stale(message)


if __name__ == '__main__':
    logger.info("Starting up. Python %s | data dir: %s | owner: %s | admins: %s | banned: %s | channels: %s",
                sys.version.split()[0], IROTECH_DIR, OWNER_ID, len(admin_ids), len(banned_users),
                len(mandatory_channels))
    for _sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(_sig, _handle_signal)
        except (ValueError, OSError) as exc:
            logger.warning("Could not install handler for %s: %s", _sig, exc)
    keep_alive()
    start_watchdog()
    logger.info("Starting polling...")
    try:
        run_polling_forever()
    finally:
        cleanup()
        logging.shutdown()
