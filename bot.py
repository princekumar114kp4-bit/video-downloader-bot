# -*- coding: utf-8 -*-
from html import escape as html_escape
import telebot
import subprocess
import os
import zipfile
import tempfile
import shutil
from telebot import types
import time
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

# --- Security Settings ---
SECURITY_CONFIG = {
    'blocked_modules': ['os.system', 'os', 'zipfile', 'subprocess.Popen', 'subprocess', 'eval', 'exec','compile', '__import__'],
    'max_file_size': MAX_UPLOAD_MB * 1024 * 1024,
    'max_script_runtime': 3600,  # 1 hour
    'allowed_extensions': ['.py', '.js'],
    'blocked_imports': ['shutil.rmtree', 'subprocess','os.remove', 'os.unlink']
}


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

    def send_message(self, *args, **kwargs):
        return self._guard(super().send_message, args, kwargs, 'send_message')

    def edit_message_text(self, *args, **kwargs):
        return self._guard(super().edit_message_text, args, kwargs, 'edit_message_text')

    def answer_callback_query(self, *args, **kwargs):
        return self._guard(super().answer_callback_query, args, kwargs, 'answer_callback_query')

    def delete_message(self, *args, **kwargs):
        return self._guard(super().delete_message, args, kwargs, 'delete_message')

    def send_document(self, *args, **kwargs):
        return self._guard(super().send_document, args, kwargs, 'send_document')

    def send_photo(self, *args, **kwargs):
        return self._guard(super().send_photo, args, kwargs, 'send_photo')

    def send_video(self, *args, **kwargs):
        return self._guard(super().send_video, args, kwargs, 'send_video')

    def send_audio(self, *args, **kwargs):
        return self._guard(super().send_audio, args, kwargs, 'send_audio')

    def send_voice(self, *args, **kwargs):
        return self._guard(super().send_voice, args, kwargs, 'send_voice')

    def send_sticker(self, *args, **kwargs):
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

# --- Security Functions ---
def _code_security_reasons(content, file_type):
    """Conservative review checks; normal bot APIs, regex, files and HTTP are allowed."""
    reasons = []
    destructive_patterns = [
        (r'(?i)\brm\s+-rf\s+/(?:\s|$)', 'recursive deletion of filesystem root'),
        (r'(?i)\bmkfs(?:\.[a-z0-9]+)?\b', 'filesystem formatting command'),
        (r'(?i)\bdd\s+if=.*\bof=/dev/(?:sd|nvme|vd)', 'raw disk overwrite command'),
        (r'(?i)\b(?:shutdown|poweroff|reboot)\b', 'host shutdown command'),
        (r'(?i)\bchmod\s+-R\s+777\b', 'recursive world-writable permissions'),
    ]
    for pattern, label in destructive_patterns:
        if re.search(pattern, content):
            reasons.append(label)

    if file_type == 'py':
        try:
            tree = ast.parse(content)
        except SyntaxError:
            # Syntax errors are reported by the runner; don't falsely label them unsafe.
            tree = None
        if tree is not None:
            for node in ast.walk(tree):
                if not isinstance(node, ast.Call):
                    continue
                parts = []
                current = node.func
                while isinstance(current, ast.Attribute):
                    parts.append(current.attr)
                    current = current.value
                if isinstance(current, ast.Name):
                    parts.append(current.id)
                dotted = '.'.join(reversed(parts))
                if dotted in {'os.system', 'os.popen', 'subprocess.Popen', 'subprocess.run',
                              'subprocess.call', 'subprocess.check_output', 'shutil.rmtree',
                              'eval', 'exec', 'compile', '__import__'}:
                    reasons.append(f'powerful operation: {dotted}')
                    if len(reasons) >= 8:
                        break
    elif file_type == 'js':
        js_patterns = [
            (r'(?i)\bchild_process\s*\.\s*(?:exec|execSync|spawn|spawnSync)\s*\(', 'Node child-process execution'),
            (r'(?i)\beval\s*\(', 'dynamic eval execution'),
            (r'(?i)\bfs\s*\.\s*(?:rmSync|rmdirSync)\s*\(', 'recursive filesystem deletion'),
        ]
        for pattern, label in js_patterns:
            if re.search(pattern, content):
                reasons.append(label)
    return list(dict.fromkeys(reasons))


def check_code_security(file_path, file_type):
    """Flag high-impact operations for admin review without blocking normal bot code."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as handle:
            content = handle.read()
        reasons = _code_security_reasons(content, file_type)
        if reasons:
            logger.warning('Code requires review: %s: %s', file_path, reasons)
            return False, 'Potentially powerful operations require admin review: ' + ', '.join(reasons[:5])
        return True, 'No high-impact patterns detected (not a security sandbox)'
    except Exception as exc:
        logger.exception('Code review scan failed for %s', file_path)
        return False, f'Security check error: {exc}'


def scan_zip_security(zip_path):
    """Inspect source files in ZIP archives for high-impact operations."""
    try:
        with zipfile.ZipFile(zip_path, 'r') as archive:
            for item in archive.infolist():
                if item.is_dir():
                    continue
                ext = os.path.splitext(item.filename)[1].lower()
                if ext not in ('.py', '.js'):
                    continue
                if item.file_size > 2 * 1024 * 1024:
                    return False, f'Source file too large to inspect: {item.filename}'
                content = archive.read(item).decode('utf-8', errors='ignore')
                reasons = _code_security_reasons(content, 'py' if ext == '.py' else 'js')
                if reasons:
                    return False, f'{item.filename} requires admin review: {", ".join(reasons[:5])}'
        return True, 'No high-impact patterns detected (not a security sandbox)'
    except Exception as exc:
        return False, f'Error scanning archive: {exc}'

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
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('➕ Add Channel', callback_data='add_mandatory_channel'),
        types.InlineKeyboardButton('➖ Remove Channel', callback_data='remove_mandatory_channel')
    )
    markup.row(types.InlineKeyboardButton('📋 List Channels', callback_data='list_mandatory_channels'))
    markup.row(types.InlineKeyboardButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_check_message(not_joined_channels):
    """Create subscription verification message"""
    message = "📢 <b>Important: Join Our Channels First:</b>\n\n"
    
    markup = types.InlineKeyboardMarkup()
    
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
            markup.add(types.InlineKeyboardButton(f"Join {channel_name}"[:64], url=channel_link))
        else:
            message += "  Private invite link unavailable; contact the bot owner.\n"
    
    markup.add(types.InlineKeyboardButton("✅ Verify Subscription", callback_data='check_subscription_status'))
    
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
def create_reply_main_menu(user_id):
    """Persistent Telegram reply keyboard for quick access to common actions."""
    markup = types.ReplyKeyboardMarkup(
        row_width=2, resize_keyboard=True, one_time_keyboard=False,
        selective=False, input_field_placeholder="Choose a hosting action..."
    )
    markup.row(types.KeyboardButton("📤 Upload File"), types.KeyboardButton("📂 Check Files"))
    markup.row(types.KeyboardButton("⚡ Bot Speed"), types.KeyboardButton("📊 Statistics"))
    markup.row(types.KeyboardButton("👤 Account"), types.KeyboardButton("🤖 My Bots"))
    markup.row(types.KeyboardButton("📢 Updates Channel"), types.KeyboardButton("📞 Contact Owner"))
    markup.row(types.KeyboardButton("🆘 Help"), types.KeyboardButton("🏠 Main Menu"))
    if user_id in admin_ids:
        markup.row(types.KeyboardButton("👑 Admin Panel"), types.KeyboardButton("👥 User Management"))
        markup.row(types.KeyboardButton("📢 Broadcast"), types.KeyboardButton("🩺 Hosting Health"))
        markup.row(types.KeyboardButton("💳 Subscriptions"), types.KeyboardButton("⚙️ Settings"))
        markup.row(types.KeyboardButton("🛠️ Manual Install"), types.KeyboardButton("📢 Channel Add"))
        markup.row(types.KeyboardButton("🔒 Lock Bot"), types.KeyboardButton("🟢 Running All Code"))
    return markup


def create_main_menu_inline(user_id):
    """Premium inline menu; retained alongside the persistent reply keyboard."""
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('📤 Upload Script', callback_data='upload'),
        types.InlineKeyboardButton('📂 My Files', callback_data='check_files')
    )
    markup.row(
        types.InlineKeyboardButton('👤 My Account', callback_data='user_account'),
        types.InlineKeyboardButton('🤖 My Running Bots', callback_data='my_running')
    )
    markup.row(
        types.InlineKeyboardButton('⚡ Speed Test', callback_data='speed'),
        types.InlineKeyboardButton('📊 Statistics', callback_data='stats')
    )
    markup.row(
        types.InlineKeyboardButton('📦 Module Install', callback_data='manual_install'),
        types.InlineKeyboardButton('🆘 Help', callback_data='user_help')
    )
    markup.row(
        types.InlineKeyboardButton('📢 Updates', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'),
        types.InlineKeyboardButton('📞 Support', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}')
    )
    if user_id in admin_ids:
        markup.row(types.InlineKeyboardButton('👑 ADMIN CONTROL CENTER', callback_data='admin_dashboard'))
        markup.row(
            types.InlineKeyboardButton('🩺 Hosting Health', callback_data='hosting_health'),
            types.InlineKeyboardButton('⚙️ Admin Settings', callback_data='admin_settings')
        )
        markup.row(
            types.InlineKeyboardButton('👥 User Management', callback_data='user_management'),
            types.InlineKeyboardButton('📢 Broadcast', callback_data='broadcast')
        )
    return markup


# --- Database / bot-data export and import ----------------------------------
# Two separate scopes:
#   * Hosting database (DATABASE_PATH): admin panel only, import limited to OWNER_ID / ADMIN_ID.
#   * One uploaded bot's own data files: only the owner of that bot, only inside that user's folder.
# Every import is staged first, shown to the person for a Yes/No confirmation, and the current
# data is backed up automatically before anything is overwritten.
DATA_EXTS = ('.db', '.sqlite', '.sqlite3', '.json', '.csv', '.txt', '.pkl', '.pickle')
DATA_SQLITE_EXTS = ('.db', '.sqlite', '.sqlite3')
DATA_SKIP_NAMES = {'requirements.txt', 'package.json', 'package-lock.json', 'tsconfig.json', 'nohup.out'}
DATA_SKIP_DIRS = {'node_modules', '__pycache__', 'venv', 'env', 'site-packages'}
SQLITE_MAGIC = b'SQLite format 3\x00'
IMPORT_TTL = 600                      # seconds a pending upload / confirmation stays valid
EXPORT_MAX_BYTES = 45 * 1024 * 1024   # Telegram bots cannot send files above ~50 MB
BACKUP_KEEP = 5                       # automatic pre-import backups kept per scope
DB_BACKUP_DIR = os.path.join(IROTECH_DIR, 'db_backups')
USER_DATA_BACKUP_DIR = os.path.join(IROTECH_DIR, 'user_data_backups')
HOSTING_DB_CORE_TABLES = ('subscriptions', 'user_files', 'active_users', 'admins')
IMPORT_LOCK = threading.RLock()
PENDING_IMPORT_WAIT = {}      # user_id -> {'kind', 'owner', 'file', 'time'}   waiting for the upload
PENDING_IMPORT_CONFIRM = {}   # token -> staged import waiting for Yes / No


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


def _expire_pending_imports():
    """Forget stale waiting states and delete staged files nobody confirmed."""
    now = time.time()
    with IMPORT_LOCK:
        for uid in [u for u, p in PENDING_IMPORT_WAIT.items() if now - p['time'] > IMPORT_TTL]:
            PENDING_IMPORT_WAIT.pop(uid, None)
        for token in [t for t, e in PENDING_IMPORT_CONFIRM.items() if now - e['time'] > IMPORT_TTL]:
            entry = PENDING_IMPORT_CONFIRM.pop(token, None)
            if entry:
                _rmtree_quiet(entry.get('dir'))


def _discard_all_pending_imports():
    with IMPORT_LOCK:
        entries = list(PENDING_IMPORT_CONFIRM.values())
        PENDING_IMPORT_CONFIRM.clear()
        PENDING_IMPORT_WAIT.clear()
    for entry in entries:
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
        raise ValueError(f'That file is too big (maximum {max_mb} MB).')
    file_info = bot.get_file(doc.file_id)
    content = bot.download_file(file_info.file_path)
    if len(content) > limit:
        raise ValueError(f'That file is too big (maximum {max_mb} MB).')
    return content


def _confirm_markup(token):
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(types.InlineKeyboardButton('✅ Yes, import', callback_data=f'impc_yes_{token}'),
               types.InlineKeyboardButton('❌ Cancel', callback_data=f'impc_no_{token}'))
    return markup


def _cancel_markup():
    return types.InlineKeyboardMarkup().add(types.InlineKeyboardButton('❌ Cancel', callback_data='impc_cancel'))


def _store_confirm(entry):
    token = os.urandom(6).hex()
    entry['time'] = time.time()
    with IMPORT_LOCK:
        PENDING_IMPORT_CONFIRM[token] = entry
    return token


# --- Hosting database (admin only) ------------------------------------------
def _can_import_global(user_id):
    """Replacing the whole database can also replace the admin list, so only the configured
    owner / main admin may do it (not admins that were added later)."""
    return user_id in (OWNER_ID, ADMIN_ID) and user_id in admin_ids


def _db_counts(path):
    """(users, scripts, subscriptions, admins) of a database file, plus an error text or ''."""
    conn = sqlite3.connect(path, timeout=10)
    try:
        counts = []
        for table in ('active_users', 'user_files', 'subscriptions', 'admins'):
            counts.append(conn.execute(f'SELECT COUNT(*) FROM {table}').fetchone()[0])
        return tuple(counts)
    finally:
        conn.close()


def _inspect_hosting_db(path):
    """Check an uploaded file really is a hosting-bot database. Returns (ok, message, counts)."""
    try:
        with open(path, 'rb') as handle:
            if handle.read(16) != SQLITE_MAGIC:
                return False, 'That is not a SQLite database file. Send the .db file you exported from this bot.', None
        conn = sqlite3.connect(path, timeout=10)
        try:
            result = conn.execute('PRAGMA integrity_check').fetchone()
            if not result or result[0] != 'ok':
                return False, 'That database file is damaged, so I did not import it.', None
            tables = {row[0] for row in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        finally:
            conn.close()
        missing = [t for t in HOSTING_DB_CORE_TABLES if t not in tables]
        if missing:
            return False, ('This database does not look like a backup of this hosting bot '
                           f'(missing: {", ".join(missing)}). Nothing was changed.'), None
        return True, '', _db_counts(path)
    except sqlite3.Error:
        return False, 'I could not read that database file. Nothing was changed.', None


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


def export_database_callback(call):
    """Send the hosting bot's own database as a file (admins only; checked by the dispatcher)."""
    bot.answer_callback_query(call.id, 'Preparing the database file...')
    tmp_dir = tempfile.mkdtemp(prefix='demon_dbexport_')
    try:
        export_path = os.path.join(tmp_dir, f'hosting_bot_database_{_now_stamp()}.db')
        with DB_LOCK:
            source = db_connect()
            try:
                target = sqlite3.connect(export_path)
                try:
                    source.backup(target)
                finally:
                    target.close()
            finally:
                source.close()
        counts = _db_counts(export_path)
        with open(export_path, 'rb') as export_file:
            bot.send_document(call.message.chat.id, export_file,
                              caption=('<b>📥 Database Export</b>\n'
                                       f'Users: <b>{counts[0]}</b> | Scripts: <b>{counts[1]}</b> | '
                                       f'Subscriptions: <b>{counts[2]}</b> | Admins: <b>{counts[3]}</b>\n'
                                       'Keep this file safe. Use <b>Import Database</b> to restore it.'),
                              parse_mode='HTML')
        logger.info("Database exported by admin %s", call.from_user.id)
    except Exception as exc:
        logger.exception('Database export failed')
        bot.send_message(call.message.chat.id,
                         f'⚠️ Database export failed: <code>{html_escape(str(exc)[:300])}</code>', parse_mode='HTML')
    finally:
        _rmtree_quiet(tmp_dir)


def import_database_callback(call):
    uid = call.from_user.id
    if not _can_import_global(uid):
        bot.answer_callback_query(call.id, '⚠️ Only the owner can import the database.', show_alert=True)
        return
    bot.answer_callback_query(call.id)
    _expire_pending_imports()
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT[uid] = {'kind': 'global', 'time': time.time()}
    bot.send_message(
        call.message.chat.id,
        ('<b>📤 Import Database</b>\n'
         'Send me the <code>.db</code> file you exported earlier (as a file/document).\n\n'
         '⚠️ This replaces <b>all</b> live hosting data (users, scripts list, subscriptions, admins, bans). '
         'I will show you a summary and ask you to confirm first, and the current database is backed up '
         'automatically before anything is overwritten.\n'
         f'The request expires in {IMPORT_TTL // 60} minutes.'),
        parse_mode='HTML', reply_markup=_cancel_markup())


def _stage_global_import(message):
    uid = message.from_user.id
    if not _can_import_global(uid):
        bot.reply_to(message, '⚠️ Only the owner can import the database.')
        return
    doc = message.document
    name = (doc.file_name or '').lower()
    if not name.endswith(DATA_SQLITE_EXTS):
        bot.reply_to(message, '⚠️ Please send the database file you exported (it ends with .db). Nothing was changed.')
        return
    tmp_dir = tempfile.mkdtemp(prefix='demon_dbimport_')
    keep = False
    try:
        try:
            content = _download_upload(message, MAX_UPLOAD_MB)
        except ValueError as exc:
            bot.reply_to(message, f'⚠️ {exc}')
            return
        except Exception as exc:
            logger.warning("Database import download failed: %s", redact_secrets(exc))
            bot.reply_to(message, '⚠️ I could not download that file. Please try again.')
            return
        staged = os.path.join(tmp_dir, 'upload.db')
        with open(staged, 'wb') as handle:
            handle.write(content)
        ok, problem, counts = _inspect_hosting_db(staged)
        if not ok:
            bot.reply_to(message, f'⚠️ {problem}')
            return
        try:
            current = _db_counts(DATABASE_PATH)
        except sqlite3.Error:
            current = ('?', '?', '?', '?')
        token = _store_confirm({'kind': 'global', 'user_id': uid, 'dir': tmp_dir, 'path': staged})
        keep = True
        bot.reply_to(
            message,
            ('<b>⚠️ Confirm database import</b>\n'
             'This will REPLACE the live hosting database.\n\n'
             f'<b>Uploaded file:</b> {counts[0]} users, {counts[1]} scripts, {counts[2]} subscriptions, {counts[3]} admins\n'
             f'<b>Current live data:</b> {current[0]} users, {current[1]} scripts, {current[2]} subscriptions, {current[3]} admins\n\n'
             'A timestamped backup of the current database is taken automatically before the switch. Continue?'),
            parse_mode='HTML', reply_markup=_confirm_markup(token))
    finally:
        if not keep:
            _rmtree_quiet(tmp_dir)


def _apply_global_import(staged_path):
    """Back up the live database, then overwrite it with the staged one. Returns (backup_path, missing_scripts)."""
    os.makedirs(DB_BACKUP_DIR, exist_ok=True)
    backup_path = os.path.join(DB_BACKUP_DIR, f'bot_data_before_import_{_now_stamp()}.db')
    with DB_LOCK:
        live = db_connect()
        try:
            backup_conn = sqlite3.connect(backup_path)
            try:
                live.backup(backup_conn)
            finally:
                backup_conn.close()
        finally:
            live.close()
        source = sqlite3.connect(staged_path, timeout=30)
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
    _prune_backups(DB_BACKUP_DIR, 'bot_data_before_import_')
    missing = 0
    for uid, items in list(user_files.items()):
        for file_name, _ftype in list(items):
            if not os.path.isfile(os.path.join(UPLOAD_BOTS_DIR, str(uid), file_name)):
                missing += 1
    return backup_path, missing


# --- One uploaded bot's own data (owner of that bot only) --------------------
def _is_safe_data_rel(rel):
    """Relative path of a data file: only plain folders and allowed data extensions."""
    if not rel or len(rel) > 200 or '\x00' in rel:
        return False
    if rel.startswith('/') or '\\' in rel or (len(rel) > 1 and rel[1] == ':'):
        return False
    parts = rel.split('/')
    for part in parts:
        if part in ('', '.', '..') or part.startswith('.'):
            return False
    if any(part in DATA_SKIP_DIRS for part in parts[:-1]):
        return False
    name = parts[-1]
    return name.lower() not in DATA_SKIP_NAMES and os.path.splitext(name)[1].lower() in DATA_EXTS


def _list_bot_data_files(user_folder):
    """Data files inside one user's folder: [(relative_path, full_path, size)]. Never leaves the folder."""
    root = os.path.realpath(user_folder)
    if not _path_inside(os.path.realpath(UPLOAD_BOTS_DIR), root) or root == os.path.realpath(UPLOAD_BOTS_DIR):
        return []
    found = []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = [d for d in dirnames
                       if d not in DATA_SKIP_DIRS and not d.startswith('.')
                       and not os.path.islink(os.path.join(dirpath, d))]
        for file_name in filenames:
            full = os.path.join(dirpath, file_name)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            if not _path_inside(root, os.path.realpath(full)):
                continue
            rel = os.path.relpath(full, root).replace(os.sep, '/')
            if not _is_safe_data_rel(rel):
                continue
            try:
                found.append((rel, full, os.path.getsize(full)))
            except OSError:
                continue
            if len(found) > MAX_ZIP_FILES:
                return sorted(found)
    return sorted(found)


def _may_manage_bot_data(user_id, owner_id):
    # Same rule as the existing per-file handlers (start / stop / delete / logs).
    return user_id == owner_id or user_id in admin_ids


def _bot_data_target(call, prefix):
    """Parse 'bdx_<owner>_<file>' / 'bdi_<owner>_<file>' and check the requester owns that bot.
    Returns (owner_id, file_name) or None after telling the user why."""
    try:
        _, owner_str, file_name = call.data.split('_', 2)
        owner_id = int(owner_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, 'Error: invalid action data.', show_alert=True)
        return None
    if not _may_manage_bot_data(call.from_user.id, owner_id):
        logger.warning("User %s tried bot-data access for user %s (%s)", call.from_user.id, owner_id, file_name)
        bot.answer_callback_query(call.id, '⚠️ You can only export or import data of your own bots.', show_alert=True)
        return None
    if not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.answer_callback_query(call.id, '⚠️ File not found.', show_alert=True)
        return None
    return owner_id, file_name


def _any_script_running(owner_id):
    return any(is_bot_running(owner_id, item[0]) for item in list(user_files.get(owner_id, [])))


def export_bot_data_callback(call):
    target = _bot_data_target(call, 'bdx')
    if not target:
        return
    owner_id, file_name = target
    files = _list_bot_data_files(get_user_folder(owner_id))
    if not files:
        bot.answer_callback_query(
            call.id, '⚠️ No data files found yet (looking for .db, .sqlite, .json, .csv, .txt, .pkl). '
                     'Run your bot first so it can create its data.', show_alert=True)
        return
    if len(files) > MAX_ZIP_FILES or sum(item[2] for item in files) > MAX_UNZIPPED_MB * 1024 * 1024:
        bot.answer_callback_query(call.id, '⚠️ Your data is too big to export in one go.', show_alert=True)
        return
    bot.answer_callback_query(call.id, 'Preparing your data file...')
    tmp_dir = tempfile.mkdtemp(prefix=f'demon_botdata_{owner_id}_')
    try:
        stem = re.sub(r'[^A-Za-z0-9_-]+', '_', os.path.splitext(file_name)[0])[:40] or 'bot'
        zip_path = os.path.join(tmp_dir, f'{stem}_data_{_now_stamp()}.zip')
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as archive:
            for index, (rel, full, _size) in enumerate(files):
                if rel.lower().endswith(DATA_SQLITE_EXTS):
                    snap = os.path.join(tmp_dir, f'snap_{index}.tmp')
                    _sqlite_snapshot(full, snap)
                    archive.write(snap, rel)
                    os.remove(snap)
                else:
                    archive.write(full, rel)
        if os.path.getsize(zip_path) > EXPORT_MAX_BYTES:
            bot.send_message(call.message.chat.id, '⚠️ Your data file is too big to send through Telegram (over 45 MB).')
            return
        listing = '\n'.join(f'• <code>{html_escape(rel)}</code>' for rel, _f, _s in files[:12])
        more = f'\n…and {len(files) - 12} more' if len(files) > 12 else ''
        with open(zip_path, 'rb') as zip_file:
            bot.send_document(
                call.message.chat.id, zip_file,
                caption=(f'<b>📥 Data export for</b> <code>{html_escape(file_name)}</code>\n'
                         f'{listing}{more}\n\nUse <b>Import Data</b> on the same bot to restore it.'),
                parse_mode='HTML')
        logger.info("Bot data exported: user=%s script=%s files=%s", owner_id, file_name, len(files))
    except Exception as exc:
        logger.exception('Bot data export failed')
        bot.send_message(call.message.chat.id,
                         f'⚠️ Data export failed: <code>{html_escape(str(exc)[:300])}</code>', parse_mode='HTML')
    finally:
        _rmtree_quiet(tmp_dir)


def import_bot_data_init_callback(call):
    target = _bot_data_target(call, 'bdi')
    if not target:
        return
    owner_id, file_name = target
    if _any_script_running(owner_id):
        bot.answer_callback_query(
            call.id, '⚠️ Stop your running bots first. They share the same data folder, so data cannot be replaced while they run.',
            show_alert=True)
        return
    bot.answer_callback_query(call.id)
    _expire_pending_imports()
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT[call.from_user.id] = {'kind': 'bot', 'owner': owner_id, 'file': file_name, 'time': time.time()}
    bot.send_message(
        call.message.chat.id,
        (f'<b>📤 Import Data for</b> <code>{html_escape(file_name)}</code>\n'
         'Send me the data file you exported earlier (the .zip), or a single data file '
         '(.db, .sqlite, .json, .csv, .txt, .pkl).\n\n'
         '⚠️ Files with the same name in your bot folder will be replaced. I will show you what changes and '
         'ask you to confirm first, and your current data is backed up automatically (and sent to you).\n'
         f'The request expires in {IMPORT_TTL // 60} minutes.'),
        parse_mode='HTML', reply_markup=_cancel_markup())


def _plan_bot_import(upload_path, upload_name, user_folder, payload_dir):
    """Validate the upload and extract it into payload_dir. Returns (list_of_rel_paths, error)."""
    lower = (upload_name or '').lower()
    max_total = MAX_UNZIPPED_MB * 1024 * 1024
    rels = []
    if lower.endswith('.zip'):
        try:
            archive = zipfile.ZipFile(upload_path)
        except zipfile.BadZipFile:
            return None, 'That zip file is damaged or not a zip.'
        with archive:
            items = [i for i in archive.infolist() if not i.is_dir()]
            if not items:
                return None, 'That zip file has no data files in it.'
            if len(items) > MAX_ZIP_FILES:
                return None, f'Too many files in the zip (maximum {MAX_ZIP_FILES}).'
            seen = set()
            for item in items:
                rel = item.filename.replace('\\', '/')
                if not _is_safe_data_rel(rel):
                    return None, (f'The zip contains a file that is not allowed: {rel[:80]}. '
                                  'Only data files (.db, .sqlite, .json, .csv, .txt, .pkl) are accepted.')
                if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                    return None, f'The zip contains a link, which is not allowed: {rel[:80]}.'
                if rel.lower() in seen:
                    return None, f'The zip contains the same file twice: {rel[:80]}.'
                seen.add(rel.lower())
                rels.append((rel, item))
            if sum(max(0, i.file_size) for _r, i in rels) > max_total:
                return None, f'The data is bigger than the {MAX_UNZIPPED_MB} MB limit.'
            written = 0
            root = os.path.realpath(payload_dir)
            for rel, item in rels:
                dest = os.path.realpath(os.path.join(root, rel))
                if not _path_inside(root, dest):
                    return None, 'The zip contains an unsafe path.'
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                with archive.open(item) as src, open(dest, 'wb') as out:
                    while True:
                        chunk = src.read(1024 * 1024)
                        if not chunk:
                            break
                        written += len(chunk)
                        if written > max_total:
                            return None, f'The data is bigger than the {MAX_UNZIPPED_MB} MB limit.'
                        out.write(chunk)
            rels = [rel for rel, _i in rels]
    else:
        base = os.path.basename((upload_name or '').replace('\\', '/'))
        base = re.sub(r'[^A-Za-z0-9_.-]+', '_', base).lstrip('.')
        if not base or os.path.splitext(base)[1].lower() not in DATA_EXTS or base.lower() in DATA_SKIP_NAMES:
            return None, ('Please send the exported .zip, or one data file '
                          '(.db, .sqlite, .json, .csv, .txt, .pkl).')
        existing = [rel for rel, _f, _s in _list_bot_data_files(user_folder) if os.path.basename(rel) == base]
        if len(existing) > 1:
            return None, f'There is more than one "{base}" in your folder. Please send the exported .zip so I know which one.'
        rel = existing[0] if existing else base
        if not _is_safe_data_rel(rel):
            return None, 'That file name is not allowed.'
        dest = os.path.join(payload_dir, rel)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        shutil.copyfile(upload_path, dest)
        rels = [rel]
    # Database files must really be databases, so a bad file cannot break the bot.
    for rel in rels:
        if rel.lower().endswith(DATA_SQLITE_EXTS):
            full = os.path.join(payload_dir, rel)
            try:
                with open(full, 'rb') as handle:
                    if handle.read(16) != SQLITE_MAGIC:
                        return None, f'"{rel}" is not a valid SQLite database.'
                conn = sqlite3.connect(full, timeout=10)
                try:
                    result = conn.execute('PRAGMA integrity_check').fetchone()
                finally:
                    conn.close()
                if not result or result[0] != 'ok':
                    return None, f'"{rel}" is a damaged database.'
            except sqlite3.Error:
                return None, f'"{rel}" could not be read as a database.'
    return rels, ''


def _stage_bot_import(message, pend):
    uid = message.from_user.id
    owner_id, file_name = pend['owner'], pend['file']
    if not _may_manage_bot_data(uid, owner_id) or not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.reply_to(message, '⚠️ You can only import data for your own bots.')
        return
    if _any_script_running(owner_id):
        bot.reply_to(message, '⚠️ Stop your running bots first, then start the import again.')
        return
    doc = message.document
    tmp_dir = tempfile.mkdtemp(prefix=f'demon_botimport_{owner_id}_')
    keep = False
    try:
        try:
            content = _download_upload(message, MAX_UPLOAD_MB)
        except ValueError as exc:
            bot.reply_to(message, f'⚠️ {exc}')
            return
        except Exception as exc:
            logger.warning("Bot data import download failed: %s", redact_secrets(exc))
            bot.reply_to(message, '⚠️ I could not download that file. Please try again.')
            return
        upload_path = os.path.join(tmp_dir, 'upload.bin')
        with open(upload_path, 'wb') as handle:
            handle.write(content)
        payload_dir = os.path.join(tmp_dir, 'payload')
        os.makedirs(payload_dir)
        user_folder = get_user_folder(owner_id)
        rels, problem = _plan_bot_import(upload_path, doc.file_name, user_folder, payload_dir)
        if problem:
            bot.reply_to(message, f'⚠️ {problem} Nothing was changed.')
            return
        existing = {rel for rel, _f, _s in _list_bot_data_files(user_folder)}
        lines = []
        for rel in sorted(rels)[:15]:
            lines.append(f'• <code>{html_escape(rel)}</code> — ' + ('replaces existing' if rel in existing else 'new'))
        more = f'\n…and {len(rels) - 15} more' if len(rels) > 15 else ''
        token = _store_confirm({'kind': 'bot', 'user_id': uid, 'owner': owner_id, 'file': file_name,
                                'dir': tmp_dir, 'payload': payload_dir, 'rels': sorted(rels)})
        keep = True
        bot.reply_to(
            message,
            (f'<b>⚠️ Confirm data import for</b> <code>{html_escape(file_name)}</code>\n'
             + '\n'.join(lines) + more +
             '\n\nExisting files with the same name will be overwritten. Your current data is backed up '
             'automatically first and the backup is sent to you. Continue?'),
            parse_mode='HTML', reply_markup=_confirm_markup(token))
    finally:
        if not keep:
            _rmtree_quiet(tmp_dir)


def _apply_bot_import(entry):
    """Back up what will be overwritten, then write the staged files. Returns (written, backup_path or None)."""
    owner_id = entry['owner']
    user_folder = get_user_folder(owner_id)
    root = os.path.realpath(user_folder)
    if not _path_inside(os.path.realpath(UPLOAD_BOTS_DIR), root) or root == os.path.realpath(UPLOAD_BOTS_DIR):
        raise RuntimeError('Your folder could not be verified.')
    backup_path = None
    overwritten = []
    for rel in entry['rels']:
        dest = os.path.join(root, rel)
        if os.path.isfile(dest) and not os.path.islink(dest) and _path_inside(root, os.path.realpath(dest)):
            overwritten.append(rel)
    if overwritten:
        backup_dir = os.path.join(USER_DATA_BACKUP_DIR, str(owner_id))
        os.makedirs(backup_dir, exist_ok=True)
        stem = re.sub(r'[^A-Za-z0-9_-]+', '_', os.path.splitext(entry['file'])[0])[:40] or 'bot'
        backup_path = os.path.join(backup_dir, f'{stem}_before_import_{_now_stamp()}.zip')
        snap_dir = tempfile.mkdtemp(prefix='demon_botbackup_')
        try:
            with zipfile.ZipFile(backup_path, 'w', zipfile.ZIP_DEFLATED) as archive:
                for index, rel in enumerate(overwritten):
                    full = os.path.join(root, rel)
                    if rel.lower().endswith(DATA_SQLITE_EXTS):
                        snap = os.path.join(snap_dir, f'snap_{index}.tmp')
                        _sqlite_snapshot(full, snap)
                        archive.write(snap, rel)
                    else:
                        archive.write(full, rel)
        finally:
            _rmtree_quiet(snap_dir)
        _prune_backups(backup_dir, f'{stem}_before_import_')
    written = 0
    for rel in entry['rels']:
        src = os.path.join(entry['payload'], rel)
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
        if rel.lower().endswith(DATA_SQLITE_EXTS):
            for suffix in ('-wal', '-shm', '-journal'):   # stale side files would corrupt the restored database
                try:
                    os.remove(dest + suffix)
                except OSError:
                    pass
        written += 1
    return written, backup_path


# --- Shared upload interception and confirmation -----------------------------
def _handle_pending_import_upload(message):
    """Called first by the document handler. True when the document belonged to a waiting import."""
    uid = message.from_user.id
    with IMPORT_LOCK:
        _expire_pending_imports()
        pend = PENDING_IMPORT_WAIT.pop(uid, None)
    if not pend:
        return False
    try:
        if pend['kind'] == 'global':
            _stage_global_import(message)
        else:
            _stage_bot_import(message, pend)
    except Exception:
        logger.exception('Import staging failed')
        bot.reply_to(message, '⚠️ Something went wrong while checking that file. Nothing was changed.')
    return True


def import_confirm_callback(call):
    uid = call.from_user.id
    if call.data == 'impc_cancel':
        with IMPORT_LOCK:
            PENDING_IMPORT_WAIT.pop(uid, None)
        bot.answer_callback_query(call.id, 'Cancelled.')
        _edit_or_send(call, '❌ Import cancelled. Nothing was changed.')
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
            bot.answer_callback_query(call.id, '⚠️ This request expired. Start the import again.', show_alert=True)
            return
        if entry['user_id'] != uid:
            bot.answer_callback_query(call.id, '⚠️ This is not your request.', show_alert=True)
            return
        PENDING_IMPORT_CONFIRM.pop(token, None)      # one use only
    try:
        if action != 'yes':
            bot.answer_callback_query(call.id, 'Cancelled.')
            _edit_or_send(call, '❌ Import cancelled. Nothing was changed.')
            return
        bot.answer_callback_query(call.id, 'Importing...')
        if entry['kind'] == 'global':
            _confirm_global_import(call, entry)
        else:
            _confirm_bot_import(call, entry)
    finally:
        _rmtree_quiet(entry.get('dir'))


def _confirm_global_import(call, entry):
    uid = call.from_user.id
    if not _can_import_global(uid):
        _edit_or_send(call, '⚠️ Only the owner can import the database. Nothing was changed.')
        return
    try:
        backup_path, missing = _apply_global_import(entry['path'])
    except Exception as exc:
        logger.exception('Database import failed')
        _edit_or_send(call, ('❌ Import failed, the live database was not replaced.\n'
                             f'<code>{html_escape(str(exc)[:300])}</code>'))
        return
    logger.warning("Hosting database replaced by import (admin %s); backup at %s", uid, backup_path)
    text = ('✅ <b>Database imported.</b>\n'
            f'Now live: {len(active_users)} users, {sum(len(v) for v in user_files.values())} scripts, '
            f'{len(user_subscriptions)} subscriptions, {len(admin_ids)} admins.\n'
            'The previous database was backed up automatically and is attached below.')
    if missing:
        text += (f'\n\nNote: {missing} script(s) in the restored list are not on disk in this server\'s upload folder. '
                 'The database brings back records, not the script files themselves.')
    _edit_or_send(call, text)
    try:
        with open(backup_path, 'rb') as backup_file:
            bot.send_document(call.message.chat.id, backup_file,
                              caption='Backup of the database as it was before this import.')
    except Exception:
        logger.exception('Could not send the pre-import backup')


def _confirm_bot_import(call, entry):
    uid = call.from_user.id
    owner_id, file_name = entry['owner'], entry['file']
    if not _may_manage_bot_data(uid, owner_id) or not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        _edit_or_send(call, '⚠️ You can only import data for your own bots. Nothing was changed.')
        return
    if _any_script_running(owner_id):
        _edit_or_send(call, '⚠️ One of your bots is running. Stop your bots and start the import again. Nothing was changed.')
        return
    try:
        written, backup_path = _apply_bot_import(entry)
    except Exception as exc:
        logger.exception('Bot data import failed')
        _edit_or_send(call, ('❌ Import failed. Some files may not have been replaced; your previous data '
                             'is in the backup if one was made.\n'
                             f'<code>{html_escape(str(exc)[:300])}</code>'))
        return
    logger.info("Bot data imported: user=%s script=%s files=%s", owner_id, file_name, written)
    _edit_or_send(call, (f'✅ <b>Data imported</b> for <code>{html_escape(file_name)}</code>: '
                         f'{written} file(s) restored.\nStart your bot again to use it.'
                         + ('\nYour previous data was backed up and is attached below.' if backup_path else '')))
    if backup_path:
        try:
            with open(backup_path, 'rb') as backup_file:
                bot.send_document(call.message.chat.id, backup_file,
                                  caption='Backup of your data as it was before this import.')
        except Exception:
            logger.exception('Could not send the pre-import data backup')


def create_control_buttons(script_owner_id, file_name, is_running=True):
    markup = types.InlineKeyboardMarkup(row_width=2)
    if is_running:
        markup.row(
            types.InlineKeyboardButton("🔴 Stop", callback_data=f'stop_{script_owner_id}_{file_name}'),
            types.InlineKeyboardButton("🔄 Restart", callback_data=f'restart_{script_owner_id}_{file_name}')
        )
        markup.row(
            types.InlineKeyboardButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}'),
            types.InlineKeyboardButton("📜 Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    else:
        markup.row(
            types.InlineKeyboardButton("🟢 Start", callback_data=f'start_{script_owner_id}_{file_name}'),
            types.InlineKeyboardButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}')
        )
        markup.row(
            types.InlineKeyboardButton("📜 View Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    markup.row(
        types.InlineKeyboardButton("📥 Export Data", callback_data=f'bdx_{script_owner_id}_{file_name}'),
        types.InlineKeyboardButton("📤 Import Data", callback_data=f'bdi_{script_owner_id}_{file_name}')
    )
    markup.add(types.InlineKeyboardButton("🔙 Back to Files", callback_data='check_files'))
    return markup

def create_admin_panel():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('➕ Add Admin', callback_data='add_admin'),
        types.InlineKeyboardButton('➖ Remove Admin', callback_data='remove_admin')
    )
    markup.row(types.InlineKeyboardButton('📋 List Admins', callback_data='list_admins'))
    markup.row(types.InlineKeyboardButton('🗄 Database Backup', callback_data='database_backup'),
               types.InlineKeyboardButton('📤 Export Users', callback_data='export_users'))
    markup.row(types.InlineKeyboardButton('📥 Export Database', callback_data='export_database'),
               types.InlineKeyboardButton('📤 Import Database', callback_data='import_database'))
    markup.row(types.InlineKeyboardButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_user_management_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('🚫 Ban User', callback_data='ban_user'),
        types.InlineKeyboardButton('✅ Unban User', callback_data='unban_user')
    )
    markup.row(
        types.InlineKeyboardButton('📊 User Info', callback_data='user_info'),
        types.InlineKeyboardButton('👥 All Users', callback_data='all_users')
    )
    markup.row(
        types.InlineKeyboardButton('🔧 Set User Limit', callback_data='set_user_limit'),
        types.InlineKeyboardButton('🗑️ Remove User Limit', callback_data='remove_user_limit')
    )
    markup.row(types.InlineKeyboardButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('➕ Add Subscription', callback_data='add_subscription'),
        types.InlineKeyboardButton('➖ Remove Subscription', callback_data='remove_subscription')
    )
    markup.row(types.InlineKeyboardButton('🔍 Check Subscription', callback_data='check_subscription'))
    markup.row(types.InlineKeyboardButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_admin_settings_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        types.InlineKeyboardButton('📊 System Info', callback_data='system_info'),
        types.InlineKeyboardButton('📈 Bot Performance', callback_data='bot_performance')
    )
    markup.row(
        types.InlineKeyboardButton('🧹 Cleanup Files', callback_data='cleanup_files'),
        types.InlineKeyboardButton('📋 Installation Logs', callback_data='install_logs')
    )
    markup.row(
        types.InlineKeyboardButton('🩺 Hosting Health', callback_data='hosting_health'),
        types.InlineKeyboardButton('🔄 Retry Failed Bots', callback_data='retry_failed_bots')
    )
    markup.row(types.InlineKeyboardButton('👑 Admin Dashboard', callback_data='admin_dashboard'))
    markup.row(types.InlineKeyboardButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

# --- File Handling ---
def _expire_pending_zips():
    """Drop zip files that have waited too long for admin review (keeps memory bounded). Caller holds STATE_LOCK."""
    now = time.time()
    for key, stored_at in list(pending_zip_times.items()):
        if now - stored_at > PENDING_ZIP_TTL:
            uid, fname = key
            pending_zip_times.pop(key, None)
            pending_zip_files.get(uid, {}).pop(fname, None)
            if uid in pending_zip_files and not pending_zip_files[uid]:
                del pending_zip_files[uid]


def handle_zip_file(downloaded_file_content, file_name_zip, message):
    user_id = message.from_user.id
    user_folder = get_user_folder(user_id)
    temp_dir = None 
    try:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_")
        logger.info(f"Temp dir for zip: {temp_dir}")
        zip_path = os.path.join(temp_dir, file_name_zip)
        with open(zip_path, 'wb') as new_file: new_file.write(downloaded_file_content)
        
        # Security check for ZIP
        is_safe, security_msg = scan_zip_security(zip_path)
        if not is_safe:
            # Send security warning to admin for approval
            security_warning_msg = f"🚨 File needs approval:\n👤 User: {user_id}\n📁 File: {file_name_zip}\n⚠️ Reason: {security_msg}"
            markup = types.InlineKeyboardMarkup()
            markup.row(
                types.InlineKeyboardButton("✅ Approve", callback_data=f"approve_zip_{user_id}_{file_name_zip}"),
                types.InlineKeyboardButton("❌ Reject", callback_data=f"reject_zip_{user_id}_{file_name_zip}")
            )
            for admin_id in admin_ids:
                try:
                    bot.send_message(admin_id, security_warning_msg, reply_markup=markup)
                except Exception as e:
                    logger.error(f"Failed to send security warning to admin {admin_id}: {e}")
            
            # Store the file content for later approval
            with STATE_LOCK:
                _expire_pending_zips()
                if sum(len(v) for v in pending_zip_files.values()) >= PENDING_ZIP_MAX_TOTAL:
                    bot.reply_to(message, "⚠️ Too many files are waiting for review right now. Please try again later.")
                    return
                pending_zip_files.setdefault(user_id, {})[file_name_zip] = downloaded_file_content
                pending_zip_times[(user_id, file_name_zip)] = time.time()
            
            bot.reply_to(message, f"⏳ File under security review. You will be notified upon approval.")
            return

        # Process ZIP file if safe
        process_zip_file(zip_path, user_id, user_folder, file_name_zip, message, temp_dir)
        
    except zipfile.BadZipFile as e:
        logger.error(f"Bad zip file from {user_id}: {e}")
        bot.reply_to(message, f"❌ Error: Invalid/corrupted ZIP. {e}")
    except Exception as e:
        logger.error(f"❌ Error processing zip for {user_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error processing zip: {str(e)}")
    finally:
        if temp_dir and os.path.exists(temp_dir):
            try: shutil.rmtree(temp_dir); logger.info(f"Cleaned temp dir: {temp_dir}")
            except Exception as e: logger.error(f"Failed to clean temp dir {temp_dir}: {e}", exc_info=True)

def process_zip_file(zip_path, user_id, user_folder, file_name_zip, message, temp_dir=None):
    """Process ZIP file extraction and setup"""
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

        extracted_items = os.listdir(extract_dir)
        py_files = [f for f in extracted_items if f.endswith('.py')]
        js_files = [f for f in extracted_items if f.endswith('.js')]
        req_file = 'requirements.txt' if 'requirements.txt' in extracted_items else None
        pkg_json = 'package.json' if 'package.json' in extracted_items else None

        if req_file:
            req_path = os.path.join(extract_dir, req_file)
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
                bot.reply_to(message, error_msg, parse_mode='Markdown'); return
            except subprocess.TimeoutExpired:
                logger.error(f"pip install -r timed out for user {user_id}")
                bot.reply_to(message, f"❌ Installing the Python deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return
            except Exception as e:
                 error_msg = f"❌ Unexpected error installing Python deps: {e}"
                 logger.error(error_msg, exc_info=True); bot.reply_to(message, error_msg); return

        if pkg_json:
            logger.info(f"package.json found, npm install in: {extract_dir}")
            bot.reply_to(message, f"🔄 Installing Node deps from `{pkg_json}`...")
            try:
                command = ['npm', 'install']
                result = subprocess.run(command, capture_output=True, text=True, check=True, cwd=extract_dir, encoding='utf-8', errors='ignore',
                                        timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=child_env())
                logger.info(f"npm install OK. Output:\n{result.stdout}")
                bot.reply_to(message, f"✅ Node deps from `{pkg_json}` installed.")
            except FileNotFoundError:
                bot.reply_to(message, "❌ 'npm' not found. Cannot install Node deps."); return 
            except subprocess.CalledProcessError as e:
                log_tail = _short_code_block((e.stderr or e.stdout or '')[-2500:], 2500)
                error_msg = f"❌ Failed to install Node deps from `{pkg_json}`.\nLog:\n```\n{log_tail}\n```"
                logger.error(error_msg)
                bot.reply_to(message, error_msg, parse_mode='Markdown'); return
            except subprocess.TimeoutExpired:
                logger.error(f"npm install timed out for user {user_id}")
                bot.reply_to(message, f"❌ Installing the Node deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return
            except Exception as e:
                 error_msg = f"❌ Unexpected error installing Node deps: {e}"
                 logger.error(error_msg, exc_info=True); bot.reply_to(message, error_msg); return

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
        logger.info(f"Saved main script '{main_script_name}' ({file_type}) for {user_id} from zip.")
        main_script_path = os.path.join(user_folder, main_script_name)
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

def _prepare_log_file(log_file_path):
    """Open a script log for appending; start a fresh file if the old one is already too big."""
    try:
        if os.path.exists(log_file_path) and os.path.getsize(log_file_path) > MAX_SCRIPT_LOG_MB * 1024 * 1024:
            os.replace(log_file_path, log_file_path + '.old')
    except OSError as exc:
        logger.warning(f"Could not rotate log {log_file_path}: {exc}")
    return open(log_file_path, 'a', encoding='utf-8', errors='ignore')


def _popen_kwargs():
    """Extra Popen arguments: own process group on POSIX (so children can be stopped too) and a clean environment."""
    kwargs = {'env': child_env()}
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
        threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, message)).start()
    except Exception as e:
        logger.error(f"❌ Error processing JS file {file_name} for {script_owner_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error processing JS file: {str(e)}")

def handle_py_file(file_path, script_owner_id, user_folder, file_name, message):
    try:
        save_user_file(script_owner_id, file_name, 'py')
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
            check_command = [sys.executable, script_path]
            logger.info(f"Running Python pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **_popen_kwargs())
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
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **_popen_kwargs()
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
            check_command = ['node', script_path]
            logger.info(f"Running JS pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **_popen_kwargs())
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
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **_popen_kwargs()
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
        # ReplyKeyboardMarkup and InlineKeyboardMarkup cannot be attached to the
        # same Telegram message, so send the persistent keyboard with the
        # welcome message and the inline quick-actions panel as a second message.
        bot.send_message(
            chat_id, welcome_msg_text,
            reply_markup=create_reply_main_menu(user_id), parse_mode='HTML'
        )
        bot.send_message(
            chat_id, '<b>⚡ QUICK ACTIONS</b>\nSelect an action below:',
            reply_markup=create_main_menu_inline(user_id), parse_mode='HTML'
        )
    except Exception as e:
        logger.error(f"Error sending welcome to {user_id}: {e}", exc_info=True)

def _logic_updates_channel(message):
    markup = types.InlineKeyboardMarkup()
    markup.add(types.InlineKeyboardButton('📢 Updates Channel', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'))
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
        bot.reply_to(message, f"⚠️ File limit ({current_files}/{limit_str}) reached. Delete files first.")
        return
    bot.reply_to(message, "📤 Send your Python (`.py`), JS (`.js`), or ZIP (`.zip`) file.")

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
        
    user_files_list = user_files.get(user_id, [])
    if not user_files_list:
        bot.reply_to(message, "📂 Your files:\n\n(No files uploaded yet)")
        return
    markup = types.InlineKeyboardMarkup(row_width=1)
    for file_name, file_type in sorted(user_files_list):
        is_running = is_bot_running(user_id, file_name) # Use user_id for checking status
        status_icon = "🟢 Running" if is_running else "🔴 Stopped"
        btn_text = f"{file_name} ({file_type}) - {status_icon}"
        # Callback data includes user_id as script_owner_id
        markup.add(types.InlineKeyboardButton(btn_text, callback_data=f'file_{user_id}_{file_name}'))
    bot.reply_to(message, "📂 Your files:\nClick to manage.", reply_markup=markup, parse_mode='Markdown')

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
    markup = types.InlineKeyboardMarkup()
    markup.add(types.InlineKeyboardButton('📞 Contact Owner', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
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
    kb = create_main_menu_inline(message.from_user.id)
    bot.send_message(message.chat.id, '<b>👤 Account Center</b>\nOpen your account overview from the button below.', parse_mode='HTML', reply_markup=types.InlineKeyboardMarkup().add(types.InlineKeyboardButton('👤 My Account', callback_data='user_account')))

@bot.message_handler(commands=['mybots'])
def command_mybots(message):
    bot.send_message(message.chat.id, '<b>🤖 Your running scripts</b>', parse_mode='HTML', reply_markup=types.InlineKeyboardMarkup().add(types.InlineKeyboardButton('Open Running Scripts', callback_data='my_running')))

@bot.message_handler(commands=['admindashboard'])
def command_admindashboard(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, 'Admin permissions required.'); return
    bot.send_message(message.chat.id, '<b>👑 Admin Control Center</b>', parse_mode='HTML', reply_markup=types.InlineKeyboardMarkup().add(types.InlineKeyboardButton('Open Dashboard', callback_data='admin_dashboard')))

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
    "👤 Account": lambda message: bot.send_message(
        message.chat.id, '<b>👤 Account Center</b>', parse_mode='HTML',
        reply_markup=types.InlineKeyboardMarkup().add(
            types.InlineKeyboardButton('👤 My Account', callback_data='user_account')
        )
    ),
    "🤖 My Bots": lambda message: bot.send_message(
        message.chat.id, '<b>🤖 Your running scripts</b>', parse_mode='HTML',
        reply_markup=types.InlineKeyboardMarkup().add(
            types.InlineKeyboardButton('Open Running Scripts', callback_data='my_running')
        )
    ),
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
        bot.reply_to(message, f"⚠️ File limit ({current_files}/{limit_str}) reached. Delete files via /checkfiles.")
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

        if file_ext == '.zip':
            handle_zip_file(downloaded_file_content, file_name, message)
        else:
            file_path = os.path.join(user_folder, file_name)
            with open(file_path, 'wb') as f: f.write(downloaded_file_content)
            logger.info(f"Saved single file to {file_path}")
            
            # Security check for script files (lightweight)
            is_safe, security_msg = check_code_security(file_path, file_ext[1:])
            if not is_safe:
                # Send security warning to admin for approval
                security_warning_msg = f"🚨 File needs approval:\n👤 User: {user_id}\n📁 File: {file_name}\n⚠️ Reason: {security_msg}"
                markup = types.InlineKeyboardMarkup()
                markup.row(
                    types.InlineKeyboardButton("✅ Approve", callback_data=f"approve_file_{user_id}_{file_name}"),
                    types.InlineKeyboardButton("❌ Reject", callback_data=f"reject_file_{user_id}_{file_name}")
                )
                for admin_id in admin_ids:
                    try:
                        bot.send_message(admin_id, security_warning_msg, reply_markup=markup)
                    except Exception as e:
                        logger.error(f"Failed to send security warning to admin {admin_id}: {e}")
                
                bot.reply_to(message, f"⏳ File under security review. You will be notified upon approval.")
                return
                
            # Pass user_id as script_owner_id
            if file_ext == '.js': handle_js_file(file_path, user_id, user_folder, file_name, message)
            elif file_ext == '.py': handle_py_file(file_path, user_id, user_folder, file_name, message)
    except telebot.apihelper.ApiTelegramException as e:
         logger.error(f"Telegram API Error handling file for {user_id}: {e}", exc_info=True)
         if "file is too big" in str(e).lower():
              bot.reply_to(message, f"❌ Telegram API Error: File too large to download (~20MB limit).")
         else: bot.reply_to(message, f"❌ Telegram API Error: {str(e)}. Try later.")
    except Exception as e:
        logger.error(f"❌ General error handling file for {user_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Unexpected error: {str(e)}")

# --- Callback Query Handlers (for Inline Buttons) ---
@bot.callback_query_handler(func=lambda call: True) 
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
        elif data == 'check_files': check_files_callback(call)
        elif data.startswith('file_'): file_control_callback(call)
        elif data.startswith('start_'): start_bot_callback(call)
        elif data.startswith('stop_'): stop_bot_callback(call)
        elif data.startswith('restart_'): restart_bot_callback(call)
        elif data.startswith('delete_'): delete_bot_callback(call)
        elif data.startswith('logs_'): logs_bot_callback(call)
        elif data == 'speed': speed_callback(call)
        elif data == 'user_account': user_account_callback(call)
        elif data == 'my_running': my_running_callback(call)
        elif data == 'user_help': user_help_callback(call)
        elif data == 'admin_dashboard': admin_required_callback(call, admin_dashboard_callback)
        elif data == 'database_backup': admin_required_callback(call, database_backup_callback)
        elif data == 'export_users': admin_required_callback(call, export_users_callback)
        elif data == 'export_database': admin_required_callback(call, export_database_callback)
        elif data == 'import_database': admin_required_callback(call, import_database_callback)
        elif data.startswith('impc_'): import_confirm_callback(call)
        elif data.startswith('bdx_'): export_bot_data_callback(call)
        elif data.startswith('bdi_'): import_bot_data_init_callback(call)
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
        # --- Security Approval Callbacks ---
        elif data.startswith('approve_file_'): admin_required_callback(call, process_approve_file)
        elif data.startswith('reject_file_'): admin_required_callback(call, process_reject_file)
        elif data.startswith('approve_zip_'): admin_required_callback(call, process_approve_zip)
        elif data.startswith('reject_zip_'): admin_required_callback(call, process_reject_zip)
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
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(types.InlineKeyboardButton('📂 Manage Files', callback_data='check_files'),
           types.InlineKeyboardButton('🤖 Running Bots', callback_data='my_running'))
    kb.add(types.InlineKeyboardButton('🏠 Main Menu', callback_data='back_to_main'))
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
    kb = types.InlineKeyboardMarkup(row_width=1)
    if rows:
        for name, key in rows[:40]:
            owner_part, file_part = key.split('_', 1)
            kb.add(types.InlineKeyboardButton(f'🟢 {name}', callback_data=f'file_{owner_part}_{file_part}'))
        body = f"<b>🤖 YOUR RUNNING SCRIPTS</b>\n━━━━━━━━━━━━━━━━━━\n🟢 Active processes: <b>{len(rows)}</b>\n\nSelect a script to open its controls."
    else:
        body = "<b>🤖 YOUR RUNNING SCRIPTS</b>\n━━━━━━━━━━━━━━━━━━\nNo scripts are running right now.\n\nUpload a script or start one from My Files."
    kb.add(types.InlineKeyboardButton('📂 My Files', callback_data='check_files'))
    kb.add(types.InlineKeyboardButton('🏠 Main Menu', callback_data='back_to_main'))
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
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(types.InlineKeyboardButton('📂 My Files', callback_data='check_files'),
           types.InlineKeyboardButton('📞 Contact Support', url='https://t.me/' + YOUR_USERNAME.replace('@', '')))
    kb.add(types.InlineKeyboardButton('🏠 Main Menu', callback_data='back_to_main'))
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
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(types.InlineKeyboardButton('🩺 Hosting Health', callback_data='hosting_health'),
           types.InlineKeyboardButton('👥 Users', callback_data='user_management'))
    kb.row(types.InlineKeyboardButton('📢 Broadcast', callback_data='broadcast'),
           types.InlineKeyboardButton('💳 Subscriptions', callback_data='subscription'))
    kb.row(types.InlineKeyboardButton('🗄 Database Backup', callback_data='database_backup'),
           types.InlineKeyboardButton('📤 Export Users', callback_data='export_users'))
    kb.row(types.InlineKeyboardButton('📥 Export Database', callback_data='export_database'),
           types.InlineKeyboardButton('📤 Import Database', callback_data='import_database'))
    kb.row(types.InlineKeyboardButton('⚙️ Settings', callback_data='admin_settings'),
           types.InlineKeyboardButton('👑 Admins', callback_data='admin_panel'))
    kb.add(types.InlineKeyboardButton('🏠 Main Menu', callback_data='back_to_main'))
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
    user_id = call.from_user.id
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
        bot.answer_callback_query(call.id, f"⚠️ File limit ({current_files}/{limit_str}) reached.", show_alert=True)
        return
    bot.answer_callback_query(call.id) 
    bot.send_message(call.message.chat.id, "📤 Send your Python (`.py`), JS (`.js`), or ZIP (`.zip`) file.")

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
        
    chat_id = call.message.chat.id 
    user_files_list = user_files.get(user_id, [])
    if not user_files_list:
        bot.answer_callback_query(call.id, "⚠️ No files uploaded.", show_alert=True)
        try:
            markup = types.InlineKeyboardMarkup()
            markup.add(types.InlineKeyboardButton("🔙 Back to Main", callback_data='back_to_main'))
            bot.edit_message_text("📂 Your files:\n\n(No files uploaded)", chat_id, call.message.message_id, reply_markup=markup)
        except Exception as e: logger.error(f"Error editing msg for empty file list: {e}")
        return
    bot.answer_callback_query(call.id) 
    markup = types.InlineKeyboardMarkup(row_width=1) 
    for file_name, file_type in sorted(user_files_list): 
        is_running = is_bot_running(user_id, file_name) # Use user_id for status check
        status_icon = "🟢 Running" if is_running else "🔴 Stopped"
        btn_text = f"{file_name} ({file_type}) - {status_icon}"
        # Callback includes user_id as script_owner_id
        markup.add(types.InlineKeyboardButton(btn_text, callback_data=f'file_{user_id}_{file_name}'))
    markup.add(types.InlineKeyboardButton("🔙 Back to Main", callback_data='back_to_main'))
    try:
        bot.edit_message_text("📂 Your files:\nClick to manage.", chat_id, call.message.message_id, reply_markup=markup, parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
         if "message is not modified" in str(e): logger.warning("Msg not modified (files).")
         else: logger.error(f"Error editing msg for file list: {e}")
    except Exception as e: logger.error(f"Unexpected error editing msg for file list: {e}", exc_info=True)

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
            bot.edit_message_text(
                f"⚙️ Controls for: `{file_name}` ({file_type}) of User `{script_owner_id}`\nStatus: {status_text}",
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
        RESTART_STATE[_script_key(script_owner_id, file_name)] = {"attempts": 0, "manual_stop": False}

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

        bot.answer_callback_query(call.id, f"⏳ Restarting {file_name} for user {script_owner_id}...")
        if is_bot_running(script_owner_id, file_name):
            logger.info(f"Restart: Stopping existing {script_key}...")
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            _forget_script(script_key)
            time.sleep(1.5) 

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
        deleted_disk = []
        if os.path.exists(file_path):
            try: os.remove(file_path); deleted_disk.append(file_name); logger.info(f"Deleted file: {file_path}")
            except OSError as e: logger.error(f"Error deleting {file_path}: {e}")
        if os.path.exists(log_path):
            try: os.remove(log_path); deleted_disk.append(os.path.basename(log_path)); logger.info(f"Deleted log: {log_path}")
            except OSError as e: logger.error(f"Error deleting log {log_path}: {e}")

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
        # Restore the persistent reply keyboard when returning from inline panels.
        bot.send_message(
            chat_id, "⌨️ Reply keyboard is ready below.",
            reply_markup=create_reply_main_menu(user_id)
        )
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
    markup = types.InlineKeyboardMarkup()
    markup.row(types.InlineKeyboardButton("✅ Confirm & Send", callback_data=f"confirm_broadcast_{message.message_id}"),
               types.InlineKeyboardButton("❌ Cancel", callback_data="cancel_broadcast"))

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
        
        users_list = list(active_users)
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
    
    markup = types.InlineKeyboardMarkup(row_width=3)
    
    if total_pages > 1:
        page_buttons = []
        if page > 0:
            page_buttons.append(types.InlineKeyboardButton("⬅️ Previous", callback_data=f"users_page_{page-1}"))
        
        page_buttons.append(types.InlineKeyboardButton(f"{page+1}/{total_pages}", callback_data="noop"))
        
        if page < total_pages - 1:
            page_buttons.append(types.InlineKeyboardButton("Next ➡️", callback_data=f"users_page_{page+1}"))
        
        markup.row(*page_buttons)
    
    markup.row(types.InlineKeyboardButton("🔙 Back to User Management", callback_data='user_management'))
    
    try:
        bot.edit_message_text(message_text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error editing users list: {e}")

@bot.callback_query_handler(func=lambda call: call.data.startswith('users_page_'))
def handle_users_page(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True)
        return
    
    try:
        page = int(call.data.split('_')[2])
        users_list = list(active_users)
        chunk_size = 20
        total_pages = (len(users_list) + chunk_size - 1) // chunk_size
        
        if 0 <= page < total_pages:
            bot.answer_callback_query(call.id)
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
            
            performance_parts.append(f"\n💾 **Resource Usage:**")
            performance_parts.append(f"• Memory: {memory_usage:.1f} MB")
            performance_parts.append(f"• CPU: {cpu_usage:.1f}%")
        except Exception as e:
            performance_parts.append(f"\n⚠️ Resource stats error: {str(e)}")
        
        # Database stats
        performance_parts.append(f"\n🗄️ **Database:**")
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
    
    markup = types.InlineKeyboardMarkup()
    for channel_id, channel_info in list(mandatory_channels.items()):
        channel_name = channel_info.get('name', 'Unknown')
        button_text = f"🗑️ {channel_name}"
        markup.add(types.InlineKeyboardButton(button_text, callback_data=f'remove_channel_{channel_id}'))
    
    markup.add(types.InlineKeyboardButton("🔙 Back", callback_data='manage_mandatory_channels'))
    
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
