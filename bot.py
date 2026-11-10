# -*- coding: utf-8 -*-
import telebot
import subprocess
import os
import zipfile
import tempfile
import shutil
from telebot import types


def make_colored_button(*args, **kwargs):
    """Create an inline button with Telegram's supported color style when available.

    Telegram supports button styles only for inline keyboard buttons on Bot API versions
    that implement the `style` field. Reply-keyboard buttons cannot be colored by bots.
    """
    label = str(kwargs.get("text", args[0] if args else "")).lower()
    action = str(kwargs.get("callback_data", "")).lower()
    combined = f"{label} {action}"
    danger_terms = (
        "delete", "remove", "ban", "block", "lock", "stop", "cancel",
        "reject", "deny", "clear", "reset", "terminate", "kick", "🗑", "🔴", "❌"
    )
    success_terms = (
        "start", "run", "upload", "add", "approve", "confirm", "verify",
        "join", "unlock", "enable", "save", "yes", "✅", "🟢", "➕"
    )
    if any(term in combined for term in danger_terms):
        style = "danger"
    elif any(term in combined for term in success_terms):
        style = "success"
    else:
        style = "primary"

    # Prefer the library's native support; fall back for older pyTelegramBotAPI versions.
    try:
        button = types.InlineKeyboardButton(*args, style=style, **kwargs)
    except TypeError:
        button = types.InlineKeyboardButton(*args, **kwargs)
        try:
            button.style = style
        except Exception:
            pass
    return button
import time
from datetime import datetime, timedelta
import logging
import psutil
import sqlite3
import threading
import re
import sys
import atexit
import requests

# --- Flask Keep Alive ---
import socket as _socket
from flask import Flask
from threading import Thread

app = Flask('')

# Silence Werkzeug's startup/request logs
import logging as _logging
_logging.getLogger('werkzeug').setLevel(_logging.ERROR)

@app.route('/')
def home():
    return "I'm Astroneth Hosting"

def _is_port_free(port):
    """Return True if the port is available to bind."""
    with _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM) as s:
        s.setsockopt(_socket.SOL_SOCKET, _socket.SO_REUSEADDR, 1)
        try:
            s.bind(('0.0.0.0', port))
            return True
        except OSError:
            return False

def run_flask():
    base_port = int(os.environ.get("PORT", 8080))
    candidates = [base_port] + [p for p in range(8081, 8096) if p != base_port]
    for port in candidates:
        if _is_port_free(port):
            try:
                logger.info(f"Flask Keep-Alive starting on port {port}")
                app.run(host='0.0.0.0', port=port, use_reloader=False)
                break
            except Exception as e:
                logger.warning(f"Flask: failed on port {port}: {e}")
        else:
            logger.warning(f"Flask: port {port} in use, skipping...")
    else:
        logger.warning("Flask Keep-Alive: no free port found. Bot will run without keep-alive.")

def keep_alive():
    t = Thread(target=run_flask)
    t.daemon = True
    t.start()
    logger.info("Flask Keep-Alive server started.")
# --- End Flask Keep Alive ---

# --- Configuration ---
TOKEN = os.environ.get('BOT_TOKEN', '9017009642:AAFp-m_9eibWd_KGJzIxiCnAGFE8JYgnwqs')
OWNER_ID = int(os.environ.get('OWNER_ID', '8597878282'))
ADMIN_ID = int(os.environ.get('ADMIN_ID', '8597878282'))
YOUR_USERNAME = os.environ.get('YOUR_USERNAME', '@U_BOTS_u')
UPDATES_CHANNEL = os.environ.get('UPDATES_CHANNEL', '@U_BOT_CHANNEL')

# Folder setup
BASE_DIR = os.path.abspath(os.path.dirname(__file__))
IROTECH_DIR = os.path.join(BASE_DIR, 'inf')
UPLOAD_BOTS_DIR = os.path.join(IROTECH_DIR, 'uploadu_bots')
DATABASE_PATH = os.path.join(IROTECH_DIR, 'botu_data.db')
PENDING_ZIPS_DIR = os.path.join(IROTECH_DIR, 'pendingu_zips')  # persisted zip files awaiting approval

# File upload limits
FREE_USER_LIMIT = 6
SUBSCRIBED_USER_LIMIT = 15
ADMIN_LIMIT = 99999
OWNER_LIMIT = float('inf')


os.makedirs(UPLOAD_BOTS_DIR, exist_ok=True)
os.makedirs(IROTECH_DIR, exist_ok=True)
os.makedirs(PENDING_ZIPS_DIR, exist_ok=True)

bot = telebot.TeleBot(TOKEN)
BOT_START_TIME = time.time()

# --- Data structures ---
bot_scripts = {}
user_subscriptions = {}
user_files = {}
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
banned_users = set()
user_limits = {}
pending_zip_files = {}
pending_script_files = {}  # {user_id: {file_name: {'path', 'type', 'is_safe', 'security_msg', 'chat_id'}}}
pending_modules = {}         # {user_id: {module_name: package_name}}
# Holds in-progress upload state while asking user for project name / main file
# {user_id: {'file_content': bytes, 'file_name': str, 'file_ext': str, 'project_name': str|None}}
pending_file_uploads = {}
bot_locked = False
force_join_channels = []  # list of channels users must join before using the bot

# --- Logging Setup ---
logging.basicConfig(level=logging.INFO,
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# --- Command Button Layouts ---
COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["📦 Manual Install", "👤 My Info"],
    ["📞 Contact Owner"]
]
ADMIN_COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["💳 Subscriptions", "📢 Broadcast"],
    ["🔒 Lock Bot", "🟢 Run All Code"],
    ["👥 User Management", "📋 Pending Files"],
    ["👑 Admin Panel", "🛠️ Manual Install"],
    ["📢 Channel Add", "👤 My Info"],
    ["📞 Contact Owner"]
]

# ============================================================
# --- Database Setup ---
# ============================================================
def init_db():
    logger.info(f"Initializing database at: {DATABASE_PATH}")
    try:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS subscriptions
                     (user_id INTEGER PRIMARY KEY, expiry TEXT)''')
        # New schema: project_name is the unique key per user, main_file is the entry point
        c.execute('''CREATE TABLE IF NOT EXISTS user_files
                     (user_id INTEGER, project_name TEXT, main_file TEXT, file_type TEXT,
                      PRIMARY KEY (user_id, project_name))''')
        # Migrate old schema: if main_file column is missing, add it and rename file_name → project_name
        try:
            c.execute('SELECT main_file FROM user_files LIMIT 1')
        except Exception:
            try:
                c.execute('ALTER TABLE user_files ADD COLUMN main_file TEXT')
                c.execute('UPDATE user_files SET main_file = file_name WHERE main_file IS NULL')
                conn.commit()
            except Exception as mig_e:
                logger.warning(f"Migration attempt: {mig_e}")
        c.execute('''CREATE TABLE IF NOT EXISTS active_users
                     (user_id INTEGER PRIMARY KEY, join_date TEXT, last_seen TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS admins
                     (user_id INTEGER PRIMARY KEY)''')
        c.execute('''CREATE TABLE IF NOT EXISTS banned_users
                     (user_id INTEGER PRIMARY KEY, reason TEXT, banned_by INTEGER, ban_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_limits
                     (user_id INTEGER PRIMARY KEY, file_limit INTEGER, set_by INTEGER, set_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS install_logs
                     (id INTEGER PRIMARY KEY AUTOINCREMENT,
                      user_id INTEGER,
                      module_name TEXT,
                      package_name TEXT,
                      status TEXT,
                      log TEXT,
                      install_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS settings
                     (key TEXT PRIMARY KEY, value TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS force_join_channels
                     (channel TEXT PRIMARY KEY, title TEXT, invite_link TEXT, added_by INTEGER, added_at TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS pending_scripts
                     (user_id INTEGER, project_name TEXT, file_path TEXT, file_type TEXT,
                      is_safe INTEGER, security_msg TEXT, chat_id INTEGER, main_file TEXT,
                      queued_at TEXT,
                      PRIMARY KEY (user_id, project_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS pending_zips
                     (user_id INTEGER, project_name TEXT, zip_path TEXT, file_name_zip TEXT,
                      main_file TEXT, patterns TEXT, queued_at TEXT,
                      PRIMARY KEY (user_id, project_name))''')
        c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (OWNER_ID,))
        if ADMIN_ID != OWNER_ID:
            c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (ADMIN_ID,))
        conn.commit()
        conn.close()
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.error(f"❌ Database initialization error: {e}", exc_info=True)

def load_data():
    logger.info("Loading data from database...")
    try:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        c.execute('SELECT user_id, expiry FROM subscriptions')
        for user_id, expiry in c.fetchall():
            try:
                user_subscriptions[user_id] = {'expiry': datetime.fromisoformat(expiry)}
            except ValueError:
                logger.warning(f"⚠️ Invalid expiry for user {user_id}: {expiry}. Skipping.")
        c.execute('SELECT user_id, project_name, main_file, file_type FROM user_files')
        for user_id, project_name, main_file, file_type in c.fetchall():
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((project_name, main_file or project_name, file_type))
        c.execute('SELECT user_id FROM active_users')
        active_users.update(user_id for (user_id,) in c.fetchall())
        c.execute('SELECT user_id FROM admins')
        admin_ids.update(user_id for (user_id,) in c.fetchall())
        # Load banned users
        try:
            c.execute('SELECT user_id FROM banned_users')
            banned_users.update(user_id for (user_id,) in c.fetchall())
        except Exception: pass
        # Load user limits
        try:
            c.execute('SELECT user_id, file_limit FROM user_limits')
            for user_id, file_limit in c.fetchall():
                user_limits[user_id] = file_limit
        except Exception: pass
        # Load force join channels list
        try:
            global force_join_channels
            c.execute("SELECT channel, title, invite_link FROM force_join_channels")
            force_join_channels = [
                {'channel': row[0], 'title': row[1] or row[0], 'invite_link': row[2]}
                for row in c.fetchall()
            ]
            logger.info(f"Loaded {len(force_join_channels)} force-join channel(s).")
        except Exception: pass
        # Load pending script files
        try:
            import json as _json
            c.execute('SELECT user_id, project_name, file_path, file_type, is_safe, security_msg, chat_id, main_file FROM pending_scripts')
            for uid, pname, fpath, ftype, is_safe, sec_msg, chat_id, main_file in c.fetchall():
                if not os.path.exists(fpath):
                    logger.warning(f"Pending script file missing on disk, skipping: {fpath}")
                    continue
                if uid not in pending_script_files:
                    pending_script_files[uid] = {}
                pending_script_files[uid][pname] = {
                    'path': fpath, 'type': ftype, 'is_safe': bool(is_safe),
                    'security_msg': sec_msg or '', 'chat_id': chat_id,
                    'project_name': pname, 'main_file': main_file or pname,
                }
            logger.info(f"Loaded {sum(len(v) for v in pending_script_files.values())} pending script(s) from DB.")
        except Exception as e:
            logger.warning(f"Could not load pending_scripts: {e}")
        # Load pending zip files
        try:
            c.execute('SELECT user_id, project_name, zip_path, file_name_zip, main_file, patterns FROM pending_zips')
            for uid, pname, zip_path, fname_zip, main_file, patterns_json in c.fetchall():
                if not os.path.exists(zip_path):
                    logger.warning(f"Pending zip file missing on disk, skipping: {zip_path}")
                    continue
                with open(zip_path, 'rb') as zf:
                    file_content = zf.read()
                patterns = _json.loads(patterns_json) if patterns_json else []
                if uid not in pending_zip_files:
                    pending_zip_files[uid] = {}
                pending_zip_files[uid][pname] = {
                    'content': file_content, 'patterns': patterns,
                    'file_name_zip': fname_zip or f"{pname}.zip",
                    'project_name': pname, 'main_file': main_file,
                }
            logger.info(f"Loaded {sum(len(v) for v in pending_zip_files.values())} pending zip(s) from DB.")
        except Exception as e:
            logger.warning(f"Could not load pending_zips: {e}")
        conn.close()
        logger.info(f"Data loaded: {len(active_users)} users, {len(user_subscriptions)} subs, {len(admin_ids)} admins, {len(banned_users)} banned.")
    except Exception as e:
        logger.error(f"❌ Error loading data: {e}", exc_info=True)

# ============================================================
# --- Helper Functions ---
# ============================================================
def md_escape(text):
    """Escape special Markdown v1 characters in dynamic text before sending."""
    for ch in ['\\', '`', '*', '_', '[', ']', '(', ')', '~', '>', '#', '+', '-', '=', '|', '{', '}', '.', '!']:
        text = str(text).replace(ch, f'\\{ch}')
    return text

def get_user_folder(user_id, project_name=None):
    if project_name:
        user_folder = os.path.join(UPLOAD_BOTS_DIR, str(user_id), str(project_name))
    else:
        user_folder = os.path.join(UPLOAD_BOTS_DIR, str(user_id))
    os.makedirs(user_folder, exist_ok=True)
    return user_folder

def get_user_file_limit(user_id):
    if user_id == OWNER_ID: return OWNER_LIMIT
    if user_id in admin_ids: return ADMIN_LIMIT
    if user_id in user_limits: return user_limits[user_id]
    if user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now():
        return SUBSCRIBED_USER_LIMIT
    return FREE_USER_LIMIT

def get_user_file_count(user_id):
    return len(user_files.get(user_id, []))

def is_user_banned(user_id):
    return user_id in banned_users

# ============================================================
# --- Force Join Channel Helpers ---
# ============================================================
def add_force_join_channel_db(channel, title, invite_link, added_by):
    """Add a channel to the mandatory join list."""
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute(
                "INSERT OR IGNORE INTO force_join_channels (channel, title, invite_link, added_by, added_at) VALUES (?, ?, ?, ?, ?)",
                (channel, title, invite_link, added_by, datetime.now().isoformat())
            )
            conn.commit()
        except Exception as e:
            logger.error(f"Error adding force_join channel {channel}: {e}")
        finally:
            conn.close()

def remove_force_join_channel_db(channel):
    """Remove a specific channel from the mandatory join list."""
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute("DELETE FROM force_join_channels WHERE channel = ?", (channel,))
            conn.commit()
        except Exception as e:
            logger.error(f"Error removing force_join channel {channel}: {e}")
        finally:
            conn.close()

def is_user_in_channel(user_id, channel):
    """Return True if user has joined the given channel."""
    try:
        member = bot.get_chat_member(channel, user_id)
        return member.status in ('member', 'administrator', 'creator')
    except Exception:
        return False

def check_force_join(message):
    """
    Check that the user has joined ALL mandatory channels.
    If any are missing, sends one message listing all unjoined channels with join buttons.
    Returns False if the user fails the check, True otherwise.
    Admins are always exempt.
    """
    if not force_join_channels:
        return True
    user_id = message.from_user.id
    if user_id == OWNER_ID:
        return True  # Only Owner is exempt; Admins must also join

    unjoined = [e for e in force_join_channels if not is_user_in_channel(user_id, e['channel'])]
    if not unjoined:
        return True

    markup = types.InlineKeyboardMarkup(row_width=1)
    for e in unjoined:
        url = e.get('invite_link') or (f"https://t.me/{e['channel'].lstrip('@')}" if e['channel'].startswith('@') else None)
        if url:
            markup.add(make_colored_button(f"📢 Join {e['title']}", url=url))
        else:
            markup.add(make_colored_button(f"📢 {e['title']} (contact admin for link)", callback_data='noop'))
    markup.add(make_colored_button("✅ I've Joined All", callback_data="check_joined"))

    if len(unjoined) == 1:
        text = (f"⚠️ *Access Restricted!*\n\n"
                f"You must join this channel to use this bot:\n"
                f"› *{unjoined[0]['title']}*\n\n"
                f"👇 Join and press *I've Joined All*:")
    else:
        ch_list = '\n'.join(f"› *{e['title']}*" for e in unjoined)
        text = (f"⚠️ *Access Restricted!*\n\n"
                f"You must join *all* of these channels to use this bot:\n\n"
                f"{ch_list}\n\n"
                f"👇 Join all and press *I've Joined All*:")

    bot.send_message(message.chat.id, text, parse_mode='Markdown', reply_markup=markup)
    return False

def is_bot_running(script_owner_id, project_name):
    script_key = f"{script_owner_id}_{project_name}"
    script_info = bot_scripts.get(script_key)
    if script_info and script_info.get('process'):
        try:
            proc = psutil.Process(script_info['process'].pid)
            is_running = proc.is_running() and proc.status() != psutil.STATUS_ZOMBIE
            if not is_running:
                if 'log_file' in script_info and hasattr(script_info['log_file'], 'close') and not script_info['log_file'].closed:
                    try: script_info['log_file'].close()
                    except Exception: pass
                if script_key in bot_scripts: del bot_scripts[script_key]
            return is_running
        except psutil.NoSuchProcess:
            if 'log_file' in script_info and hasattr(script_info['log_file'], 'close') and not script_info['log_file'].closed:
                try: script_info['log_file'].close()
                except Exception: pass
            if script_key in bot_scripts: del bot_scripts[script_key]
            return False
        except Exception as e:
            logger.error(f"Error checking process status for {script_key}: {e}")
            return False
    return False

def kill_process_tree(process_info):
    pid = None
    script_key = process_info.get('script_key', 'N/A')
    try:
        if 'log_file' in process_info and hasattr(process_info['log_file'], 'close') and not process_info['log_file'].closed:
            try: process_info['log_file'].close()
            except Exception as log_e: logger.error(f"Error closing log file for {script_key}: {log_e}")
        process = process_info.get('process')
        if process and hasattr(process, 'pid'):
            pid = process.pid
            if pid:
                try:
                    parent = psutil.Process(pid)
                    children = parent.children(recursive=True)
                    for child in children:
                        try: child.terminate()
                        except psutil.NoSuchProcess: pass
                        except Exception:
                            try: child.kill()
                            except Exception: pass
                    gone, alive = psutil.wait_procs(children, timeout=1)
                    for p in alive:
                        try: p.kill()
                        except Exception: pass
                    try:
                        parent.terminate()
                        try: parent.wait(timeout=1)
                        except psutil.TimeoutExpired: parent.kill()
                    except psutil.NoSuchProcess: pass
                    except Exception:
                        try: parent.kill()
                        except Exception: pass
                except psutil.NoSuchProcess: pass
    except Exception as e:
        logger.error(f"❌ Unexpected error killing process tree for PID {pid} ({script_key}): {e}", exc_info=True)

# ============================================================
# --- Security / Dangerous Pattern Detection ---
# ============================================================
# Each entry is (regex, score, label).
# A file gets flagged when its total score hits SECURITY_SCORE_THRESHOLD.
# Using a score system avoids false alarms from common harmless patterns.

SECURITY_SCORE_THRESHOLD = 10

# --- Critical: any single match auto-flags the file (score 10) ---
CRITICAL_PATTERNS = [
    (r'\bos\.system\s*\(',                              10, "os.system() shell execution"),
    (r'\bsubprocess\.(Popen|call|run|check_output|getoutput|getstatusoutput)\s*\(', 10, "subprocess shell execution"),
    (r'\beval\s*\(',                                    10, "eval() code execution"),
    (r'\bexec\s*\(',                                    10, "exec() code execution"),
    (r'\b__import__\s*\(',                              10, "dynamic __import__()"),
    (r'rm\s+-rf\s+[/~\.\*]',                            10, "destructive rm -rf"),
    (r'/bin/(sh|bash|zsh|dash)',                        10, "shell binary reference"),
    (r'nc\s+-[elp]',                                    10, "netcat flag (reverse shell)"),
    (r'\bnetcat\b',                                     10, "netcat usage"),
    (r'\bshellcode\b',                                  10, "shellcode reference"),
    (r'\bmetasploit\b',                                 10, "metasploit framework"),
    (r'\brootkit\b',                                    10, "rootkit reference"),
    (r'\bbackdoor\b',                                   10, "backdoor reference"),
    (r'/etc/shadow',                                    10, "shadow password file"),
    (r'/etc/passwd',                                    10, "passwd file access"),
    (r'\bid_rsa\b',                                     10, "SSH private key"),
    (r'\bauthorized_keys\b',                            10, "SSH authorized_keys"),
    (r'\bdd\s+(if=/dev/(zero|random)|of=/dev/sda)',     10, "disk destruction"),
    (r'wget\s+.*\|\s*(bash|sh)',                        10, "remote code exec via wget"),
    (r'curl\s+.*\|\s*(bash|sh)',                        10, "remote code exec via curl"),
    (r'\bos\.(remove|unlink)\s*\(',                     10, "file deletion via os"),
    (r'\bos\.(popen|fork|execv|execvp|spawnl)\s*\(',    10, "os process spawning"),
    (r'shutil\.rmtree\s*\(',                            10, "recursive directory removal"),
    (r'\bwin32api\b|\bwin32com\b|\bwin32process\b',     10, "Windows API abuse"),
    (r'\bGetAsyncKeyState\b|\bSetWindowsHookEx\b',      10, "Windows keystroke hook"),
]

# --- Obfuscation: techniques used to hide malicious code (score 8) ---
OBFUSCATION_PATTERNS = [
    (r'base64\.b64decode',   8, "base64 decode (obfuscation)"),
    (r'(?<!re\.)(?<!pattern\.)(?<!\.)(?<![a-zA-Z_]re)\bcompile\s*\(', 8, "dynamic compile() call"),
    (r'marshal\.loads',      8, "marshal deserialization"),
    (r'zlib\.decompress',    8, "zlib decompression (obfuscation)"),
]

# --- High-risk: dangerous libraries or techniques (score 5) ---
HIGH_RISK_PATTERNS = [
    (r'\bparamiko\b',                   5, "SSH/SFTP library"),
    (r'\bnmap\b',                       5, "network scanner"),
    (r'\bscapy\b',                      5, "packet manipulation"),
    (r'\bpynput\b',                     5, "keylogger library"),
    (r'\bpyautogui\b',                  5, "screen automation/capture"),
    (r'\bpyscreenshot\b|\bImageGrab\b', 5, "screen capture"),
    (r'\bptrace\b',                     5, "process tracing (anti-debug)"),
    (r'\bmmap\b',                       5, "memory mapping"),
    (r'VirtualAlloc|VirtualProtect|HeapAlloc', 5, "memory manipulation"),
    (r'\bimportlib\b',                  5, "dynamic module loading"),
    (r'\bpickle\.loads\b',              5, "unsafe pickle deserialization"),
    (r'\bcPickle\b',                    5, "unsafe cPickle"),
    (r'\bftplib\b',                     5, "FTP library"),
    (r'nc\s+.*\s+-[0-9]',              5, "netcat connection"),
    (r'\bschtasks\b|\btaskkill\b',      5, "Windows task manipulation"),
    (r'\bchattr\b',                     5, "file attribute manipulation"),
]

# --- Medium-risk: can appear in legit bots too, depends on context (score 2) ---
MEDIUM_RISK_PATTERNS = [
    (r'\bsocket\.socket\s*\(',  2, "raw socket creation"),
    (r'\bos\.environ\b',        2, "environment variable access"),
    (r'\.ssh/',                 2, "SSH directory reference"),
    (r'\bgetpass\b',            2, "password input"),
    (r'\bcrontab\b',            2, "crontab manipulation"),
    (r'\bsystemctl\b',          2, "systemctl service control"),
    (r'chmod\s+777|chmod\s+\+x',2, "permissive chmod"),
    (r'\bwhoami\b',             2, "system identity query"),
    (r'/proc/',                 2, "procfs access"),
    (r'\bsudo\b',               2, "sudo privilege escalation"),
    (r'\busermod\b|\badduser\b|\bdeluser\b', 2, "user account manipulation"),
]

# Flat list of all patterns for ZIP scan backward compatibility
DANGEROUS_PATTERNS = (
    [p for p, _, _ in CRITICAL_PATTERNS] +
    [p for p, _, _ in OBFUSCATION_PATTERNS] +
    [p for p, _, _ in HIGH_RISK_PATTERNS] +
    [p for p, _, _ in MEDIUM_RISK_PATTERNS]
)


# All pattern tiers merged for scored scanning
_ALL_SCORED_PATTERNS = CRITICAL_PATTERNS + OBFUSCATION_PATTERNS + HIGH_RISK_PATTERNS + MEDIUM_RISK_PATTERNS

def scan_code_security(content):
    """
    Scored security scan on raw code content.
    Returns (matched_labels: list[str], total_score: int).
    A score >= SECURITY_SCORE_THRESHOLD means the file is dangerous.
    Using scores prevents common-but-harmless patterns (open, requests, threading)
    from causing false positives, while critical patterns auto-trigger on their own.
    """
    matched_labels = []
    total_score = 0
    seen_patterns = set()
    for pattern, score, label in _ALL_SCORED_PATTERNS:
        if pattern in seen_patterns:
            continue
        if re.search(pattern, content, re.IGNORECASE):
            seen_patterns.add(pattern)
            matched_labels.append(label)
            total_score += score
    return matched_labels, total_score

def check_code_security(file_path, file_type='py'):
    """
    Scan a script file for dangerous patterns using scored detection.
    Returns (is_safe: bool, message: str).
    """
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        labels, score = scan_code_security(content)
        if score >= SECURITY_SCORE_THRESHOLD:
            logger.warning(f"🚨 Security score {score} in {file_path}: {labels[:5]}")
            return False, f"⚠️ Risk score: {score}/10 — Detected: {', '.join(labels[:3])}"
        return True, "✅ Code passed security scan"
    except Exception as e:
        logger.error(f"Error in security check: {e}")
        return False, f"Security check error: {str(e)}"

def scan_zip_file(zip_path):
    """
    Deep scan all .py/.js files inside a ZIP for dangerous patterns.
    Returns list of (filename, matched_labels, score) for any risky files.
    """
    findings = []
    try:
        with zipfile.ZipFile(zip_path, 'r') as z:
            for file in z.namelist():
                if file.endswith(('.py', '.js')):
                    try:
                        content = z.read(file).decode('utf-8', errors='ignore')
                    except Exception:
                        continue
                    labels, score = scan_code_security(content)
                    if score >= SECURITY_SCORE_THRESHOLD:
                        findings.append((file, labels, score))
    except Exception as e:
        logger.error(f"Error in ZIP deep scan: {e}")
    return findings

def scan_zip_security(zip_path):
    """
    Scan ZIP contents using the scored security system.
    Returns (is_safe: bool, message: str).
    """
    try:
        findings = scan_zip_file(zip_path)
        if findings:
            first_file, labels, score = findings[0]
            return False, (f"⚠️ '{first_file}' — Risk score: {score} — "
                           f"Detected: {', '.join(labels[:3])}")
        return True, "✅ Archive passed security scan"
    except Exception as e:
        return False, f"Error scanning archive: {str(e)}"

# ============================================================
# --- Sandboxed Environment for User Scripts ---
# ============================================================
# User scripts run in a clean, isolated environment.
# get_clean_env() returns a minimal env with no host secrets passed through.

def get_clean_env():
    env = os.environ.copy()
    env["HOME"] = os.environ.get("HOME", "/data/data/com.termux/files/home")
    env["LANG"] = "en_US.UTF-8"
    env["PYTHONUNBUFFERED"] = "1"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env

# ============================================================
# --- Manual Module Installation System ---
# ============================================================
TELEGRAM_MODULES = {
    # Main Bot Frameworks (verified on PyPI)
    'telebot': 'pyTelegramBotAPI',
    'telegram': 'python-telegram-bot',
    'python_telegram_bot': 'python-telegram-bot',
    'aiogram': 'aiogram',
    'pyrogram': 'pyrogram',
    'telethon': 'telethon',
    'telethon.sync': 'telethon',
    'from telethon.sync import telegramclient': 'telethon',

    # Additional verified libraries
    'telepot': 'telepot',
    'tgcrypto': 'tgcrypto',
    'telegram_upload': 'telegram-upload',
    'telegram_send': 'telegram-send',

    # MTProto & Low-Level
    'tl': 'telethon',

    # Common non-telegram packages (verified on PyPI)
    'bs4': 'beautifulsoup4',
    'requests': 'requests',
    'pillow': 'Pillow',
    'PIL': 'Pillow',
    'cv2': 'opencv-python',
    'yaml': 'PyYAML',
    'dotenv': 'python-dotenv',
    'dateutil': 'python-dateutil',
    'pandas': 'pandas',
    'numpy': 'numpy',
    'flask': 'Flask',
    'django': 'Django',
    'sqlalchemy': 'SQLAlchemy',
    'aiohttp': 'aiohttp',
    'httpx': 'httpx',
    'psutil': 'psutil',
    'pymongo': 'pymongo',
    'redis': 'redis',
    'celery': 'celery',
    'pydantic': 'pydantic',
    'fastapi': 'fastapi',
    'uvicorn': 'uvicorn',
    'cryptography': 'cryptography',
    'paramiko': 'paramiko',
    'qrcode': 'qrcode',
    'barcode': 'python-barcode',
    'schedule': 'schedule',
    'apscheduler': 'APScheduler',
    'pytz': 'pytz',
    'motor': 'motor',
    'aiosqlite': 'aiosqlite',

    # Core modules — skip installation
    'asyncio': None,
    'json': None,
    'datetime': None,
    'os': None,
    'sys': None,
    're': None,
    'time': None,
    'math': None,
    'random': None,
    'logging': None,
    'threading': None,
    'subprocess': None,
    'zipfile': None,
    'tempfile': None,
    'shutil': None,
    'sqlite3': None,
    'atexit': None,
    'pathlib': None,
    'collections': None,
    'itertools': None,
    'functools': None,
    'typing': None,
    'abc': None,
    'copy': None,
    'io': None,
    'struct': None,
    'hashlib': None,
    'hmac': None,
    'base64': None,
    'urllib': None,
    'http': None,
    'socket': None,
    'ssl': None,
    'uuid': None,
    'enum': None,
    'dataclasses': None,
    'contextlib': None,
    'traceback': None,
    'inspect': None,
    'gc': None,
    'weakref': None,
    'signal': None,
    'platform': None,
    'glob': None,
    'fnmatch': None,
    'stat': None,
    'pickle': None,
    'csv': None,
    'configparser': None,
    'argparse': None,
    'string': None,
    'textwrap': None,
    'unicodedata': None,
    'html': None,
    'xml': None,
}

def save_install_log(user_id, module_name, package_name, status, log):
    """Save installation log to database."""
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            install_date = datetime.now().isoformat()
            c.execute('INSERT INTO install_logs (user_id, module_name, package_name, status, log, install_date) VALUES (?, ?, ?, ?, ?, ?)',
                      (user_id, module_name, package_name, status, log, install_date))
            conn.commit()
        except Exception as e:
            logger.error(f"❌ Error saving install log: {e}")
        finally:
            conn.close()

def attempt_install_pip(module_name, message, manual_request=False):
    """Install a Python package via pip."""
    package_name = TELEGRAM_MODULES.get(module_name.lower(), module_name)
    if package_name is None:
        bot.reply_to(message, f"ℹ️ `{module_name}` is a core Python module — no installation needed.", parse_mode='Markdown')
        return False, "Core module"
    try:
        prefix = "🔄 Manual install" if manual_request else "🐍 Auto-installing"
        bot.reply_to(message, f"{prefix}: `{module_name}` → `{package_name}`...", parse_mode='Markdown')
        result = subprocess.run([sys.executable, '-m', 'pip', 'install', package_name],
                                capture_output=True, text=True, check=False, encoding='utf-8', errors='ignore')
        if result.returncode == 0:
            log_msg = f"Installed {package_name}.\n{result.stdout}"
            bot.reply_to(message, f"✅ `{package_name}` installed successfully!", parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "success", log_msg)
            return True, log_msg
        else:
            err = (result.stderr or result.stdout)[:3000]
            error_msg = f"❌ Failed to install `{package_name}`.\n```\n{err}\n```"
            bot.reply_to(message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "failed", error_msg)
            return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error: {str(e)}"
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, package_name, "error", error_msg)
        return False, error_msg

def attempt_install_npm(module_name, user_folder, message, manual_request=False):
    """Install a Node.js package via npm."""
    try:
        prefix = "🔄 Manual install" if manual_request else "🟠 Auto-installing"
        bot.reply_to(message, f"{prefix} Node package: `{module_name}`...", parse_mode='Markdown')
        result = subprocess.run(['npm', 'install', module_name], capture_output=True, text=True,
                                check=False, cwd=user_folder, encoding='utf-8', errors='ignore')
        if result.returncode == 0:
            log_msg = f"Installed {module_name}.\n{result.stdout}"
            bot.reply_to(message, f"✅ Node package `{module_name}` installed!", parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "success", log_msg)
            return True, log_msg
        else:
            err = (result.stderr or result.stdout)[:3000]
            error_msg = f"❌ Failed to install `{module_name}`.\n```\n{err}\n```"
            bot.reply_to(message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "failed", error_msg)
            return False, error_msg
    except FileNotFoundError:
        error_msg = "❌ `npm` not found. Make sure Node.js is installed."
        bot.reply_to(message, error_msg, parse_mode='Markdown')
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error: {str(e)}"
        bot.reply_to(message, error_msg)
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg

# ============================================================
# --- Dependency Auto-Install Helpers ---
# ============================================================

# ── Dependency-install helpers ────────────────────────────────────────────────

def _dep_file_hash(file_path):
    """SHA-256 hex digest of a file."""
    import hashlib
    h = hashlib.sha256()
    with open(file_path, 'rb') as f:
        h.update(f.read())
    return h.hexdigest()
def _dep_marker_path(user_folder, marker_name):
    """
    Return a path for a hash-marker file stored under the project folder.
    """
    import hashlib

    folder_key = hashlib.sha256(user_folder.encode()).hexdigest()[:16]
    marker_dir = os.path.join(user_folder, ".deps_cache", folder_key)
    os.makedirs(marker_dir, exist_ok=True)

    return os.path.join(marker_dir, marker_name)

def _dep_read_marker(marker_path):
    try:
        with open(marker_path, 'r') as f:
            return f.read().strip()
    except Exception:
        return None

def _dep_write_marker(marker_path, hash_value):
    try:
        with open(marker_path, 'w') as f:
            f.write(hash_value)
    except Exception as e:
        logger.warning(f"Could not write dep marker {marker_path}: {e}")

# ──────────────────────────────────────────────────────────────────────────────

def install_requirements_if_present(user_folder, user_id, message_obj):
    """
    Install packages from requirements.txt if present.

    Skips installation when requirements.txt is unchanged since the last
    successful install in this server session (hash stored in /tmp).
    On server restart /tmp is wiped, so deps are always installed fresh once.
    Returns True on success or when no requirements.txt exists, False on error.
    """
    req_path = os.path.join(user_folder, 'requirements.txt')
    if not os.path.exists(req_path):
        return True

    current_hash = _dep_file_hash(req_path)
    marker_path  = _dep_marker_path(user_folder, 'pip_deps_hash')
    if _dep_read_marker(marker_path) == current_hash:
        logger.info(f"pip deps unchanged for user {user_id} – skipping install.")
        return True

    try:
        bot.reply_to(message_obj,
            "🔄 Installing dependencies from `requirements.txt`...",
            parse_mode='Markdown')
        result = subprocess.run(
            [sys.executable, '-m', 'pip', 'install', '-r', req_path],
            capture_output=True, text=True, check=False,
            encoding='utf-8', errors='ignore', env=get_clean_env()
        )
        if result.returncode == 0:
            _dep_write_marker(marker_path, current_hash)
            bot.reply_to(message_obj,
                "✅ Dependencies from `requirements.txt` installed successfully.",
                parse_mode='Markdown')
            return True
        else:
            err = (result.stderr or result.stdout)[:1500]
            bot.reply_to(message_obj,
                f"❌ Failed to install `requirements.txt` dependencies:\n```\n{err}\n```",
                parse_mode='Markdown')
            return False
    except Exception as e:
        logger.error(f"install_requirements_if_present error for {user_id}: {e}")
        bot.reply_to(message_obj,
            f"❌ Error installing `requirements.txt` dependencies: {e}",
            parse_mode='Markdown')
        return False


def install_package_json_if_present(user_folder, user_id, message_obj):
    """
    Run npm install if package.json is present.

    Skips installation when package.json is unchanged since the last
    successful install in this server session (hash stored in /tmp).
    On server restart /tmp is wiped, so deps are always installed fresh once.
    Returns True on success or when no package.json exists, False on error.
    """
    pkg_path = os.path.join(user_folder, 'package.json')
    if not os.path.exists(pkg_path):
        return True

    current_hash = _dep_file_hash(pkg_path)
    marker_path  = _dep_marker_path(user_folder, 'npm_deps_hash')
    if _dep_read_marker(marker_path) == current_hash:
        logger.info(f"npm deps unchanged for user {user_id} – skipping install.")
        return True

    try:
        bot.reply_to(message_obj,
            "🔄 Installing Node.js dependencies from `package.json`...",
            parse_mode='Markdown')
        result = subprocess.run(
            ['npm', 'install'],
            capture_output=True, text=True, check=False,
            cwd=user_folder, encoding='utf-8', errors='ignore', env=get_clean_env()
        )
        if result.returncode == 0:
            _dep_write_marker(marker_path, current_hash)
            bot.reply_to(message_obj,
                "✅ Node.js dependencies installed successfully.",
                parse_mode='Markdown')
            return True
        else:
            err = (result.stderr or result.stdout)[:1500]
            bot.reply_to(message_obj,
                f"❌ Failed to install Node.js dependencies:\n```\n{err}\n```",
                parse_mode='Markdown')
            return False
    except FileNotFoundError:
        bot.reply_to(message_obj,
            "❌ `npm` not found. Install Node.js on the server.", parse_mode='Markdown')
        return False
    except Exception as e:
        logger.error(f"install_package_json_if_present error for {user_id}: {e}")
        bot.reply_to(message_obj,
            f"❌ Error installing Node.js dependencies: {e}", parse_mode='Markdown')
        return False


def auto_install_py_imports(script_path, user_folder, user_id, message_obj):
    """
    Scan a single .py file for top-level import statements and proactively install
    any third-party packages that are not yet importable.
    Also writes a requirements.txt with ALL detected third-party packages so that
    deps are automatically reinstalled on server restart (via install_requirements_if_present).
    """
    try:
        with open(script_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception:
        return

    import_names = set()
    for m in re.finditer(r'^\s*import\s+([\w\.]+)', content, re.MULTILINE):
        import_names.add(m.group(1).split('.')[0])
    for m in re.finditer(r'^\s*from\s+([\w\.]+)\s+import', content, re.MULTILINE):
        name = m.group(1).split('.')[0]
        if name not in ('__future__',):
            import_names.add(name)

    all_packages = []  # all detected packages for requirements.txt
    to_install = []    # only packages not yet installed
    for mod in import_names:
        # TELEGRAM_MODULES maps module name to package; None means it's stdlib
        if mod in TELEGRAM_MODULES:
            if TELEGRAM_MODULES[mod] is None:
                continue  # stdlib, skip
            pkg = TELEGRAM_MODULES[mod]
        else:
            pkg = mod  # best-effort: use the import name as package name
        if not pkg:
            continue
        if pkg not in all_packages:
            all_packages.append(pkg)
        # Try importing — only add to install queue if it fails
        try:
            __import__(mod)
        except ImportError:
            if pkg not in to_install:
                to_install.append(pkg)
        except Exception:
            pass  # not an ImportError (e.g. SyntaxError inside module) — skip

    # --- Persist requirements.txt so dependencies reinstall automatically ---
    # We write ALL detected third-party packages (not just missing ones), because on a
    # fresh deployment even "already installed" packages won't be present.
    if all_packages:
        req_path = os.path.join(user_folder, 'requirements.txt')
        try:
            existing = set()
            if os.path.exists(req_path):
                with open(req_path, 'r', encoding='utf-8') as f:
                    existing = {line.strip() for line in f if line.strip()}
            merged = sorted(existing | set(all_packages))
            with open(req_path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(merged) + '\n')
            logger.info(f"requirements.txt written for user {user_id} in {user_folder}: {merged}")
        except Exception as e:
            logger.warning(f"Could not write requirements.txt for user {user_id}: {e}")

    if not to_install:
        return

    bot.reply_to(message_obj,
        f"📦 *Auto-installing missing packages:* `{', '.join(to_install)}`...",
        parse_mode='Markdown')
    try:
        result = subprocess.run(
            [sys.executable, '-m', 'pip', 'install'] + to_install,
            capture_output=True, text=True, check=False,
            encoding='utf-8', errors='ignore', env=get_clean_env()
        )
        if result.returncode == 0:
            bot.reply_to(message_obj,
                f"✅ Auto-installed: `{', '.join(to_install)}`",
                parse_mode='Markdown')
        else:
            err = (result.stderr or result.stdout)[:1000]
            bot.reply_to(message_obj,
                f"⚠️ Some packages may not have installed:\n```\n{err}\n```",
                parse_mode='Markdown')
    except Exception as e:
        logger.error(f"auto_install_py_imports error for {user_id}: {e}")


def auto_install_js_requires(script_path, user_folder, user_id, message_obj):
    """
    Scan a single .js file for require() calls and install any missing npm packages.
    Used when a user uploads a single .js file (no package.json present).
    Also writes/updates a package.json with ALL detected packages BEFORE running
    npm install, so that deps are automatically reinstalled on server restart
    (via install_package_json_if_present).
    Skips built-in Node.js core modules and relative paths.
    """
    import json as _json

    # Node.js built-in core modules — no npm install needed
    NODE_BUILTINS = {
        # Filesystem & I/O
        'fs': None,
        'path': None,
        'readline': None,
        'stream': None,
        'string_decoder': None,
        'tty': None,
        'buffer': None,

        # Networking
        'http': None,
        'http2': None,
        'https': None,
        'net': None,
        'dgram': None,
        'dns': None,
        'tls': None,
        'url': None,
        'querystring': None,
        'punycode': None,

        # Process & System
        'process': None,
        'os': None,
        'child_process': None,
        'cluster': None,
        'worker_threads': None,
        'timers': None,
        'perf_hooks': None,
        'trace_events': None,
        'sys': None,
        'signal': None,

        # Crypto & Security
        'crypto': None,

        # Utilities
        'util': None,
        'assert': None,
        'events': None,
        'module': None,
        'repl': None,
        'vm': None,
        'v8': None,
        'domain': None,
        'console': None,
        'constants': None,
        'zlib': None,
    }
    try:
        with open(script_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception:
        return

    requires = set()
    for m in re.finditer(r'''require\s*\(\s*['"](@?[^'"./][^'"]*)['"]\s*\)''', content):
        raw = m.group(1)
        # Scoped packages: @scope/name → keep as-is; others: take first path segment
        if raw.startswith('@'):
            parts = raw.split('/')
            pkg = '/'.join(parts[:2]) if len(parts) >= 2 else parts[0]
        else:
            pkg = raw.split('/')[0]
        if pkg not in NODE_BUILTINS:
            requires.add(pkg)

    if not requires:
        return

    # --- Persist package.json with ALL detected packages BEFORE npm install ---
    # This ensures install_package_json_if_present can reinstall on server restart,
    # even for single-file projects that didn't originally have a package.json.
    pkg_json_path = os.path.join(user_folder, 'package.json')
    try:
        if os.path.exists(pkg_json_path):
            with open(pkg_json_path, 'r', encoding='utf-8') as f:
                pkg_data = _json.load(f)
        else:
            pkg_data = {
                "name": re.sub(r'[^\w\-]', '_', os.path.basename(user_folder))[:40],
                "version": "1.0.0",
                "description": "Auto-generated by Astroneth Hosting",
                "dependencies": {}
            }
        deps = pkg_data.setdefault('dependencies', {})
        for pkg in requires:
            if pkg not in deps:
                deps[pkg] = "*"
        with open(pkg_json_path, 'w', encoding='utf-8') as f:
            _json.dump(pkg_data, f, indent=2)
        logger.info(f"package.json written for user {user_id} in {user_folder}: {list(requires)}")
    except Exception as e:
        logger.warning(f"Could not write package.json for user {user_id}: {e}")

    # Only attempt to install packages that are not already resolvable
    to_install = []
    for pkg in requires:
        check = subprocess.run(
            ['node', '-e', f'require("{pkg}")'],
            capture_output=True, cwd=user_folder, env=get_clean_env()
        )
        if check.returncode != 0:
            to_install.append(pkg)

    if not to_install:
        return

    bot.reply_to(message_obj,
        f"📦 *Auto-installing npm packages:* `{', '.join(to_install)}`...",
        parse_mode='Markdown')
    try:
        result = subprocess.run(
            ['npm', 'install'] + to_install,
            capture_output=True, text=True, check=False,
            cwd=user_folder, encoding='utf-8', errors='ignore', env=get_clean_env()
        )
        if result.returncode == 0:
            bot.reply_to(message_obj,
                f"✅ Auto-installed npm: `{', '.join(to_install)}`",
                parse_mode='Markdown')
        else:
            err = (result.stderr or result.stdout)[:1000]
            bot.reply_to(message_obj,
                f"⚠️ Some npm packages may not have installed:\n```\n{err}\n```",
                parse_mode='Markdown')
    except FileNotFoundError:
        bot.reply_to(message_obj,
            "❌ `npm` not found. Install Node.js on the server.", parse_mode='Markdown')
    except Exception as e:
        logger.error(f"auto_install_js_requires error for {user_id}: {e}")


def manual_install_module_init(message):
    """Entry point for the 📦 Manual Install feature."""
    user_id = message.from_user.id
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned from using this bot."); return
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "⚠️ Bot is locked by admin. Try again later."); return
    msg = bot.reply_to(message,
        "📦 *Manual Module Installer*\n"
        "──────────────────────\n\n"
        "Enter the name of the module to install:\n\n"
        "🐍 *Python:* `requests`, `pillow`, `numpy`…\n"
        "🟨 *Node.js:* `npm:express`, `npm:axios`…\n\n"
        "Type /cancel to abort.",
        parse_mode='Markdown')
    bot.register_next_step_handler(msg, process_manual_install_module)

def process_manual_install_module(message):
    """Process the module name sent by user and run installation."""
    user_id = message.from_user.id
    if is_user_banned(user_id):
        bot.reply_to(message, "❌ You are banned."); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Installation cancelled."); return
    module_name = (message.text or '').strip()
    if not module_name:
        bot.reply_to(message, "⚠️ Please send a valid module name."); return
    if module_name.lower().startswith('npm:'):
        module_name = module_name[4:].strip()
        user_folder = get_user_folder(user_id)
        attempt_install_npm(module_name, user_folder, message, manual_request=True)
    else:
        attempt_install_pip(module_name, message, manual_request=True)

def _logic_manual_install(message):
    """Logic handler for 📦 Manual Install button."""
    manual_install_module_init(message)

# ============================================================
# --- Database Operations ---
# ============================================================
DB_LOCK = threading.Lock()

def save_user_file(user_id, project_name, main_file, file_type='py'):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('INSERT OR REPLACE INTO user_files (user_id, project_name, main_file, file_type) VALUES (?, ?, ?, ?)',
                      (user_id, project_name, main_file, file_type))
            conn.commit()
            if user_id not in user_files: user_files[user_id] = []
            user_files[user_id] = [(pn, mf, ft) for pn, mf, ft in user_files[user_id] if pn != project_name]
            user_files[user_id].append((project_name, main_file, file_type))
        except Exception as e: logger.error(f"❌ Error saving file for {user_id}: {e}")
        finally: conn.close()

def remove_user_file_db(user_id, project_name):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_files WHERE user_id = ? AND project_name = ?', (user_id, project_name))
            conn.commit()
            if user_id in user_files:
                user_files[user_id] = [f for f in user_files[user_id] if f[0] != project_name]
                if not user_files[user_id]: del user_files[user_id]
        except Exception as e: logger.error(f"❌ Error removing file for {user_id}: {e}")
        finally: conn.close()

def update_main_file_db(user_id, project_name, new_main_file):
    """Update the main file for an existing project."""
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('UPDATE user_files SET main_file = ? WHERE user_id = ? AND project_name = ?',
                      (new_main_file, user_id, project_name))
            conn.commit()
            if user_id in user_files:
                user_files[user_id] = [
                    (pn, new_main_file if pn == project_name else mf, ft)
                    for pn, mf, ft in user_files[user_id]
                ]
            return True
        except Exception as e:
            logger.error(f"❌ Error updating main file for {user_id}/{project_name}: {e}")
            return False
        finally:
            conn.close()

def add_active_user(user_id):
    active_users.add(user_id)
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            join_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO active_users (user_id, join_date, last_seen) VALUES (?, ?, ?)',
                      (user_id, join_date, join_date))
            conn.commit()
        except Exception as e: logger.error(f"❌ Error adding active user {user_id}: {e}")
        finally: conn.close()

def save_subscription(user_id, expiry):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            expiry_str = expiry.isoformat()
            c.execute('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)', (user_id, expiry_str))
            conn.commit()
            user_subscriptions[user_id] = {'expiry': expiry}
        except Exception as e: logger.error(f"❌ Error saving sub for {user_id}: {e}")
        finally: conn.close()

def remove_subscription_db(user_id):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('DELETE FROM subscriptions WHERE user_id = ?', (user_id,))
            conn.commit()
            if user_id in user_subscriptions: del user_subscriptions[user_id]
        except Exception as e: logger.error(f"❌ Error removing sub for {user_id}: {e}")
        finally: conn.close()

def add_admin_db(admin_id):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (admin_id,))
            conn.commit()
            admin_ids.add(admin_id)
        except Exception as e: logger.error(f"❌ Error adding admin {admin_id}: {e}")
        finally: conn.close()
    return True

def remove_admin_db(admin_id):
    if admin_id == OWNER_ID:
        logger.warning("Attempted to remove OWNER_ID from admins.")
        return False
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        removed = False
        try:
            c.execute('SELECT 1 FROM admins WHERE user_id = ?', (admin_id,))
            if c.fetchone():
                c.execute('DELETE FROM admins WHERE user_id = ?', (admin_id,))
                conn.commit()
                removed = c.rowcount > 0
                if removed: admin_ids.discard(admin_id)
            else:
                admin_ids.discard(admin_id)
            return removed
        except Exception as e: logger.error(f"❌ Error removing admin {admin_id}: {e}"); return False
        finally: conn.close()

def ban_user_db(user_id, reason, banned_by):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            ban_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO banned_users (user_id, reason, banned_by, ban_date) VALUES (?, ?, ?, ?)',
                      (user_id, reason, banned_by, ban_date))
            conn.commit()
            banned_users.add(user_id)
            logger.info(f"Banned user {user_id} by {banned_by}. Reason: {reason}")
            return True
        except Exception as e: logger.error(f"❌ Error banning user {user_id}: {e}"); return False
        finally: conn.close()

def unban_user_db(user_id):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('DELETE FROM banned_users WHERE user_id = ?', (user_id,))
            conn.commit()
            banned_users.discard(user_id)
            logger.info(f"Unbanned user {user_id}")
            return True
        except Exception as e: logger.error(f"❌ Error unbanning user {user_id}: {e}"); return False
        finally: conn.close()

def set_user_limit_db(user_id, file_limit, set_by):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            set_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO user_limits (user_id, file_limit, set_by, set_date) VALUES (?, ?, ?, ?)',
                      (user_id, file_limit, set_by, set_date))
            conn.commit()
            user_limits[user_id] = file_limit
            return True
        except Exception as e: logger.error(f"❌ Error setting limit for {user_id}: {e}"); return False
        finally: conn.close()

def remove_user_limit_db(user_id):
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_limits WHERE user_id = ?', (user_id,))
            conn.commit()
            user_limits.pop(user_id, None)
            return True
        except Exception as e: logger.error(f"❌ Error removing limit for {user_id}: {e}"); return False
        finally: conn.close()

# ============================================================
# --- Pending Files DB Helpers ---
# ============================================================
def save_pending_script_db(user_id, project_name, entry):
    """Persist a pending script entry to DB so it survives restarts."""
    import json as _json
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute(
                '''INSERT OR REPLACE INTO pending_scripts
                   (user_id, project_name, file_path, file_type, is_safe, security_msg, chat_id, main_file, queued_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                (user_id, project_name, entry['path'], entry['type'],
                 1 if entry.get('is_safe') else 0, entry.get('security_msg', ''),
                 entry.get('chat_id', 0), entry.get('main_file', project_name),
                 datetime.now().isoformat())
            )
            conn.commit()
        except Exception as e:
            logger.error(f"❌ Error saving pending script for {user_id}/{project_name}: {e}")
        finally:
            conn.close()

def remove_pending_script_db(user_id, project_name):
    """Remove a pending script entry from DB after approval/rejection."""
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute('DELETE FROM pending_scripts WHERE user_id = ? AND project_name = ?',
                         (user_id, project_name))
            conn.commit()
        except Exception as e:
            logger.error(f"❌ Error removing pending script for {user_id}/{project_name}: {e}")
        finally:
            conn.close()

def save_pending_zip_db(user_id, project_name, entry):
    """
    Persist a pending zip entry to DB.
    Saves the raw zip bytes to PENDING_ZIPS_DIR so they survive restarts.
    """
    import json as _json
    zip_filename = f"{user_id}_{project_name}.zip"
    zip_disk_path = os.path.join(PENDING_ZIPS_DIR, zip_filename)
    try:
        with open(zip_disk_path, 'wb') as f:
            f.write(entry['content'])
    except Exception as e:
        logger.error(f"❌ Could not save pending zip to disk for {user_id}/{project_name}: {e}")
        return
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute(
                '''INSERT OR REPLACE INTO pending_zips
                   (user_id, project_name, zip_path, file_name_zip, main_file, patterns, queued_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?)''',
                (user_id, project_name, zip_disk_path,
                 entry.get('file_name_zip', f"{project_name}.zip"),
                 entry.get('main_file'), _json.dumps(entry.get('patterns', [])),
                 datetime.now().isoformat())
            )
            conn.commit()
        except Exception as e:
            logger.error(f"❌ Error saving pending zip for {user_id}/{project_name}: {e}")
        finally:
            conn.close()

def remove_pending_zip_db(user_id, project_name):
    """Remove a pending zip entry from DB and delete the saved zip file."""
    zip_filename = f"{user_id}_{project_name}.zip"
    zip_disk_path = os.path.join(PENDING_ZIPS_DIR, zip_filename)
    try:
        if os.path.exists(zip_disk_path):
            os.remove(zip_disk_path)
    except Exception as e:
        logger.warning(f"Could not delete pending zip file {zip_disk_path}: {e}")
    with DB_LOCK:
        conn = sqlite3.connect(DATABASE_PATH, check_same_thread=False)
        try:
            conn.execute('DELETE FROM pending_zips WHERE user_id = ? AND project_name = ?',
                         (user_id, project_name))
            conn.commit()
        except Exception as e:
            logger.error(f"❌ Error removing pending zip for {user_id}/{project_name}: {e}")
        finally:
            conn.close()
def create_main_menu_inline(user_id):
    markup = types.InlineKeyboardMarkup(row_width=2)
    buttons = [
        make_colored_button('📢 Updates Channel', url=f'https://t.me/{UPDATES_CHANNEL.replace("@", "")}'),
        make_colored_button('📤 Upload File', callback_data='upload'),
        make_colored_button('📂 Check Files', callback_data='check_files'),
        make_colored_button('⚡ Bot Speed', callback_data='speed'),
        make_colored_button('📊 Statistics', callback_data='stats'),
        make_colored_button('📦 Manual Install', callback_data='manual_install'),
        make_colored_button('👤 My Info', callback_data='my_info'),
        make_colored_button('📞 Contact Owner', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}')
    ]
    if user_id in admin_ids:
        admin_buttons = [
            make_colored_button('💳 Subscriptions', callback_data='subscription'),        # 0
            make_colored_button('🔒 Lock Bot' if not bot_locked else '🔓 Unlock Bot',
                                       callback_data='lock_bot' if not bot_locked else 'unlock_bot'),  # 1
            make_colored_button('📢 Broadcast', callback_data='broadcast'),               # 2
            make_colored_button('👑 Admin Panel', callback_data='admin_panel'),           # 3
            make_colored_button('🟢 Run All Scripts', callback_data='run_all_scripts'),   # 4
            make_colored_button('👥 User Management', callback_data='user_management'),   # 5
            make_colored_button('📋 Pending Files', callback_data='pending_files'),       # 6
            make_colored_button('📢 Channel Add', callback_data='channel_add'),           # 7
        ]
        # Admin layout:
        # ["📢 Updates Channel"]
        # ["📤 Upload File",      "📂 Check Files"]
        # ["⚡ Bot Speed",        "📊 Statistics"]
        # ["💳 Subscriptions",   "📢 Broadcast"]
        # ["🔒 Lock Bot",        "🟢 Run All Scripts"]
        # ["👥 User Management", "📋 Pending Files"]
        # ["👑 Admin Panel",     "📦 Manual Install"]
        # ["📢 Channel Add",     "👤 My Info"]
        # ["📞 Contact Owner"]
        markup.add(buttons[0])
        markup.add(buttons[1], buttons[2])
        markup.add(buttons[3], buttons[4])
        markup.add(admin_buttons[0], admin_buttons[2])
        markup.add(admin_buttons[1], admin_buttons[4])
        markup.add(admin_buttons[5], admin_buttons[6])
        markup.add(admin_buttons[3], buttons[5])
        markup.add(admin_buttons[7], buttons[6])
        markup.add(buttons[7])
    else:
        # User layout:
        # ["📢 Updates Channel"]
        # ["📤 Upload File",     "📂 Check Files"]
        # ["⚡ Bot Speed",       "📊 Statistics"]
        # ["📦 Manual Install",  "👤 My Info"]
        # ["📞 Contact Owner"]
        markup.add(buttons[0])
        markup.add(buttons[1], buttons[2])
        markup.add(buttons[3], buttons[4])
        markup.add(buttons[5], buttons[6])
        markup.add(buttons[7])
    return markup

def create_reply_keyboard_main_menu(user_id):
    markup = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    if user_id in admin_ids:
        for row_buttons_text in ADMIN_COMMAND_BUTTONS_LAYOUT_USER_SPEC:
            # Dynamically swap the lock/unlock label based on current bot_locked state
            resolved = []
            for text in row_buttons_text:
                if text == "🔒 Lock Bot":
                    resolved.append("🔓 Unlock Bot" if bot_locked else "🔒 Lock Bot")
                else:
                    resolved.append(text)
            markup.add(*[types.KeyboardButton(t) for t in resolved])
    else:
        for row_buttons_text in COMMAND_BUTTONS_LAYOUT_USER_SPEC:
            markup.add(*[types.KeyboardButton(text) for text in row_buttons_text])
    return markup

def create_control_buttons(script_owner_id, project_name, is_running=True, back_callback='check_files'):
    markup = types.InlineKeyboardMarkup(row_width=2)
    if is_running:
        markup.row(
            make_colored_button("🔴 Stop", callback_data=f'stop_{script_owner_id}_{project_name}'),
            make_colored_button("🔄 Restart", callback_data=f'restart_{script_owner_id}_{project_name}')
        )
        markup.row(
            make_colored_button("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{project_name}'),
            make_colored_button("📜 Logs", callback_data=f'logs_{script_owner_id}_{project_name}')
        )
    else:
        markup.row(
            make_colored_button("🟢 Start", callback_data=f'start_{script_owner_id}_{project_name}'),
            make_colored_button("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{project_name}')
        )
        markup.row(
            make_colored_button("📜 View Logs", callback_data=f'logs_{script_owner_id}_{project_name}')
        )
    markup.row(
        make_colored_button("✏️ Change Main File", callback_data=f'changemain_{script_owner_id}_{project_name}')
    )
    back_label = "🔙 Back to Projects" if back_callback == 'check_files' else "🔙 Back to User's Projects"
    markup.add(make_colored_button(back_label, callback_data=back_callback))
    return markup

def _extract_back_callback(call):
    """Read the back button's callback_data from the current message's inline keyboard.
    This preserves the entry-point context (Check Files vs User Management) through
    all subsequent actions (start, stop, restart) without any extra state.
    Falls back to 'check_files' if the keyboard cannot be read.
    """
    try:
        keyboard = call.message.reply_markup
        if keyboard:
            for row in keyboard.keyboard:
                for btn in row:
                    if btn.callback_data and btn.callback_data.startswith('admin_user_files_'):
                        return btn.callback_data
    except Exception:
        pass
    return 'check_files'

def create_admin_panel():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        make_colored_button('➕ Add Admin', callback_data='add_admin'),
        make_colored_button('➖ Remove Admin', callback_data='remove_admin')
    )
    markup.row(make_colored_button('📋 List Admins', callback_data='list_admins'))
    markup.row(make_colored_button('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        make_colored_button('➕ Add Subscription', callback_data='add_subscription'),
        make_colored_button('➖ Remove Subscription', callback_data='remove_subscription')
    )
    markup.row(make_colored_button('🔍 Check Subscription', callback_data='check_subscription'))
    markup.row(make_colored_button('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_user_management_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.row(
        make_colored_button('🚫 Ban User', callback_data='ban_user'),
        make_colored_button('✅ Unban User', callback_data='unban_user')
    )
    markup.row(
        make_colored_button('👤 User Info', callback_data='user_info'),
        make_colored_button('👥 All Users', callback_data='all_users')
    )
    markup.row(
        make_colored_button('🔧 Set User Limit', callback_data='set_user_limit'),
        make_colored_button('🗑️ Remove User Limit', callback_data='remove_user_limit')
    )
    markup.row(make_colored_button('🔙 Back to Main', callback_data='back_to_main'))
    return markup

# ============================================================
# --- Package Installation ---
# ============================================================
# TELEGRAM_MODULES, attempt_install_pip, attempt_install_npm are defined
# above in the Manual Module Installation System section.


# ============================================================
# --- Script Running ---
# ============================================================
def run_script(script_path, script_owner_id, user_folder, project_name, message_obj_for_reply, attempt=1, skip_deps_install=False):
    max_attempts = 2
    if attempt > max_attempts:
        bot.reply_to(message_obj_for_reply, f"❌ Failed to run project `{project_name}` after {max_attempts} attempts.", parse_mode='Markdown')
        return
    script_key = f"{script_owner_id}_{project_name}"
    logger.info(f"Attempt {attempt} to run: {script_path} (Key: {script_key})")
    try:
        if not os.path.exists(script_path):
            bot.reply_to(message_obj_for_reply, f"❌ Script for `{project_name}` not found!", parse_mode='Markdown')
            remove_user_file_db(script_owner_id, project_name)
            return
        if attempt == 1:
            # Install requirements.txt if present and not already handled by caller
            if not skip_deps_install:
                if not install_requirements_if_present(user_folder, script_owner_id, message_obj_for_reply):
                    return  # Abort if deps failed to install
            check_proc = None
            try:
                check_proc = subprocess.Popen([sys.executable, script_path], cwd=user_folder,
                                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                              text=True, encoding='utf-8', errors='ignore',
                                              env=get_clean_env())
                stdout, stderr = check_proc.communicate(timeout=5)
                rc = check_proc.returncode
                if rc != 0 and stderr:
                    match = re.search(r"ModuleNotFoundError: No module named '(.+?)'", stderr)
                    if match:
                        module_name = match.group(1).strip()
                        if attempt_install_pip(module_name, message_obj_for_reply):
                            bot.reply_to(message_obj_for_reply, f"🔄 Package installed. Retrying `{project_name}`...", parse_mode='Markdown')
                            time.sleep(2)
                            threading.Thread(target=run_script,
                                             args=(script_path, script_owner_id, user_folder, project_name,
                                                   message_obj_for_reply, attempt + 1, True)).start()
                            return
                        else:
                            bot.reply_to(message_obj_for_reply, f"❌ Package install failed for `{project_name}`.", parse_mode='Markdown')
                            return
                    err_summary = stderr[:500]
                    bot.reply_to(message_obj_for_reply, f"❌ Error in `{project_name}`:\n```\n{err_summary}\n```", parse_mode='Markdown')
                    return
            except subprocess.TimeoutExpired:
                logger.info("Python pre-check timed out. Proceeding to long run.")
                if check_proc and check_proc.poll() is None: check_proc.kill(); check_proc.communicate()
            except FileNotFoundError:
                bot.reply_to(message_obj_for_reply, "❌ Python interpreter not found!")
                return
            except Exception as e:
                bot.reply_to(message_obj_for_reply, f"❌ Pre-check error: {e}")
                return
            finally:
                if check_proc and check_proc.poll() is None:
                    check_proc.kill(); check_proc.communicate()

        log_file_path = os.path.join(user_folder, f"{project_name}.log")
        log_file = None
        try:
            log_file = open(log_file_path, 'w', encoding='utf-8', errors='ignore')
        except Exception as e:
            bot.reply_to(message_obj_for_reply, f"❌ Failed to open log file: {e}")
            return
        try:
            startupinfo = None; creationflags = 0
            if os.name == 'nt':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
            process = subprocess.Popen(
                [sys.executable, script_path], cwd=user_folder,
                stdout=log_file, stderr=log_file, stdin=subprocess.PIPE,
                startupinfo=startupinfo, creationflags=creationflags,
                encoding='utf-8', errors='ignore',
                env=get_clean_env()
            )
            bot_scripts[script_key] = {
                'process': process, 'log_file': log_file, 'project_name': project_name,
                'chat_id': message_obj_for_reply.chat.id, 'script_owner_id': script_owner_id,
                'start_time': datetime.now(), 'user_folder': user_folder,
                'type': 'py', 'script_key': script_key
            }
            bot.reply_to(message_obj_for_reply, f"✅ Project `{project_name}` started! (PID: {process.pid})", parse_mode='Markdown')
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            bot.reply_to(message_obj_for_reply, f"❌ Error starting `{project_name}`: {md_escape(e)}", parse_mode='Markdown')
            if script_key in bot_scripts: del bot_scripts[script_key]
    except Exception as e:
        bot.reply_to(message_obj_for_reply, f"❌ Unexpected error running `{project_name}`: {md_escape(e)}", parse_mode='Markdown')
        if script_key in bot_scripts:
            kill_process_tree(bot_scripts[script_key])
            del bot_scripts[script_key]

def run_js_script(script_path, script_owner_id, user_folder, project_name, message_obj_for_reply, attempt=1, skip_deps_install=False):
    max_attempts = 2
    if attempt > max_attempts:
        bot.reply_to(message_obj_for_reply, f"❌ Failed to run `{project_name}` after {max_attempts} attempts.", parse_mode='Markdown')
        return
    script_key = f"{script_owner_id}_{project_name}"
    logger.info(f"Attempt {attempt} to run JS: {script_path} (Key: {script_key})")
    try:
        if not os.path.exists(script_path):
            bot.reply_to(message_obj_for_reply, f"❌ Script `{project_name}` not found!", parse_mode='Markdown')
            remove_user_file_db(script_owner_id, project_name)
            return
        if attempt == 1:
            # Install package.json deps if present and not already handled by caller
            if not skip_deps_install:
                if not install_package_json_if_present(user_folder, script_owner_id, message_obj_for_reply):
                    return  # Abort if deps failed to install
            check_proc = None
            try:
                check_proc = subprocess.Popen(['node', script_path], cwd=user_folder,
                                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                              text=True, encoding='utf-8', errors='ignore',
                                              env=get_clean_env())
                stdout, stderr = check_proc.communicate(timeout=5)
                rc = check_proc.returncode
                if rc != 0 and stderr:
                    match_js = re.search(r"Cannot find module '(.+?)'", stderr)
                    if match_js:
                        module_name = match_js.group(1).strip().strip("'\"")
                        if not module_name.startswith('.') and not module_name.startswith('/'):
                            if attempt_install_npm(module_name, user_folder, message_obj_for_reply):
                                bot.reply_to(message_obj_for_reply, f"🔄 NPM Install OK. Retrying `{project_name}`...", parse_mode='Markdown')
                                time.sleep(2)
                                threading.Thread(target=run_js_script,
                                                 args=(script_path, script_owner_id, user_folder, project_name,
                                                       message_obj_for_reply, attempt + 1, True)).start()
                                return
                            else:
                                bot.reply_to(message_obj_for_reply, f"❌ NPM Install failed for `{project_name}`.", parse_mode='Markdown')
                                return
                    err_summary = stderr[:500]
                    bot.reply_to(message_obj_for_reply, f"❌ JS error in `{project_name}`:\n```\n{err_summary}\n```", parse_mode='Markdown')
                    return
            except subprocess.TimeoutExpired:
                if check_proc and check_proc.poll() is None: check_proc.kill(); check_proc.communicate()
            except FileNotFoundError:
                bot.reply_to(message_obj_for_reply, "❌ `node` not found. Install Node.js.", parse_mode='Markdown')
                return
            except Exception as e:
                bot.reply_to(message_obj_for_reply, f"❌ JS pre-check error: {e}")
                return
            finally:
                if check_proc and check_proc.poll() is None: check_proc.kill(); check_proc.communicate()

        log_file_path = os.path.join(user_folder, f"{project_name}.log")
        log_file = None
        try:
            log_file = open(log_file_path, 'w', encoding='utf-8', errors='ignore')
        except Exception as e:
            bot.reply_to(message_obj_for_reply, f"❌ Failed to open log file: {e}")
            return
        try:
            startupinfo = None; creationflags = 0
            if os.name == 'nt':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
            process = subprocess.Popen(
                ['node', script_path], cwd=user_folder,
                stdout=log_file, stderr=log_file, stdin=subprocess.PIPE,
                startupinfo=startupinfo, creationflags=creationflags,
                encoding='utf-8', errors='ignore',
                env=get_clean_env()
            )
            bot_scripts[script_key] = {
                'process': process, 'log_file': log_file, 'project_name': project_name,
                'chat_id': message_obj_for_reply.chat.id, 'script_owner_id': script_owner_id,
                'start_time': datetime.now(), 'user_folder': user_folder,
                'type': 'js', 'script_key': script_key
            }
            bot.reply_to(message_obj_for_reply, f"✅ JS project `{project_name}` started! (PID: {process.pid})", parse_mode='Markdown')
        except FileNotFoundError:
            if log_file and not log_file.closed: log_file.close()
            bot.reply_to(message_obj_for_reply, "❌ `node` not found for long run.", parse_mode='Markdown')
            if script_key in bot_scripts: del bot_scripts[script_key]
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            bot.reply_to(message_obj_for_reply, f"❌ Error starting `{project_name}`: {md_escape(e)}", parse_mode='Markdown')
            if script_key in bot_scripts: del bot_scripts[script_key]
    except Exception as e:
        bot.reply_to(message_obj_for_reply, f"❌ Unexpected error running `{project_name}`: {md_escape(e)}", parse_mode='Markdown')
        if script_key in bot_scripts:
            kill_process_tree(bot_scripts[script_key])
            del bot_scripts[script_key]

# ============================================================
# --- File Handling ---
# ============================================================
def process_zip_file(file_content, file_name_zip, user_id, user_folder, message, project_name=None, main_file_override=None):
    """Extract and run a pre-approved ZIP. Called after admin approval — no security scan."""
    temp_dir = None
    try:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_run_")
        zip_path = os.path.join(temp_dir, file_name_zip)
        with open(zip_path, 'wb') as f: f.write(file_content)

        # Safe extraction
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            for member in zip_ref.infolist():
                member_path = os.path.abspath(os.path.join(temp_dir, member.filename))
                if not member_path.startswith(os.path.abspath(temp_dir)):
                    raise zipfile.BadZipFile(f"Unsafe path: {member.filename}")
            zip_ref.extractall(temp_dir)

        extracted_items = [f for f in os.listdir(temp_dir) if f != file_name_zip]
        py_files = [f for f in extracted_items if f.endswith('.py')]
        js_files = [f for f in extracted_items if f.endswith('.js')]
        req_file = 'requirements.txt' if 'requirements.txt' in extracted_items else None
        pkg_json = 'package.json' if 'package.json' in extracted_items else None

        if req_file:
            req_path = os.path.join(temp_dir, req_file)
            bot.send_message(user_id, f"🔄 Installing Python deps from `{req_file}`...", parse_mode='Markdown')
            try:
                subprocess.run([sys.executable, '-m', 'pip', 'install', '-r', req_path],
                               capture_output=True, text=True, check=True, encoding='utf-8',
                               env=get_clean_env())
                bot.send_message(user_id, f"✅ Python deps from `{req_file}` installed.", parse_mode='Markdown')
            except subprocess.CalledProcessError as e:
                bot.send_message(user_id, f"❌ Failed to install Python deps.\n```\n{(e.stderr or e.stdout)[:2000]}\n```", parse_mode='Markdown'); return
            except Exception as e:
                bot.send_message(user_id, f"❌ Error installing Python deps: {e}"); return

        if pkg_json:
            bot.send_message(user_id, f"🔄 Installing Node deps from `{pkg_json}`...", parse_mode='Markdown')
            try:
                subprocess.run(['npm', 'install'], capture_output=True, text=True,
                               check=True, cwd=temp_dir, encoding='utf-8',
                               env=get_clean_env())
                bot.send_message(user_id, f"✅ Node deps from `{pkg_json}` installed.", parse_mode='Markdown')
            except FileNotFoundError:
                bot.send_message(user_id, "❌ `npm` not found.", parse_mode='Markdown'); return
            except subprocess.CalledProcessError as e:
                bot.send_message(user_id, f"❌ Failed Node deps.\n```\n{(e.stderr or e.stdout)[:2000]}\n```", parse_mode='Markdown'); return
            except Exception as e:
                bot.send_message(user_id, f"❌ Error installing Node deps: {e}"); return

        # Determine main script
        if main_file_override:
            main_script_name = main_file_override
            file_type = 'py' if main_script_name.endswith('.py') else 'js'
        else:
            main_script_name = None; file_type = None
            preferred_py = ['main.py', 'bot.py', 'app.py']
            preferred_js = ['index.js', 'main.js', 'bot.js', 'app.js']
            for p in preferred_py:
                if p in py_files: main_script_name = p; file_type = 'py'; break
            if not main_script_name:
                for p in preferred_js:
                    if p in js_files: main_script_name = p; file_type = 'js'; break
            if not main_script_name:
                if py_files: main_script_name = py_files[0]; file_type = 'py'
                elif js_files: main_script_name = js_files[0]; file_type = 'js'
        if not main_script_name:
            bot.send_message(user_id, "❌ No `.py` or `.js` script found in archive!", parse_mode='Markdown'); return

        # Use project_name as folder, fallback to zip stem
        if not project_name:
            project_name = os.path.splitext(file_name_zip)[0]
        project_folder = get_user_folder(user_id, project_name)

        for item_name in extracted_items:
            src = os.path.join(temp_dir, item_name)
            dst = os.path.join(project_folder, item_name)
            if os.path.isdir(dst): shutil.rmtree(dst)
            elif os.path.exists(dst): os.remove(dst)
            shutil.move(src, dst)

        save_user_file(user_id, project_name, main_script_name, file_type)
        main_script_path = os.path.join(project_folder, main_script_name)
        bot.send_message(user_id, f"✅ Project `{project_name}` extracted. Starting `{main_script_name}`...", parse_mode='Markdown')
        if file_type == 'py':
            threading.Thread(target=run_script, args=(main_script_path, user_id, project_folder, project_name, message)).start()
        elif file_type == 'js':
            threading.Thread(target=run_js_script, args=(main_script_path, user_id, project_folder, project_name, message)).start()

    except zipfile.BadZipFile as e:
        bot.send_message(user_id, f"❌ Invalid/corrupted ZIP: {e}")
    except Exception as e:
        logger.error(f"❌ Error processing approved zip for {user_id}: {e}", exc_info=True)
        bot.send_message(user_id, f"❌ Error processing zip: {str(e)}")
    finally:
        if temp_dir and os.path.exists(temp_dir):
            try: shutil.rmtree(temp_dir)
            except Exception: pass


def handle_js_file(file_path, script_owner_id, user_folder, file_name, message, project_name=None):
    if not project_name:
        project_name = os.path.splitext(file_name)[0]
    try:
        save_user_file(script_owner_id, project_name, file_name, 'js')
        # Single-file project: no package.json, so scan require() calls and auto-install
        auto_install_js_requires(file_path, user_folder, script_owner_id, message)
        # skip_deps_install=True because we just handled it above
        threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, project_name, message, 1, True)).start()
    except Exception as e:
        bot.reply_to(message, f"❌ Error processing JS file: {e}")

def handle_py_file(file_path, script_owner_id, user_folder, file_name, message, project_name=None):
    if not project_name:
        project_name = os.path.splitext(file_name)[0]
    try:
        save_user_file(script_owner_id, project_name, file_name, 'py')
        # Single-file project: no requirements.txt, so scan imports and auto-install
        auto_install_py_imports(file_path, user_folder, script_owner_id, message)
        # skip_deps_install=True because we just handled it above
        threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, project_name, message, 1, True)).start()
    except Exception as e:
        bot.reply_to(message, f"❌ Error processing Python file: {e}")

# ============================================================
# --- Logic Functions ---
# ============================================================
def _logic_send_welcome(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    user_name = message.from_user.first_name
    user_username = message.from_user.username
    photo_file_id = None

    if is_user_banned(user_id):
        bot.send_message(chat_id, "🚫 You are banned from using this bot.")
        return

    if not check_force_join(message):
        return

    if bot_locked and user_id not in admin_ids:
        bot.send_message(chat_id, "🔒 *Bot Temporarily Locked*\n\nThe admin has disabled the bot. Please try again later.", parse_mode='Markdown')
        return

    # Re-register users who exist in DB (have files) but not in active_users in memory
    # This happens when the bot is restarted without persistent state in memory
    if user_id not in active_users:
        add_active_user(user_id)
        # Only notify owner about brand-new users (not re-registrations)
        if user_id not in user_files:
            user_bio = "No bio"
            photo_file_id = None
            try: user_bio = bot.get_chat(user_id).bio or "No bio"
            except Exception: pass
            try:
                photos = bot.get_user_profile_photos(user_id, limit=1)
                if photos.photos: photo_file_id = photos.photos[0][-1].file_id
            except Exception: pass
            try:
                def _md_escape(text):
                    for ch in ['\\', '_', '*', '`', '[']:
                        text = text.replace(ch, '\\' + ch)
                    return text
                safe_name = _md_escape(str(user_name))
                safe_username = _md_escape(str(user_username)) if user_username else 'N/A'
                safe_bio = _md_escape(str(user_bio))
                notif = (
                    f"🎉 *New User Joined!*\n"
                    f"──────────────────────\n\n"
                    f"👤 *Name:* {safe_name}\n"
                    f"✳️ *Username:* @{safe_username}\n"
                    f"🆔 *ID:* `{user_id}`\n"
                    f"📝 *Bio:* {safe_bio}\n"
                    f"──────────────────────")
                bot.send_message(OWNER_ID, notif, parse_mode='Markdown')
                if photo_file_id: bot.send_photo(OWNER_ID, photo_file_id, caption=f"New user {user_id}")
            except Exception as e: logger.error(f"Failed to notify owner: {e}")

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    expiry_info = ""
    if user_id == OWNER_ID: user_status = "👑 Owner"
    elif user_id in admin_ids: user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"
            days_left = (expiry_date - datetime.now()).days
            expiry_info = f"\n⏳ Subscription expires in: *{days_left} days*"
        else:
            user_status = "🆓 Free User"
            remove_subscription_db(user_id)
    else: user_status = "🆓 Free User"

    welcome_msg = (
        f"╔═════════════════════╗\n"
        f"      🚀 *Astroneth Hosting*\n"
        f"╚═════════════════════╝\n"
        f"👋 Hey *{user_name}*, welcome back!\n\n"
        f"──────────────────────\n"
        f"🆔 *ID:* `{user_id}`\n"
        f"✳️ *Username:* `@{user_username or 'Not set'}`\n"
        f"🏖️ *Rank:* {user_status}{expiry_info}\n"
        f"📁 *Projects:* `{current_files}` / `{limit_str}`\n"
        f"──────────────────────\n\n"
        f"⚡ *What can I do for you?*\n"
        f"› Upload `.py` / `.js` scripts or `.zip` archives\n"
        f"› Run & manage your bots 24/7\n"
        f"› Auto-install missing packages\n\n"
        f"👇 *Tap a button below to get started!*"
    )
    main_reply_markup = create_reply_keyboard_main_menu(user_id)
    try:
        if photo_file_id:
            bot.send_photo(chat_id, photo_file_id, caption=welcome_msg,
                           reply_markup=main_reply_markup, parse_mode='Markdown')
        else:
            bot.send_message(chat_id, welcome_msg, reply_markup=main_reply_markup, parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error sending welcome to {user_id}: {e}")
        try: bot.send_message(chat_id, welcome_msg, reply_markup=main_reply_markup, parse_mode='Markdown')
        except Exception as fe: logger.error(f"Fallback send_message failed: {fe}")

def _logic_updates_channel(message):
    bot.reply_to(
        message,
        "📣 *Stay in the loop!*\n\n"
        "Get notified about:\n"
        "› 🆕 New features & updates\n"
        "› 🐛 Bug fixes & patches\n"
        "› 📢 Important announcements\n\n"
        "👇 Hit the button to join now!",
        parse_mode='Markdown',
        reply_markup=types.InlineKeyboardMarkup().add(
            make_colored_button("🚀 Join Updates Channel", url=f'https://t.me/{UPDATES_CHANNEL.replace("@", "")}')
        )
    )

def _logic_upload_file(message):
    user_id = message.from_user.id
    if is_user_banned(user_id):
        bot.reply_to(message, "🚫 You are banned from using this bot.")
        return
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "🔒 *Bot Temporarily Locked*\n\nFile uploads are disabled. Please try again later.", parse_mode='Markdown')
        return
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.reply_to(message, f"⚠️ File limit reached (`{current_files}/{limit_str}`). Delete files first.", parse_mode='Markdown')
        return
    bot.reply_to(message,
        "📤 *Upload Your Project*\n\n"
        "Send one of the following:\n"
        "🐍 `.py` — Python script\n"
        "🟨 `.js` — Node.js script\n"
        "🗜️ `.zip` — Full project archive\n\n"
        "💡 _All projects support_ `requirements.txt` _&_ `package.json` _— deps auto-reinstall on restart._",
        parse_mode='Markdown')

def _logic_check_files(message):
    user_id = message.from_user.id
    user_files_list = user_files.get(user_id, [])
    if not user_files_list:
        bot.reply_to(message, "📂 *Your Projects*\n\n_You have no projects yet._\n\nUse 📤 *Upload File* to add your first script!", parse_mode='Markdown')
        return
    markup = types.InlineKeyboardMarkup(row_width=1)
    for project_name, main_file, file_type in sorted(user_files_list):
        is_running = is_bot_running(user_id, project_name)
        status_icon = "🟢" if is_running else "🔴"
        markup.add(make_colored_button(f"{status_icon} {project_name}", callback_data=f'file_{user_id}_{project_name}'))
    bot.reply_to(message, "📂 *Your projects:*\nTap to manage.", reply_markup=markup, parse_mode='Markdown')

def _logic_bot_speed(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    start_time_ping = time.time()
    wait_msg = bot.reply_to(message, "🏃 Testing speed...")
    try:
        bot.send_chat_action(chat_id, 'typing')
        response_time = round((time.time() - start_time_ping) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now():
            user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        rating = "✅ Excellent" if response_time < 300 else ("⚠️ Moderate" if response_time < 800 else "🔴 Slow")
        speed_msg = (
            f"⚡ *Bot Speed & Status*\n"
            f"──────────────────────\n\n"
            f"🏓 *API Response:* `{response_time} ms` {rating}\n"
            f"🚦 *Bot Status:* {status}\n"
            f"🏖️ *Your Rank:* {user_level}\n"
            f"──────────────────────")
        bot.edit_message_text(speed_msg, chat_id, wait_msg.message_id, parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error during speed test: {e}")
        bot.edit_message_text("❌ Error during speed test.", chat_id, wait_msg.message_id)

def _logic_contact_owner(message):
    markup = types.InlineKeyboardMarkup()
    markup.add(make_colored_button('💬 Chat with Owner', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
    bot.reply_to(message,
        "📞 *Contact the Owner*\n\n"
        "Have a question, issue, or suggestion?\n"
        "The owner is ready to help you! 👇",
        reply_markup=markup, parse_mode='Markdown')

def _logic_my_info(message):
    user_id = message.from_user.id
    user_name = message.from_user.first_name or "User"
    user_username = message.from_user.username
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
            hours_left = int(((expiry_date - datetime.now()).seconds) / 3600)
            expiry_info = f"\n⏳ *Subscription Expiry:* {expiry_date.strftime('%Y-%m-%d %H:%M')} UTC\n📅 *Days Remaining:* `{days_left}d {hours_left}h`"
        else:
            user_status = "🆓 Free User"
            remove_subscription_db(user_id)
    else:
        user_status = "🆓 Free User"
    running_count = sum(
        1 for sk in list(bot_scripts.keys())
        if sk.startswith(f"{user_id}_") and is_bot_running(user_id, sk.split('_', 1)[1])
    )
    is_banned = "🚫 Yes" if is_user_banned(user_id) else "✅ No"
    info_msg = (
        f"👤 *My Profile*\n"
        f"──────────────────────\n\n"
        f"🆔 *User ID:* `{user_id}`\n"
        f"📛 *Name:* {user_name}\n"
        f"✳️ *Username:* `@{user_username or 'Not set'}`\n"
        f"🏖️ *Rank:* {user_status}{expiry_info}\n"
        f"🚫 *Banned:* {is_banned}\n\n"
        f"──────────────────────\n"
        f"📁 *Projects:* `{current_files} / {limit_str}`\n"
        f"🟢 *Running Scripts:* `{running_count}`\n"
        f"──────────────────────"
    )
    markup = types.InlineKeyboardMarkup()
    markup.add(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))
    bot.reply_to(message, info_msg, reply_markup=markup, parse_mode='Markdown')

def _logic_subscriptions_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "💳 *Subscription Management*", reply_markup=create_subscription_menu(), parse_mode='Markdown')

def _format_uptime(seconds: float) -> str:
    """Formats a duration in seconds to  Xd Xh Xm Xs."""
    total = int(seconds)
    d, rem  = divmod(total, 86400)
    h, rem  = divmod(rem,   3600)
    m, s    = divmod(rem,   60)
    parts = []
    if d: parts.append(f"{d}d")
    if h: parts.append(f"{h}h")
    if m: parts.append(f"{m}m")
    parts.append(f"{s}s")
    return " ".join(parts)

def _logic_statistics(message):
    user_id = message.from_user.id
    total_users = len(active_users)
    total_files = sum(len(f) for f in user_files.values())
    running_count = 0
    user_running = 0
    for sk, si in list(bot_scripts.items()):
        owner_id_str = sk.split('_', 1)[0]
        if is_bot_running(int(owner_id_str), si['project_name']):
            running_count += 1
            if int(owner_id_str) == user_id: user_running += 1

    uptime_str = _format_uptime(time.time() - BOT_START_TIME)

    stats_msg = (
        f"📊 *Bot Statistics*\n"
        f"──────────────────────\n\n"
        f"👥 *Total Users:* `{total_users}`\n"
        f"🚫 *Banned Users:* `{len(banned_users)}`\n\n"
        f"📂 *Total Projects:* `{total_files}`\n"
        f"🟢 *Running Bots:* `{running_count}`\n"
        f"🤖 *Your Running Bots:* `{user_running}`\n\n"
        f"⏱️ *Uptime:* `{uptime_str}`\n"
        f"🔒 *Status:* {'🔴 Locked' if bot_locked else '🟢 Unlocked'}\n"
        f"──────────────────────")
    try:
        bot.reply_to(message, stats_msg, parse_mode='Markdown')
    except Exception:
        # Strip Markdown and retry as plain text on connection/parse errors
        plain = stats_msg.replace('*', '').replace('`', '').replace('_', '')
        try: bot.reply_to(message, plain)
        except Exception as e: logger.error(f"Stats send failed: {e}")

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
    status = "locked 🔒" if bot_locked else "unlocked 🔓"
    logger.warning(f"Bot {status} by Admin {message.from_user.id}")
    bot.reply_to(message, f"Bot has been *{status}*.", parse_mode='Markdown',
                 reply_markup=create_reply_keyboard_main_menu(message.from_user.id))

def _logic_admin_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "👑 *Admin Panel*\nManage admins.", reply_markup=create_admin_panel(), parse_mode='Markdown')

def _logic_run_all_scripts(message_or_call):
    if isinstance(message_or_call, telebot.types.Message):
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.chat.id
        reply_func = lambda text, **kw: bot.reply_to(message_or_call, text, **kw)
        admin_msg_obj = message_or_call
    elif isinstance(message_or_call, telebot.types.CallbackQuery):
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.message.chat.id
        bot.answer_callback_query(message_or_call.id)
        reply_func = lambda text, **kw: bot.send_message(admin_chat_id, text, **kw)
        admin_msg_obj = message_or_call.message
    else: return

    if admin_user_id not in admin_ids:
        reply_func("⚠️ Admin permissions required.")
        return

    reply_func("⏳ Starting all user scripts... (installing deps where needed)")
    started_count = 0; skipped_files = 0

    def _start_one(target_user_id, project_name, main_file, file_type, user_folder, file_path):
        """Run in a thread: install deps then start the project."""
        try:
            if file_type == 'py':
                if not install_requirements_if_present(user_folder, target_user_id, admin_msg_obj):
                    return
                run_script(file_path, target_user_id, user_folder, project_name, admin_msg_obj,
                           attempt=1, skip_deps_install=True)
            elif file_type == 'js':
                if not install_package_json_if_present(user_folder, target_user_id, admin_msg_obj):
                    return
                run_js_script(file_path, target_user_id, user_folder, project_name, admin_msg_obj,
                              attempt=1, skip_deps_install=True)
        except Exception as e:
            logger.error(f"Error starting {project_name} for {target_user_id}: {e}")

    all_user_files_snapshot = dict(user_files)
    for target_user_id, files_for_user in all_user_files_snapshot.items():
        if not files_for_user: continue
        for project_name, main_file, file_type in files_for_user:
            if not is_bot_running(target_user_id, project_name):
                user_folder = get_user_folder(target_user_id, project_name)
                file_path = os.path.join(user_folder, main_file)
                if os.path.exists(file_path):
                    try:
                        threading.Thread(
                            target=_start_one,
                            args=(target_user_id, project_name, main_file, file_type, user_folder, file_path)
                        ).start()
                        started_count += 1
                        time.sleep(0.5)
                    except Exception as e:
                        skipped_files += 1
                        logger.error(f"Error starting {project_name} for {target_user_id}: {e}")
                else:
                    skipped_files += 1

    reply_func(f"✅ Run All Scripts Complete!\n▶️ Started: `{started_count}`\n⚠️ Skipped: `{skipped_files}`", parse_mode='Markdown')

def _logic_user_management(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    bot.reply_to(message, "👥 *User Management*\nSelect an action:", reply_markup=create_user_management_menu(), parse_mode='Markdown')

def _logic_pending_files(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    _show_pending_files(message.chat.id, message_id=None)

def _logic_view_user_files(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    msg = bot.reply_to(message, "🔍 Enter the User ID to view their files:\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_view_user_files_id)

def process_view_user_files_id(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Not authorized.")
        return
    if message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Cancelled.")
        return
    try:
        target_user_id = int(message.text.strip())
        if target_user_id <= 0: raise ValueError("ID must be positive")
        _show_user_files_admin(message, target_user_id)
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Must be a number.")
    except Exception as e:
        bot.reply_to(message, f"❌ Error: {e}")

def _show_user_files_admin(message_or_call, target_user_id):
    """Show files of any user to admin (send as new message)."""
    chat_id = message_or_call.chat.id if hasattr(message_or_call, 'chat') else message_or_call.message.chat.id
    files_list = user_files.get(target_user_id, [])
    if not files_list:
        bot.send_message(chat_id, f"📂 User `{target_user_id}` has no projects.", parse_mode='Markdown')
        return
    markup = types.InlineKeyboardMarkup(row_width=1)
    for project_name, main_file, file_type in sorted(files_list):
        is_running = is_bot_running(target_user_id, project_name)
        status_icon = "🟢" if is_running else "🔴"
        btn_text = f"{status_icon} {project_name}"
        markup.add(make_colored_button(btn_text, callback_data=f'umfile_{target_user_id}_{project_name}'))
    bot.send_message(chat_id, f"📂 *Projects for User* `{target_user_id}`:\nTap to manage.", reply_markup=markup, parse_mode='Markdown')

# ============================================================
# --- Broadcast ---
# ============================================================
def process_broadcast_message(message):
    user_id = message.from_user.id
    if user_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, "❌ Broadcast cancelled."); return
    broadcast_content = message.text
    if not broadcast_content and not (message.photo or message.video or message.document):
        bot.reply_to(message, "⚠️ Cannot broadcast empty message. Or /cancel.")
        msg = bot.send_message(message.chat.id, "📢 Send broadcast message or /cancel.")
        bot.register_next_step_handler(msg, process_broadcast_message)
        return
    target_count = len(active_users)
    markup = types.InlineKeyboardMarkup()
    markup.row(make_colored_button("✅ Confirm & Send", callback_data=f"confirm_broadcast_{message.message_id}"),
               make_colored_button("❌ Cancel", callback_data="cancel_broadcast"))
    preview_text = broadcast_content[:1000].strip() if broadcast_content else "(Media message)"
    bot.reply_to(message, f"⚠️ *Confirm Broadcast*\n\n```\n{preview_text}\n```\nTo *{target_count}* users. Sure?",
                 reply_markup=markup, parse_mode='Markdown')

def handle_confirm_broadcast(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    if user_id not in admin_ids: bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True); return
    try:
        original_message = call.message.reply_to_message
        if not original_message: raise ValueError("Could not retrieve original message.")
        broadcast_text = None; broadcast_photo_id = None; broadcast_video_id = None
        if original_message.text: broadcast_text = original_message.text
        elif original_message.photo: broadcast_photo_id = original_message.photo[-1].file_id
        elif original_message.video: broadcast_video_id = original_message.video.file_id
        else: raise ValueError("No supported content for broadcast.")
        bot.answer_callback_query(call.id, "🚀 Starting broadcast...")
        bot.edit_message_text(f"📢 Broadcasting to {len(active_users)} users...", chat_id, call.message.message_id)
        threading.Thread(target=execute_broadcast,
                         args=(broadcast_text, broadcast_photo_id, broadcast_video_id,
                               original_message.caption if (broadcast_photo_id or broadcast_video_id) else None,
                               chat_id)).start()
    except ValueError as ve:
        bot.edit_message_text(f"❌ Broadcast error: {ve}", chat_id, call.message.message_id)
    except Exception as e:
        logger.error(f"Error in handle_confirm_broadcast: {e}", exc_info=True)
        bot.edit_message_text("❌ Unexpected error during broadcast.", chat_id, call.message.message_id)

def handle_cancel_broadcast(call):
    bot.answer_callback_query(call.id, "❌ Broadcast cancelled.")
    bot.delete_message(call.message.chat.id, call.message.message_id)
    if call.message.reply_to_message:
        try: bot.delete_message(call.message.chat.id, call.message.reply_to_message.message_id)
        except Exception: pass

def execute_broadcast(broadcast_text, photo_id, video_id, caption, admin_chat_id):
    sent_count = 0; failed_count = 0; blocked_count = 0
    start_time = time.time()
    users_to_broadcast = list(active_users)
    total = len(users_to_broadcast)
    batch_size = 25; delay_batches = 1.5
    for i, uid in enumerate(users_to_broadcast):
        try:
            if broadcast_text: bot.send_message(uid, broadcast_text, parse_mode='Markdown')
            elif photo_id: bot.send_photo(uid, photo_id, caption=caption, parse_mode='Markdown' if caption else None)
            elif video_id: bot.send_video(uid, video_id, caption=caption, parse_mode='Markdown' if caption else None)
            sent_count += 1
        except telebot.apihelper.ApiTelegramException as e:
            err = str(e).lower()
            if any(s in err for s in ["bot was blocked", "user is deactivated", "chat not found"]): blocked_count += 1
            elif "flood control" in err or "too many requests" in err:
                retry_after = 5
                match = re.search(r"retry after (\d+)", err)
                if match: retry_after = int(match.group(1)) + 1
                time.sleep(retry_after)
                try:
                    if broadcast_text: bot.send_message(uid, broadcast_text, parse_mode='Markdown')
                    elif photo_id: bot.send_photo(uid, photo_id, caption=caption)
                    sent_count += 1
                except Exception: failed_count += 1
            else: failed_count += 1
        except Exception: failed_count += 1
        if (i + 1) % batch_size == 0 and i < total - 1: time.sleep(delay_batches)
        elif i % 5 == 0: time.sleep(0.2)
    duration = round(time.time() - start_time, 2)
    result = (f"📢 *Broadcast Complete!*\n\n✅ Sent: `{sent_count}`\n❌ Failed: `{failed_count}`\n"
              f"🚫 Blocked/Inactive: `{blocked_count}`\n👥 Targets: `{total}`\n⏱️ Duration: `{duration}s`")
    try: bot.send_message(admin_chat_id, result, parse_mode='Markdown')
    except Exception as e: logger.error(f"Failed to send broadcast result: {e}")

# ============================================================
# --- Command Handlers ---
# ============================================================
@bot.message_handler(commands=['start'])
def command_send_welcome(message): _logic_send_welcome(message)

@bot.message_handler(commands=['help'])
def command_help(message): _logic_help(message)

@bot.message_handler(commands=['status'])
def command_show_status(message): _logic_statistics(message)

@bot.message_handler(commands=['ping'])
def ping(message):
    start_ping_time = time.time()
    msg = bot.reply_to(message, "Pong!")
    latency = round((time.time() - start_ping_time) * 1000, 2)
    bot.edit_message_text(f"🏓 Pong! Latency: `{latency} ms`", message.chat.id, msg.message_id, parse_mode='Markdown')

def _logic_help(message):
    help_msg = (
        "       📖 Help & Guide\n"
        "──────────────────────\n"
        "🤖 *Astroneth Hosting* runs your Telegram bots 24/7 — just upload and go!\n\n"
        "──────────────────────\n"
        "⚡ *Quick Commands*\n\n"
        "📤 `/uploadfile` — Upload a script\n"
        "📂 `/checkfiles` — Manage your bots\n"
        "📦 `/manualinstall` — Install a package\n"
        "👤 `/myinfo` — Your profile & usage\n"
        "🏓 `/ping` — Check response speed\n\n"
        "──────────────────────\n"
        "📁 *Supported Formats*\n\n"
        "🐍 `.py` — Python scripts\n"
        "🟨 `.js` — Node.js scripts\n"
        "📦 `.zip` — Full projects with multiple files"
    )
    bot.reply_to(message, help_msg, parse_mode='Markdown')

def _logic_channel_add(message, override_user_id=None):
    """Admin-only: manage mandatory join channels."""
    check_id = override_user_id if override_user_id is not None else message.from_user.id
    if check_id not in admin_ids:
        bot.reply_to(message, "⚠️ Admin permissions required.")
        return
    markup = types.InlineKeyboardMarkup(row_width=1)
    if force_join_channels:
        for e in force_join_channels:
            markup.add(make_colored_button(
                f"🔴 Remove {e['title']}",
                callback_data=f"remove_force_join_{e['channel']}"))
    markup.add(make_colored_button("➕ Add Channel", callback_data="set_force_join"))
    if force_join_channels:
        ch_list = '\n'.join(f"  {i+1}. *{e['title']}*" for i, e in enumerate(force_join_channels))
        status = (
            f"🔒 *Access restricted — {len(force_join_channels)} channel(s) active.*\n"
            f"Users must join all channels before using this bot.\n\n"
            f"──────────────────────\n"
            f"📋 *Required Channels:*\n{ch_list}\n\n"
            f"──────────────────────\n"
            f"👇 Manage channels below:"
        )
    else:
        status = (
            "🔕 *No channels active.*\n"
            "Users can access the bot freely.\n\n"
            "──────────────────────\n"
            "👇 Add a channel to restrict access:"
        )
    bot.reply_to(
        message,
        f"   📢 Force Join Channels\n"
        f"──────────────────────\n"
        f"{status}",
        parse_mode='Markdown',
        reply_markup=markup
    )

BUTTON_TEXT_TO_LOGIC = {
    "📢 Updates Channel": _logic_updates_channel,
    "📤 Upload File": _logic_upload_file,
    "📂 Check Files": _logic_check_files,
    "⚡ Bot Speed": _logic_bot_speed,
    "📞 Contact Owner": _logic_contact_owner,
    "📊 Statistics": _logic_statistics,
    "💳 Subscriptions": _logic_subscriptions_panel,
    "📢 Broadcast": _logic_broadcast_init,
    "🔒 Lock Bot": _logic_toggle_lock_bot,
    "🔓 Unlock Bot": _logic_toggle_lock_bot,
    "🟢 Run All Code": _logic_run_all_scripts,
    "👑 Admin Panel": _logic_admin_panel,
    "👥 User Management": _logic_user_management,
    "📋 Pending Files": _logic_pending_files,
    "📦 Manual Install": _logic_manual_install,
    "🛠️ Manual Install": _logic_manual_install,
    "👤 My Info": _logic_my_info,
    "📢 Channel Add": _logic_channel_add,
}

def setup_command_menu():
    """Register the bot's slash-command menu with Telegram.

    • Regular users see a concise set of everyday commands.
    • Each admin/owner gets an extended menu that includes all
      admin-only commands, set via per-chat scope so it never
      leaks to normal users.
    """
    # ------------------------------------------------------------------
    # Commands shown to every user (default scope)
    # ------------------------------------------------------------------
    user_commands = [
        types.BotCommand('start',          '🏠 Start / show main menu'),
        types.BotCommand('help',           '❓ Show help & main menu'),
        types.BotCommand('uploadfile',     '📤 Upload a .py / .js / .zip file'),
        types.BotCommand('checkfiles',     '📂 List & manage your files'),
        types.BotCommand('statistics',     '📊 View bot statistics'),
        types.BotCommand('botspeed',       '⚡ Test bot response speed'),
        types.BotCommand('updateschannel', '📢 Join the updates channel'),
        types.BotCommand('contactowner',   '📞 Contact the bot owner'),
        types.BotCommand('ping',           '🏓 Ping the bot'),
        types.BotCommand('manualinstall',  '📦 Install a Python / Node.js module'),
        types.BotCommand('myinfo',         '👤 View your profile, status & file usage'),
    ]

    # ------------------------------------------------------------------
    # Extra commands shown only to admins/owner (per-chat scope)
    # ------------------------------------------------------------------
    admin_extra_commands = [
        types.BotCommand('subscriptions',   '💳 Manage user subscriptions'),
        types.BotCommand('broadcast',       '📢 Broadcast a message to all users'),
        types.BotCommand('lockbot',         '🔒 Toggle bot lock on/off'),
        types.BotCommand('runallcode',  '🟢 Start all uploaded scripts'),
        types.BotCommand('adminpanel',      '👑 Open the admin panel'),
        types.BotCommand('usermanagement',  '👥 Ban / unban / inspect users'),
        types.BotCommand('channeladd',      '📢 Set / remove mandatory join channel'),
    ]

    try:
        # Set default scope for all users
        bot.set_my_commands(user_commands, scope=types.BotCommandScopeDefault())
        logger.info("✅ Command menu set for all users.")
    except Exception as e:
        logger.error(f"❌ Failed to set default command menu: {e}")

    # Set extended menu for each admin individually
    for admin_id in admin_ids:
        try:
            bot.set_my_commands(
                user_commands + admin_extra_commands,
                scope=types.BotCommandScopeChat(chat_id=admin_id)
            )
            logger.info(f"✅ Extended command menu set for admin {admin_id}.")
        except Exception as e:
            logger.error(f"❌ Failed to set admin command menu for {admin_id}: {e}")


@bot.message_handler(func=lambda message: message.text in BUTTON_TEXT_TO_LOGIC)
def handle_button_text(message):
    if is_user_banned(message.from_user.id):
        bot.reply_to(message, "🚫 You are banned from using this bot.")
        return
    # Allow these buttons without force-join check
    _no_join_check = {"📢 Updates Channel", "📞 Contact Owner", "📢 Channel Add"}
    if message.text not in _no_join_check and not check_force_join(message):
        return
    logic_func = BUTTON_TEXT_TO_LOGIC.get(message.text)
    if logic_func: logic_func(message)

@bot.message_handler(commands=['updateschannel'])
def cmd_updates_channel(message): _logic_updates_channel(message)
@bot.message_handler(commands=['uploadfile'])
def cmd_upload_file(message): _logic_upload_file(message)
@bot.message_handler(commands=['checkfiles'])
def cmd_check_files(message): _logic_check_files(message)
@bot.message_handler(commands=['botspeed'])
def cmd_bot_speed(message): _logic_bot_speed(message)
@bot.message_handler(commands=['contactowner'])
def cmd_contact_owner(message): _logic_contact_owner(message)
@bot.message_handler(commands=['subscriptions'])
def cmd_subscriptions(message): _logic_subscriptions_panel(message)
@bot.message_handler(commands=['statistics'])
def cmd_statistics(message): _logic_statistics(message)
@bot.message_handler(commands=['broadcast'])
def cmd_broadcast(message): _logic_broadcast_init(message)
@bot.message_handler(commands=['lockbot'])
def cmd_lock_bot(message): _logic_toggle_lock_bot(message)
@bot.message_handler(commands=['adminpanel'])
def cmd_admin_panel(message): _logic_admin_panel(message)
@bot.message_handler(commands=['runallcode'])
def cmd_run_all(message): _logic_run_all_scripts(message)
@bot.message_handler(commands=['usermanagement'])
def cmd_user_management(message): _logic_user_management(message)
@bot.message_handler(commands=['manualinstall'])
def cmd_manual_install(message): _logic_manual_install(message)
@bot.message_handler(commands=['myinfo'])
def cmd_my_info(message): _logic_my_info(message)
@bot.message_handler(commands=['channeladd'])
def cmd_channel_add(message): _logic_channel_add(message)

# ============================================================
# --- Document Handler ---
# ============================================================
@bot.message_handler(content_types=['document'])
def handle_file_upload_doc(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    doc = message.document
    logger.info(f"Doc from {user_id}: {doc.file_name} ({doc.mime_type}), Size: {doc.file_size}")

    if is_user_banned(user_id):
        bot.reply_to(message, "🚫 You are banned from using this bot.")
        return
    if not check_force_join(message):
        return
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, "⚠️ Bot locked, cannot accept files.")
        return
    # Redirect users who haven't done /start yet
    if user_id not in active_users:
        bot.reply_to(message, "👋 Please run /start first to register, then upload your file.")
        return

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.reply_to(message, f"⚠️ File limit (`{current_files}/{limit_str}`) reached. Delete files first.", parse_mode='Markdown')
        return

    file_name = doc.file_name
    if not file_name: bot.reply_to(message, "⚠️ No file name."); return
    file_ext = os.path.splitext(file_name)[1].lower()
    if file_ext not in ['.py', '.js', '.zip']:
        bot.reply_to(message, "⚠️ Unsupported type! Only `.py`, `.js`, `.zip` allowed.", parse_mode='Markdown')
        return
    max_file_size = 20 * 1024 * 1024
    if doc.file_size > max_file_size:
        bot.reply_to(message, f"⚠️ File too large (Max: 20 MB)."); return

    try:
        try:
            bot.forward_message(OWNER_ID, chat_id, message.message_id)
            bot.send_message(OWNER_ID, f"⬆️ File `{file_name}` from `{user_id}`", parse_mode='Markdown')
        except Exception as e: logger.error(f"Failed to forward to OWNER: {e}")

        download_wait_msg = bot.reply_to(message, f"⏳ Downloading `{file_name}`...", parse_mode='Markdown')
        file_info_tg = bot.get_file(doc.file_id)
        downloaded_file_content = bot.download_file(file_info_tg.file_path)
        bot.edit_message_text(f"✅ Downloaded `{file_name}`. Now let's set up the project...", chat_id, download_wait_msg.message_id, parse_mode='Markdown')

        # Store state and ask for project name
        pending_file_uploads[user_id] = {
            'file_content': downloaded_file_content,
            'file_name': file_name,
            'file_ext': file_ext,
            'project_name': None,
        }
        ask_msg = bot.send_message(
            chat_id,
            "📁 *New Upload — Project Name*\n\n"
            "Give this upload a project name:\n"
            "• It will appear in your control panel\n"
            "• Example: `MyBot` or `NotificationBot`\n\n"
            "/cancel to abort.",
            parse_mode='Markdown'
        )
        bot.register_next_step_handler(ask_msg, process_upload_project_name)

    except telebot.apihelper.ApiTelegramException as e:
        logger.error(f"Telegram API Error for {user_id}: {e}")
        if "file is too big" in str(e).lower():
            bot.reply_to(message, "❌ File too large to download (~20MB limit).")
        else:
            bot.reply_to(message, f"❌ Telegram API Error: {str(e)}.")
    except Exception as e:
        logger.error(f"❌ General error for {user_id}: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Unexpected error: {str(e)}")


def process_upload_project_name(message):
    """Step 1: User provides the project name."""
    user_id = message.from_user.id
    if message.text and message.text.strip().lower() == '/cancel':
        pending_file_uploads.pop(user_id, None)
        bot.reply_to(message, "❌ Upload cancelled.")
        return
    if user_id not in pending_file_uploads:
        bot.reply_to(message, "⚠️ No pending upload found. Please send your file again.")
        return

    raw_name = (message.text or '').strip()
    # Sanitise: keep only alphanumeric, dash, underscore
    project_name = re.sub(r'[^\w\-]', '_', raw_name)[:40]
    if not project_name:
        msg = bot.reply_to(message, "⚠️ Invalid name. Use letters, numbers, dashes, or underscores.\nTry again or /cancel.")
        bot.register_next_step_handler(msg, process_upload_project_name)
        return

    # Check duplicate project name for this user
    existing_projects = [pn for pn, _, _ in user_files.get(user_id, [])]
    if project_name in existing_projects:
        msg = bot.reply_to(message, f"⚠️ You already have a project named `{project_name}`.\nChoose a different name or /cancel.", parse_mode='Markdown')
        bot.register_next_step_handler(msg, process_upload_project_name)
        return

    pending_file_uploads[user_id]['project_name'] = project_name
    file_ext = pending_file_uploads[user_id]['file_ext']

    if file_ext == '.zip':
        # For ZIPs, also ask for main file
        msg = bot.send_message(
            message.chat.id,
            f"✅ Project name set to `{project_name}`.\n\n"
            "📁 *Step 2 of 2 — Main File*\n\n"
            "Send the main script filename to run:\n"
            "• Python: `bot.py`, `main.py`, `app.py`…\n"
            "• Node.js: `index.js`, `bot.js`…\n\n"
            "Type /skip to auto-detect, or /cancel to abort.",
            parse_mode='Markdown'
        )
        bot.register_next_step_handler(msg, process_upload_main_file)
    else:
        # For .py/.js: the uploaded file itself is the main file; skip step 2
        pending_file_uploads[user_id]['main_file'] = pending_file_uploads[user_id]['file_name']
        _finalize_upload(message, user_id)


def process_upload_main_file(message):
    """Step 2: User provides the main file name (ZIP uploads only)."""
    user_id = message.from_user.id
    text = (message.text or '').strip()
    if text.lower() == '/cancel':
        pending_file_uploads.pop(user_id, None)
        bot.reply_to(message, "❌ Upload cancelled.")
        return
    if user_id not in pending_file_uploads:
        bot.reply_to(message, "⚠️ No pending upload found. Please send your file again.")
        return

    if text.lower() == '/skip':
        pending_file_uploads[user_id]['main_file'] = None  # will auto-detect
        bot.reply_to(message, "⏭️ Skipped — main file will be auto-detected from the archive.")
    else:
        main_file = text
        if not (main_file.endswith('.py') or main_file.endswith('.js')):
            msg = bot.reply_to(message, "⚠️ Main file must end in `.py` or `.js`.\nTry again, /skip to auto-detect, or /cancel.", parse_mode='Markdown')
            bot.register_next_step_handler(msg, process_upload_main_file)
            return
        pending_file_uploads[user_id]['main_file'] = main_file
        bot.reply_to(message, f"✅ Main file set to `{main_file}`.", parse_mode='Markdown')

    _finalize_upload(message, user_id)


def _finalize_upload(message, user_id):
    """Process the saved file now that we have project_name and main_file."""
    chat_id = message.chat.id
    if user_id not in pending_file_uploads:
        bot.send_message(chat_id, "⚠️ Upload state lost. Please send the file again.")
        return

    state = pending_file_uploads.pop(user_id)
    file_content = state['file_content']
    file_name = state['file_name']
    file_ext = state['file_ext']
    project_name = state['project_name']
    main_file = state.get('main_file')

    project_folder = get_user_folder(user_id, project_name)

    if file_ext == '.zip':
        # Pass project_name and optional main_file into zip processing
        threading.Thread(
            target=_queue_zip_for_approval,
            args=(file_content, file_name, user_id, project_name, main_file, message)
        ).start()
    else:
        # Single script file
        file_path = os.path.join(project_folder, file_name)
        with open(file_path, 'wb') as f: f.write(file_content)
        is_safe, security_msg = check_code_security(file_path, file_ext.lstrip('.'))

        if user_id not in pending_script_files: pending_script_files[user_id] = {}
        pending_script_files[user_id][project_name] = {
            'path': file_path, 'type': file_ext.lstrip('.'),
            'is_safe': is_safe, 'security_msg': security_msg,
            'chat_id': chat_id, 'project_name': project_name,
            'main_file': file_name,
        }
        save_pending_script_db(user_id, project_name, pending_script_files[user_id][project_name])
        markup = types.InlineKeyboardMarkup()
        markup.row(
            make_colored_button("✅ Approve", callback_data=f"approve_file_{user_id}_{project_name}"),
            make_colored_button("❌ Reject", callback_data=f"reject_file_{user_id}_{project_name}")
        )
        markup.row(make_colored_button("📋 View in Pending Files", callback_data=f"pending_user_{user_id}"))
        if not is_safe:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as _fscan:
                    _content = _fscan.read()
                found_patterns = [p for p in DANGEROUS_PATTERNS if re.search(p, _content, re.IGNORECASE)]
                pattern_lines = '\n'.join(f"  ⚠️ `{p}`" for p in found_patterns[:10])
                if len(found_patterns) > 10:
                    pattern_lines += f"\n  ... and `{len(found_patterns) - 10}` more"
                danger_detail = f"🚨 *Dangerous Patterns Found:* `{len(found_patterns)}`\n{pattern_lines}"
            except Exception:
                danger_detail = f"🚨 *Security Issue:* `{security_msg}`"
        else:
            danger_detail = "✅ *Security:* No dangerous patterns detected"
        warning = (f"🔔 *New File Upload — Review Required*\n\n"
                   f"👤 User: `{user_id}`\n"
                   f"📦 Project: `{project_name}`\n"
                   f"📁 File: `{file_name}` (`.{file_ext.lstrip('.')}`)\n\n"
                   f"{danger_detail}")
        for aid in admin_ids:
            try: bot.send_message(aid, warning, reply_markup=markup, parse_mode='Markdown')
            except Exception: pass
        bot.send_message(chat_id,
            f"✅ Project `{project_name}` queued for review. You'll be notified upon approval.",
            parse_mode='Markdown')


def _queue_zip_for_approval(file_content, file_name_zip, user_id, project_name, main_file, message):
    """Scan and queue a ZIP upload for admin approval, now with project_name attached."""
    temp_dir = None
    try:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_")
        zip_path = os.path.join(temp_dir, file_name_zip)
        with open(zip_path, 'wb') as f: f.write(file_content)

        is_safe, security_msg = scan_zip_security(zip_path)

        all_found = []
        try:
            with zipfile.ZipFile(zip_path, 'r') as _zref:
                for _fi in _zref.infolist():
                    if _fi.filename.endswith(('.py', '.js', '.zip', '.txt', '.sh', '.bat', '.cmd')):
                        with _zref.open(_fi.filename) as _f:
                            try:
                                _content = _f.read().decode('utf-8', errors='ignore')
                            except Exception:
                                continue
                            for _p in DANGEROUS_PATTERNS:
                                if _p not in all_found and re.search(_p, _content, re.IGNORECASE):
                                    all_found.append(_p)
        except Exception:
            pass

        if user_id not in pending_zip_files: pending_zip_files[user_id] = {}
        pending_zip_files[user_id][project_name] = {
            'content': file_content,
            'patterns': all_found,
            'file_name_zip': file_name_zip,
            'project_name': project_name,
            'main_file': main_file,
        }
        save_pending_zip_db(user_id, project_name, pending_zip_files[user_id][project_name])

        markup_approval = types.InlineKeyboardMarkup()
        markup_approval.row(
            make_colored_button("✅ Approve", callback_data=f"approve_zip_{user_id}_{project_name}"),
            make_colored_button("❌ Reject", callback_data=f"reject_zip_{user_id}_{project_name}")
        )
        markup_approval.row(make_colored_button("📋 View in Pending Files", callback_data=f"pending_user_{user_id}"))

        if all_found:
            pattern_lines = '\n'.join(f"  ⚠️ `{p}`" for p in all_found[:10])
            if len(all_found) > 10:
                pattern_lines += f"\n  ... and `{len(all_found) - 10}` more"
            danger_detail = f"🚨 *Dangerous Patterns Found:* `{len(all_found)}`\n{pattern_lines}"
        else:
            danger_detail = "✅ *Security:* No dangerous patterns detected"

        warning = (f"🔔 *New ZIP Upload — Review Required*\n\n"
                   f"👤 User: `{user_id}`\n"
                   f"📦 Project: `{project_name}`\n"
                   f"📁 File: `{file_name_zip}`\n\n"
                   f"{danger_detail}")
        for aid in admin_ids:
            try: bot.send_message(aid, warning, reply_markup=markup_approval, parse_mode='Markdown')
            except Exception: pass
        bot.send_message(message.chat.id,
            f"✅ Project `{project_name}` is under review. You'll be notified upon approval.",
            parse_mode='Markdown')

    except zipfile.BadZipFile as e:
        bot.send_message(message.chat.id, f"❌ Invalid/corrupted ZIP: {e}")
    except Exception as e:
        logger.error(f"❌ Error queuing zip for {user_id}: {e}", exc_info=True)
        bot.send_message(message.chat.id, f"❌ Error processing zip: {str(e)}")
    finally:
        if temp_dir and os.path.exists(temp_dir):
            try: shutil.rmtree(temp_dir)
            except Exception: pass

# ============================================================
# --- Callback Query Handler ---
# ============================================================
@bot.callback_query_handler(func=lambda call: True)
def handle_callbacks(call):
    user_id = call.from_user.id
    data = call.data
    logger.info(f"Callback: User={user_id}, Data='{data}'")

    if is_user_banned(user_id) and data not in ['back_to_main']:
        bot.answer_callback_query(call.id, "🚫 You are banned from using this bot.", show_alert=True)
        return

    if bot_locked and user_id not in admin_ids and data not in ['back_to_main', 'speed', 'stats', 'my_info']:
        bot.answer_callback_query(call.id, "⚠️ Bot locked by admin.", show_alert=True)
        return

    try:
        if data == 'upload': upload_callback(call)
        elif data == 'check_files': check_files_callback(call)
        elif data.startswith('file_'): file_control_callback(call)
        elif data.startswith('umfile_'): um_file_control_callback(call)
        elif data.startswith('changemain_'): change_main_file_callback(call)
        elif data.startswith('start_'): start_bot_callback(call)
        elif data.startswith('stop_'): stop_bot_callback(call)
        elif data.startswith('restart_'): restart_bot_callback(call)
        elif data.startswith('delete_'): delete_bot_callback(call)
        elif data.startswith('logs_'): logs_bot_callback(call)
        elif data == 'speed': speed_callback(call)
        elif data == 'my_info': my_info_callback(call)
        elif data == 'back_to_main': back_to_main_callback(call)
        elif data.startswith('confirm_broadcast_'): handle_confirm_broadcast(call)
        elif data == 'cancel_broadcast': handle_cancel_broadcast(call)
        elif data == 'noop': bot.answer_callback_query(call.id)
        elif data == 'manual_install':
            bot.answer_callback_query(call.id)
            manual_install_module_init(call.message)
        # Admin callbacks
        elif data == 'subscription': admin_required_callback(call, subscription_management_callback)
        elif data == 'stats': stats_callback(call)
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
        # User Management callbacks
        elif data == 'user_management': admin_required_callback(call, user_management_callback)
        elif data == 'ban_user': admin_required_callback(call, ban_user_callback)
        elif data == 'unban_user': admin_required_callback(call, unban_user_callback)
        elif data == 'user_info': admin_required_callback(call, user_info_callback)
        elif data == 'all_users': admin_required_callback(call, all_users_callback)
        elif data == 'set_user_limit': admin_required_callback(call, set_user_limit_callback)
        elif data == 'remove_user_limit': admin_required_callback(call, remove_user_limit_callback)
        elif data.startswith('users_page_'): admin_required_callback(call, handle_users_page)
        elif data == 'view_user_files': admin_required_callback(call, view_user_files_callback)
        elif data == 'pending_files': admin_required_callback(call, pending_files_callback)
        elif data.startswith('pending_user_'): admin_required_callback(call, pending_user_callback)
        elif data.startswith('chat_user_'): admin_required_callback(call, chat_user_callback)
        elif data.startswith('admin_user_files_'): admin_required_callback(call, admin_user_files_callback)
        # File Approval callbacks
        elif data.startswith('approve_file_'): admin_required_callback(call, process_approve_file)
        elif data.startswith('reject_file_'): admin_required_callback(call, process_reject_file)
        elif data.startswith('approve_zip_'): admin_required_callback(call, process_approve_zip)
        elif data.startswith('reject_zip_'): admin_required_callback(call, process_reject_zip)
        # Force Join Channel callbacks
        elif data == 'channel_add': admin_required_callback(call, lambda c: _logic_channel_add(c.message, override_user_id=c.from_user.id))
        elif data == 'set_force_join': admin_required_callback(call, set_force_join_callback)
        elif data.startswith('remove_force_join_'): admin_required_callback(call, remove_force_join_callback)
        elif data == 'check_joined': check_joined_callback(call)
        else:
            bot.answer_callback_query(call.id, "Unknown action.")
            logger.warning(f"Unhandled callback: {data} from {user_id}")
    except Exception as e:
        logger.error(f"Error handling callback '{data}' for {user_id}: {e}", exc_info=True)
        try: bot.answer_callback_query(call.id, "Error processing request.", show_alert=True)
        except Exception: pass

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

# ============================================================
# --- User Callbacks ---
# ============================================================
def change_main_file_callback(call):
    """Let the user change the main file of an existing project."""
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == project_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); return
        bot.answer_callback_query(call.id)
        msg = bot.send_message(
            call.message.chat.id,
            f"📁 *Change Main File — {project_name}*\n\n"
            f"Send the new main script filename to run:\n"
            f"• Python: `bot.py`, `main.py`, `app.py`…\n"
            f"• Node.js: `index.js`, `bot.js`…\n\n"
            f"The file must already exist inside the project folder.\n\n"
            f"/cancel to abort.",
            parse_mode='Markdown'
        )
        bot.register_next_step_handler(msg, process_change_main_file, script_owner_id, project_name, call.message)
    except Exception as e:
        logger.error(f"Error in change_main_file_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error.", show_alert=True)

def process_change_main_file(message, script_owner_id, project_name, original_msg):
    """Process the new main file name provided by the user."""
    if message.text and message.text.strip().lower() == '/cancel':
        bot.reply_to(message, "❌ Change cancelled.")
        return
    new_main_file = (message.text or '').strip()
    if not (new_main_file.endswith('.py') or new_main_file.endswith('.js')):
        msg = bot.reply_to(message, "⚠️ File must end in `.py` or `.js`. Try again or /cancel.", parse_mode='Markdown')
        bot.register_next_step_handler(msg, process_change_main_file, script_owner_id, project_name, original_msg)
        return
    project_folder = get_user_folder(script_owner_id, project_name)
    new_file_path = os.path.join(project_folder, new_main_file)
    if not os.path.exists(new_file_path):
        msg = bot.reply_to(message,
            f"⚠️ `{new_main_file}` not found inside project `{project_name}`.\n"
            f"Make sure the file was uploaded as part of the project. Try again or /cancel.",
            parse_mode='Markdown')
        bot.register_next_step_handler(msg, process_change_main_file, script_owner_id, project_name, original_msg)
        return
    if update_main_file_db(script_owner_id, project_name, new_main_file):
        bot.reply_to(message, f"✅ Main file for project `{project_name}` updated to `{new_main_file}`.\nRestart the project to apply the change.", parse_mode='Markdown')
    else:
        bot.reply_to(message, "❌ Failed to update main file. Please try again.")

def upload_callback(call):
    user_id = call.from_user.id
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "🚫 You are banned.", show_alert=True); return
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        bot.answer_callback_query(call.id, f"⚠️ File limit ({current_files}/{limit_str}) reached.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    bot.send_message(call.message.chat.id,
        "📤 *Upload Your Project*\n\n"
        "Send one of the following:\n"
        "🐍 `.py` — Python script\n"
        "🟨 `.js` — Node.js script\n"
        "🗜️ `.zip` — Full project archive\n\n"
        "💡 _All projects support_ `requirements.txt` _&_ `package.json` _— deps auto-reinstall on restart._",
        parse_mode='Markdown')

def check_files_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    user_files_list = user_files.get(user_id, [])
    if not user_files_list:
        bot.answer_callback_query(call.id, "⚠️ No projects uploaded.", show_alert=True)
        try:
            markup = types.InlineKeyboardMarkup()
            markup.add(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))
            bot.edit_message_text("📂 *Your projects:*\n\n_(No projects uploaded yet)_", chat_id,
                                  call.message.message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception: pass
        return
    bot.answer_callback_query(call.id)
    markup = types.InlineKeyboardMarkup(row_width=1)
    for project_name, main_file, file_type in sorted(user_files_list):
        is_running = is_bot_running(user_id, project_name)
        status_icon = "🟢" if is_running else "🔴"
        markup.add(make_colored_button(f"{status_icon} {project_name}", callback_data=f'file_{user_id}_{project_name}'))
    markup.add(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))
    try:
        bot.edit_message_text("📂 *Your projects:*\nTap to manage.", chat_id, call.message.message_id,
                              reply_markup=markup, parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
        if "message is not modified" not in str(e): logger.error(f"Error editing file list: {e}")

def file_control_callback(call):
    """File control panel opened from Check Files — back button returns to own file list."""
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ You can only manage your own projects.", show_alert=True)
            check_files_callback(call); return
        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == project_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True)
            check_files_callback(call); return
        bot.answer_callback_query(call.id)
        _, main_file, file_type = file_info
        is_running = is_bot_running(script_owner_id, project_name)
        status_text = '🟢 Running' if is_running else '🔴 Stopped'
        try:
            bot.edit_message_text(
                f"⚙️ *Project:* `{project_name}`\n"
                f"📄 *Main File:* `{main_file}` `({file_type})`\n"
                f"👤 Owner: `{script_owner_id}`\n"
                f"📊 Status: {status_text}",
                call.message.chat.id, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, project_name, is_running, 'check_files'),
                parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
            if "message is not modified" not in str(e): raise
    except (ValueError, IndexError) as ve:
        logger.error(f"Error parsing file control: {ve}")
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in file_control_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)

def um_file_control_callback(call):
    """File control panel opened from User Management — back button returns to that user's file panel."""
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        if requesting_user_id not in admin_ids:
            bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == project_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True)
            _show_user_files_admin_inline(call.message.chat.id, call.message.message_id, script_owner_id); return
        bot.answer_callback_query(call.id)
        _, main_file, file_type = file_info
        is_running = is_bot_running(script_owner_id, project_name)
        status_text = '🟢 Running' if is_running else '🔴 Stopped'
        try:
            bot.edit_message_text(
                f"⚙️ *Project:* `{project_name}`\n"
                f"📄 *Main File:* `{main_file}` `({file_type})`\n"
                f"👤 Owner: `{script_owner_id}`\n"
                f"📊 Status: {status_text}",
                call.message.chat.id, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, project_name, is_running, f'admin_user_files_{script_owner_id}'),
                parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
            if "message is not modified" not in str(e): raise
    except (ValueError, IndexError) as ve:
        logger.error(f"Error parsing um file control: {ve}")
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in um_file_control_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)

def start_bot_callback(call):
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == project_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); check_files_callback(call); return
        _, main_file, file_type = file_info
        user_folder = get_user_folder(script_owner_id, project_name)
        file_path = os.path.join(user_folder, main_file)
        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ Main file `{main_file}` missing! Re-upload.", show_alert=True)
            remove_user_file_db(script_owner_id, project_name); check_files_callback(call); return
        if is_bot_running(script_owner_id, project_name):
            bot.answer_callback_query(call.id, f"⚠️ Project already running.", show_alert=True)
            try: bot.edit_message_reply_markup(chat_id_for_reply, call.message.message_id,
                                               reply_markup=create_control_buttons(script_owner_id, project_name, True, _extract_back_callback(call)))
            except Exception: pass
            return
        bot.answer_callback_query(call.id, f"⏳ Starting {project_name}...")

        def _start_with_deps():
            if file_type == 'py':
                if not install_requirements_if_present(user_folder, script_owner_id, call.message):
                    return
                run_script(file_path, script_owner_id, user_folder, project_name, call.message,
                           attempt=1, skip_deps_install=True)
            elif file_type == 'js':
                if not install_package_json_if_present(user_folder, script_owner_id, call.message):
                    return
                run_js_script(file_path, script_owner_id, user_folder, project_name, call.message,
                              attempt=1, skip_deps_install=True)
            else:
                bot.send_message(chat_id_for_reply, f"❌ Unknown file type `{file_type}`.", parse_mode='Markdown')

        threading.Thread(target=_start_with_deps).start()
        time.sleep(1.5)
        is_now_running = is_bot_running(script_owner_id, project_name)
        status_text = '🟢 Running' if is_now_running else '🟡 Starting...'
        try:
            bot.edit_message_text(
                f"⚙️ *Project:* `{project_name}`\n📄 *Main File:* `{main_file}` `({file_type})`\n👤 Owner: `{script_owner_id}`\nStatus: {status_text}",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, project_name, is_now_running, _extract_back_callback(call)), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
            if "message is not modified" not in str(e): raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing start callback: {e}")
        bot.answer_callback_query(call.id, "Error: Invalid start command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in start_bot_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error starting project.", show_alert=True)

def stop_bot_callback(call):
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == project_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); return
        _, main_file, file_type = file_info
        script_key = f"{script_owner_id}_{project_name}"
        if not is_bot_running(script_owner_id, project_name):
            bot.answer_callback_query(call.id, f"⚠️ Project already stopped.", show_alert=True)
            try:
                bot.edit_message_text(
                    f"⚙️ *Project:* `{project_name}`\n📄 *Main File:* `{main_file}` `({file_type})`\n👤 Owner: `{script_owner_id}`\nStatus: 🔴 Stopped",
                    chat_id_for_reply, call.message.message_id,
                    reply_markup=create_control_buttons(script_owner_id, project_name, False, _extract_back_callback(call)), parse_mode='Markdown')
            except Exception: pass
            return
        bot.answer_callback_query(call.id, f"⏳ Stopping {project_name}...")
        process_info = bot_scripts.get(script_key)
        if process_info:
            kill_process_tree(process_info)
            if script_key in bot_scripts: del bot_scripts[script_key]
        try:
            bot.edit_message_text(
                f"⚙️ *Project:* `{project_name}`\n📄 *Main File:* `{main_file}` `({file_type})`\n👤 Owner: `{script_owner_id}`\nStatus: 🔴 Stopped",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, project_name, False, _extract_back_callback(call)), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
            if "message is not modified" not in str(e): raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing stop callback: {e}")
        bot.answer_callback_query(call.id, "Error: Invalid stop command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in stop_bot_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error stopping project.", show_alert=True)

def restart_bot_callback(call):
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == project_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); check_files_callback(call); return
        _, main_file, file_type = file_info
        user_folder = get_user_folder(script_owner_id, project_name)
        file_path = os.path.join(user_folder, main_file)
        script_key = f"{script_owner_id}_{project_name}"
        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ Main file `{main_file}` missing! Re-upload.", show_alert=True)
            remove_user_file_db(script_owner_id, project_name)
            if script_key in bot_scripts: del bot_scripts[script_key]
            check_files_callback(call); return
        bot.answer_callback_query(call.id, f"⏳ Restarting {project_name}...")
        if is_bot_running(script_owner_id, project_name):
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            if script_key in bot_scripts: del bot_scripts[script_key]
            time.sleep(1.5)
        if file_type == 'py':
            threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, project_name, call.message)).start()
        elif file_type == 'js':
            threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, project_name, call.message)).start()
        else:
            bot.send_message(chat_id_for_reply, f"❌ Unknown type `{file_type}`.", parse_mode='Markdown'); return
        time.sleep(1.5)
        is_now_running = is_bot_running(script_owner_id, project_name)
        status_text = '🟢 Running' if is_now_running else '🟡 Starting...'
        try:
            bot.edit_message_text(
                f"⚙️ *Project:* `{project_name}`\n📄 *Main File:* `{main_file}` `({file_type})`\n👤 Owner: `{script_owner_id}`\nStatus: {status_text}",
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, project_name, is_now_running, _extract_back_callback(call)), parse_mode='Markdown'
            )
        except telebot.apihelper.ApiTelegramException as e:
            if "message is not modified" not in str(e): raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing restart callback: {e}")
        bot.answer_callback_query(call.id, "Error: Invalid restart command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in restart_bot_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error restarting.", show_alert=True)

def delete_bot_callback(call):
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == project_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); check_files_callback(call); return
        bot.answer_callback_query(call.id, f"🗑️ Deleting {project_name}...")
        script_key = f"{script_owner_id}_{project_name}"
        if is_bot_running(script_owner_id, project_name):
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            if script_key in bot_scripts: del bot_scripts[script_key]
            time.sleep(0.5)
        # Delete entire project folder
        project_folder = get_user_folder(script_owner_id, project_name)
        if os.path.exists(project_folder):
            try: shutil.rmtree(project_folder)
            except OSError as e: logger.error(f"Error deleting project folder {project_folder}: {e}")
        remove_user_file_db(script_owner_id, project_name)
        try:
            bot.edit_message_text(
                f"🗑️ Project `{project_name}` (User `{script_owner_id}`) deleted.",
                chat_id_for_reply, call.message.message_id, reply_markup=None, parse_mode='Markdown'
            )
        except Exception as e:
            logger.error(f"Error editing msg after delete: {e}")
            bot.send_message(chat_id_for_reply, f"🗑️ Project `{project_name}` deleted.", parse_mode='Markdown')
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing delete callback: {e}")
        bot.answer_callback_query(call.id, "Error: Invalid delete command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in delete_bot_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error deleting.", show_alert=True)

def logs_bot_callback(call):
    try:
        _, script_owner_id_str, project_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == project_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ Project not found.", show_alert=True); check_files_callback(call); return
        user_folder = get_user_folder(script_owner_id, project_name)
        log_path = os.path.join(user_folder, f"{project_name}.log")
        if not os.path.exists(log_path):
            bot.answer_callback_query(call.id, f"⚠️ No logs for '{project_name}'.", show_alert=True); return
        bot.answer_callback_query(call.id)
        try:
            log_content = ""
            file_size = os.path.getsize(log_path)
            max_log_kb = 100; max_tg_msg = 4000
            if file_size == 0:
                log_content = "(Log is empty)"
            elif file_size > max_log_kb * 1024:
                with open(log_path, 'rb') as f:
                    f.seek(-max_log_kb * 1024, os.SEEK_END)
                    log_bytes = f.read()
                log_content = f"(Last {max_log_kb}KB)\n...\n" + log_bytes.decode('utf-8', errors='ignore')
            else:
                with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                    log_content = f.read()
            if len(log_content) > max_tg_msg:
                log_content = log_content[-max_tg_msg:]
                first_nl = log_content.find('\n')
                if first_nl != -1: log_content = "...\n" + log_content[first_nl+1:]
                else: log_content = "...\n" + log_content
            if not log_content.strip(): log_content = "(No visible content)"
            bot.send_message(chat_id_for_reply,
                             f"📜 *Logs for project* `{project_name}` *(User* `{script_owner_id}`*):\n*\n```\n{log_content}\n```",
                             parse_mode='Markdown')
        except Exception as e:
            logger.error(f"Error reading/sending log: {e}")
            bot.send_message(chat_id_for_reply, f"❌ Error reading log for `{project_name}`.", parse_mode='Markdown')
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing logs callback: {e}")
        bot.answer_callback_query(call.id, "Error: Invalid logs command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in logs_bot_callback: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error fetching logs.", show_alert=True)

def speed_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    start_cb_ping_time = time.time()
    try:
        bot.edit_message_text("🏃 Testing speed...", chat_id, call.message.message_id)
        bot.send_chat_action(chat_id, 'typing')
        response_time = round((time.time() - start_cb_ping_time) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now():
            user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        rating = "✅ Excellent" if response_time < 300 else ("⚠️ Moderate" if response_time < 800 else "🔴 Slow")
        speed_msg = (
            f"⚡ *Bot Speed & Status*\n"
            f"──────────────────────\n\n"
            f"🏓 *API Response:* `{response_time} ms` {rating}\n"
            f"🚦 *Bot Status:* {status}\n"
            f"🏖️ *Your Rank:* {user_level}\n"
            f"──────────────────────")
        bot.answer_callback_query(call.id)
        bot.edit_message_text(speed_msg, chat_id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error during speed test (cb): {e}")
        bot.answer_callback_query(call.id, "Error in speed test.", show_alert=True)
        try: bot.edit_message_text("〽️ Main Menu", chat_id, call.message.message_id,
                                   reply_markup=create_main_menu_inline(user_id))
        except Exception: pass

def my_info_callback(call):
    user_id = call.from_user.id
    user_name = call.from_user.first_name or "User"
    user_username = call.from_user.username
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
            hours_left = int(((expiry_date - datetime.now()).seconds) / 3600)
            expiry_info = f"\n⏳ *Subscription Expiry:* {expiry_date.strftime('%Y-%m-%d %H:%M')} UTC\n📅 *Days Remaining:* `{days_left}d {hours_left}h`"
        else:
            user_status = "🆓 Free User"
            remove_subscription_db(user_id)
    else:
        user_status = "🆓 Free User"
    running_count = sum(
        1 for sk in list(bot_scripts.keys())
        if sk.startswith(f"{user_id}_") and is_bot_running(user_id, sk.split('_', 1)[1])
    )
    is_banned = "🚫 Yes" if is_user_banned(user_id) else "✅ No"
    info_msg = (
        f"👤 *My Profile*\n"
        f"──────────────────────\n\n"
        f"🆔 *User ID:* `{user_id}`\n"
        f"📛 *Name:* {user_name}\n"
        f"✳️ *Username:* `@{user_username or 'Not set'}`\n"
        f"🏖️ *Rank:* {user_status}{expiry_info}\n"
        f"🚫 *Banned:* {is_banned}\n\n"
        f"──────────────────────\n"
        f"📁 *Projects:* `{current_files} / {limit_str}`\n"
        f"🟢 *Running Scripts:* `{running_count}`\n"
        f"──────────────────────"
    )
    markup = types.InlineKeyboardMarkup()
    markup.add(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))
    try:
        bot.answer_callback_query(call.id)
        bot.edit_message_text(info_msg, call.message.chat.id, call.message.message_id,
                              reply_markup=markup, parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
        if "message is not modified" not in str(e): logger.error(f"Error showing my_info: {e}")
    except Exception as e:
        logger.error(f"Error in my_info_callback: {e}")

def back_to_main_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "🚫 You are banned.", show_alert=True); return
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    expiry_info = ""
    if user_id == OWNER_ID: user_status = "👑 Owner"
    elif user_id in admin_ids: user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"
            days_left = (expiry_date - datetime.now()).days
            expiry_info = f"\n⏳ Subscription expires in: *{days_left} days*"
        else: user_status = "🆓 Free User"
    else: user_status = "🆓 Free User"
    main_menu_text = (f"〽️ *Welcome back, {call.from_user.first_name}!*\n\n"
                      f"🆔 ID: `{user_id}`\n"
                      f"🔰 Status: {user_status}{expiry_info}\n"
                      f"📁 Files: *{current_files} / {limit_str}*\n\n"
                      f"👇 Use buttons or type commands.")
    try:
        bot.answer_callback_query(call.id)
        bot.edit_message_text(main_menu_text, chat_id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
        if "message is not modified" not in str(e): logger.error(f"API error on back_to_main: {e}")
    except Exception as e: logger.error(f"Error handling back_to_main: {e}")

# ============================================================
# --- Admin Callbacks ---
# ============================================================
def subscription_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("💳 *Subscription Management*\nSelect action:",
                              call.message.chat.id, call.message.message_id,
                              reply_markup=create_subscription_menu(), parse_mode='Markdown')
    except Exception as e: logger.error(f"Error showing sub menu: {e}")

def stats_callback(call):
    bot.answer_callback_query(call.id)
    _logic_statistics(call.message)
    try:
        bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                      reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception: pass

def lock_bot_callback(call):
    global bot_locked; bot_locked = True
    user_id = call.from_user.id
    logger.warning(f"Bot locked by Admin {user_id}")
    bot.answer_callback_query(call.id, "🔒 Bot is now Locked.")
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    menu_text = (f"〽️ *Main Menu*\n\n"
                 f"🆔 ID: `{user_id}`\n"
                 f"🔰 Status: 🛡️ Admin\n"
                 f"📁 Files: *{current_files} / {limit_str}*\n\n"
                 f"🔒 *Bot has been Locked.*\n"
                 f"👇 Use buttons or type commands.")
    try:
        bot.edit_message_text(menu_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
        if "message is not modified" not in str(e):
            logger.error(f"Error updating inline keyboard after lock: {e}")
    except Exception as e:
        logger.error(f"Error in lock_bot_callback: {e}")
    # Refresh reply keyboard so it shows 🔓 Unlock Bot
    try:
        bot.send_message(call.message.chat.id, "🔒 Bot locked. Reply keyboard updated.",
                         reply_markup=create_reply_keyboard_main_menu(user_id))
    except Exception as e:
        logger.error(f"Error refreshing reply keyboard after lock: {e}")

def unlock_bot_callback(call):
    global bot_locked; bot_locked = False
    user_id = call.from_user.id
    logger.warning(f"Bot unlocked by Admin {user_id}")
    bot.answer_callback_query(call.id, "🔓 Bot is now Unlocked.")
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
    menu_text = (f"〽️ *Main Menu*\n\n"
                 f"🆔 ID: `{user_id}`\n"
                 f"🔰 Status: 🛡️ Admin\n"
                 f"📁 Files: *{current_files} / {limit_str}*\n\n"
                 f"🔓 *Bot has been Unlocked.*\n"
                 f"👇 Use buttons or type commands.")
    try:
        bot.edit_message_text(menu_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='Markdown')
    except telebot.apihelper.ApiTelegramException as e:
        if "message is not modified" not in str(e):
            logger.error(f"Error updating inline keyboard after unlock: {e}")
    except Exception as e:
        logger.error(f"Error in unlock_bot_callback: {e}")
    # Refresh reply keyboard so it shows 🔒 Lock Bot
    try:
        bot.send_message(call.message.chat.id, "🔓 Bot unlocked. Reply keyboard updated.",
                         reply_markup=create_reply_keyboard_main_menu(user_id))
    except Exception as e:
        logger.error(f"Error refreshing reply keyboard after unlock: {e}")

def run_all_scripts_callback(call):
    _logic_run_all_scripts(call)

def broadcast_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "📢 Send message to broadcast.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_broadcast_message)

def admin_panel_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text("👑 *Admin Panel*\nManage admins.",
                              call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_panel(), parse_mode='Markdown')
    except Exception as e: logger.error(f"Error showing admin panel: {e}")

def add_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👑 Enter User ID to promote to Admin.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_add_admin_id)

def process_add_admin_id(message):
    if message.from_user.id != OWNER_ID: bot.reply_to(message, "⚠️ Owner only."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Admin promotion cancelled."); return
    try:
        new_admin_id = int(message.text.strip())
        if new_admin_id <= 0: raise ValueError("ID must be positive")
        if new_admin_id == OWNER_ID: bot.reply_to(message, "⚠️ Owner is already Owner."); return
        if new_admin_id in admin_ids: bot.reply_to(message, f"⚠️ User `{new_admin_id}` is already an Admin.", parse_mode='Markdown'); return
        add_admin_db(new_admin_id)
        bot.reply_to(message, f"✅ User `{new_admin_id}` promoted to Admin.", parse_mode='Markdown')
        try: bot.send_message(new_admin_id, "🎉 Congrats! You are now an Admin.")
        except Exception: pass
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "👑 Enter User ID to promote or /cancel.")
        bot.register_next_step_handler(msg, process_add_admin_id)
    except Exception as e: logger.error(f"Error adding admin: {e}"); bot.reply_to(message, "❌ Error.")

def remove_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👑 Enter User ID of Admin to remove.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_admin_id)

def process_remove_admin_id(message):
    if message.from_user.id != OWNER_ID: bot.reply_to(message, "⚠️ Owner only."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Admin removal cancelled."); return
    try:
        admin_id_remove = int(message.text.strip())
        if admin_id_remove <= 0: raise ValueError("ID must be positive")
        if admin_id_remove == OWNER_ID: bot.reply_to(message, "⚠️ Cannot remove Owner."); return
        if admin_id_remove not in admin_ids: bot.reply_to(message, f"⚠️ User `{admin_id_remove}` is not an Admin.", parse_mode='Markdown'); return
        if remove_admin_db(admin_id_remove):
            bot.reply_to(message, f"✅ Admin `{admin_id_remove}` removed.", parse_mode='Markdown')
            try: bot.send_message(admin_id_remove, "ℹ️ You are no longer an Admin.")
            except Exception: pass
        else: bot.reply_to(message, f"❌ Failed to remove admin `{admin_id_remove}`.", parse_mode='Markdown')
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "👑 Enter Admin ID to remove or /cancel.")
        bot.register_next_step_handler(msg, process_remove_admin_id)
    except Exception as e: logger.error(f"Error removing admin: {e}"); bot.reply_to(message, "❌ Error.")

def list_admins_callback(call):
    bot.answer_callback_query(call.id)
    try:
        admin_list_str = "\n".join(
            f"• `{aid}` {'👑 Owner' if aid == OWNER_ID else '🛡️ Admin'}"
            for aid in sorted(list(admin_ids))
        )
        if not admin_list_str: admin_list_str = "(No admins configured)"
        bot.edit_message_text(f"👑 *Current Admins:*\n\n{admin_list_str}",
                              call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_panel(), parse_mode='Markdown')
    except Exception as e: logger.error(f"Error listing admins: {e}")

def add_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID & days (e.g., `12345678 30`).\n/cancel to abort.", parse_mode='Markdown')
    bot.register_next_step_handler(msg, process_add_subscription_details)

def process_add_subscription_details(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Sub add cancelled."); return
    try:
        parts = message.text.split()
        if len(parts) != 2: raise ValueError("Incorrect format")
        sub_user_id = int(parts[0].strip()); days = int(parts[1].strip())
        if sub_user_id <= 0 or days <= 0: raise ValueError("User ID/days must be positive")
        current_expiry = user_subscriptions.get(sub_user_id, {}).get('expiry')
        start_date = datetime.now()
        if current_expiry and current_expiry > start_date: start_date = current_expiry
        new_expiry = start_date + timedelta(days=days)
        save_subscription(sub_user_id, new_expiry)
        bot.reply_to(message, f"✅ Sub for `{sub_user_id}` extended by `{days}` days.\nNew expiry: `{new_expiry:%Y-%m-%d}`", parse_mode='Markdown')
        try: bot.send_message(sub_user_id, f"🎉 Sub activated/extended by {days} days! Expires: `{new_expiry:%Y-%m-%d}`.", parse_mode='Markdown')
        except Exception: pass
    except ValueError as e:
        bot.reply_to(message, f"⚠️ Invalid: {md_escape(e)}. Format: `ID days` or /cancel.", parse_mode='Markdown')
        msg = bot.send_message(message.chat.id, "💳 Enter User ID & days, or /cancel.")
        bot.register_next_step_handler(msg, process_add_subscription_details)
    except Exception as e: logger.error(f"Error adding sub: {e}"); bot.reply_to(message, "❌ Error.")

def remove_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to remove sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_subscription_id)

def process_remove_subscription_id(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Sub removal cancelled."); return
    try:
        sub_user_id = int(message.text.strip())
        if sub_user_id not in user_subscriptions: bot.reply_to(message, f"⚠️ User `{sub_user_id}` has no active sub.", parse_mode='Markdown'); return
        remove_subscription_db(sub_user_id)
        bot.reply_to(message, f"✅ Sub for `{sub_user_id}` removed.", parse_mode='Markdown')
        try: bot.send_message(sub_user_id, "ℹ️ Your subscription was removed by admin.")
        except Exception: pass
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to remove sub, or /cancel.")
        bot.register_next_step_handler(msg, process_remove_subscription_id)
    except Exception as e: logger.error(f"Error removing sub: {e}"); bot.reply_to(message, "❌ Error.")

def check_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to check sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_check_subscription_id)

def process_check_subscription_id(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Sub check cancelled."); return
    try:
        sub_user_id = int(message.text.strip())
        if sub_user_id in user_subscriptions:
            expiry_dt = user_subscriptions[sub_user_id].get('expiry')
            if expiry_dt:
                if expiry_dt > datetime.now():
                    days_left = (expiry_dt - datetime.now()).days
                    bot.reply_to(message, f"✅ User `{sub_user_id}` has active sub.\nExpires: `{expiry_dt:%Y-%m-%d %H:%M}` (`{days_left}` days left).", parse_mode='Markdown')
                else:
                    bot.reply_to(message, f"⚠️ User `{sub_user_id}` sub expired on `{expiry_dt:%Y-%m-%d}`.", parse_mode='Markdown')
                    remove_subscription_db(sub_user_id)
            else: bot.reply_to(message, f"⚠️ User `{sub_user_id}` in sub list but expiry missing.", parse_mode='Markdown')
        else: bot.reply_to(message, f"ℹ️ User `{sub_user_id}` has no subscription.", parse_mode='Markdown')
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid ID. Send numerical ID or /cancel.")
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to check, or /cancel.")
        bot.register_next_step_handler(msg, process_check_subscription_id)
    except Exception as e: logger.error(f"Error checking sub: {e}"); bot.reply_to(message, "❌ Error.")

# ============================================================
# --- User Management Callbacks ---
# ============================================================
def user_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(
            "👥 *User Management*\nSelect an action:",
            call.message.chat.id, call.message.message_id,
            reply_markup=create_user_management_menu(), parse_mode='Markdown'
        )
    except Exception as e: logger.error(f"Error showing user management: {e}")

def view_user_files_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🔍 Enter User ID to view their files:\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_view_user_files_id)

def ban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           "🚫 Enter User ID and reason to ban.\n"
                           "Format: `user_id reason`\nExample: `12345678 Spamming`\n/cancel to abort.",
                           parse_mode='Markdown')
    bot.register_next_step_handler(msg, process_ban_user)

def process_ban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Ban cancelled."); return
    try:
        parts = message.text.strip().split(None, 1)
        if len(parts) < 2:
            bot.reply_to(message, "⚠️ Format: `user_id reason`\nExample: `12345678 Spamming`", parse_mode='Markdown')
            return
        user_id = int(parts[0])
        reason = parts[1]
        if user_id <= 0: raise ValueError("ID must be positive")
        if user_id == OWNER_ID: bot.reply_to(message, "⚠️ Cannot ban the Owner."); return
        if user_id in admin_ids: bot.reply_to(message, "⚠️ Cannot ban an Admin."); return
        if ban_user_db(user_id, reason, admin_id):
            bot.reply_to(message, f"✅ User `{user_id}` banned.\n📝 Reason: {reason}", parse_mode='Markdown')
            # Stop all scripts for banned user
            for project_name, _, _ in user_files.get(user_id, []):
                script_key = f"{user_id}_{project_name}"
                if script_key in bot_scripts:
                    kill_process_tree(bot_scripts[script_key])
                    del bot_scripts[script_key]
            try: bot.send_message(user_id, f"🚫 You have been banned from this bot.\nReason: {reason}")
            except Exception: pass
        else:
            bot.reply_to(message, "❌ Failed to ban user.")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error banning user: {e}", exc_info=True)
        bot.reply_to(message, f"❌ Error: {str(e)}")

def unban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "✅ Enter User ID to unban.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_unban_user)

def process_unban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Unban cancelled."); return
    try:
        user_id = int(message.text.strip())
        if user_id not in banned_users:
            bot.reply_to(message, f"ℹ️ User `{user_id}` is not banned.", parse_mode='Markdown'); return
        if unban_user_db(user_id):
            bot.reply_to(message, f"✅ User `{user_id}` has been unbanned.", parse_mode='Markdown')
            try: bot.send_message(user_id, "✅ Your ban has been lifted. You can use the bot again.")
            except Exception: pass
        else:
            bot.reply_to(message, "❌ Failed to unban user.")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error unbanning user: {e}"); bot.reply_to(message, f"❌ Error: {str(e)}")

def user_info_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👤 Enter User ID to get info.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_user_info)

def process_user_info(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Info request cancelled."); return
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        parts = [f"👤 *User ID:* `{user_id}`"]
        if user_id == OWNER_ID: parts.append("👑 *Status:* Owner")
        elif user_id in admin_ids: parts.append("🛡️ *Status:* Admin")
        elif user_id in banned_users: parts.append("🚫 *Status:* Banned")
        elif user_id in user_subscriptions:
            expiry = user_subscriptions[user_id].get('expiry')
            if expiry and expiry > datetime.now():
                days_left = (expiry - datetime.now()).days
                parts.append(f"⭐ *Status:* Premium (Expires in `{days_left}` days)")
            else: parts.append("🆓 *Status:* Free User (Expired sub)")
        else: parts.append("🆓 *Status:* Free User")
        file_count = get_user_file_count(user_id)
        file_limit = get_user_file_limit(user_id)
        limit_str = str(file_limit) if file_limit != float('inf') else "Unlimited"
        parts.append(f"📁 *Files:* `{file_count}/{limit_str}`")
        if user_id in user_limits: parts.append(f"⚙️ *Custom Limit:* `{user_limits[user_id]}`")
        running = sum(1 for pn, _, _ in user_files.get(user_id, []) if is_bot_running(user_id, pn))
        parts.append(f"🤖 *Running Scripts:* `{running}`")
        if user_id in active_users: parts.append("🟢 *Activity:* Active user")
        bot.reply_to(message, "\n".join(parts), parse_mode='Markdown')
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error getting user info: {e}"); bot.reply_to(message, f"❌ Error: {str(e)}")

def all_users_callback(call):
    bot.answer_callback_query(call.id)
    try:
        if not active_users:
            bot.edit_message_text("👥 *No active users yet.*", call.message.chat.id,
                                  call.message.message_id, parse_mode='Markdown')
            return
        users_list = list(active_users)
        chunk_size = 20
        total_pages = (len(users_list) + chunk_size - 1) // chunk_size
        display_users_list(call.message.chat.id, call.message.message_id, users_list, 0, total_pages, chunk_size)
    except Exception as e:
        logger.error(f"Error displaying all users: {e}")
        bot.answer_callback_query(call.id, "Error displaying users.", show_alert=True)

def display_users_list(chat_id, message_id, users_list, page, total_pages, chunk_size):
    start_idx = page * chunk_size
    end_idx = min(start_idx + chunk_size, len(users_list))
    user_chunk = users_list[start_idx:end_idx]
    msg_text = f"👥 *Active Users* (Page `{page + 1}/{total_pages}`)\n"
    msg_text += f"📊 Total: `{len(users_list)}` | 🚫 Banned: `{len(banned_users)}`\n\n"
    msg_text += "👇 Tap any user to open their file control panel:"
    markup = types.InlineKeyboardMarkup(row_width=1)
    for uid in user_chunk:
        if uid == OWNER_ID: s = "👑"
        elif uid in admin_ids: s = "🛡️"
        elif uid in banned_users: s = "🚫"
        elif uid in user_subscriptions and user_subscriptions[uid].get('expiry', datetime.min) > datetime.now(): s = "⭐"
        else: s = "🆓"
        file_count = get_user_file_count(uid)
        running = sum(1 for pn, _, _ in user_files.get(uid, []) if is_bot_running(uid, pn))
        markup.add(make_colored_button(
            f"{s} {uid}  |  📁 {file_count}  |  🟢 {running}",
            callback_data=f"admin_user_files_{uid}"
        ))
    if total_pages > 1:
        page_buttons = []
        if page > 0:
            page_buttons.append(make_colored_button("⬅️", callback_data=f"users_page_{page-1}"))
        page_buttons.append(make_colored_button(f"{page+1}/{total_pages}", callback_data="noop"))
        if page < total_pages - 1:
            page_buttons.append(make_colored_button("➡️", callback_data=f"users_page_{page+1}"))
        markup.row(*page_buttons)
    markup.row(make_colored_button("🔙 Back to User Mgmt", callback_data='user_management'))
    try:
        bot.edit_message_text(msg_text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
    except Exception as e: logger.error(f"Error editing users list: {e}")

def admin_user_files_callback(call):
    """Open full file control panel for a user clicked from All Users list."""
    bot.answer_callback_query(call.id)
    try:
        target_user_id = int(call.data.split('_')[3])
        _show_user_files_admin_inline(call.message.chat.id, call.message.message_id, target_user_id)
    except Exception as e:
        logger.error(f"Error in admin_user_files_callback: {e}")
        bot.answer_callback_query(call.id, "Error opening user panel.", show_alert=True)

def _show_user_files_admin_inline(chat_id, message_id, target_user_id):
    """Show full file control panel for a user (edits current message)."""
    files_list = user_files.get(target_user_id, [])
    if target_user_id == OWNER_ID: s = "👑 Owner"
    elif target_user_id in admin_ids: s = "🛡️ Admin"
    elif target_user_id in banned_users: s = "🚫 Banned"
    elif target_user_id in user_subscriptions and user_subscriptions[target_user_id].get('expiry', datetime.min) > datetime.now(): s = "⭐ Premium"
    else: s = "🆓 Free User"
    running_count = sum(1 for pn, _, _ in files_list if is_bot_running(target_user_id, pn))
    file_limit = get_user_file_limit(target_user_id)
    limit_str = str(file_limit) if file_limit != float('inf') else "∞"
    text = (f"👤 *User Project Control Panel*\n\n"
            f"🆔 ID: `{target_user_id}`\n"
            f"🔰 Status: {s}\n"
            f"📁 Projects: `{len(files_list)}/{limit_str}` | 🟢 Running: `{running_count}`\n\n")
    markup = types.InlineKeyboardMarkup(row_width=1)
    if not files_list:
        text += "_(No projects uploaded yet)_"
    else:
        text += "Tap a project to manage:"
        for project_name, main_file, file_type in sorted(files_list):
            is_running = is_bot_running(target_user_id, project_name)
            status_icon = "🟢" if is_running else "🔴"
            markup.add(make_colored_button(
                f"{status_icon} {project_name}",
                callback_data=f"umfile_{target_user_id}_{project_name}"
            ))
    markup.row(make_colored_button("🔙 Back to All Users", callback_data='all_users'))
    try:
        bot.edit_message_text(text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error showing user files admin inline: {e}")
        bot.send_message(chat_id, text, reply_markup=markup, parse_mode='Markdown')

def handle_users_page(call):
    try:
        page = int(call.data.split('_')[2])
        users_list = list(active_users)
        chunk_size = 20
        total_pages = (len(users_list) + chunk_size - 1) // chunk_size
        if 0 <= page < total_pages:
            bot.answer_callback_query(call.id)
            display_users_list(call.message.chat.id, call.message.message_id, users_list, page, total_pages, chunk_size)
    except Exception as e:
        logger.error(f"Error handling users page: {e}")
        bot.answer_callback_query(call.id, "Error.", show_alert=True)

def set_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           "🔧 Enter User ID and new limit.\nFormat: `user_id limit`\n/cancel to abort.",
                           parse_mode='Markdown')
    bot.register_next_step_handler(msg, process_set_user_limit)

def pending_files_callback(call):
    bot.answer_callback_query(call.id)
    _show_pending_files(call.message.chat.id, call.message.message_id)

def _show_pending_files(chat_id, message_id=None):
    """Show users who have pending files awaiting admin approval."""
    users_with_pending = set()
    for uid, files in pending_script_files.items():
        if files: users_with_pending.add(uid)
    for uid, files in pending_zip_files.items():
        if files: users_with_pending.add(uid)

    back_markup = types.InlineKeyboardMarkup()
    back_markup.row(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))

    if not users_with_pending:
        text = "📋 *Pending Files*\n\n✅ No files awaiting approval."
        if message_id:
            try: bot.edit_message_text(text, chat_id, message_id, reply_markup=back_markup, parse_mode='Markdown')
            except Exception: bot.send_message(chat_id, text, reply_markup=back_markup, parse_mode='Markdown')
        else:
            bot.send_message(chat_id, text, reply_markup=back_markup, parse_mode='Markdown')
        return

    total_files = sum(
        len(pending_script_files.get(uid, {})) + len(pending_zip_files.get(uid, {}))
        for uid in users_with_pending
    )
    text = (f"📋 *Pending Files*\n\n"
            f"📊 `{total_files}` file(s) from `{len(users_with_pending)}` user(s) awaiting review\n\n"
            f"👇 Tap a user to review their files:")

    markup = types.InlineKeyboardMarkup(row_width=1)
    for uid in sorted(users_with_pending):
        script_count = len(pending_script_files.get(uid, {}))
        zip_count = len(pending_zip_files.get(uid, {}))
        total = script_count + zip_count
        has_danger = (
            any(not info.get('is_safe', True) for info in pending_script_files.get(uid, {}).values())
            or any(
                bool(entry.get('patterns')) if isinstance(entry, dict) else False
                for entry in pending_zip_files.get(uid, {}).values()
            )
        )
        danger_icon = "🚨 " if has_danger else "📁 "
        markup.add(make_colored_button(
            f"{danger_icon}User {uid} — {total} file(s)" + (" [DANGER]" if has_danger else ""),
            callback_data=f"pending_user_{uid}"
        ))
    markup.row(make_colored_button("🔙 Back to Main", callback_data='back_to_main'))

    if message_id:
        try: bot.edit_message_text(text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
        except Exception: bot.send_message(chat_id, text, reply_markup=markup, parse_mode='Markdown')
    else:
        bot.send_message(chat_id, text, reply_markup=markup, parse_mode='Markdown')

def _show_pending_user_files(chat_id, message_id, target_user_id):
    """Show all pending files for a specific user with full security details, approve/reject, and chat."""
    script_files = dict(pending_script_files.get(target_user_id, {}))
    zip_files_dict = dict(pending_zip_files.get(target_user_id, {}))

    back_markup = types.InlineKeyboardMarkup()
    back_markup.row(make_colored_button("🔙 Back to Pending", callback_data='pending_files'))

    if not script_files and not zip_files_dict:
        try: bot.edit_message_text(f"✅ No pending projects for User `{target_user_id}`.", chat_id, message_id, reply_markup=back_markup, parse_mode='Markdown')
        except Exception: bot.send_message(chat_id, f"✅ No pending projects for User `{target_user_id}`.", reply_markup=back_markup, parse_mode='Markdown')
        return

    text = f"📋 *Pending Projects — User* `{target_user_id}`\n\n"
    markup = types.InlineKeyboardMarkup(row_width=2)

    for project_name, info in script_files.items():
        ftype = info.get('type', '?')
        main_file = info.get('main_file', project_name)
        is_safe = info.get('is_safe', True)
        security_msg_raw = info.get('security_msg', '')

        if is_safe:
            safety_line = "🛡️ Security: ✅ *Safe*"
        else:
            file_path = info.get('path', '')
            found_patterns = []
            if file_path and os.path.exists(file_path):
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    found_patterns = [p for p in DANGEROUS_PATTERNS if re.search(p, content, re.IGNORECASE)]
                except Exception:
                    pass
            if found_patterns:
                pattern_lines = '\n'.join(f"  ⚠️ `{p}`" for p in found_patterns[:15])
                if len(found_patterns) > 15:
                    pattern_lines += f"\n  ... and `{len(found_patterns) - 15}` more"
                safety_line = f"🚨 *DANGEROUS* — `{len(found_patterns)}` pattern(s):\n{pattern_lines}"
            else:
                safety_line = f"🚨 *DANGEROUS*\n  ⚠️ `{security_msg_raw}`"

        text += f"📦 *Project:* `{project_name}`\n?? *Main File:* `{main_file}` (`{ftype}`)\n{safety_line}\n\n"
        danger_label = "🚨 " if not is_safe else ""
        markup.add(make_colored_button(f"📦 {danger_label}{project_name}", callback_data='noop'))
        markup.row(
            make_colored_button("✅ Approve", callback_data=f"approve_file_{target_user_id}_{project_name}"),
            make_colored_button("❌ Reject", callback_data=f"reject_file_{target_user_id}_{project_name}")
        )

    for project_name, zip_entry in zip_files_dict.items():
        zip_found_patterns = zip_entry.get('patterns', []) if isinstance(zip_entry, dict) else []
        main_file = zip_entry.get('main_file', '(auto-detect)') if isinstance(zip_entry, dict) else '(auto-detect)'
        file_name_zip = zip_entry.get('file_name_zip', f"{project_name}.zip") if isinstance(zip_entry, dict) else f"{project_name}.zip"

        if zip_found_patterns:
            zip_pattern_lines = '\n'.join(f"  ⚠️ `{p}`" for p in zip_found_patterns[:15])
            if len(zip_found_patterns) > 15:
                zip_pattern_lines += f"\n  ... and `{len(zip_found_patterns) - 15}` more"
            zip_safety_line = f"🚨 *DANGEROUS* — `{len(zip_found_patterns)}` pattern(s):\n{zip_pattern_lines}"
            zip_danger_label = "🚨 "
        else:
            zip_safety_line = "🛡️ Security: ✅ *Safe*"
            zip_danger_label = ""

        text += f"📦 *Project:* `{project_name}`\n📁 *Archive:* `{file_name_zip}`\n📄 *Main File:* `{main_file or '(auto-detect)'}`\n{zip_safety_line}\n\n"
        markup.add(make_colored_button(f"📦 {zip_danger_label}{project_name}", callback_data='noop'))
        markup.row(
            make_colored_button("✅ Approve", callback_data=f"approve_zip_{target_user_id}_{project_name}"),
            make_colored_button("❌ Reject", callback_data=f"reject_zip_{target_user_id}_{project_name}")
        )

    markup.row(make_colored_button(f"💬 Chat with User {target_user_id}", callback_data=f"chat_user_{target_user_id}"))
    markup.row(make_colored_button("🔙 Back to Pending Users", callback_data='pending_files'))

    try: bot.edit_message_text(text, chat_id, message_id, reply_markup=markup, parse_mode='Markdown')
    except Exception: bot.send_message(chat_id, text, reply_markup=markup, parse_mode='Markdown')

def pending_user_callback(call):
    """Handle click on a user in the pending files list."""
    try: bot.answer_callback_query(call.id)
    except Exception: pass  # may already be expired if queue was busy
    try:
        target_user_id = int(call.data.split('_')[2])
        # Run in a thread so the telebot worker is never blocked by rendering
        threading.Thread(
            target=_show_pending_user_files,
            args=(call.message.chat.id, call.message.message_id, target_user_id),
            daemon=True
        ).start()
    except Exception as e:
        logger.error(f"Error in pending_user_callback: {e}")

def chat_user_callback(call):
    """Allow admin to send a chat message to a user."""
    bot.answer_callback_query(call.id)
    try:
        target_user_id = int(call.data.split('_')[2])
        msg = bot.send_message(
            call.message.chat.id,
            f"💬 *Send message to User* `{target_user_id}`\n\nType your message below, or /cancel to abort.",
            parse_mode='Markdown'
        )
        bot.register_next_step_handler(msg, lambda m: process_admin_chat_user(m, target_user_id))
    except Exception as e:
        logger.error(f"Error in chat_user_callback: {e}")

def process_admin_chat_user(message, target_user_id):
    """Process and send admin's message to a user."""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, "❌ Message cancelled."); return
    try:
        bot.send_message(target_user_id,
                         f"📨 *Message from Admin:*\n\n{message.text or '(Media message)'}",
                         parse_mode='Markdown')
        bot.reply_to(message, f"✅ Message sent to User `{target_user_id}` successfully.", parse_mode='Markdown')
    except Exception as e:
        bot.reply_to(message, f"❌ Failed to deliver message: `{md_escape(e)}`", parse_mode='Markdown')

def process_set_user_limit(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Cancelled."); return
    try:
        parts = message.text.split()
        if len(parts) != 2: raise ValueError("Format: user_id limit")
        user_id = int(parts[0]); limit = int(parts[1])
        if user_id <= 0 or limit <= 0: raise ValueError("ID and limit must be positive")
        if set_user_limit_db(user_id, limit, message.from_user.id):
            bot.reply_to(message, f"✅ File limit set to `{limit}` for user `{user_id}`.", parse_mode='Markdown')
            try: bot.send_message(user_id, f"⚙️ Your file limit has been set to `{limit}`.", parse_mode='Markdown')
            except Exception: pass
        else: bot.reply_to(message, "❌ Failed to set limit.")
    except ValueError as e:
        bot.reply_to(message, f"⚠️ Invalid input: {md_escape(e)}\nFormat: `user_id limit`", parse_mode='Markdown')
    except Exception as e:
        logger.error(f"Error setting limit: {e}"); bot.reply_to(message, f"❌ Error: {str(e)}")

def remove_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🗑️ Enter User ID to remove custom limit.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_user_limit)

def process_remove_user_limit(message):
    if message.from_user.id not in admin_ids: bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text.lower() == '/cancel': bot.reply_to(message, "❌ Cancelled."); return
    try:
        user_id = int(message.text.strip())
        if user_id not in user_limits:
            bot.reply_to(message, f"ℹ️ User `{user_id}` has no custom limit.", parse_mode='Markdown'); return
        if remove_user_limit_db(user_id):
            bot.reply_to(message, f"✅ Custom limit removed for user `{user_id}`.", parse_mode='Markdown')
            try: bot.send_message(user_id, "⚙️ Your custom file limit has been removed.")
            except Exception: pass
        else: bot.reply_to(message, "❌ Failed to remove limit.")
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid user ID. Must be a number.")
    except Exception as e:
        logger.error(f"Error removing limit: {e}"); bot.reply_to(message, f"❌ Error: {str(e)}")

# ============================================================
# --- File Approval Callbacks ---
# ============================================================
def process_approve_file(call):
    """Approve a pending .py or .js file."""
    data_parts = call.data.split('_', 3)
    if len(data_parts) < 4:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True); return
    user_id = int(data_parts[2])
    project_name = data_parts[3]
    if user_id not in pending_script_files or project_name not in pending_script_files[user_id]:
        bot.answer_callback_query(call.id, "❌ Pending entry not found.", show_alert=True); return
    entry = pending_script_files[user_id][project_name]
    file_path = entry['path']
    file_type = entry['type']
    main_file = entry.get('main_file', os.path.basename(file_path))
    project_folder = os.path.dirname(file_path)
    if not os.path.exists(file_path):
        bot.answer_callback_query(call.id, "❌ File not found.", show_alert=True); return
    try:
        if file_type == 'js': handle_js_file(file_path, user_id, project_folder, main_file, call.message, project_name)
        elif file_type == 'py': handle_py_file(file_path, user_id, project_folder, main_file, call.message, project_name)
        # Clean up from pending
        del pending_script_files[user_id][project_name]
        if not pending_script_files[user_id]: del pending_script_files[user_id]
        remove_pending_script_db(user_id, project_name)
        bot.answer_callback_query(call.id, "✅ Project approved!")
        bot.edit_message_text(f"✅ Project `{project_name}` approved for user `{user_id}`.",
                              call.message.chat.id, call.message.message_id, parse_mode='Markdown')
        try: bot.send_message(user_id, f"✅ Your project `{project_name}` has been approved and started!", parse_mode='Markdown')
        except Exception: pass
        remaining = len(pending_script_files.get(user_id, {})) + len(pending_zip_files.get(user_id, {}))
        if remaining > 0:
            try: _show_pending_user_files(call.message.chat.id, call.message.message_id, user_id)
            except Exception: pass
    except Exception as e:
        logger.error(f"Error processing approved file: {e}")
        bot.answer_callback_query(call.id, "❌ Error processing file.", show_alert=True)

def process_reject_file(call):
    """Reject a pending .py or .js file."""
    data_parts = call.data.split('_', 3)
    if len(data_parts) < 4:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True); return
    user_id = int(data_parts[2])
    project_name = data_parts[3]
    if user_id in pending_script_files and project_name in pending_script_files[user_id]:
        entry = pending_script_files[user_id][project_name]
        file_path = entry.get('path', '')
        if file_path and os.path.exists(file_path):
            try: os.remove(file_path)
            except Exception as e: logger.error(f"Error deleting rejected file: {e}")
        del pending_script_files[user_id][project_name]
        if not pending_script_files[user_id]: del pending_script_files[user_id]
        remove_pending_script_db(user_id, project_name)
    bot.answer_callback_query(call.id, "❌ Project rejected!")
    bot.edit_message_text(f"❌ Project `{project_name}` rejected for user `{user_id}`.",
                          call.message.chat.id, call.message.message_id, parse_mode='Markdown')
    try: bot.send_message(user_id, f"❌ Your project `{project_name}` was rejected for security reasons.", parse_mode='Markdown')
    except Exception: pass
    remaining = len(pending_script_files.get(user_id, {})) + len(pending_zip_files.get(user_id, {}))
    if remaining > 0:
        try: _show_pending_user_files(call.message.chat.id, call.message.message_id, user_id)
        except Exception: pass

def process_approve_zip(call):
    """Approve a pending ZIP file."""
    data_parts = call.data.split('_', 3)
    if len(data_parts) < 4:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True); return
    user_id = int(data_parts[2])
    project_name = data_parts[3]
    if user_id in pending_zip_files and project_name in pending_zip_files[user_id]:
        zip_entry = pending_zip_files[user_id][project_name]
        file_content = zip_entry['content'] if isinstance(zip_entry, dict) else zip_entry
        file_name_zip = zip_entry.get('file_name_zip', f"{project_name}.zip") if isinstance(zip_entry, dict) else f"{project_name}.zip"
        main_file = zip_entry.get('main_file') if isinstance(zip_entry, dict) else None
        user_folder = get_user_folder(user_id)
        try:
            del pending_zip_files[user_id][project_name]
            if not pending_zip_files[user_id]: del pending_zip_files[user_id]
            remove_pending_zip_db(user_id, project_name)
            bot.answer_callback_query(call.id, "✅ Archive approved!")
            bot.edit_message_text(f"✅ Archive for project `{project_name}` approved for user `{user_id}`.",
                                  call.message.chat.id, call.message.message_id, parse_mode='Markdown')
            try: bot.send_message(user_id, f"✅ Your project `{project_name}` archive has been approved and is being processed...", parse_mode='Markdown')
            except Exception: pass
            threading.Thread(target=process_zip_file, args=(file_content, file_name_zip, user_id, user_folder, call.message, project_name, main_file)).start()
        except Exception as e:
            logger.error(f"Error processing approved zip: {e}", exc_info=True)
            bot.answer_callback_query(call.id, "❌ Error processing archive.", show_alert=True)
    else:
        bot.answer_callback_query(call.id, "❌ File content not found. Ask user to re-upload.", show_alert=True)

def process_reject_zip(call):
    """Reject a pending ZIP file."""
    data_parts = call.data.split('_', 3)
    if len(data_parts) < 4:
        bot.answer_callback_query(call.id, "❌ Invalid data.", show_alert=True); return
    user_id = int(data_parts[2])
    project_name = data_parts[3]
    if user_id in pending_zip_files and project_name in pending_zip_files[user_id]:
        del pending_zip_files[user_id][project_name]
        if not pending_zip_files[user_id]: del pending_zip_files[user_id]
        remove_pending_zip_db(user_id, project_name)
    bot.answer_callback_query(call.id, "❌ Archive rejected!")
    bot.edit_message_text(f"❌ Archive for project `{project_name}` rejected for user `{user_id}`.",
                          call.message.chat.id, call.message.message_id, parse_mode='Markdown')
    try: bot.send_message(user_id, f"❌ Your project `{project_name}` archive was rejected for security reasons.", parse_mode='Markdown')
    except Exception: pass

# ============================================================
# --- Force Join Channel Callbacks ---
# ============================================================
def set_force_join_callback(call):
    """Admin: prompt to add a mandatory join channel via username, chat ID, or forwarded message."""
    bot.answer_callback_query(call.id)
    msg = bot.send_message(
        call.message.chat.id,
        "📢 *Add Force Channel*\n"
        "──────────────────────\n"
        "Send the channel in any of these ways:\n\n"
        "🔗 *Username*  →  `@mychannel`\n"
        "🆔 *Chat ID*   →  `-1001234567890`\n"
        "📨 *Forward*   →  Forward any message from the channel\n\n"
        "──────────────────────\n"
        "⚠️ Make sure this bot is an *admin* in that channel first.\n\n"
        "❌ /cancel to abort.",
        parse_mode='Markdown'
    )
    bot.register_next_step_handler(msg, process_set_force_join)

def process_set_force_join(message):
    global force_join_channels
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, "⚠️ Not authorized."); return
    if message.text and message.text.strip().lower() == '/cancel':
        bot.reply_to(message, "❌ Cancelled."); return

    channel = None

    # Method 1: Forwarded message from a channel
    if message.forward_from_chat and message.forward_from_chat.type == 'channel':
        channel = message.forward_from_chat.username
        if channel:
            channel = f"@{channel}"
        else:
            channel = str(message.forward_from_chat.id)

    # Method 2: Text input — username or chat ID
    elif message.text:
        raw = message.text.strip()
        if raw.lstrip('-').isdigit():
            channel = raw
        else:
            channel = raw if raw.startswith('@') else f"@{raw}"
    else:
        bot.reply_to(message,
            "⚠️ Could not detect channel.\n"
            "Send a `@username`, a chat ID like `-1001234567890`, or forward a message from the channel.",
            parse_mode='Markdown')
        return

    # Verify bot can access the channel
    try:
        chat_info = bot.get_chat(channel)
        channel = f"@{chat_info.username}" if chat_info.username else str(chat_info.id)
        title = chat_info.title or channel
    except Exception:
        bot.reply_to(message,
            f"❌ *Could not access* `{channel}`\n"
            "──────────────────────\n"
            "Please check that:\n\n"
            "› Channel *exists*\n"
            "› This bot is an *admin* in the channel\n"
            "› The username/ID is *correct*",
            parse_mode='Markdown')
        return

    # Generate invite link — works for both public and private channels
    try:
        invite_link = bot.export_chat_invite_link(channel)
    except Exception:
        # Fallback for public channels if export fails
        invite_link = f"https://t.me/{channel.lstrip('@')}" if channel.startswith('@') else None

    if any(e['channel'] == channel for e in force_join_channels):
        bot.reply_to(message, f"ℹ️ *{title}* is already in the mandatory join list.", parse_mode='Markdown')
        return

    force_join_channels.append({'channel': channel, 'title': title, 'invite_link': invite_link})
    add_force_join_channel_db(channel, title, invite_link, message.from_user.id)
    bot.reply_to(message,
        f"✅ *{title}* added to mandatory join list.\n"
        f"📋 Total channels: *{len(force_join_channels)}*",
        parse_mode='Markdown')
    logger.info(f"Force join channel added: {title} ({channel}) by {message.from_user.id}")

def remove_force_join_callback(call):
    """Admin: remove a specific channel from the mandatory join list."""
    global force_join_channels
    channel = call.data[len('remove_force_join_'):]
    entry = next((e for e in force_join_channels if e['channel'] == channel), None)
    if not entry:
        bot.answer_callback_query(call.id, "ℹ️ Channel not in list.", show_alert=True); return
    force_join_channels.remove(entry)
    remove_force_join_channel_db(channel)
    bot.answer_callback_query(call.id, f"✅ {entry['title']} removed!")
    logger.info(f"Force join channel removed: {entry['title']} ({channel}) by {call.from_user.id}")
    # Refresh panel inline
    markup = types.InlineKeyboardMarkup(row_width=1)
    if force_join_channels:
        for e in force_join_channels:
            markup.add(make_colored_button(
                f"🔴 Remove {e['title']}", callback_data=f"remove_force_join_{e['channel']}"))
    markup.add(make_colored_button("➕ Add Channel", callback_data="set_force_join"))
    if force_join_channels:
        ch_list = '\n'.join(f"  {i+1}. *{e['title']}*" for i, e in enumerate(force_join_channels))
        status = (
            f"🔒 *Access restricted — {len(force_join_channels)} channel(s) active.*\n"
            f"Users must join all channels before using this bot.\n\n"
            f"──────────────────────\n"
            f"📋 *Required Channels:*\n{ch_list}\n\n"
            f"──────────────────────\n"
            f"👇 Manage channels below:"
        )
    else:
        status = (
            "🔕 *No channels active.*\n"
            "Users can access the bot freely.\n\n"
            "──────────────────────\n"
            "👇 Add a channel to restrict access:"
        )
    try:
        bot.edit_message_text(
            f"   📢 Force Join Channels\n"
            f"──────────────────────\n"
            f"{status}",
            call.message.chat.id, call.message.message_id,
            parse_mode='Markdown', reply_markup=markup)
    except Exception: pass

def check_joined_callback(call):
    """User presses 'I've Joined All' — re-check membership for all channels."""
    user_id = call.from_user.id
    if not force_join_channels:
        bot.answer_callback_query(call.id, "✅ No restriction active.")
        return
    unjoined = [e for e in force_join_channels if not is_user_in_channel(user_id, e['channel'])]
    if not unjoined:
        bot.answer_callback_query(call.id, "✅ Verified! Welcome.", show_alert=True)
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, "✅ Access granted! Use /start to continue.")
    else:
        titles = ', '.join(e['title'] for e in unjoined)
        bot.answer_callback_query(
            call.id,
            f"❌ Still not joined: {titles}",
            show_alert=True)

# ============================================================
# --- Cleanup ---
# ============================================================
def cleanup():
    logger.warning("Shutdown. Cleaning up processes...")
    script_keys_to_stop = list(bot_scripts.keys())
    if not script_keys_to_stop: logger.info("No scripts running."); return
    for key in script_keys_to_stop:
        if key in bot_scripts:
            logger.info(f"Stopping: {key}")
            kill_process_tree(bot_scripts[key])
    logger.warning("Cleanup finished.")
atexit.register(cleanup)

# ============================================================
# --- Main Execution ---
# ============================================================
if __name__ == '__main__':
    def startup():
        """Initialize DB and load persisted data. Called once at startup."""
        init_db()
        load_data()

    logger.info("="*50 + "\n🤖 Astroneth Hosting Starting...\n" +
                f"🐍 Python: {sys.version.split()[0]}\n"
                f"🔧 Base Dir: {BASE_DIR}\n📁 Upload Dir: {UPLOAD_BOTS_DIR}\n"
                f"📊 Data Dir: {IROTECH_DIR}\n🔑 Owner ID: {OWNER_ID}\n"
                f"🛡️ Admins: {len(admin_ids)} | 🚫 Banned: {len(banned_users)}\n" + "="*50)
    startup()
    keep_alive()
    setup_command_menu()
    logger.info("🚀 Starting polling...")
    while True:
        try:
            bot.infinity_polling(logger_level=logging.INFO, timeout=60, long_polling_timeout=30)
        except requests.exceptions.ReadTimeout:
            logger.warning("Polling ReadTimeout. Restarting in 5s...")
            time.sleep(5)
        except requests.exceptions.ConnectionError as ce:
            logger.error(f"Polling ConnectionError: {ce}. Retrying in 15s...")
            time.sleep(15)
        except Exception as e:
            logger.critical(f"💥 Unrecoverable polling error: {e}", exc_info=True)
            logger.info("Restarting polling in 30s...")
            time.sleep(30)
        finally:
            logger.warning("Polling attempt finished. Will restart if in loop.")
            time.sleep(1)