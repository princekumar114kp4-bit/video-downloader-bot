"""
Premium File Sharing Telegram Bot
----------------------------------

Features:
- Sirf AUTHORIZED_USERS files upload/store kar sakte hain.
- Normal users sirf shared link ya /get FILE_ID se file receive kar sakte hain.
- File size kahin display nahi hoga.
- Received file ke saath "📣 JOIN CHANNEL" inline button aayega.
- Authorized uploader apni file /delete FILE_ID se delete kar sakta hai.
- /start par authorized user ko complete command menu milega.
- /help command available hai.
- /myfiles se apni uploaded files dekh sakte ho.
- /get FILE_ID se file manually receive kar sakte ho.
- Private storage channel mein files store hoti hain.
- Har file ka private deep-link generate hota hai.

Install:
    pip install python-telegram-bot==21.0

IMPORTANT:
    Apna NEW BOT TOKEN neeche BOT_TOKEN mein daalo.
    Purana exposed token use mat karna.
"""

import html
import json
import logging
import os
import uuid
from datetime import datetime, timezone

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    ContextTypes,
    filters,
)


# =========================================================
# CONFIG
# =========================================================

# =========================================================
# APNA NEW BOT TOKEN YAHAN DALO
# =========================================================

BOT_TOKEN = "8781514301:AAH4HhLVD0ye_JjoUQVC7VjtBYflxE6qz80"


# Bot username WITHOUT @
BOT_USERNAME = "FilesharingUbot"


# Private storage channel ID
STORAGE_CHANNEL_ID = -1004439722221


# Sirf in Telegram user IDs ko upload/delete permission hai
AUTHORIZED_USERS = [
    8597878282
]


# =========================================================
# APNA CHANNEL LINK YAHAN DALO
# =========================================================

JOIN_CHANNEL_URL = "https://t.me/U_BOT_CHANNEL"


# Example:
# JOIN_CHANNEL_URL = "https://t.me/MyChannel"
#
# Ya private channel invite:
# JOIN_CHANNEL_URL = "https://t.me/+xxxxxxxxxxxxxxxx"


# Database file
DB_FILE = "storage.json"


# =========================================================
# LOGGING
# =========================================================

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)

logger = logging.getLogger(__name__)


# =========================================================
# DATABASE
# =========================================================

def load_db():
    if not os.path.exists(DB_FILE):
        return {}

    try:
        with open(DB_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)

            if isinstance(data, dict):
                return data

            return {}

    except (json.JSONDecodeError, FileNotFoundError):
        return {}


def save_db(data):
    temp_file = DB_FILE + ".tmp"

    with open(temp_file, "w", encoding="utf-8") as f:
        json.dump(
            data,
            f,
            ensure_ascii=False,
            indent=2
        )

    os.replace(temp_file, DB_FILE)


def is_authorized(user_id: int) -> bool:
    return user_id in AUTHORIZED_USERS


def safe_html(text: str) -> str:
    return html.escape(
        str(text),
        quote=False
    )


# =========================================================
# INLINE BUTTONS
# =========================================================

def join_channel_keyboard():
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    "📣 JOIN CHANNEL",
                    url=JOIN_CHANNEL_URL
                )
            ]
        ]
    )


def share_keyboard(share_link: str):
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    "🔗 SHARE FILE",
                    url=f"https://t.me/share/url?url={share_link}"
                )
            ],
            [
                InlineKeyboardButton(
                    "📣 JOIN CHANNEL",
                    url=JOIN_CHANNEL_URL
                )
            ]
        ]
    )


# =========================================================
# START / HELP MENU
# =========================================================

def get_menu_text(authorized: bool):

    if authorized:

        return (
            "<b>👑 PREMIUM FILE MANAGER</b>\n"
            "━━━━━━━━━━━━━━━━━━\n\n"

            "📤 <b>UPLOAD</b>\n"
            "Simply send me a document, photo, video, "
            "audio or voice message.\n\n"

            "I will store the file securely and create "
            "a private share link for you.\n\n"

            "⚙️ <b>COMMANDS</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"

            "<code>/start</code> — Open main menu\n"
            "<code>/help</code> — Show command list\n"
            "<code>/get FILE_ID</code> — Receive a file\n"
            "<code>/myfiles</code> — Show your files\n"
            "<code>/delete FILE_ID</code> — Delete your file\n\n"

            "✨ <i>Premium mode is active for your account.</i>"
        )

    return (
        "<b>✨ PREMIUM FILE DELIVERY</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"

        "📁 <b>FILE RECEIVER</b>\n"
        "Open a valid file-sharing link and "
        "I will send the file here.\n\n"

        "⚙️ <b>COMMANDS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"

        "<code>/start</code> — Open main menu\n"
        "<code>/help</code> — Show command list\n"
        "<code>/get FILE_ID</code> — Receive a file\n\n"

        "🔐 <i>File uploading is restricted to authorized users.</i>"
    )


# =========================================================
# /START
# =========================================================

async def start(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    message = update.effective_message
    user = update.effective_user

    # -----------------------------------------------------
    # Deep link:
    # /start ABC123
    # -----------------------------------------------------

    if context.args:

        file_id = context.args[0].strip()

        await send_file_by_id(
            update,
            context,
            file_id
        )

        return

    # -----------------------------------------------------
    # Normal start
    # -----------------------------------------------------

    await message.reply_text(
        get_menu_text(
            is_authorized(user.id)
        ),
        parse_mode="HTML",
        disable_web_page_preview=True
    )


# =========================================================
# /HELP
# =========================================================

async def help_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    user = update.effective_user

    await update.effective_message.reply_text(
        get_menu_text(
            is_authorized(user.id)
        ),
        parse_mode="HTML",
        disable_web_page_preview=True
    )


# =========================================================
# HANDLE FILE UPLOAD
# =========================================================

async def handle_file(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    message = update.effective_message
    user = update.effective_user

    # -----------------------------------------------------
    # AUTH CHECK
    # -----------------------------------------------------

    if not is_authorized(user.id):

        await message.reply_text(
            "<b>🔒 UPLOAD ACCESS LOCKED</b>\n\n"
            "Only authorized users can upload and store files.\n\n"
            "You can still receive shared files.",
            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # DETECT FILE TYPE
    # -----------------------------------------------------

    file_type = None
    file_name = "file"

    if message.document:

        file_type = "document"

        file_name = (
            message.document.file_name
            or "document"
        )

    elif message.photo:

        file_type = "photo"
        file_name = "photo.jpg"

    elif message.video:

        file_type = "video"

        file_name = (
            message.video.file_name
            or "video.mp4"
        )

    elif message.audio:

        file_type = "audio"

        file_name = (
            message.audio.file_name
            or "audio.mp3"
        )

    elif message.voice:

        file_type = "voice"
        file_name = "voice.ogg"

    else:

        await message.reply_text(
            "<b>⚠️ UNSUPPORTED FILE</b>\n\n"
            "Please send a document, photo, video, "
            "audio or voice message.",
            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # SAVE FILE TO PRIVATE CHANNEL
    # -----------------------------------------------------

    try:

        forwarded = await context.bot.forward_message(

            chat_id=STORAGE_CHANNEL_ID,

            from_chat_id=message.chat_id,

            message_id=message.message_id
        )

    except Exception as e:

        logger.exception(
            "Storage channel forwarding failed"
        )

        await message.reply_text(

            "<b>❌ UPLOAD FAILED</b>\n\n"

            "I couldn't save this file.\n\n"

            f"Error: <code>{safe_html(type(e).__name__)}</code>\n\n"

            "Make sure the bot is an administrator "
            "in your storage channel.",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # CREATE FILE ID
    # -----------------------------------------------------

    file_id = uuid.uuid4().hex[:10].upper()

    uploaded_at = datetime.now(
        timezone.utc
    ).strftime(
        "%d %b %Y, %H:%M UTC"
    )

    # -----------------------------------------------------
    # SAVE METADATA
    #
    # SIZE intentionally NOT stored
    # -----------------------------------------------------

    db = load_db()

    db[file_id] = {

        "channel_message_id":
            forwarded.message_id,

        "file_type":
            file_type,

        "file_name":
            file_name,

        "owner":
            user.id,

        "uploaded_at":
            uploaded_at,
    }

    save_db(db)

    # -----------------------------------------------------
    # SHARE LINK
    # -----------------------------------------------------

    share_link = (
        f"https://t.me/"
        f"{BOT_USERNAME}"
        f"?start={file_id}"
    )

    safe_name = safe_html(file_name)

    # -----------------------------------------------------
    # SUCCESS MESSAGE
    # -----------------------------------------------------

    await message.reply_text(

        "<b>✅ FILE STORED SUCCESSFULLY</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"

        f"📁 <b>Name:</b> {safe_name}\n"
        f"🆔 <b>ID:</b> <code>{file_id}</code>\n"
        f"🕒 <b>Saved:</b> {uploaded_at}\n\n"

        "🔗 <b>PRIVATE SHARE LINK</b>\n"
        f"<code>{share_link}</code>\n\n"

        "✨ Share this link with anyone.\n"
        "They will receive the file directly.",

        parse_mode="HTML",

        disable_web_page_preview=True,

        reply_markup=share_keyboard(
            share_link
        )
    )


# =========================================================
# SEND FILE BY ID
# =========================================================

async def send_file_by_id(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    file_id: str
):

    message = update.effective_message

    file_id = file_id.strip().upper()

    db = load_db()

    record = db.get(file_id)

    # -----------------------------------------------------
    # FILE NOT FOUND
    # -----------------------------------------------------

    if not record:

        await message.reply_text(

            "<b>🔍 FILE NOT FOUND</b>\n\n"

            "This file ID is invalid or the file "
            "has already been deleted.",

            parse_mode="HTML"
        )

        return

    safe_name = safe_html(
        record.get(
            "file_name",
            "file"
        )
    )

    # -----------------------------------------------------
    # PREMIUM STATUS MESSAGE
    # -----------------------------------------------------

    status = await message.reply_text(

        "<b>✨ SECURE FILE DELIVERY</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"

        f"📁 <b>{safe_name}</b>\n"

        "⏳ Preparing your file...",

        parse_mode="HTML"
    )

    try:

        # -------------------------------------------------
        # FILE SEND
        #
        # JOIN CHANNEL BUTTON DIRECTLY FILE KE SAATH
        # -------------------------------------------------

        await context.bot.copy_message(

            chat_id=message.chat_id,

            from_chat_id=STORAGE_CHANNEL_ID,

            message_id=record[
                "channel_message_id"
            ],

            reply_markup=join_channel_keyboard()
        )

        # -------------------------------------------------
        # REMOVE STATUS MESSAGE
        # -------------------------------------------------

        try:

            await status.delete()

        except Exception:

            pass

    except Exception as e:

        logger.exception(
            "File delivery failed"
        )

        try:

            await status.edit_text(

                "<b>❌ DELIVERY FAILED</b>\n\n"

                "This file may have been deleted "
                "from storage.\n\n"

                f"<code>{safe_html(type(e).__name__)}</code>",

                parse_mode="HTML"
            )

        except Exception:

            await message.reply_text(

                "<b>❌ DELIVERY FAILED</b>\n\n"

                "This file may have been removed "
                "from storage.",

                parse_mode="HTML"
            )


# =========================================================
# /GET
# =========================================================

async def get_file(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    if not context.args:

        await update.effective_message.reply_text(

            "<b>📌 GET FILE</b>\n\n"

            "Usage:\n"
            "<code>/get FILE_ID</code>\n\n"

            "Example:\n"
            "<code>/get ABC1234567</code>",

            parse_mode="HTML"
        )

        return

    await send_file_by_id(

        update,
        context,
        context.args[0]
    )


# =========================================================
# /MYFILES
# =========================================================

async def my_files(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    user_id = update.effective_user.id

    # -----------------------------------------------------
    # AUTH CHECK
    # -----------------------------------------------------

    if not is_authorized(user_id):

        await update.effective_message.reply_text(

            "<b>🔒 ACCESS DENIED</b>\n\n"

            "This command is only available "
            "to authorized upload users.",

            parse_mode="HTML"
        )

        return

    db = load_db()

    user_files = {

        fid: rec

        for fid, rec in db.items()

        if rec.get("owner") == user_id
    }

    # -----------------------------------------------------
    # EMPTY
    # -----------------------------------------------------

    if not user_files:

        await update.effective_message.reply_text(

            "<b>📭 NO SAVED FILES</b>\n\n"

            "You haven't uploaded any files yet.",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # BUILD RESPONSE
    # -----------------------------------------------------

    lines = [

        "<b>📂 YOUR SAVED FILES</b>",

        "━━━━━━━━━━━━━━━━━━",

        ""
    ]

    for fid, rec in user_files.items():

        safe_name = safe_html(
            rec.get(
                "file_name",
                "file"
            )
        )

        link = (
            f"https://t.me/"
            f"{BOT_USERNAME}"
            f"?start={fid}"
        )

        lines.append(

            f"📁 <b>{safe_name}</b>\n"
            f"🆔 <code>{fid}</code>\n"
            f"🔗 {link}\n"

        )

    await update.effective_message.reply_text(

        "\n".join(lines),

        parse_mode="HTML",

        disable_web_page_preview=True
    )


# =========================================================
# /DELETE
# =========================================================

async def delete_file(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):

    user_id = update.effective_user.id

    # -----------------------------------------------------
    # AUTH
    # -----------------------------------------------------

    if not is_authorized(user_id):

        await update.effective_message.reply_text(

            "<b>🔒 DELETE ACCESS LOCKED</b>\n\n"

            "Only authorized users can delete files.",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # ID CHECK
    # -----------------------------------------------------

    if not context.args:

        await update.effective_message.reply_text(

            "<b>🗑️ DELETE FILE</b>\n\n"

            "Usage:\n"
            "<code>/delete FILE_ID</code>\n\n"

            "Example:\n"
            "<code>/delete ABC1234567</code>",

            parse_mode="HTML"
        )

        return

    file_id = context.args[0].strip().upper()

    db = load_db()

    record = db.get(file_id)

    # -----------------------------------------------------
    # NOT FOUND
    # -----------------------------------------------------

    if not record:

        await update.effective_message.reply_text(

            "<b>🔍 FILE NOT FOUND</b>\n\n"

            "That file ID does not exist "
            "in the database.",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # OWNER CHECK
    # -----------------------------------------------------

    if record.get("owner") != user_id:

        await update.effective_message.reply_text(

            "<b>⛔ NOT YOUR FILE</b>\n\n"

            "You can only delete files "
            "that you uploaded.",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # DELETE FROM STORAGE CHANNEL
    # -----------------------------------------------------

    try:

        await context.bot.delete_message(

            chat_id=STORAGE_CHANNEL_ID,

            message_id=record[
                "channel_message_id"
            ]
        )

    except Exception as e:

        logger.exception(
            "Storage message deletion failed"
        )

        await update.effective_message.reply_text(

            "<b>❌ DELETE FAILED</b>\n\n"

            "I could not delete the stored file "
            "from the storage channel.\n\n"

            "Make sure the bot has delete permission "
            "in the storage channel.\n\n"

            f"<code>{safe_html(type(e).__name__)}</code>",

            parse_mode="HTML"
        )

        return

    # -----------------------------------------------------
    # DELETE DATABASE RECORD
    # -----------------------------------------------------

    del db[file_id]

    save_db(db)

    # -----------------------------------------------------
    # SUCCESS
    # -----------------------------------------------------

    await update.effective_message.reply_text(

        "<b>🗑️ FILE DELETED SUCCESSFULLY</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"

        f"🆔 <code>{file_id}</code>\n\n"

        "✅ Storage message deleted.\n"