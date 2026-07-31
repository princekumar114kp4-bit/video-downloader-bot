"""
Premium File Sharing Telegram Bot
------------------------------------
- Sirf AUTHORIZED_USERS (owner/admins) hi file upload/store kar sakte hain.
- Koi bhi normal user file store NAHI kar sakta — sirf link/ID se receive kar sakta hai.
- Owner file bhejta hai -> bot use PRIVATE CHANNEL me forward karta hai (permanent storage)
  aur ek direct SHARE LINK deta hai: https://t.me/<bot_username>?start=<file_id>
- Ye link kisi ko bhi bhej do -> wo bot ko /start karte hi seedha file receive kar lega.
  (Jaise premium "file to link" bots kaam karte hain)

Requirements:
    pip install python-telegram-bot==21.0

Setup steps:
    1. @BotFather se bot bana kar token le lo. Bot ka USERNAME bhi note kar lo
       (jaise @MyFileBot) — share link banane ke liye chahiye hoga.
    2. Apna Telegram numeric user ID pata karo -> @userinfobot ko koi message bhejo,
       wo tumhara ID dega (jaise 123456789).
    3. Ek naya PRIVATE channel banao, bot ko us channel me ADMIN banao
       ("Post Messages" permission ke saath).
    4. Channel ID nikalo -> channel ka koi message @userinfobot ko forward karo,
       wo channel ID dega jaise -1001234567890.
    5. Neeche BOT_TOKEN, BOT_USERNAME, STORAGE_CHANNEL_ID, AUTHORIZED_USERS fill karo.
    6. Run karo: python premium_file_bot.py

Note:
    - AUTHORIZED_USERS list me jitne bhi Telegram user ID daaloge, sirf wahi log
      file upload/store kar payenge. Baaki sab ke liye upload band rahega.
    - "storage.json" me sirf metadata (channel message_id, owner, file naam) rehta hai.
"""

import json
import os
import uuid
import logging
from datetime import datetime, timezone

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

# ---------------- CONFIG ----------------
BOT_TOKEN = "8781514301:AAH4HhLVD0ye_JjoUQVC7VjtBYflxE6qz80"  # <-- token revoke karke NAYA token daalo
BOT_USERNAME = "FilesharingUbot"  # ⚠️ @ MAT lagana yaha — sirf naam
STORAGE_CHANNEL_ID = -1004439722221  # apna private channel ID

# Sirf inhi user IDs ko file upload/store karne ki permission hogi.
# Apna ID daalo, aur chaho to aur logon ke bhi (comma se separate karke).
AUTHORIZED_USERS = [8597878282]  # <-- apna Telegram user ID yaha daalo

DB_FILE = "storage.json"

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)


# ---------------- STORAGE HELPERS ----------------
def load_db():
    if not os.path.exists(DB_FILE):
        return {}
    try:
        with open(DB_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, FileNotFoundError):
        return {}


def save_db(data):
    with open(DB_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def is_authorized(user_id: int) -> bool:
    return user_id in AUTHORIZED_USERS


def format_size(size_bytes: int) -> str:
    if not size_bytes:
        return "Unknown"
    for unit in ["B", "KB", "MB", "GB"]:
        if size_bytes < 1024:
            return f"{size_bytes:.1f} {unit}" if unit != "B" else f"{size_bytes} {unit}"
        size_bytes /= 1024
    return f"{size_bytes:.1f} TB"


# ---------------- COMMAND HANDLERS ----------------
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # Agar /start <file_id> ke saath aaya hai (deep link click), to seedha file bhejo
    if context.args:
        file_id = context.args[0]
        await send_file_by_id(update, context, file_id)
        return

    if is_authorized(update.message.from_user.id):
        await update.message.reply_text(
            "👋 Welcome back. Please send me any file, photo, video or audio whenever you're ready, "
            "and I will store it safely for you.\n\n"
            "Once saved, I'll hand you a private link 🔗 — simply pass that along, and whoever receives "
            "it will get the file the moment they open it."
        )
    else:
        await update.message.reply_text(
            "👋 Hello, and welcome. This is a private file-sharing assistant.\n\n"
            "If someone has shared a link with you, please go ahead and open it — your file will "
            "be on its way shortly. 📁"
        )


async def handle_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.message
    user_id = message.from_user.id

    # ---- SIRF AUTHORIZED USER HI STORE KAR SAKTA HAI ----
    if not is_authorized(user_id):
        await message.reply_text(
            "🙏 I'm afraid I can't accept uploads from you — this assistant only stores files for "
            "its owner. If someone has sent you a link, please feel free to open it instead."
        )
        return

    file_type = None
    file_name = "file"

    if message.document:
        file_type = "document"
        file_name = message.document.file_name or "document"
    elif message.photo:
        file_type = "photo"
        file_name = "photo.jpg"
    elif message.video:
        file_type = "video"
        file_name = message.video.file_name or "video.mp4"
    elif message.audio:
        file_type = "audio"
        file_name = message.audio.file_name or "audio.mp3"
    elif message.voice:
        file_type = "voice"
        file_name = "voice.ogg"
    else:
        await message.reply_text(
            "🤔 That particular file type isn't something I can store just yet — a document, "
            "photo, video, audio clip, or voice note would work perfectly."
        )
        return

    try:
        forwarded = await context.bot.forward_message(
            chat_id=STORAGE_CHANNEL_ID,
            from_chat_id=message.chat_id,
            message_id=message.message_id,
        )
    except Exception as e:
        logger.error(f"Channel me forward karte waqt error: {type(e).__name__}: {e}")
        await message.reply_text(
            "⚠️ I wasn't able to store that file just now.\n\n"
            f"Here is what went wrong: `{type(e).__name__}: {e}`\n\n"
            "Could you please check the following?\n"
            "• Is the bot an administrator in the storage channel, with permission to post messages?\n"
            "• Is the storage channel ID correct? You may verify it using @RawDataBot.",
            parse_mode="Markdown",
        )
        return

    file_id = str(uuid.uuid4())[:8]

    # File size nikaalo (jo bhi type ho usse)
    size_bytes = 0
    if file_type == "document":
        size_bytes = message.document.file_size or 0
    elif file_type == "video":
        size_bytes = message.video.file_size or 0
    elif file_type == "audio":
        size_bytes = message.audio.file_size or 0
    elif file_type == "voice":
        size_bytes = message.voice.file_size or 0

    db = load_db()
    db[file_id] = {
        "channel_message_id": forwarded.message_id,
        "file_type": file_type,
        "file_name": file_name,
        "file_size": size_bytes,
        "owner": user_id,
        "uploaded_at": datetime.now(timezone.utc).strftime("%d %b %Y, %H:%M UTC"),
    }
    save_db(db)

    share_link = f"https://t.me/{BOT_USERNAME}?start={file_id}"
    size_str = format_size(size_bytes)

    keyboard = InlineKeyboardMarkup(
        [[InlineKeyboardButton("🔗 Share this file", url=f"https://t.me/share/url?url={share_link}")]]
    )

    await message.reply_text(
        f"✅ Your file has been saved.\n\n"
        f"📁 *Name:* {file_name}\n"
        f"📦 *Size:* {size_str}\n"
        f"🆔 *Reference ID:* `{file_id}`\n"
        f"🕒 *Saved on:* {db[file_id]['uploaded_at']}\n\n"
        f"🔗 Here is the private link — feel free to share it with anyone:\n{share_link}",
        parse_mode="Markdown",
        reply_markup=keyboard,
    )


async def send_file_by_id(update: Update, context: ContextTypes.DEFAULT_TYPE, file_id: str):
    db = load_db()
    record = db.get(file_id)

    if not record:
        await update.message.reply_text(
            "🔍 I couldn't find a file matching that link — it may have expired, or the link "
            "might not be quite right."
        )
        return

    size_str = format_size(record.get("file_size", 0))

    await update.message.reply_text(
        f"📁 Here is *{record['file_name']}* ({size_str}). One moment, please. ⏳",
        parse_mode="Markdown",
    )

    try:
        await context.bot.copy_message(
            chat_id=update.message.chat_id,
            from_chat_id=STORAGE_CHANNEL_ID,
            message_id=record["channel_message_id"],
        )
    except Exception as e:
        logger.error(f"File bhejte waqt error: {e}")
        await update.message.reply_text(
            "😔 I'm sorry, something went wrong while sending that file — it may have been removed "
            "from storage."
        )


async def get_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Fallback manual command: /get <id> — koi bhi user use kar sakta hai (receive-only)."""
    if not context.args:
        await update.message.reply_text("📌 Please include a reference ID, like this: /get <id>")
        return
    await send_file_by_id(update, context, context.args[0])


async def my_files(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.message.from_user.id

    if not is_authorized(user_id):
        await update.message.reply_text("🔒 This particular list is only available to the owner.")
        return

    db = load_db()
    user_files = {fid: rec for fid, rec in db.items() if rec["owner"] == user_id}

    if not user_files:
        await update.message.reply_text("📭 You haven't saved any files with me yet.")
        return

    lines = ["📂 Here are the files you've saved so far:\n"]
    for fid, rec in user_files.items():
        link = f"https://t.me/{BOT_USERNAME}?start={fid}"
        size_str = format_size(rec.get("file_size", 0))
        lines.append(
            f"📁 *{rec['file_name']}*\n"
            f"🆔 Reference ID: `{fid}` · 📦 Size: {size_str}\n"
            f"{link}\n"
        )

    await update.message.reply_text("\n".join(lines), parse_mode="Markdown")


async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "🤔 I'm not quite sure how to help with that. If you have a share link, please go ahead "
        "and open it — I'll take care of the rest."
    )


# ---------------- MAIN ----------------
def main():
    app = ApplicationBuilder().token(BOT_TOKEN).build()

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("get", get_file))
    app.add_handler(CommandHandler("myfiles", my_files))

    app.add_handler(
        MessageHandler(
            filters.Document.ALL
            | filters.PHOTO
            | filters.VIDEO
            | filters.AUDIO
            | filters.VOICE,
            handle_file,
        )
    )

    app.add_handler(MessageHandler(filters.COMMAND, unknown))

    logger.info("Bot chalu ho gaya... 🚀")
    app.run_polling()


if __name__ == "__main__":
    main()
