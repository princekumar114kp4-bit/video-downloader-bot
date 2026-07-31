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

from telegram import Update
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

# ---------------- CONFIG ----------------
BOT_TOKEN = "8465780049:AAFCj2uVmo-4CAkYLbzNyJmsrsg3WrZUJMc"
BOT_USERNAME = "Chatbot_Ai_Ubot"  # bina @ ke, jaise: MyFileBot
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


# ---------------- COMMAND HANDLERS ----------------
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # Agar /start <file_id> ke saath aaya hai (deep link click), to seedha file bhejo
    if context.args:
        file_id = context.args[0]
        await send_file_by_id(update, context, file_id)
        return

    if is_authorized(update.message.from_user.id):
        await update.message.reply_text(
            "👋 Namaste Owner! Mujhe koi bhi file, photo, video ya audio bhejo.\n"
            "Main use permanently save karke ek SHARE LINK dunga.\n\n"
            "Wo link kisi ko bhi bhej do, wo /start karte hi file paa lega."
        )
    else:
        await update.message.reply_text(
            "👋 Namaste! Ye ek private file-sharing bot hai.\n"
            "Aapko koi share link mila ho to us pe click karo, file mil jaayegi.\n"
            "Ye bot khud se naya upload accept nahi karta."
        )


async def handle_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.message
    user_id = message.from_user.id

    # ---- SIRF AUTHORIZED USER HI STORE KAR SAKTA HAI ----
    if not is_authorized(user_id):
        await message.reply_text(
            "🚫 Sorry, aap file store nahi kar sakte.\n"
            "Ye bot sirf receive karne ke liye hai. Agar aapke paas koi\n"
            "share link hai, to us pe click karo."
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
        await message.reply_text("⚠️ Ye file type support nahi hai.")
        return

    try:
        forwarded = await context.bot.forward_message(
            chat_id=STORAGE_CHANNEL_ID,
            from_chat_id=message.chat_id,
            message_id=message.message_id,
        )
    except Exception as e:
        logger.error(f"Channel me forward karte waqt error: {e}")
        await message.reply_text(
            "⚠️ File channel me save nahi ho payi. Check karo:\n"
            "- Bot channel me admin hai?\n"
            "- STORAGE_CHANNEL_ID sahi hai?"
        )
        return

    file_id = str(uuid.uuid4())[:8]
    db = load_db()
    db[file_id] = {
        "channel_message_id": forwarded.message_id,
        "file_type": file_type,
        "file_name": file_name,
        "owner": user_id,
    }
    save_db(db)

    share_link = f"https://t.me/{BOT_USERNAME}?start={file_id}"

    await message.reply_text(
        f"✅ File permanently save ho gayi!\n\n"
        f"📁 Naam: {file_name}\n"
        f"🆔 ID: `{file_id}`\n\n"
        f"🔗 Share Link:\n{share_link}\n\n"
        f"Ye link kisi ko bhi bhejo, click karte hi file mil jaayegi.",
        parse_mode="Markdown",
    )


async def send_file_by_id(update: Update, context: ContextTypes.DEFAULT_TYPE, file_id: str):
    db = load_db()
    record = db.get(file_id)

    if not record:
        await update.message.reply_text("❌ Ye link/ID valid nahi hai ya file expire ho chuki hai.")
        return

    try:
        await context.bot.copy_message(
            chat_id=update.message.chat_id,
            from_chat_id=STORAGE_CHANNEL_ID,
            message_id=record["channel_message_id"],
        )
    except Exception as e:
        logger.error(f"File bhejte waqt error: {e}")
        await update.message.reply_text(
            "⚠️ File bhejte waqt error aaya. Ho sakta hai file delete ho gayi ho."
        )


async def get_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Fallback manual command: /get <id> — koi bhi user use kar sakta hai (receive-only)."""
    if not context.args:
        await update.message.reply_text("⚠️ Sahi tarika: /get <id>")
        return
    await send_file_by_id(update, context, context.args[0])


async def my_files(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.message.from_user.id

    if not is_authorized(user_id):
        await update.message.reply_text("🚫 Ye command sirf owner ke liye hai.")
        return

    db = load_db()
    user_files = {fid: rec for fid, rec in db.items() if rec["owner"] == user_id}

    if not user_files:
        await update.message.reply_text("📭 Aapne abhi tak koi file save nahi ki.")
        return

    lines = ["📂 Aapki saved files:\n"]
    for fid, rec in user_files.items():
        link = f"https://t.me/{BOT_USERNAME}?start={fid}"
        lines.append(f"🆔 {fid} — {rec['file_name']}\n{link}\n")

    await update.message.reply_text("\n".join(lines))


async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "🤔 Samajh nahi aaya. Agar aapke paas koi share link hai, us pe click karo."
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
