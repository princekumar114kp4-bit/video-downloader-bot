import telebot
import yt_dlp
import os

# Yahan apna Telegram Bot Token dalo (BotFather se le kar)
BOT_TOKEN = "8465780049:AAFCj2uVmo-4CAkYLbzNyJmsrsg3WrZUJMc"

bot = telebot.TeleBot(BOT_TOKEN)

@bot.message_handler(commands=['start'])
def send_welcome(message):
    bot.reply_to(message, "👋 Namaste! Mujhe koi bhi video link bhejo, mai download karke bhej dunga.")

@bot.message_handler(func=lambda message: True)
def download_video(message):
    url = message.text
    if not (url.startswith("http://") or url.startswith("https://")):
        bot.reply_to(message, "⚠️ Kripya valid video URL bhejein.")
        return

    msg = bot.reply_to(message, "⏳ Video download ho raha hai, kripya intezar karein...")

    ydl_opts = {
        'format': 'best[ext=mp4]/best',
        'outtmpl': 'video.mp4',
        'quiet': True
    }

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            ydl.download([url])
        
        with open('video.mp4', 'rb') as video:
            bot.send_video(message.chat.id, video, caption="✅ Take your video!")
        
        bot.delete_message(message.chat.id, msg.message_id)
        if os.path.exists('video.mp4'):
            os.remove('video.mp4')

    except Exception as e:
        bot.edit_message_text("❌ Download fail ho gaya. Link check karein.", message.chat.id, msg.message_id)
        if os.path.exists('video.mp4'):
            os.remove('video.mp4')

bot.infinity_polling()
