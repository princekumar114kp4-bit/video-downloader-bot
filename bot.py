import telebot
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton
import yt_dlp
import os

# Yahan apna Telegram Bot Token dalo (BotFather wala)
BOT_TOKEN = "8465780049:AAFCj2uVmo-4CAkYLbzNyJmsrsg3WrZUJMc"

bot = telebot.TeleBot(BOT_TOKEN)

user_data = {}

@bot.message_handler(commands=['start'])
def send_welcome(message):
    bot.reply_to(message, "👋 Namaste! Mujhe koi bhi video link bhejo, main Video ya Audio download karke dunga.")

@bot.message_handler(func=lambda message: True)
def handle_link(message):
    url = message.text.strip()
    
    if not (url.startswith("http://") or url.startswith("https://")):
        bot.reply_to(message, "⚠️ Kripya valid video URL bhejein.")
        return

    user_data[message.chat.id] = url

    markup = InlineKeyboardMarkup()
    btn_video = InlineKeyboardButton("🎬 Download Video (MP4)", callback_data="download_video")
    btn_audio = InlineKeyboardButton("🎵 Download Audio", callback_data="download_audio")
    markup.add(btn_video)
    markup.add(btn_audio)

    bot.reply_to(message, "Kripya Option chuno:", reply_markup=markup)

@bot.callback_query_handler(func=lambda call: True)
def callback_query(call):
    chat_id = call.message.chat.id
    url = user_data.get(chat_id)

    if not url:
        bot.answer_callback_query(call.id, "❌ Link expire ho gaya. Dobara link bhejo.")
        return

    if call.data == "download_video":
        bot.edit_message_text("⏳ Video download ho raha hai, kripya intezar karein...", chat_id, call.message.message_id)
        
        file_path = f"video_{chat_id}.mp4"
        ydl_opts = {
            'format': 'best[ext=mp4]/best',
            'outtmpl': file_path,
            'quiet': True
        }
        
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            
            with open(file_path, 'rb') as video:
                bot.send_video(chat_id, video, caption="✅ Video Downloaded!")
            
            bot.delete_message(chat_id, call.message.message_id)
        except Exception as e:
            bot.send_message(chat_id, "❌ Video download fail ho gaya.")
        finally:
            if os.path.exists(file_path):
                os.remove(file_path)

    elif call.data == "download_audio":
        bot.edit_message_text("⏳ Audio download ho raha hai, kripya intezar karein...", chat_id, call.message.message_id)
        
        file_path = f"audio_{chat_id}.m4a"
        ydl_opts = {
            'format': 'bestaudio/best',
            'outtmpl': file_path,
            'quiet': True
        }

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            
            with open(file_path, 'rb') as audio:
                bot.send_audio(chat_id, audio, caption="🎵 Audio Downloaded!")
            
            bot.delete_message(chat_id, call.message.message_id)
        except Exception as e:
            bot.send_message(chat_id, "❌ Audio download fail ho gaya.")
        finally:
            if os.path.exists(file_path):
                os.remove(file_path)

bot.infinity_polling()
