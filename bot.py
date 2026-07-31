import telebot
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton
import yt_dlp
import os

BOT_TOKEN = "8465780049:AAFCj2uVmo-4CAkYLbzNyJmsrsg3WrZUJMc"  # Yahan apna Telegram Bot Token dalo
bot = telebot.TeleBot(BOT_TOKEN)

# User-wise temporary links save karne ke liye dictionary
user_data = {}

@bot.message_handler(commands=['start'])
def send_welcome(message):
    bot.reply_to(message, "👋 Namaste! Mujhe koi bhi video link bhejo, main Video ya MP3 me download karke dunga.")

@bot.message_handler(func=lambda message: True)
def handle_link(message):
    url = message.text.strip()
    
    if not (url.startswith("http://") or url.startswith("https://")):
        bot.reply_to(message, "⚠️ Kripya valid video URL bhejein.")
        return

    # Link ko user ID ke saath store kar lo
    user_data[message.chat.id] = url

    # Buttons Create Karo
    markup = InlineKeyboardMarkup()
    btn_video = InlineKeyboardButton("🎬 Download Video (MP4)", callback_data="download_video")
    btn_audio = InlineKeyboardButton("🎵 Download Audio (MP3)", callback_data="download_audio")
    markup.add(btn_video)
    markup.add(btn_audio)

    bot.reply_to(message, "Kripya Format chuno:", reply_markup=markup)


# Button Click Handle karne ke liye handler
@bot.callback_query_handler(func=lambda call: True)
def callback_query(call):
    chat_id = call.message.chat.id
    url = user_data.get(chat_id)

    if not url:
        bot.answer_callback_query(call.id, "❌ Error: Link expire ho chuka hai. Dobara link bhejein.")
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
            bot.send_message(chat_id, "❌ Video download fail ho gaya. Link check karein.")
        finally:
            if os.path.exists(file_path):
                os.remove(file_path)

    elif call.data == "download_audio":
        bot.edit_message_text("⏳ Audio extract ho raha hai, kripya intezar karein...", chat_id, call.message.message_id)
        
        file_path = f"audio_{chat_id}.mp3"
        ydl_opts = {
            'format': 'bestaudio/best',
            'postprocessors': [{
                'key': 'FFmpegExtractAudio',
                'preferredcodec': 'mp3',
                'preferredquality': '192',
            }],
            'outtmpl': file_path.replace('.mp3', ''), # yt-dlp automatically appends .mp3
            'quiet': True
        }

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            
            # Final output file check (yt-dlp extension issue handeling)
            final_audio_path = file_path if os.path.exists(file_path) else f"{file_path.replace('.mp3', '')}.mp3"

            with open(final_audio_path, 'rb') as audio:
                bot.send_audio(chat_id, audio, caption="🎵 Audio Extracted Successfully!")
            
            bot.delete_message(chat_id, call.message.message_id)
        except Exception as e:
            bot.send_message(chat_id, "❌ Audio extract fail ho gaya.")
        finally:
            for f in [file_path, f"{file_path.replace('.mp3', '')}.mp3"]:
                if os.path.exists(f):
                    os.remove(f)

bot.infinity_polling()
