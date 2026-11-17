# -*- coding: utf-8 -*-
"""
🕌 Prayer Times Bot
Languages: English, Русский, Oʻzbekcha, Тоҷикӣ, العربية
Everything is controlled with inline buttons.

Env vars:
  BOT_TOKEN     - token from @BotFather
  DATABASE_URL  - PostgreSQL URL (Railway sets it for you)
  ADMIN_ID      - your Telegram user ID (enables the admin panel)
  ADMIN_IDS     - (optional) more admins, comma-separated Telegram IDs
  WEBAPP_URL    - (optional) mini app address; on Railway it is detected automatically
  CONTACT       - (optional) your email/@username, sent to the geocoder as required by its usage policy
"""
import asyncio
import csv
import hashlib
import hmac
import html
import io
import json
import logging
import math
import os
import re
import time as _time
from collections import deque
from datetime import date, datetime, time as dtime, timedelta
from pathlib import Path
from urllib.parse import parse_qsl, quote
from zoneinfo import ZoneInfo

import asyncpg
import art
from ayahs import AYAHS
import httpx
from aiohttp import web
from telegram import (
    BotCommand,
    CopyTextButton,
    ForceReply,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InlineQueryResultArticle,
    InlineQueryResultCachedMpeg4Gif,
    InlineQueryResultCachedPhoto,
    InlineQueryResultCachedVideo,
    InlineQueryResultMpeg4Gif,
    InlineQueryResultPhoto,
    InlineQueryResultsButton,
    InputMediaPhoto,
    InputTextMessageContent,
    KeyboardButton,
    LabeledPrice,
    MenuButtonCommands,
    MenuButtonDefault,
    MenuButtonWebApp,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    LinkPreviewOptions,
    Update,
    WebAppInfo,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, Forbidden, RetryAfter
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    InlineQueryHandler,
    PreCheckoutQueryHandler,
    MessageHandler,
    TypeHandler,
    filters,
)

BOT_TOKEN = os.environ["BOT_TOKEN"]
DATABASE_URL = os.environ["DATABASE_URL"]
CONTACT = os.getenv("CONTACT", "prayer-times-bot")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0") or 0)  # your Telegram ID; 0 = admin panel disabled
ADMINS = {ADMIN_ID} | {int(x) for x in os.getenv("ADMIN_IDS", "").replace(";", ",").replace(" ", ",").split(",")
                       if x.strip().lstrip("-").isdigit()}
ADMINS.discard(0)
START_TS = _time.time()

logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("prayer-bot")

ERRBUF = deque(maxlen=8)  # last errors, shown in the admin panel


class ErrBuf(logging.Handler):
    def emit(self, record):
        if record.levelno >= logging.ERROR:
            msg = record.getMessage()
            if record.exc_info and record.exc_info[1]:
                msg += f" | {record.exc_info[1]!r}"
            ERRBUF.append((datetime.utcnow(), msg[:200]))


logging.getLogger().addHandler(ErrBuf())

POOL: asyncpg.Pool = None  # type: ignore
HTTP: httpx.AsyncClient = None  # type: ignore

# ───────────────────────── constants ─────────────────────────

LANGS = ["en", "ru", "uz", "uzc", "tg", "ar"]  # uzc = Uzbek in Cyrillic
LANG_BUTTONS = {
    "en": "🇬🇧 English",
    "ru": "🇷🇺 Русский",
    "uz": "🇺🇿 Oʻzbekcha",
    "uzc": "🇺🇿 Ўзбекча",
    "tg": "🇹🇯 Тоҷикӣ",
    "ar": "🇸🇦 العربية",
}
LANG_PICK_TEXT = (
    "🌐 <b>Choose your language</b>\n"
    "Выберите язык · Tilni tanlang · Тилни танланг\n"
    "Забонро интихоб кунед · اختر لغتك"
)

EVENTS = ["Fajr", "Dhuhr", "Asr", "Maghrib", "Isha"]  # prayers that get reminders
ROWS = [("Fajr", "🌌"), ("Sunrise", "🌅"), ("Dhuhr", "☀️"), ("Asr", "🌤"), ("Maghrib", "🌇"), ("Isha", "🌙")]
LEAD_OPTIONS = [5, 10, 15, 30, 0]  # 0 = no early reminder
SUH_OPTS = [-1, 10, 20, 30, 60]    # minutes before Fajr; -1 = off
IFT_OPTS = [-1, 0, 5, 10, 15, 30]  # minutes before Maghrib; 0 = at Maghrib; -1 = off
PRAYER_MODES = "sqo"               # s = with sound, q = silent, o = no reminder
QUIET_PRESETS = [(23, 4), (22, 5), (0, 5)]
DEFAULT_LEAD = 10
KAABA = (21.4225, 39.8262)
ARROWS = ["⬆️", "↗️", "➡️", "↘️", "⬇️", "↙️", "⬅️", "↖️"]

# Aladhan calculation methods by country (ISO code). Anything else -> 3 (Muslim World League).
# Edit freely: https://aladhan.com/calculation-methods
METHOD_BY_COUNTRY = {
    "ru": 14, "tr": 13, "sa": 4, "ae": 16, "kw": 9, "qa": 10, "eg": 5, "pk": 1, "in": 1,
    "bd": 1, "af": 1, "us": 2, "ca": 2, "sg": 11, "my": 17, "id": 20, "ma": 21, "dz": 19,
    "tn": 18, "fr": 12, "jo": 23,
    "uz": "ca",  # tuned to the official calendar of Uzbekistan (used only if namozvaqti.uz can't be read)
}
DEFAULT_METHOD = 3
# Custom settings for Aladhan: twilight angles Fajr/Isha + minute adjustments (Imsak,Fajr,Sunrise,Dhuhr,Asr,Maghrib,Sunset,Isha,Midnight)
CUSTOM_METHODS = {
    "ca": {"method": 99, "methodSettings": "15.5,null,15", "tune": "0,0,0,3,0,2,2,0,0"},
}


def method_for(country):
    return METHOD_BY_COUNTRY.get((country or "").lower(), DEFAULT_METHOD)


def method_params(method):
    return dict(CUSTOM_METHODS.get(method) or {"method": method})


# ───────────────────────── names ─────────────────────────

PN = {  # prayer names
    "en": dict(fajr="Fajr", sunrise="Sunrise", dhuhr="Dhuhr", asr="Asr", maghrib="Maghrib", isha="Isha"),
    "ru": dict(fajr="Фаджр", sunrise="Восход", dhuhr="Зухр", asr="Аср", maghrib="Магриб", isha="Иша"),
    "uz": dict(fajr="Bomdod", sunrise="Quyosh", dhuhr="Peshin", asr="Asr", maghrib="Shom", isha="Xufton"),
    "tg": dict(fajr="Бомдод", sunrise="Офтоб", dhuhr="Пешин", asr="Аср", maghrib="Шом", isha="Хуфтан"),
    "ar": dict(fajr="الفجر", sunrise="الشروق", dhuhr="الظهر", asr="العصر", maghrib="المغرب", isha="العشاء"),
}

HM = {  # hijri months
    "en": ["Muharram", "Safar", "Rabi' al-awwal", "Rabi' al-thani", "Jumada al-ula", "Jumada al-thani",
           "Rajab", "Sha'ban", "Ramadan", "Shawwal", "Dhu al-Qi'dah", "Dhu al-Hijjah"],
    "ru": ["Мухаррам", "Сафар", "Раби аль-авваль", "Раби ас-сани", "Джумада аль-уля", "Джумада ас-сания",
           "Раджаб", "Шаабан", "Рамадан", "Шавваль", "Зуль-каада", "Зуль-хиджа"],
    "uz": ["Muharram", "Safar", "Rabiul avval", "Rabiul oxir", "Jumodul avval", "Jumodul oxir",
           "Rajab", "Sha'bon", "Ramazon", "Shavvol", "Zulqa'da", "Zulhijja"],
    "tg": ["Муҳаррам", "Сафар", "Рабеъулаввал", "Рабеъуссонӣ", "Ҷумодулаввал", "Ҷумодуссонӣ",
           "Раҷаб", "Шаъбон", "Рамазон", "Шаввол", "Зулқаъда", "Зулҳиҷҷа"],
    "ar": ["محرم", "صفر", "ربيع الأول", "ربيع الآخر", "جمادى الأولى", "جمادى الآخرة",
           "رجب", "شعبان", "رمضان", "شوال", "ذو القعدة", "ذو الحجة"],
}

# ───────────────────────── translations ─────────────────────────

EN = {
    "ask_madhab": "🕌 <b>Choose your madhab</b>\n\nIt changes the time of <b>Asr</b> prayer. Other prayers stay the same.",
    "madhab_std": "Shafi'i · Maliki · Hanbali",
    "madhab_hanafi": "Hanafi",
    "ask_city": "📍 <b>Where are you?</b>\n\nType the name of your city, e.g. <i>Tashkent</i>.\nOr share your location with the button below 👇",
    "city_confirm": "📍 <b>Found:</b> {place}\n\nIs this your city?",
    "btn_city_yes": "✅ Yes, that's right",
    "btn_city_no": "✏️ No, type again",
    "loc_btn": "📍 Share my location",
    "loc_hint": "👇 Or tap the button below to share your location",
    "city_not_found": "😔 I couldn't find that place. Please try again — city and country, e.g. <i>Kazan, Russia</i>",
    "error": "⚠️ Something went wrong. Please try again in a moment.",
    "times_title": "🕌 <b>Prayer times</b>",
    "ram_banner": "🌙 <i>Ramadan Mubarak</i>",
    "suhoor": "Suhoor ends",
    "iftar": "Iftar",
    "next_line": "⏳ Next: <b>{name}</b> in {left}",
    "left_hm": "{h} h {m} min",
    "left_m": "{m} min",
    "ask_remind": "🔔 <b>Would you like reminders?</b>\n\nI'll remind you {phrase}.",
    "btn_yes": "✅ Yes, remind me",
    "btn_no": "❌ No, thanks",
    "remind_on": "✅ <b>Reminders are on!</b>\nI'll remind you {phrase}.\n\nYou can change this any time in ⚙️ Settings.",
    "remind_off": "👌 Okay, no reminders. You can turn them on any time from the menu.",
    "menu_title": "🏠 <b>Main menu</b>\n📍 {city}",
    "btn_times": "🕌 Prayer times",
    "btn_qibla": "🕋 Qibla",
    "btn_rem_on": "🔔 Reminders: ON ✅",
    "btn_rem_off": "🔕 Reminders: OFF ❌",
    "btn_settings": "⚙️ Settings",
    "btn_back": "⬅️ Back",
    "btn_menu": "🏠 Menu",
    "settings_title": "⚙️ <b>Settings</b>",
    "btn_city": "📍 Change city",
    "btn_lang": "🌐 Language",
    "btn_madhab": "🕌 Madhab",
    "btn_lead": "⏰ Reminder time",
    "btn_quiet": "🔕 Quiet hours",
    "btn_ram_on": "🌙 Ramadan mode: ON ✅",
    "btn_ram_off": "🌙 Ramadan mode: OFF ❌",
    "lead_title": "⏰ <b>How early should I remind you?</b>",
    "lead_n": "{n} min before",
    "lead_0": "At prayer time",
    "phrase_n": "{n} minutes before each prayer",
    "phrase_0": "right at each prayer time",
    "quiet_title": "🔕 <b>Quiet hours</b>\n\nI won't send reminders during these hours.",
    "quiet_off": "Off",
    "qibla": "🕋 <b>Qibla direction</b>\n📍 {city}\n\n{arrow} <b>{deg}°</b> clockwise from North\n\nStand facing this direction. For best accuracy use a compass app.",
    "btn_kaaba": "🗺 Kaaba on map",
    "rem_std_b": "🔔 <b>{name}</b> in {n} min · {time}\nTime to get ready 🤍",
    "rem_std_n": "🕌 <b>{name}</b> time has come · {time}\nMay Allah accept your prayer 🤍",
    "rem_jumah_b": "🕌 <b>Jumu'ah</b> prayer in {n} min · {time}\nGet ready for Friday prayer 🤍",
    "rem_jumah_n": "🕌 <b>Jumu'ah</b> time has come · {time}\nJumu'ah Mubarak 🤍",
    "rem_fajr_ram_b": "🌙 <b>Fajr</b> in {n} min · {time}\nSuhoor is ending — finish your meal 🤍",
    "rem_fajr_ram_n": "🌙 <b>Fajr</b> time has come · {time}\nSuhoor has ended. May your fast be accepted 🤍",
    "rem_iftar_b": "🌇 <b>Iftar</b> in {n} min · {time}\nGet ready to break your fast 🤍",
    "rem_iftar_n": "🌇 <b>Iftar</b> time has come · {time}\nBismillah — enjoy your iftar 🤍",
}

RU = {
    "ask_madhab": "🕌 <b>Выберите ваш мазхаб</b>\n\nОт него зависит время молитвы <b>Аср</b>. Остальные молитвы не меняются.",
    "madhab_std": "Шафиитский · Маликитский · Ханбалитский",
    "madhab_hanafi": "Ханафитский",
    "ask_city": "📍 <b>Где вы находитесь?</b>\n\nНапишите название вашего города, например: <i>Ташкент</i>.\nИли отправьте геопозицию кнопкой ниже 👇",
    "city_confirm": "📍 <b>Нашёл:</b> {place}\n\nЭто ваш город?",
    "btn_city_yes": "✅ Да, верно",
    "btn_city_no": "✏️ Нет, ввести заново",
    "loc_btn": "📍 Отправить геопозицию",
    "loc_hint": "👇 Или нажмите кнопку ниже, чтобы отправить геопозицию",
    "city_not_found": "😔 Не удалось найти это место. Попробуйте ещё раз — город и страна, например: <i>Казань, Россия</i>",
    "error": "⚠️ Что-то пошло не так. Попробуйте ещё раз чуть позже.",
    "times_title": "🕌 <b>Время намаза</b>",
    "ram_banner": "🌙 <i>Рамадан мубарак</i>",
    "suhoor": "Конец сухура",
    "iftar": "Ифтар",
    "next_line": "⏳ Следующая: <b>{name}</b> через {left}",
    "left_hm": "{h} ч {m} мин",
    "left_m": "{m} мин",
    "ask_remind": "🔔 <b>Включить напоминания?</b>\n\nЯ напомню {phrase}.",
    "btn_yes": "✅ Да, напоминать",
    "btn_no": "❌ Нет, спасибо",
    "remind_on": "✅ <b>Напоминания включены!</b>\nЯ напомню {phrase}.\n\nИзменить можно в любой момент в ⚙️ Настройках.",
    "remind_off": "👌 Хорошо, без напоминаний. Включить их можно в любой момент в меню.",
    "menu_title": "🏠 <b>Главное меню</b>\n📍 {city}",
    "btn_times": "🕌 Время намаза",
    "btn_qibla": "🕋 Кибла",
    "btn_rem_on": "🔔 Напоминания: ВКЛ ✅",
    "btn_rem_off": "🔕 Напоминания: ВЫКЛ ❌",
    "btn_settings": "⚙️ Настройки",
    "btn_back": "⬅️ Назад",
    "btn_menu": "🏠 Меню",
    "settings_title": "⚙️ <b>Настройки</b>",
    "btn_city": "📍 Сменить город",
    "btn_lang": "🌐 Язык",
    "btn_madhab": "🕌 Мазхаб",
    "btn_lead": "⏰ За сколько напомнить",
    "btn_quiet": "🔕 Тихие часы",
    "btn_ram_on": "🌙 Режим Рамадана: ВКЛ ✅",
    "btn_ram_off": "🌙 Режим Рамадана: ВЫКЛ ❌",
    "lead_title": "⏰ <b>За сколько минут напоминать?</b>",
    "lead_n": "За {n} мин",
    "lead_0": "В момент азана",
    "phrase_n": "за {n} минут до каждой молитвы",
    "phrase_0": "в момент каждой молитвы",
    "quiet_title": "🔕 <b>Тихие часы</b>\n\nВ это время напоминания приходить не будут.",
    "quiet_off": "Выключены",
    "qibla": "🕋 <b>Направление на Киблу</b>\n📍 {city}\n\n{arrow} <b>{deg}°</b> по часовой стрелке от севера\n\nВстаньте лицом в этом направлении. Для точности используйте компас на телефоне.",
    "btn_kaaba": "🗺 Кааба на карте",
    "rem_std_b": "🔔 <b>{name}</b> через {n} мин · {time}\nВремя подготовиться 🤍",
    "rem_std_n": "🕌 Наступило время <b>{name}</b> · {time}\nПусть Аллах примет вашу молитву 🤍",
    "rem_jumah_b": "🕌 <b>Джума-намаз</b> через {n} мин · {time}\nГотовьтесь к пятничной молитве 🤍",
    "rem_jumah_n": "🕌 Наступило время <b>Джума-намаза</b> · {time}\nДжума мубарак 🤍",
    "rem_fajr_ram_b": "🌙 <b>Фаджр</b> через {n} мин · {time}\nСухур заканчивается — завершайте трапезу 🤍",
    "rem_fajr_ram_n": "🌙 Наступил <b>Фаджр</b> · {time}\nСухур закончился. Пусть Аллах примет ваш пост 🤍",
    "rem_iftar_b": "🌇 <b>Ифтар</b> через {n} мин · {time}\nГотовьтесь разговеться 🤍",
    "rem_iftar_n": "🌇 Наступило время <b>Ифтара</b> · {time}\nПриятного ифтара 🤍",
}

UZ = {
    "ask_madhab": "🕌 <b>Mazhabingizni tanlang</b>\n\nU <b>Asr</b> namozi vaqtiga ta'sir qiladi. Boshqa namozlar o'zgarmaydi.",
    "madhab_std": "Shofiiy · Molikiy · Hanbaliy",
    "madhab_hanafi": "Hanafiy",
    "ask_city": "📍 <b>Qayerdasiz?</b>\n\nShahringiz nomini yozing, masalan: <i>Toshkent</i>.\nYoki quyidagi tugma orqali joylashuvingizni yuboring 👇",
    "city_confirm": "📍 <b>Topildi:</b> {place}\n\nBu sizning shahringizmi?",
    "btn_city_yes": "✅ Ha, to'g'ri",
    "btn_city_no": "✏️ Yo'q, qayta yozish",
    "loc_btn": "📍 Joylashuvni yuborish",
    "loc_hint": "👇 Yoki joylashuvni yuborish uchun quyidagi tugmani bosing",
    "city_not_found": "😔 Bu joy topilmadi. Yana urinib ko'ring — shahar va davlat, masalan: <i>Qozon, Rossiya</i>",
    "error": "⚠️ Xatolik yuz berdi. Birozdan so'ng qayta urinib ko'ring.",
    "times_title": "🕌 <b>Namoz vaqtlari</b>",
    "ram_banner": "🌙 <i>Ramazon muborak</i>",
    "suhoor": "Saharlik tugashi",
    "iftar": "Iftor",
    "next_line": "⏳ Keyingisi: <b>{name}</b> · {left} qoldi",
    "left_hm": "{h} soat {m} daqiqa",
    "left_m": "{m} daqiqa",
    "ask_remind": "🔔 <b>Eslatmalarni yoqaymi?</b>\n\nMen sizga {phrase} eslataman.",
    "btn_yes": "✅ Ha, eslatib turing",
    "btn_no": "❌ Yo'q, rahmat",
    "remind_on": "✅ <b>Eslatmalar yoqildi!</b>\nMen sizga {phrase} eslataman.\n\nIstalgan payt ⚙️ Sozlamalarda o'zgartirishingiz mumkin.",
    "remind_off": "👌 Mayli, eslatmalarsiz. Ularni istalgan payt menyudan yoqishingiz mumkin.",
    "menu_title": "🏠 <b>Asosiy menyu</b>\n📍 {city}",
    "btn_times": "🕌 Namoz vaqtlari",
    "btn_qibla": "🕋 Qibla",
    "btn_rem_on": "🔔 Eslatmalar: YOQILGAN ✅",
    "btn_rem_off": "🔕 Eslatmalar: O'CHIQ ❌",
    "btn_settings": "⚙️ Sozlamalar",
    "btn_back": "⬅️ Orqaga",
    "btn_menu": "🏠 Menyu",
    "settings_title": "⚙️ <b>Sozlamalar</b>",
    "btn_city": "📍 Shaharni o'zgartirish",
    "btn_lang": "🌐 Til",
    "btn_madhab": "🕌 Mazhab",
    "btn_lead": "⏰ Eslatma vaqti",
    "btn_quiet": "🔕 Tinch soatlar",
    "btn_ram_on": "🌙 Ramazon rejimi: YOQILGAN ✅",
    "btn_ram_off": "🌙 Ramazon rejimi: O'CHIQ ❌",
    "lead_title": "⏰ <b>Necha daqiqa oldin eslatay?</b>",
    "lead_n": "{n} daqiqa oldin",
    "lead_0": "Namoz vaqtida",
    "phrase_n": "har bir namozdan {n} daqiqa oldin",
    "phrase_0": "har bir namoz vaqti kirganda",
    "quiet_title": "🔕 <b>Tinch soatlar</b>\n\nBu vaqtda eslatmalar yuborilmaydi.",
    "quiet_off": "O'chiq",
    "qibla": "🕋 <b>Qibla yo'nalishi</b>\n📍 {city}\n\n{arrow} Shimoldan soat mili bo'yicha <b>{deg}°</b>\n\nShu tomonga qarab turing. Aniqroq bo'lishi uchun telefondagi kompasdan foydalaning.",
    "btn_kaaba": "🗺 Ka'ba xaritada",
    "rem_std_b": "🔔 <b>{name}</b> namoziga {n} daqiqa qoldi · {time}\nTayyorlanish vaqti 🤍",
    "rem_std_n": "🕌 <b>{name}</b> vaqti kirdi · {time}\nAllohdan namozingiz qabul bo'lishini tilaymiz 🤍",
    "rem_jumah_b": "🕌 <b>Juma namozi</b>ga {n} daqiqa qoldi · {time}\nJuma namoziga tayyorlaning 🤍",
    "rem_jumah_n": "🕌 <b>Juma namozi</b> vaqti kirdi · {time}\nJuma muborak 🤍",
    "rem_fajr_ram_b": "🌙 <b>Bomdod</b>ga {n} daqiqa qoldi · {time}\nSaharlik tugayapti — ovqatlanishni yakunlang 🤍",
    "rem_fajr_ram_n": "🌙 <b>Bomdod</b> vaqti kirdi · {time}\nSaharlik tugadi. Allohdan ro'zangiz qabul bo'lsin 🤍",
    "rem_iftar_b": "🌇 <b>Iftor</b>ga {n} daqiqa qoldi · {time}\nOg'iz ochishga tayyorlaning 🤍",
    "rem_iftar_n": "🌇 <b>Iftor</b> vaqti kirdi · {time}\nIftoringiz qabul bo'lsin 🤍",
}

TG = {
    "ask_madhab": "🕌 <b>Мазҳаби худро интихоб кунед</b>\n\nИн ба вақти намози <b>Аср</b> таъсир мерасонад. Намозҳои дигар тағйир намеёбанд.",
    "madhab_std": "Шофеӣ · Моликӣ · Ҳанбалӣ",
    "madhab_hanafi": "Ҳанафӣ",
    "ask_city": "📍 <b>Шумо дар куҷо ҳастед?</b>\n\nНоми шаҳри худро нависед, масалан: <i>Душанбе</i>.\nЁ бо тугмаи поён ҷойгиршавиатонро фиристед 👇",
    "city_confirm": "📍 <b>Ёфт шуд:</b> {place}\n\nИн шаҳри шумост?",
    "btn_city_yes": "✅ Бале, дуруст",
    "btn_city_no": "✏️ Не, аз нав навиштан",
    "loc_btn": "📍 Фиристодани ҷойгиршавӣ",
    "loc_hint": "👇 Ё барои фиристодани ҷойгиршавӣ тугмаи поёнро пахш кунед",
    "city_not_found": "😔 Ин ҷой ёфт нашуд. Дубора кӯшиш кунед — шаҳр ва кишвар, масалан: <i>Қазон, Русия</i>",
    "error": "⚠️ Хатогӣ рух дод. Каме дертар дубора кӯшиш кунед.",
    "times_title": "🕌 <b>Вақти намоз</b>",
    "ram_banner": "🌙 <i>Рамазон муборак</i>",
    "suhoor": "Анҷоми саҳарӣ",
    "iftar": "Ифтор",
    "next_line": "⏳ Навбатӣ: <b>{name}</b> баъди {left}",
    "left_hm": "{h} соат {m} дақиқа",
    "left_m": "{m} дақиқа",
    "ask_remind": "🔔 <b>Ёдоварӣ фаъол карда шавад?</b>\n\nМан ба шумо {phrase} ёдрас мекунам.",
    "btn_yes": "✅ Бале, ёдрас кунед",
    "btn_no": "❌ Не, ташаккур",
    "remind_on": "✅ <b>Ёдоварӣ фаъол шуд!</b>\nМан ба шумо {phrase} ёдрас мекунам.\n\nМетавонед дар ҳар вақт дар ⚙️ Танзимот иваз кунед.",
    "remind_off": "👌 Хуб, бе ёдоварӣ. Онро дар ҳар вақт аз меню фаъол кардан мумкин аст.",
    "menu_title": "🏠 <b>Менюи асосӣ</b>\n📍 {city}",
    "btn_times": "🕌 Вақти намоз",
    "btn_qibla": "🕋 Қибла",
    "btn_rem_on": "🔔 Ёдоварӣ: ФАЪОЛ ✅",
    "btn_rem_off": "🔕 Ёдоварӣ: ХОМӮШ ❌",
    "btn_settings": "⚙️ Танзимот",
    "btn_back": "⬅️ Бозгашт",
    "btn_menu": "🏠 Меню",
    "settings_title": "⚙️ <b>Танзимот</b>",
    "btn_city": "📍 Иваз кардани шаҳр",
    "btn_lang": "🌐 Забон",
    "btn_madhab": "🕌 Мазҳаб",
    "btn_lead": "⏰ Вақти ёдоварӣ",
    "btn_quiet": "🔕 Соатҳои оромӣ",
    "btn_ram_on": "🌙 Ҳолати Рамазон: ФАЪОЛ ✅",
    "btn_ram_off": "🌙 Ҳолати Рамазон: ХОМӮШ ❌",
    "lead_title": "⏰ <b>Чанд дақиқа пеш ёдоварӣ кунам?</b>",
    "lead_n": "{n} дақиқа пеш",
    "lead_0": "Дар вақти намоз",
    "phrase_n": "{n} дақиқа пеш аз ҳар намоз",
    "phrase_0": "ҳангоми дохилшавии вақти ҳар намоз",
    "quiet_title": "🔕 <b>Соатҳои оромӣ</b>\n\nДар ин вақт ёдоварӣ фиристода намешавад.",
    "quiet_off": "Хомӯш",
    "qibla": "🕋 <b>Самти қибла</b>\n📍 {city}\n\n{arrow} Аз шимол ба самти ақрабаки соат <b>{deg}°</b>\n\nРӯ ба ҳамин самт истед. Барои дурустӣ компаси телефонро истифода баред.",
    "btn_kaaba": "🗺 Каъба дар харита",
    "rem_std_b": "🔔 <b>{name}</b> баъди {n} дақиқа · {time}\nВақти омодашавӣ 🤍",
    "rem_std_n": "🕌 Вақти <b>{name}</b> даромад · {time}\nАллоҳ намози шуморо қабул кунад 🤍",
    "rem_jumah_b": "🕌 <b>Намози ҷумъа</b> баъди {n} дақиқа · {time}\nБарои намози ҷумъа омода шавед 🤍",
    "rem_jumah_n": "🕌 Вақти <b>намози ҷумъа</b> даромад · {time}\nҶумъаатон муборак 🤍",
    "rem_fajr_ram_b": "🌙 <b>Бомдод</b> баъди {n} дақиқа · {time}\nСаҳарӣ ба охир мерасад — хӯрданро анҷом диҳед 🤍",
    "rem_fajr_ram_n": "🌙 Вақти <b>Бомдод</b> даромад · {time}\nСаҳарӣ тамом шуд. Аллоҳ рӯзаатонро қабул кунад 🤍",
    "rem_iftar_b": "🌇 <b>Ифтор</b> баъди {n} дақиқа · {time}\nБарои ифтор омода шавед 🤍",
    "rem_iftar_n": "🌇 Вақти <b>Ифтор</b> даромад · {time}\nИфтори шумо муборак 🤍",
}

AR = {
    "ask_madhab": "🕌 <b>اختر مذهبك</b>\n\nيؤثر على وقت صلاة <b>العصر</b>. باقي الصلوات لا تتغير.",
    "madhab_std": "شافعي · مالكي · حنبلي",
    "madhab_hanafi": "حنفي",
    "ask_city": "📍 <b>أين أنت؟</b>\n\nاكتب اسم مدينتك، مثل: <i>مكة</i>.\nأو أرسل موقعك عبر الزر أدناه 👇",
    "city_confirm": "📍 <b>تم العثور على:</b> {place}\n\nهل هذه مدينتك؟",
    "btn_city_yes": "✅ نعم، صحيح",
    "btn_city_no": "✏️ لا، أكتب من جديد",
    "loc_btn": "📍 إرسال موقعي",
    "loc_hint": "👇 أو اضغط الزر أدناه لإرسال موقعك",
    "city_not_found": "😔 لم أجد هذا المكان. حاول مرة أخرى بكتابة المدينة والدولة، مثل: <i>قازان، روسيا</i>",
    "error": "⚠️ حدث خطأ ما. حاول مرة أخرى بعد قليل.",
    "times_title": "🕌 <b>مواقيت الصلاة</b>",
    "ram_banner": "🌙 <i>رمضان مبارك</i>",
    "suhoor": "نهاية السحور",
    "iftar": "الإفطار",
    "next_line": "⏳ التالية: <b>{name}</b> بعد {left}",
    "left_hm": "{h} ساعة و{m} دقيقة",
    "left_m": "{m} دقيقة",
    "ask_remind": "🔔 <b>هل تريد تفعيل التذكيرات؟</b>\n\nسأذكّرك {phrase}.",
    "btn_yes": "✅ نعم، ذكّرني",
    "btn_no": "❌ لا، شكراً",
    "remind_on": "✅ <b>تم تفعيل التذكيرات!</b>\nسأذكّرك {phrase}.\n\nيمكنك التغيير في أي وقت من ⚙️ الإعدادات.",
    "remind_off": "👌 حسناً، بدون تذكيرات. يمكنك تفعيلها في أي وقت من القائمة.",
    "menu_title": "🏠 <b>القائمة الرئيسية</b>\n📍 {city}",
    "btn_times": "🕌 مواقيت الصلاة",
    "btn_qibla": "🕋 القبلة",
    "btn_rem_on": "🔔 التذكيرات: مفعّلة ✅",
    "btn_rem_off": "🔕 التذكيرات: متوقفة ❌",
    "btn_settings": "⚙️ الإعدادات",
    "btn_back": "⬅️ رجوع",
    "btn_menu": "🏠 القائمة",
    "settings_title": "⚙️ <b>الإعدادات</b>",
    "btn_city": "📍 تغيير المدينة",
    "btn_lang": "🌐 اللغة",
    "btn_madhab": "🕌 المذهب",
    "btn_lead": "⏰ وقت التذكير",
    "btn_quiet": "🔕 ساعات الهدوء",
    "btn_ram_on": "🌙 وضع رمضان: مفعّل ✅",
    "btn_ram_off": "🌙 وضع رمضان: متوقف ❌",
    "lead_title": "⏰ <b>قبل كم دقيقة أذكّرك؟</b>",
    "lead_n": "قبل {n} دقيقة",
    "lead_0": "عند دخول الوقت",
    "phrase_n": "قبل كل صلاة بـ {n} دقيقة",
    "phrase_0": "عند دخول وقت كل صلاة",
    "quiet_title": "🔕 <b>ساعات الهدوء</b>\n\nلن أرسل تذكيرات خلال هذه الساعات.",
    "quiet_off": "متوقفة",
    "qibla": "🕋 <b>اتجاه القبلة</b>\n📍 {city}\n\n{arrow} <b>{deg}°</b> مع عقارب الساعة من الشمال\n\nاستقبل هذا الاتجاه. للدقة استخدم تطبيق البوصلة في هاتفك.",
    "btn_kaaba": "🗺 الكعبة على الخريطة",
    "rem_std_b": "🔔 <b>{name}</b> بعد {n} دقيقة · {time}\nحان وقت الاستعداد 🤍",
    "rem_std_n": "🕌 دخل وقت <b>{name}</b> · {time}\nتقبّل الله صلاتك 🤍",
    "rem_jumah_b": "🕌 <b>صلاة الجمعة</b> بعد {n} دقيقة · {time}\nتهيّأ لصلاة الجمعة 🤍",
    "rem_jumah_n": "🕌 دخل وقت <b>صلاة الجمعة</b> · {time}\nجمعة مباركة 🤍",
    "rem_fajr_ram_b": "🌙 <b>الفجر</b> بعد {n} دقيقة · {time}\nيقترب انتهاء السحور — أتمّ طعامك 🤍",
    "rem_fajr_ram_n": "🌙 دخل وقت <b>الفجر</b> · {time}\nانتهى السحور. تقبّل الله صيامك 🤍",
    "rem_iftar_b": "🌇 <b>الإفطار</b> بعد {n} دقيقة · {time}\nتهيّأ للإفطار 🤍",
    "rem_iftar_n": "🌇 حان وقت <b>الإفطار</b> · {time}\nإفطاراً هنيئاً 🤍",
}

T = {"en": EN, "ru": RU, "uz": UZ, "tg": TG, "ar": AR}

# Texts for groups, channels and support (merged into the dictionaries above)
EXTRA = {
    "en": {
        "btn_add_group": "➕ Add to group",
        "btn_add_channel": "📢 Add to channel",
        "btn_my_channels": "📢 My channels",
        "btn_my_menu": "🏠 My menu",
        "btn_support": "💬 Support",
        "btn_cancel": "❌ Cancel",
        "btn_setup": "⚙️ Set up",
        "btn_daily": "📅 Daily schedule",
        "support_prompt": "💬 <b>Support</b>\n\nWrite your message — text, photo, video, voice, file, anything.\nWe'll reply right here in the bot 🤍",
        "support_sent": "✅ Message sent! We'll reply soon 🤍",
        "support_reply_header": "💬 <b>Reply from support:</b>",
        "support_slow": "⏳ Too many messages. Please wait a minute.",
        "only_admins": "🔒 Only group admins can change the settings",
        "group_ask_city": "📍 <b>Reply to this message</b> with your city name, e.g. <i>Tashkent</i> ✍️",
        "city_ph": "City…",
        "channel_menu_title": "📢 <b>{title}</b>\n📍 {city}",
        "my_channels_title": "📢 <b>My channels</b>\n\nChoose a channel to manage 👇",
        "no_channels": "📢 <b>You have no channels yet</b>\n\nAdd me to your channel as an admin with the «Post messages» permission 👇",
        "channel_added": "📢 You added me to <b>{title}</b>!\n\nLet's set it up — prayer times and reminders will be posted there 👇",
        "channel_no_rights": "⚠️ I was added to <b>{title}</b>, but I can't post there.\n\nPlease make me an admin with the «Post messages» permission.",
        "daily_title": "📅 <b>Daily schedule</b>\n\nPost the day's prayer times every day:",
        "daily_off": "Off",
        "daily_fajr": "At Fajr time",
        "daily_sunrise": "After sunrise",
    },
    "ru": {
        "btn_add_group": "➕ Добавить в группу",
        "btn_add_channel": "📢 Добавить в канал",
        "btn_my_channels": "📢 Мои каналы",
        "btn_my_menu": "🏠 Моё меню",
        "btn_support": "💬 Поддержка",
        "btn_cancel": "❌ Отмена",
        "btn_setup": "⚙️ Настроить",
        "btn_daily": "📅 Расписание на день",
        "support_prompt": "💬 <b>Поддержка</b>\n\nНапишите ваше сообщение — текст, фото, видео, голосовое, файл, что угодно.\nМы ответим прямо здесь, в боте 🤍",
        "support_sent": "✅ Сообщение отправлено! Скоро ответим 🤍",
        "support_reply_header": "💬 <b>Ответ поддержки:</b>",
        "support_slow": "⏳ Слишком много сообщений. Подождите минуту.",
        "only_admins": "🔒 Настройки могут менять только админы группы",
        "group_ask_city": "📍 <b>Ответьте на это сообщение</b> названием города, например: <i>Ташкент</i> ✍️",
        "city_ph": "Город…",
        "channel_menu_title": "📢 <b>{title}</b>\n📍 {city}",
        "my_channels_title": "📢 <b>Мои каналы</b>\n\nВыберите канал для настройки 👇",
        "no_channels": "📢 <b>У вас пока нет каналов</b>\n\nДобавьте меня в свой канал админом с правом «Публикация сообщений» 👇",
        "channel_added": "📢 Вы добавили меня в канал <b>{title}</b>!\n\nДавайте настроим — туда будут приходить время намаза и напоминания 👇",
        "channel_no_rights": "⚠️ Меня добавили в <b>{title}</b>, но я не могу там публиковать.\n\nСделайте меня админом с правом «Публикация сообщений».",
        "daily_title": "📅 <b>Расписание на день</b>\n\nПубликовать время намаза каждый день:",
        "daily_off": "Выключено",
        "daily_fajr": "В момент Фаджра",
        "daily_sunrise": "После восхода",
    },
    "uz": {
        "btn_add_group": "➕ Guruhga qo'shish",
        "btn_add_channel": "📢 Kanalga qo'shish",
        "btn_my_channels": "📢 Kanallarim",
        "btn_my_menu": "🏠 Mening menyum",
        "btn_support": "💬 Yordam",
        "btn_cancel": "❌ Bekor qilish",
        "btn_setup": "⚙️ Sozlash",
        "btn_daily": "📅 Kunlik jadval",
        "support_prompt": "💬 <b>Yordam xizmati</b>\n\nXabaringizni yozing — matn, rasm, video, ovozli xabar, fayl, istalgan narsa.\nJavobni shu yerda, botda beramiz 🤍",
        "support_sent": "✅ Xabar yuborildi! Tez orada javob beramiz 🤍",
        "support_reply_header": "💬 <b>Yordam xizmati javobi:</b>",
        "support_slow": "⏳ Juda ko'p xabar. Bir daqiqa kuting.",
        "only_admins": "🔒 Sozlamalarni faqat guruh adminlari o'zgartira oladi",
        "group_ask_city": "📍 <b>Shu xabarga javob tariqasida</b> shahar nomini yozing, masalan: <i>Toshkent</i> ✍️",
        "city_ph": "Shahar…",
        "channel_menu_title": "📢 <b>{title}</b>\n📍 {city}",
        "my_channels_title": "📢 <b>Kanallarim</b>\n\nSozlash uchun kanalni tanlang 👇",
        "no_channels": "📢 <b>Sizda hali kanal yo'q</b>\n\nMeni kanalingizga «Xabarlarni joylash» huquqi bilan admin qilib qo'shing 👇",
        "channel_added": "📢 Siz meni <b>{title}</b> kanaliga qo'shdingiz!\n\nKeling, sozlaymiz — u yerga namoz vaqtlari va eslatmalar yuboriladi 👇",
        "channel_no_rights": "⚠️ Meni <b>{title}</b> ga qo'shishdi, lekin u yerda xabar joylay olmayman.\n\nMeni «Xabarlarni joylash» huquqi bilan admin qiling.",
        "daily_title": "📅 <b>Kunlik jadval</b>\n\nHar kuni namoz vaqtlarini joylash:",
        "daily_off": "O'chiq",
        "daily_fajr": "Bomdod vaqtida",
        "daily_sunrise": "Quyosh chiqqandan keyin",
    },
    "tg": {
        "btn_add_group": "➕ Ба гурӯҳ илова кардан",
        "btn_add_channel": "📢 Ба канал илова кардан",
        "btn_my_channels": "📢 Каналҳои ман",
        "btn_my_menu": "🏠 Менюи ман",
        "btn_support": "💬 Дастгирӣ",
        "btn_cancel": "❌ Бекор кардан",
        "btn_setup": "⚙️ Танзим кардан",
        "btn_daily": "📅 Ҷадвали рӯз",
        "support_prompt": "💬 <b>Дастгирӣ</b>\n\nПаёми худро нависед — матн, акс, видео, паёми овозӣ, файл, ҳар чиз.\nҶавобро дар ҳамин ҷо, дар бот медиҳем 🤍",
        "support_sent": "✅ Паём фиристода шуд! Ба зудӣ ҷавоб медиҳем 🤍",
        "support_reply_header": "💬 <b>Ҷавоби дастгирӣ:</b>",
        "support_slow": "⏳ Паёмҳо зиёданд. Як дақиқа интизор шавед.",
        "only_admins": "🔒 Танзимотро танҳо админҳои гурӯҳ иваз карда метавонанд",
        "group_ask_city": "📍 <b>Ба ин паём ҷавоб дода</b>, номи шаҳрро нависед, масалан: <i>Душанбе</i> ✍️",
        "city_ph": "Шаҳр…",
        "channel_menu_title": "📢 <b>{title}</b>\n📍 {city}",
        "my_channels_title": "📢 <b>Каналҳои ман</b>\n\nБарои танзим каналро интихоб кунед 👇",
        "no_channels": "📢 <b>Шумо ҳоло канал надоред</b>\n\nМаро ба канали худ ҳамчун админ бо ҳуқуқи «Нашри паёмҳо» илова кунед 👇",
        "channel_added": "📢 Шумо маро ба канали <b>{title}</b> илова кардед!\n\nБиёед танзим кунем — ба он ҷо вақти намоз ва ёдовариҳо фиристода мешаванд 👇",
        "channel_no_rights": "⚠️ Маро ба <b>{title}</b> илова карданд, аммо ман дар он ҷо нашр карда наметавонам.\n\nМаро админ бо ҳуқуқи «Нашри паёмҳо» кунед.",
        "daily_title": "📅 <b>Ҷадвали рӯз</b>\n\nҲар рӯз вақти намозро нашр кардан:",
        "daily_off": "Хомӯш",
        "daily_fajr": "Дар вақти Бомдод",
        "daily_sunrise": "Баъд аз тулӯи офтоб",
    },
    "ar": {
        "btn_add_group": "➕ إضافة إلى مجموعة",
        "btn_add_channel": "📢 إضافة إلى قناة",
        "btn_my_channels": "📢 قنواتي",
        "btn_my_menu": "🏠 قائمتي",
        "btn_support": "💬 الدعم",
        "btn_cancel": "❌ إلغاء",
        "btn_setup": "⚙️ إعداد",
        "btn_daily": "📅 جدول اليوم",
        "support_prompt": "💬 <b>الدعم</b>\n\nاكتب رسالتك — نص أو صورة أو فيديو أو رسالة صوتية أو ملف، أي شيء.\nسنرد عليك هنا في البوت 🤍",
        "support_sent": "✅ تم إرسال رسالتك! سنرد قريباً 🤍",
        "support_reply_header": "💬 <b>رد الدعم:</b>",
        "support_slow": "⏳ رسائل كثيرة. انتظر دقيقة من فضلك.",
        "only_admins": "🔒 فقط مشرفو المجموعة يمكنهم تغيير الإعدادات",
        "group_ask_city": "📍 <b>ردّ على هذه الرسالة</b> باسم مدينتك، مثل: <i>مكة</i> ✍️",
        "city_ph": "المدينة…",
        "channel_menu_title": "📢 <b>{title}</b>\n📍 {city}",
        "my_channels_title": "📢 <b>قنواتي</b>\n\nاختر قناة لإعدادها 👇",
        "no_channels": "📢 <b>ليست لديك قنوات بعد</b>\n\nأضفني إلى قناتك كمشرف مع صلاحية «نشر الرسائل» 👇",
        "channel_added": "📢 لقد أضفتني إلى قناة <b>{title}</b>!\n\nلنقم بالإعداد — سيتم نشر مواقيت الصلاة والتذكيرات هناك 👇",
        "channel_no_rights": "⚠️ تمت إضافتي إلى <b>{title}</b> لكن لا يمكنني النشر هناك.\n\nاجعلني مشرفاً مع صلاحية «نشر الرسائل».",
        "daily_title": "📅 <b>جدول اليوم</b>\n\nنشر مواقيت الصلاة كل يوم:",
        "daily_off": "متوقف",
        "daily_fajr": "عند الفجر",
        "daily_sunrise": "بعد الشروق",
    },
}
for _l, _d in EXTRA.items():
    T[_l].update(_d)

EXTRA2 = {
    "en": {"lead_none": "Don't remind early",
           "phrase_both": "{n} minutes before each prayer and at prayer time",
           "phrase_off": "— reminders are turned off in ⚙️ Settings",
           "btn_at_on": "🕌 At prayer time: ON ✅", "btn_at_off": "🕌 At prayer time: OFF ❌",
           "btn_app": "📱 Open the app", "btn_compass": "🧭 Live compass",
           "qibla_img_hint": "📱 Hold your phone flat and turn it so that <b>N</b> points north — the gold arrow shows the Qibla."},
    "ru": {"lead_none": "Не напоминать заранее",
           "phrase_both": "за {n} минут до каждой молитвы и в момент азана",
           "phrase_off": "— напоминания выключены в ⚙️ Настройках",
           "btn_at_on": "🕌 В момент намаза: ВКЛ ✅", "btn_at_off": "🕌 В момент намаза: ВЫКЛ ❌",
           "btn_app": "📱 Открыть приложение", "btn_compass": "🧭 Живой компас",
           "qibla_img_hint": "📱 Положите телефон ровно и поверните так, чтобы <b>N</b> смотрела на север — золотая стрелка покажет Киблу."},
    "uz": {"lead_none": "Oldindan eslatmaslik",
           "phrase_both": "har bir namozdan {n} daqiqa oldin va namoz vaqti kirganda",
           "phrase_off": "— eslatmalar ⚙️ Sozlamalarda o'chirilgan",
           "btn_at_on": "🕌 Namoz vaqtida: YOQILGAN ✅", "btn_at_off": "🕌 Namoz vaqtida: O'CHIQ ❌",
           "btn_app": "📱 Ilovani ochish", "btn_compass": "🧭 Jonli kompas",
           "qibla_img_hint": "📱 Telefonni tekis ushlang va <b>N</b> shimolga qaraydigan qilib buring — oltin strelka Qiblani ko'rsatadi."},
    "tg": {"lead_none": "Пешакӣ ёдрас накардан",
           "phrase_both": "{n} дақиқа пеш аз ҳар намоз ва ҳангоми дохилшавии вақти он",
           "phrase_off": "— ёдовариҳо дар ⚙️ Танзимот хомӯшанд",
           "btn_at_on": "🕌 Дар вақти намоз: ФАЪОЛ ✅", "btn_at_off": "🕌 Дар вақти намоз: ХОМӮШ ❌",
           "btn_app": "📱 Кушодани барнома", "btn_compass": "🧭 Компаси зинда",
           "qibla_img_hint": "📱 Телефонро рост нигоҳ доред ва тавре гардонед, ки <b>N</b> ба шимол нигарад — тирчаи тиллоӣ қибларо нишон медиҳад."},
    "ar": {"lead_none": "لا تذكير مسبق",
           "phrase_both": "قبل كل صلاة بـ {n} دقيقة وعند دخول وقتها",
           "phrase_off": "— التذكيرات متوقفة في ⚙️ الإعدادات",
           "btn_at_on": "🕌 عند دخول الوقت: مفعّل ✅", "btn_at_off": "🕌 عند دخول الوقت: متوقف ❌",
           "btn_app": "📱 فتح التطبيق", "btn_compass": "🧭 بوصلة حية",
           "qibla_img_hint": "📱 ضع هاتفك بشكل مستوٍ وأدره حتى يشير <b>N</b> إلى الشمال — السهم الذهبي يشير إلى القبلة."},
}
for _l, _d in EXTRA2.items():
    T[_l].update(_d)

EXTRA3 = {
    "en": {"btn_auto": "🔄 Auto-update: {v}", "auto_title": "🔄 <b>Auto-update of the prayer times card</b>\n\nThe last card in the chat updates itself: countdown, current prayer and the new day's times.",
           "auto_off": "Off", "auto_1": "Every minute", "auto_n": "Every {n} min", "updated_at": "🔄 Updated at {time}"},
    "ru": {"btn_auto": "🔄 Автообновление: {v}", "auto_title": "🔄 <b>Автообновление карточки времени</b>\n\nПоследняя карточка в чате обновляется сама: отсчёт, текущий намаз и время на новый день.",
           "auto_off": "Выкл", "auto_1": "Каждую минуту", "auto_n": "Каждые {n} мин", "updated_at": "🔄 Обновлено в {time}"},
    "uz": {"btn_auto": "🔄 Avtoyangilash: {v}", "auto_title": "🔄 <b>Namoz vaqtlari kartasini avtoyangilash</b>\n\nChatdagi oxirgi karta o'zi yangilanadi: qolgan vaqt, joriy namoz va yangi kun vaqtlari.",
           "auto_off": "O'chiq", "auto_1": "Har daqiqada", "auto_n": "Har {n} daqiqada", "updated_at": "🔄 {time} da yangilandi"},
    "tg": {"btn_auto": "🔄 Навсозии худкор: {v}", "auto_title": "🔄 <b>Навсозии худкори корти вақти намоз</b>\n\nКорти охирин дар чат худаш нав мешавад: вақти боқимонда, намози ҷорӣ ва вақтҳои рӯзи нав.",
           "auto_off": "Хомӯш", "auto_1": "Ҳар дақиқа", "auto_n": "Ҳар {n} дақиқа", "updated_at": "🔄 Соати {time} нав шуд"},
    "ar": {"btn_auto": "🔄 التحديث التلقائي: {v}", "auto_title": "🔄 <b>التحديث التلقائي لبطاقة المواقيت</b>\n\nآخر بطاقة في المحادثة تتحدث تلقائياً: العد التنازلي والصلاة الحالية ومواقيت اليوم الجديد.",
           "auto_off": "متوقف", "auto_1": "كل دقيقة", "auto_n": "كل {n} دقيقة", "updated_at": "🔄 تم التحديث {time}"},
}
for _l, _d in EXTRA3.items():
    T[_l].update(_d)

EXTRA4 = {
    "en": {"btn_azr_on": "🌅 Adhkar reminder: ON ✅", "btn_azr_off": "🌅 Adhkar reminder: OFF ❌",
           "btn_wk_on": "📈 Weekly report: ON ✅", "btn_wk_off": "📈 Weekly report: OFF ❌",
           "az_rem_m": "🌅 <b>Time for the morning adhkar</b>\nStart your day with the remembrance of Allah 🤍",
           "az_rem_e": "🌙 <b>Time for the evening adhkar</b>\nEnd your day with the remembrance of Allah 🤍",
           "btn_open_azkar": "📖 Open the adhkar", "btn_open_tracker": "✅ Open the tracker", "btn_open_ch": "🤝 Open the challenge",
           "wk_title": "📈 <b>Your week</b> · {range}", "wk_prayers": "✅ Prayers: <b>{n} of 35</b> ({p}%)",
           "wk_full": "🟢 Complete days: <b>{d} of 7</b>", "wk_streak": "🔥 Current streak: <b>{s}</b> d.",
           "wk_great": "MashaAllah, keep it up! 🤍", "wk_good": "A good week — let's make the next one even better 🤍",
           "wk_start": "Every prayer counts. Let's make this week better together 🤍",
           "in_open": "🕌 Open the bot", "in_hint": "Type a city name",
           "ch_joined": "🤝 You joined the challenge <b>{t}</b>!\n\n{d} days of all 5 prayers — together with friends. Mark your prayers in the tracker 🤍",
           "ch_nf": "😔 This challenge was not found or has already ended.", "ch_full": "😔 This challenge is already full."},
    "ru": {"btn_azr_on": "🌅 Напоминание об азкарах: ВКЛ ✅", "btn_azr_off": "🌅 Напоминание об азкарах: ВЫКЛ ❌",
           "btn_wk_on": "📈 Отчёт за неделю: ВКЛ ✅", "btn_wk_off": "📈 Отчёт за неделю: ВЫКЛ ❌",
           "az_rem_m": "🌅 <b>Время утренних азкаров</b>\nНачните день с поминания Аллаха 🤍",
           "az_rem_e": "🌙 <b>Время вечерних азкаров</b>\nЗавершите день поминанием Аллаха 🤍",
           "btn_open_azkar": "📖 Открыть азкары", "btn_open_tracker": "✅ Открыть трекер", "btn_open_ch": "🤝 Открыть вызов",
           "wk_title": "📈 <b>Твоя неделя</b> · {range}", "wk_prayers": "✅ Намазов: <b>{n} из 35</b> ({p}%)",
           "wk_full": "🟢 Полных дней: <b>{d} из 7</b>", "wk_streak": "🔥 Текущая серия: <b>{s}</b> дн.",
           "wk_great": "Машаллах, так держать! 🤍", "wk_good": "Хорошая неделя — пусть следующая будет ещё лучше 🤍",
           "wk_start": "Каждый намаз важен. Давай сделаем эту неделю лучше 🤍",
           "in_open": "🕌 Открыть бота", "in_hint": "Напишите название города",
           "ch_joined": "🤝 Ты присоединился к вызову <b>{t}</b>!\n\n{d} дней все 5 намазов — вместе с друзьями. Отмечай намазы в трекере 🤍",
           "ch_nf": "😔 Вызов не найден или уже закончился.", "ch_full": "😔 В этом вызове уже нет мест."},
    "uz": {"btn_azr_on": "🌅 Zikr eslatmasi: YOQILGAN ✅", "btn_azr_off": "🌅 Zikr eslatmasi: O'CHIQ ❌",
           "btn_wk_on": "📈 Haftalik hisobot: YOQILGAN ✅", "btn_wk_off": "📈 Haftalik hisobot: O'CHIQ ❌",
           "az_rem_m": "🌅 <b>Tong zikrlari vaqti</b>\nKuningizni Allohni zikr qilish bilan boshlang 🤍",
           "az_rem_e": "🌙 <b>Kech zikrlari vaqti</b>\nKuningizni Allohni zikr qilish bilan yakunlang 🤍",
           "btn_open_azkar": "📖 Zikrlarni ochish", "btn_open_tracker": "✅ Kundalikni ochish", "btn_open_ch": "🤝 Musobaqani ochish",
           "wk_title": "📈 <b>Haftangiz</b> · {range}", "wk_prayers": "✅ Namozlar: <b>35 tadan {n} ta</b> ({p}%)",
           "wk_full": "🟢 To'liq kunlar: <b>7 dan {d}</b>", "wk_streak": "🔥 Joriy ketma-ketlik: <b>{s}</b> kun",
           "wk_great": "Mashaalloh, shunday davom eting! 🤍", "wk_good": "Yaxshi hafta — keyingisi bundan ham yaxshi bo'lsin 🤍",
           "wk_start": "Har bir namoz muhim. Bu haftani yaxshiroq qilaylik 🤍",
           "in_open": "🕌 Botni ochish", "in_hint": "Shahar nomini yozing",
           "ch_joined": "🤝 Siz <b>{t}</b> musobaqasiga qo'shildingiz!\n\n{d} kun barcha 5 namoz — do'stlar bilan birga. Namozlarni kundalikda belgilang 🤍",
           "ch_nf": "😔 Musobaqa topilmadi yoki tugagan.", "ch_full": "😔 Bu musobaqada joy qolmadi."},
    "tg": {"btn_azr_on": "🌅 Ёдоварии зикрҳо: ФАЪОЛ ✅", "btn_azr_off": "🌅 Ёдоварии зикрҳо: ХОМӮШ ❌",
           "btn_wk_on": "📈 Ҳисоботи ҳафтаина: ФАЪОЛ ✅", "btn_wk_off": "📈 Ҳисоботи ҳафтаина: ХОМӮШ ❌",
           "az_rem_m": "🌅 <b>Вақти зикрҳои субҳ</b>\nРӯзи худро бо зикри Аллоҳ оғоз кунед 🤍",
           "az_rem_e": "🌙 <b>Вақти зикрҳои шом</b>\nРӯзи худро бо зикри Аллоҳ анҷом диҳед 🤍",
           "btn_open_azkar": "📖 Кушодани зикрҳо", "btn_open_tracker": "✅ Кушодани рӯйхат", "btn_open_ch": "🤝 Кушодани мусобиқа",
           "wk_title": "📈 <b>Ҳафтаи шумо</b> · {range}", "wk_prayers": "✅ Намозҳо: <b>{n} аз 35</b> ({p}%)",
           "wk_full": "🟢 Рӯзҳои пурра: <b>{d} аз 7</b>", "wk_streak": "🔥 Силсилаи ҷорӣ: <b>{s}</b> рӯз",
           "wk_great": "Мошоаллоҳ, ҳамин тавр идома диҳед! 🤍", "wk_good": "Ҳафтаи хуб — бигзор ояндааш боз беҳтар бошад 🤍",
           "wk_start": "Ҳар намоз муҳим аст. Биёед ин ҳафтаро беҳтар кунем 🤍",
           "in_open": "🕌 Кушодани бот", "in_hint": "Номи шаҳрро нависед",
           "ch_joined": "🤝 Шумо ба мусобиқаи <b>{t}</b> ҳамроҳ шудед!\n\n{d} рӯз ҳамаи 5 намоз — якҷоя бо дӯстон. Намозҳоро дар рӯйхат қайд кунед 🤍",
           "ch_nf": "😔 Мусобиқа ёфт нашуд ё ба охир расидааст.", "ch_full": "😔 Дар ин мусобиқа ҷой намонд."},
    "ar": {"btn_azr_on": "🌅 تذكير الأذكار: مفعّل ✅", "btn_azr_off": "🌅 تذكير الأذكار: متوقف ❌",
           "btn_wk_on": "📈 التقرير الأسبوعي: مفعّل ✅", "btn_wk_off": "📈 التقرير الأسبوعي: متوقف ❌",
           "az_rem_m": "🌅 <b>حان وقت أذكار الصباح</b>\nابدأ يومك بذكر الله 🤍",
           "az_rem_e": "🌙 <b>حان وقت أذكار المساء</b>\nاختم يومك بذكر الله 🤍",
           "btn_open_azkar": "📖 فتح الأذكار", "btn_open_tracker": "✅ فتح متابعة الصلوات", "btn_open_ch": "🤝 فتح التحدي",
           "wk_title": "📈 <b>أسبوعك</b> · {range}", "wk_prayers": "✅ الصلوات: <b>{n} من 35</b> ({p}%)",
           "wk_full": "🟢 الأيام الكاملة: <b>{d} من 7</b>", "wk_streak": "🔥 السلسلة الحالية: <b>{s}</b> يوم",
           "wk_great": "ما شاء الله، استمر! 🤍", "wk_good": "أسبوع جيد — لنجعل القادم أفضل 🤍",
           "wk_start": "كل صلاة مهمة. لنجعل هذا الأسبوع أفضل 🤍",
           "in_open": "🕌 فتح البوت", "in_hint": "اكتب اسم المدينة",
           "ch_joined": "🤝 انضممت إلى تحدي <b>{t}</b>!\n\n{d} يوماً كل الصلوات الخمس — مع الأصدقاء. سجّل صلواتك في المتابعة 🤍",
           "ch_nf": "😔 لم يتم العثور على التحدي أو انتهى.", "ch_full": "😔 لا توجد أماكن في هذا التحدي."},
}
for _l, _d in EXTRA4.items():
    T[_l].update(_d)

EXTRA5 = {
    "en": {"on": "on", "off": "off",
           "btn_rem_s_on": "🔔 Reminders ✅", "btn_rem_s_off": "🔕 Reminders ❌",
           "sb_lead": "⏰ In advance", "sb_at_on": "🕌 At time ✅", "sb_at_off": "🕌 At time ❌",
           "sb_auto": "🔄 Auto-update", "sb_ram_on": "🌙 Ramadan ✅", "sb_ram_off": "🌙 Ramadan ❌",
           "sb_wk_on": "📈 Report ✅", "sb_wk_off": "📈 Report ❌", "sb_azan": "🔊 Adhan: {v}",
           "st_at": "🕌 At prayer time: {v}", "st_ram": "🌙 Ramadan mode: {v}", "st_wk": "📈 Weekly report: {v}", "st_azan": "🔊 Adhan: {v}",
           "btn_groups": "👥 Groups & channels", "btn_dev": "👨‍💻 Developer",
           "groups_title": "👥 <b>Groups & channels</b>\n\nAdd me to a group or a channel — I'll post the prayer times there and remind everyone 🤍",
           "btn_share": "📤 Share", "share_footer": "🕌 Prayer times for your city — {bot}",
           "btn_prayed": "✅ I prayed", "btn_prayed_done": "✅ Marked in the tracker", "prayed_toast": "Marked in the tracker 🤍",
           "azan_title": "🔊 <b>Adhan</b>\n\nRight after the reminder at prayer time, a recording of the adhan will arrive silently. Choose a muezzin:",
           "badge_new": "🏅 <b>New achievement!</b>\n\n{list}\n\nMay Allah accept your prayers 🤍",
           "badge_share": "I earned «{name}» in Mawaqit 🤍",
           "b_s7": "🔥 7 days in a row — all 5 prayers", "b_s30": "🏅 30 days in a row — all 5 prayers", "b_s100": "👑 100 days in a row — all 5 prayers",
           "b_t100": "💯 100 prayers", "b_t500": "🏆 500 prayers", "b_t1000": "🌟 1000 prayers",
           "btn_open_tracker2": "✅ Tracker",
           "sum_m_title": "🎁 <b>Your {period}</b>", "sum_y_title": "🎁 <b>Your year {period}</b>",
           "sum_prayers": "✅ Prayers: <b>{n}</b> of {m} ({p}%)", "sum_full": "🟢 Complete days: <b>{d}</b>",
           "sum_best": "🔥 Best streak: <b>{s}</b> d.", "sum_top": "⭐ Most steady prayer: <b>{name}</b>",
           "sum_end": "May Allah accept every prayer 🤍", "sum_share": "My {period} in Mawaqit: {n} prayers 🤍",
           "img_prayers": "prayers", "img_full": "complete days", "img_best": "best streak", "img_top": "most steady",
           "ref_joined": "🤲 One more person joined through you. Total: <b>{n}</b>\n\nMay it be a sadaqah jariyah for you 🤍",
           "months": ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"]},
    "ru": {"on": "вкл", "off": "выкл",
           "btn_rem_s_on": "🔔 Напоминания ✅", "btn_rem_s_off": "🔕 Напоминания ❌",
           "sb_lead": "⏰ Заранее", "sb_at_on": "🕌 В момент ✅", "sb_at_off": "🕌 В момент ❌",
           "sb_auto": "🔄 Автообновление", "sb_ram_on": "🌙 Рамадан ✅", "sb_ram_off": "🌙 Рамадан ❌",
           "sb_wk_on": "📈 Отчёт ✅", "sb_wk_off": "📈 Отчёт ❌", "sb_azan": "🔊 Азан: {v}",
           "st_at": "🕌 В момент намаза: {v}", "st_ram": "🌙 Режим Рамадана: {v}", "st_wk": "📈 Отчёт за неделю: {v}", "st_azan": "🔊 Азан: {v}",
           "btn_groups": "👥 Группы и каналы", "btn_dev": "👨‍💻 Разработчик",
           "groups_title": "👥 <b>Группы и каналы</b>\n\nДобавьте меня в группу или канал — я буду публиковать время намаза и напоминать всем 🤍",
           "btn_share": "📤 Поделиться", "share_footer": "🕌 Время намаза для вашего города — {bot}",
           "btn_prayed": "✅ Прочитал", "btn_prayed_done": "✅ Отмечено в трекере", "prayed_toast": "Отмечено в трекере 🤍",
           "azan_title": "🔊 <b>Азан</b>\n\nСразу после напоминания в момент намаза тихо придёт запись азана. Выберите муэдзина:",
           "badge_new": "🏅 <b>Новое достижение!</b>\n\n{list}\n\nПусть Аллах примет ваши намазы 🤍",
           "badge_share": "Я получил достижение «{name}» в Mawaqit 🤍",
           "b_s7": "🔥 7 дней подряд все 5 намазов", "b_s30": "🏅 30 дней подряд все 5 намазов", "b_s100": "👑 100 дней подряд все 5 намазов",
           "b_t100": "💯 100 намазов", "b_t500": "🏆 500 намазов", "b_t1000": "🌟 1000 намазов",
           "btn_open_tracker2": "✅ Трекер",
           "sum_m_title": "🎁 <b>Итоги: {period}</b>", "sum_y_title": "🎁 <b>Итоги {period} года</b>",
           "sum_prayers": "✅ Намазов: <b>{n}</b> из {m} ({p}%)", "sum_full": "🟢 Полных дней: <b>{d}</b>",
           "sum_best": "🔥 Лучшая серия: <b>{s}</b> дн.", "sum_top": "⭐ Самый стабильный намаз: <b>{name}</b>",
           "sum_end": "Пусть Аллах примет каждый намаз 🤍", "sum_share": "Мои итоги ({period}) в Mawaqit: {n} намазов 🤍",
           "img_prayers": "намазов", "img_full": "полных дней", "img_best": "лучшая серия", "img_top": "самый стабильный",
           "ref_joined": "🤲 Через тебя присоединился ещё 1 человек. Всего: <b>{n}</b>\n\nПусть это будет садака джария 🤍",
           "months": ["Январь", "Февраль", "Март", "Апрель", "Май", "Июнь", "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь"]},
    "uz": {"on": "yoqilgan", "off": "o'chiq",
           "btn_rem_s_on": "🔔 Eslatmalar ✅", "btn_rem_s_off": "🔕 Eslatmalar ❌",
           "sb_lead": "⏰ Oldindan", "sb_at_on": "🕌 Vaqtida ✅", "sb_at_off": "🕌 Vaqtida ❌",
           "sb_auto": "🔄 Avtoyangilash", "sb_ram_on": "🌙 Ramazon ✅", "sb_ram_off": "🌙 Ramazon ❌",
           "sb_wk_on": "📈 Hisobot ✅", "sb_wk_off": "📈 Hisobot ❌", "sb_azan": "🔊 Azon: {v}",
           "st_at": "🕌 Namoz vaqtida: {v}", "st_ram": "🌙 Ramazon rejimi: {v}", "st_wk": "📈 Haftalik hisobot: {v}", "st_azan": "🔊 Azon: {v}",
           "btn_groups": "👥 Guruh va kanallar", "btn_dev": "👨‍💻 Dasturchi",
           "groups_title": "👥 <b>Guruh va kanallar</b>\n\nMeni guruh yoki kanalga qo'shing — u yerda namoz vaqtlarini e'lon qilib, hammaga eslataman 🤍",
           "btn_share": "📤 Ulashish", "share_footer": "🕌 Shahringiz uchun namoz vaqtlari — {bot}",
           "btn_prayed": "✅ O'qidim", "btn_prayed_done": "✅ Kundalikda belgilandi", "prayed_toast": "Kundalikda belgilandi 🤍",
           "azan_title": "🔊 <b>Azon</b>\n\nNamoz vaqtidagi eslatmadan so'ng azon yozuvi ovozsiz keladi. Muazzinni tanlang:",
           "badge_new": "🏅 <b>Yangi yutuq!</b>\n\n{list}\n\nAlloh namozlaringizni qabul qilsin 🤍",
           "badge_share": "Mawaqit'da «{name}» yutug'ini oldim 🤍",
           "b_s7": "🔥 7 kun ketma-ket 5 vaqt namoz", "b_s30": "🏅 30 kun ketma-ket 5 vaqt namoz", "b_s100": "👑 100 kun ketma-ket 5 vaqt namoz",
           "b_t100": "💯 100 namoz", "b_t500": "🏆 500 namoz", "b_t1000": "🌟 1000 namoz",
           "btn_open_tracker2": "✅ Kundalik",
           "sum_m_title": "🎁 <b>Yakunlar: {period}</b>", "sum_y_title": "🎁 <b>{period} yil yakunlari</b>",
           "sum_prayers": "✅ Namozlar: <b>{m} tadan {n} ta</b> ({p}%)", "sum_full": "🟢 To'liq kunlar: <b>{d}</b>",
           "sum_best": "🔥 Eng uzun ketma-ketlik: <b>{s}</b> kun", "sum_top": "⭐ Eng barqaror namoz: <b>{name}</b>",
           "sum_end": "Alloh har bir namozni qabul qilsin 🤍", "sum_share": "Mawaqit'dagi yakunlarim ({period}): {n} namoz 🤍",
           "img_prayers": "namoz", "img_full": "to'liq kun", "img_best": "eng uzun seriya", "img_top": "eng barqaror",
           "ref_joined": "🤲 Siz orqali yana 1 kishi qo'shildi. Jami: <b>{n}</b>\n\nBu siz uchun sadaqai joriya bo'lsin 🤍",
           "months": ["Yanvar", "Fevral", "Mart", "Aprel", "May", "Iyun", "Iyul", "Avgust", "Sentabr", "Oktabr", "Noyabr", "Dekabr"]},
    "tg": {"on": "фаъол", "off": "хомӯш",
           "btn_rem_s_on": "🔔 Ёдовариҳо ✅", "btn_rem_s_off": "🔕 Ёдовариҳо ❌",
           "sb_lead": "⏰ Пешакӣ", "sb_at_on": "🕌 Дар вақташ ✅", "sb_at_off": "🕌 Дар вақташ ❌",
           "sb_auto": "🔄 Навсозии худкор", "sb_ram_on": "🌙 Рамазон ✅", "sb_ram_off": "🌙 Рамазон ❌",
           "sb_wk_on": "📈 Ҳисобот ✅", "sb_wk_off": "📈 Ҳисобот ❌", "sb_azan": "🔊 Азон: {v}",
           "st_at": "🕌 Дар вақти намоз: {v}", "st_ram": "🌙 Ҳолати Рамазон: {v}", "st_wk": "📈 Ҳисоботи ҳафтаина: {v}", "st_azan": "🔊 Азон: {v}",
           "btn_groups": "👥 Гурӯҳҳо ва каналҳо", "btn_dev": "👨‍💻 Барномасоз",
           "groups_title": "👥 <b>Гурӯҳҳо ва каналҳо</b>\n\nМаро ба гурӯҳ ё канал илова кунед — ман вақти намозро нашр карда, ба ҳама ёдрас мекунам 🤍",
           "btn_share": "📤 Мубодила", "share_footer": "🕌 Вақти намоз барои шаҳри шумо — {bot}",
           "btn_prayed": "✅ Хондам", "btn_prayed_done": "✅ Дар рӯйхат қайд шуд", "prayed_toast": "Дар рӯйхат қайд шуд 🤍",
           "azan_title": "🔊 <b>Азон</b>\n\nБаъди ёдоварӣ дар вақти намоз сабти азон бесадо меояд. Муаззинро интихоб кунед:",
           "badge_new": "🏅 <b>Дастоварди нав!</b>\n\n{list}\n\nАллоҳ намозҳои шуморо қабул кунад 🤍",
           "badge_share": "Ман дар Mawaqit дастоварди «{name}»-ро гирифтам 🤍",
           "b_s7": "🔥 7 рӯз пайиҳам ҳамаи 5 намоз", "b_s30": "🏅 30 рӯз пайиҳам ҳамаи 5 намоз", "b_s100": "👑 100 рӯз пайиҳам ҳамаи 5 намоз",
           "b_t100": "💯 100 намоз", "b_t500": "🏆 500 намоз", "b_t1000": "🌟 1000 намоз",
           "btn_open_tracker2": "✅ Рӯйхат",
           "sum_m_title": "🎁 <b>Натиҷаҳо: {period}</b>", "sum_y_title": "🎁 <b>Натиҷаҳои соли {period}</b>",
           "sum_prayers": "✅ Намозҳо: <b>{n}</b> аз {m} ({p}%)", "sum_full": "🟢 Рӯзҳои пурра: <b>{d}</b>",
           "sum_best": "🔥 Беҳтарин силсила: <b>{s}</b> рӯз", "sum_top": "⭐ Устувортарин намоз: <b>{name}</b>",
           "sum_end": "Аллоҳ ҳар намозро қабул кунад 🤍", "sum_share": "Натиҷаҳои ман ({period}) дар Mawaqit: {n} намоз 🤍",
           "img_prayers": "намоз", "img_full": "рӯзи пурра", "img_best": "беҳтарин силсила", "img_top": "устувортарин",
           "ref_joined": "🤲 Тавассути шумо боз 1 нафар ҳамроҳ шуд. Ҳамагӣ: <b>{n}</b>\n\nБигзор ин барои шумо садақаи ҷория бошад 🤍",
           "months": ["Январ", "Феврал", "Март", "Апрел", "Май", "Июн", "Июл", "Август", "Сентябр", "Октябр", "Ноябр", "Декабр"]},
    "ar": {"on": "مفعّل", "off": "متوقف",
           "btn_rem_s_on": "🔔 التذكيرات ✅", "btn_rem_s_off": "🔕 التذكيرات ❌",
           "sb_lead": "⏰ مسبقاً", "sb_at_on": "🕌 عند الوقت ✅", "sb_at_off": "🕌 عند الوقت ❌",
           "sb_auto": "🔄 التحديث التلقائي", "sb_ram_on": "🌙 رمضان ✅", "sb_ram_off": "🌙 رمضان ❌",
           "sb_wk_on": "📈 التقرير ✅", "sb_wk_off": "📈 التقرير ❌", "sb_azan": "🔊 الأذان: {v}",
           "st_at": "🕌 عند دخول الوقت: {v}", "st_ram": "🌙 وضع رمضان: {v}", "st_wk": "📈 التقرير الأسبوعي: {v}", "st_azan": "🔊 الأذان: {v}",
           "btn_groups": "👥 المجموعات والقنوات", "btn_dev": "👨‍💻 المطوّر",
           "groups_title": "👥 <b>المجموعات والقنوات</b>\n\nأضفني إلى مجموعة أو قناة — سأنشر مواقيت الصلاة وأذكّر الجميع 🤍",
           "btn_share": "📤 مشاركة", "share_footer": "🕌 مواقيت الصلاة لمدينتك — {bot}",
           "btn_prayed": "✅ صلّيت", "btn_prayed_done": "✅ سُجّلت في المتابعة", "prayed_toast": "سُجّلت في المتابعة 🤍",
           "azan_title": "🔊 <b>الأذان</b>\n\nبعد التذكير عند دخول الوقت يصلك تسجيل الأذان بصمت. اختر المؤذن:",
           "badge_new": "🏅 <b>إنجاز جديد!</b>\n\n{list}\n\nتقبّل الله صلواتك 🤍",
           "badge_share": "حصلت على إنجاز «{name}» في مواقيت 🤍",
           "b_s7": "🔥 7 أيام متتالية بالصلوات الخمس", "b_s30": "🏅 30 يوماً متتالياً بالصلوات الخمس", "b_s100": "👑 100 يوم متتالٍ بالصلوات الخمس",
           "b_t100": "💯 100 صلاة", "b_t500": "🏆 500 صلاة", "b_t1000": "🌟 1000 صلاة",
           "btn_open_tracker2": "✅ المتابعة",
           "sum_m_title": "🎁 <b>حصاد {period}</b>", "sum_y_title": "🎁 <b>حصاد عام {period}</b>",
           "sum_prayers": "✅ الصلوات: <b>{n}</b> من {m} ({p}%)", "sum_full": "🟢 الأيام الكاملة: <b>{d}</b>",
           "sum_best": "🔥 أطول سلسلة: <b>{s}</b> يوم", "sum_top": "⭐ أكثر صلاة ثباتاً: <b>{name}</b>",
           "sum_end": "تقبّل الله كل صلاة 🤍", "sum_share": "حصادي ({period}) في مواقيت: {n} صلاة 🤍",
           "img_prayers": "صلاة", "img_full": "يوم كامل", "img_best": "أطول سلسلة", "img_top": "الأكثر ثباتاً",
           "ref_joined": "🤲 انضم شخص آخر عن طريقك. المجموع: <b>{n}</b>\n\nجعلها الله لك صدقة جارية 🤍",
           "months": ["يناير", "فبراير", "مارس", "أبريل", "مايو", "يونيو", "يوليو", "أغسطس", "سبتمبر", "أكتوبر", "نوفمبر", "ديسمبر"]},
}
for _l, _d in EXTRA5.items():
    T[_l].update(_d)

EXTRA6 = {"en": {"admin_msg_header": "📩 <b>Message from the administrator:</b>"},
          "ru": {"admin_msg_header": "📩 <b>Сообщение от администратора:</b>"},
          "uz": {"admin_msg_header": "📩 <b>Administrator xabari:</b>"},
          "tg": {"admin_msg_header": "📩 <b>Паёми маъмур:</b>"},
          "ar": {"admin_msg_header": "📩 <b>رسالة من المشرف:</b>"}}
for _l, _d in EXTRA6.items():
    T[_l].update(_d)


EXTRA7 = {
    "en": {"btn_fast": "🥣 Suhoor & Iftar", "btn_snd": "🔔 Prayer sounds",
           "fast_title": "🥣 <b>Suhoor & Iftar</b>\n\nToday: suhoor ends at <b>{s}</b>, iftar at <b>{i}</b>.\nReminders arrive every day while they are on.",
           "fast_show_on": "👁 Show in the times card: ON ✅", "fast_show_off": "👁 Show in the times card: OFF ❌",
           "fast_suh": "🥣 Suhoor reminder:", "fast_ift": "🍽 Iftar reminder:", "fast_at": "At Maghrib",
           "fast_snd_on": "🔔 These reminders: with sound", "fast_snd_off": "🔕 These reminders: silent",
           "snd_title": "🔔 <b>Prayer sounds</b>\n\nTap a prayer to switch: with sound → silent → no reminder.\n<i>Silent: the message arrives without sound or vibration.</i>",
           "mode_s": "🔔 With sound", "mode_q": "🔕 Silent", "mode_o": "❌ No reminder",
           "suh_rem": "🥣 <b>Suhoor</b> ends in {n} min · {time}\nFinish your meal 🤍"},
    "ru": {"btn_fast": "🥣 Сухур и ифтар", "btn_snd": "🔔 Звук намазов",
           "fast_title": "🥣 <b>Сухур и ифтар</b>\n\nСегодня: сухур до <b>{s}</b>, ифтар в <b>{i}</b>.\nНапоминания приходят каждый день, пока включены.",
           "fast_show_on": "👁 Показывать в карточке: ВКЛ ✅", "fast_show_off": "👁 Показывать в карточке: ВЫКЛ ❌",
           "fast_suh": "🥣 Напомнить о конце сухура:", "fast_ift": "🍽 Напомнить об ифтаре:", "fast_at": "В момент Магриба",
           "fast_snd_on": "🔔 Эти напоминания: со звуком", "fast_snd_off": "🔕 Эти напоминания: без звука",
           "snd_title": "🔔 <b>Звук намазов</b>\n\nНажмите на намаз, чтобы переключить: со звуком → без звука → не напоминать.\n<i>Без звука — сообщение придёт тихо, без звука и вибрации.</i>",
           "mode_s": "🔔 Со звуком", "mode_q": "🔕 Без звука", "mode_o": "❌ Не напоминать",
           "suh_rem": "🥣 <b>Сухур</b> заканчивается через {n} мин · {time}\nУспейте поесть 🤍"},
    "uz": {"btn_fast": "🥣 Saharlik va iftor", "btn_snd": "🔔 Namozlar ovozi",
           "fast_title": "🥣 <b>Saharlik va iftor</b>\n\nBugun: saharlik <b>{s}</b> gacha, iftor <b>{i}</b> da.\nEslatmalar yoqilgan ekan, har kuni keladi.",
           "fast_show_on": "👁 Kartada ko'rsatish: YOQILGAN ✅", "fast_show_off": "👁 Kartada ko'rsatish: O'CHIQ ❌",
           "fast_suh": "🥣 Saharlik tugashini eslatish:", "fast_ift": "🍽 Iftorni eslatish:", "fast_at": "Shom vaqtida",
           "fast_snd_on": "🔔 Bu eslatmalar: ovozli", "fast_snd_off": "🔕 Bu eslatmalar: ovozsiz",
           "snd_title": "🔔 <b>Namozlar ovozi</b>\n\nAlmashtirish uchun namozni bosing: ovozli → ovozsiz → eslatmaslik.\n<i>Ovozsiz — xabar ovoz va tebranishsiz keladi.</i>",
           "mode_s": "🔔 Ovozli", "mode_q": "🔕 Ovozsiz", "mode_o": "❌ Eslatmaslik",
           "suh_rem": "🥣 <b>Saharlik</b> tugashiga {n} daqiqa qoldi · {time}\nOvqatlanishga ulguring 🤍"},
    "tg": {"btn_fast": "🥣 Саҳарӣ ва ифтор", "btn_snd": "🔔 Садои намозҳо",
           "fast_title": "🥣 <b>Саҳарӣ ва ифтор</b>\n\nИмрӯз: саҳарӣ то <b>{s}</b>, ифтор соати <b>{i}</b>.\nЁдовариҳо то фаъол ҳастанд, ҳар рӯз меоянд.",
           "fast_show_on": "👁 Дар корт нишон додан: ФАЪОЛ ✅", "fast_show_off": "👁 Дар корт нишон додан: ХОМӮШ ❌",
           "fast_suh": "🥣 Ёдоварии анҷоми саҳарӣ:", "fast_ift": "🍽 Ёдоварии ифтор:", "fast_at": "Дар вақти Шом",
           "fast_snd_on": "🔔 Ин ёдовариҳо: бо садо", "fast_snd_off": "🔕 Ин ёдовариҳо: бесадо",
           "snd_title": "🔔 <b>Садои намозҳо</b>\n\nБарои иваз кардан намозро пахш кунед: бо садо → бесадо → ёдоварӣ нашавад.\n<i>Бесадо — паём бе садо ва ларзиш меояд.</i>",
           "mode_s": "🔔 Бо садо", "mode_q": "🔕 Бесадо", "mode_o": "❌ Ёдоварӣ нашавад",
           "suh_rem": "🥣 <b>Саҳарӣ</b> баъди {n} дақиқа анҷом меёбад · {time}\nХӯрокро тамом кунед 🤍"},
    "ar": {"btn_fast": "🥣 السحور والإفطار", "btn_snd": "🔔 أصوات الصلوات",
           "fast_title": "🥣 <b>السحور والإفطار</b>\n\nاليوم: السحور حتى <b>{s}</b>، والإفطار الساعة <b>{i}</b>.\nتصل التذكيرات كل يوم ما دامت مفعّلة.",
           "fast_show_on": "👁 العرض في البطاقة: مفعّل ✅", "fast_show_off": "👁 العرض في البطاقة: متوقف ❌",
           "fast_suh": "🥣 تذكير بانتهاء السحور:", "fast_ift": "🍽 تذكير بالإفطار:", "fast_at": "عند المغرب",
           "fast_snd_on": "🔔 هذه التذكيرات: بصوت", "fast_snd_off": "🔕 هذه التذكيرات: بصمت",
           "snd_title": "🔔 <b>أصوات الصلوات</b>\n\nاضغط على الصلاة للتبديل: بصوت ← بصمت ← بدون تذكير.\n<i>بصمت: تصل الرسالة دون صوت أو اهتزاز.</i>",
           "mode_s": "🔔 بصوت", "mode_q": "🔕 بصمت", "mode_o": "❌ بدون تذكير",
           "suh_rem": "🥣 ينتهي <b>السحور</b> بعد {n} دقيقة · {time}\nأكمل طعامك 🤍"},
}
for _l, _d in EXTRA7.items():
    T[_l].update(_d)


EXTRA8 = {
    "en": {"rb_morning": "🌅 Morning adhkar", "rb_evening": "🌙 Evening adhkar", "rb_tracker": "✅ Mark today's prayers",
           "mb_azkar": "📿 Adhkar", "mb_tracker": "✅ Tracker",
           "tour_text": "✨ <b>There's more in the app</b>\n\n🧭 Qibla with a live compass\n📿 Tasbih and 🌅 morning & evening adhkar\n✅ Prayer tracker, streaks and challenges with friends\n📅 Calendar for the month and Ramadan\n🤲 Daily duas and the 99 Names of Allah\n\nOpen any section 👇",
           "tb_qibla": "🧭 Qibla", "tb_tasbih": "📿 Tasbih", "tb_azkar": "🌅 Adhkar", "tb_tracker": "✅ Tracker", "tb_cal": "📅 Calendar", "tb_duas": "🤲 Duas",
           "app_menu": "🕌 App"},
    "ru": {"rb_morning": "🌅 Утренние азкары", "rb_evening": "🌙 Вечерние азкары", "rb_tracker": "✅ Отметить намазы за день",
           "mb_azkar": "📿 Азкары", "mb_tracker": "✅ Трекер",
           "tour_text": "✨ <b>В приложении есть ещё много полезного</b>\n\n🧭 Кибла с живым компасом\n📿 Тасбих и 🌅 утренние и вечерние азкары\n✅ Трекер намазов, серии и вызовы с друзьями\n📅 Календарь на месяц и Рамадан\n🤲 Дуа на каждый день и 99 имён Аллаха\n\nОткройте любой раздел 👇",
           "tb_qibla": "🧭 Кибла", "tb_tasbih": "📿 Тасбих", "tb_azkar": "🌅 Азкары", "tb_tracker": "✅ Трекер", "tb_cal": "📅 Календарь", "tb_duas": "🤲 Дуа",
           "app_menu": "🕌 Приложение"},
    "uz": {"rb_morning": "🌅 Tong zikrlari", "rb_evening": "🌙 Kech zikrlari", "rb_tracker": "✅ Bugungi namozlarni belgilash",
           "mb_azkar": "📿 Zikrlar", "mb_tracker": "✅ Kundalik",
           "tour_text": "✨ <b>Ilovada yana ko'p foydali narsalar bor</b>\n\n🧭 Jonli kompasli qibla\n📿 Tasbeh va 🌅 tong va kech zikrlari\n✅ Namoz kundaligi, ketma-ketlik va do'stlar bilan musobaqalar\n📅 Oylik taqvim va Ramazon\n🤲 Har kunlik duolar va Allohning 99 ismi\n\nIstalgan bo'limni oching 👇",
           "tb_qibla": "🧭 Qibla", "tb_tasbih": "📿 Tasbeh", "tb_azkar": "🌅 Zikrlar", "tb_tracker": "✅ Kundalik", "tb_cal": "📅 Taqvim", "tb_duas": "🤲 Duolar",
           "app_menu": "🕌 Ilova"},
    "tg": {"rb_morning": "🌅 Зикрҳои субҳ", "rb_evening": "🌙 Зикрҳои шом", "rb_tracker": "✅ Қайди намозҳои имрӯз",
           "mb_azkar": "📿 Зикрҳо", "mb_tracker": "✅ Рӯйхат",
           "tour_text": "✨ <b>Дар барнома боз чизҳои муфид зиёданд</b>\n\n🧭 Қибла бо компаси зинда\n📿 Тасбеҳ ва 🌅 зикрҳои субҳу шом\n✅ Рӯйхати намозҳо, силсила ва мусобиқа бо дӯстон\n📅 Тақвими моҳ ва Рамазон\n🤲 Дуоҳои ҳаррӯза ва 99 номи Аллоҳ\n\nҲар бахшро кушоед 👇",
           "tb_qibla": "🧭 Қибла", "tb_tasbih": "📿 Тасбеҳ", "tb_azkar": "🌅 Зикрҳо", "tb_tracker": "✅ Рӯйхат", "tb_cal": "📅 Тақвим", "tb_duas": "🤲 Дуоҳо",
           "app_menu": "🕌 Барнома"},
    "ar": {"rb_morning": "🌅 أذكار الصباح", "rb_evening": "🌙 أذكار المساء", "rb_tracker": "✅ سجّل صلوات اليوم",
           "mb_azkar": "📿 الأذكار", "mb_tracker": "✅ المتابعة",
           "tour_text": "✨ <b>في التطبيق المزيد من الفوائد</b>\n\n🧭 القبلة مع بوصلة حيّة\n📿 التسبيح و🌅 أذكار الصباح والمساء\n✅ متابعة الصلوات والسلاسل وتحديات مع الأصدقاء\n📅 تقويم الشهر ورمضان\n🤲 أدعية يومية وأسماء الله الحسنى\n\nافتح أي قسم 👇",
           "tb_qibla": "🧭 القبلة", "tb_tasbih": "📿 التسبيح", "tb_azkar": "🌅 الأذكار", "tb_tracker": "✅ المتابعة", "tb_cal": "📅 التقويم", "tb_duas": "🤲 الأدعية",
           "app_menu": "🕌 التطبيق"},
}
for _l, _d in EXTRA8.items():
    T[_l].update(_d)


EXTRA9 = {
    "en": {"ai_btn": "🤖 Ask about Islam",
           "ai_intro": "🤖 <b>Questions about Islam</b>\n\nWrite your question — about prayer, fasting, adhkar, the Qur'an, manners. You can ask follow-up questions.\n\n<i>Answers are written by AI and may contain mistakes. For important matters, ask an imam.</i>\n\n💬 Questions left today: <b>{n}</b>",
           "ai_left": "💬 Questions left today: {n}", "ai_limit": "⏳ That's all the questions for today ({n} a day). Come back tomorrow 🤍",
           "ai_disclaimer": "🤖 AI answer — it may contain mistakes. For important matters, ask an imam.",
           "ai_err": "😔 Couldn't get an answer right now. Please try again a little later.",
           "ai_new": "🧹 New conversation", "ai_exit": "❌ Exit", "ai_reset_done": "🧹 Started a new conversation. Ask your question 👇",
           "ai_blocked": "😔 I can't answer this question."},
    "ru": {"ai_btn": "🤖 Вопрос об исламе",
           "ai_intro": "🤖 <b>Вопросы об исламе</b>\n\nНапишите вопрос — о намазе, посте, азкарах, Коране, этике. Можно задавать уточняющие вопросы.\n\n<i>Ответы пишет ИИ, он может ошибаться. По важным вопросам обращайтесь к имаму.</i>\n\n💬 Осталось вопросов сегодня: <b>{n}</b>",
           "ai_left": "💬 Осталось вопросов сегодня: {n}", "ai_limit": "⏳ На сегодня вопросы закончились ({n} в день). Возвращайтесь завтра 🤍",
           "ai_disclaimer": "🤖 Ответ ИИ — он может ошибаться. По важным вопросам обращайтесь к имаму.",
           "ai_err": "😔 Сейчас не получилось получить ответ. Попробуйте чуть позже.",
           "ai_new": "🧹 Новый диалог", "ai_exit": "❌ Выйти", "ai_reset_done": "🧹 Начали новый диалог. Задайте вопрос 👇",
           "ai_blocked": "😔 На этот вопрос я ответить не могу."},
    "uz": {"ai_btn": "🤖 Islom haqida savol",
           "ai_intro": "🤖 <b>Islom haqida savollar</b>\n\nSavolingizni yozing — namoz, ro'za, zikrlar, Qur'on, odob haqida. Qo'shimcha savollar ham berishingiz mumkin.\n\n<i>Javoblarni sun'iy intellekt yozadi, u xato qilishi mumkin. Muhim masalalarda imomga murojaat qiling.</i>\n\n💬 Bugun qolgan savollar: <b>{n}</b>",
           "ai_left": "💬 Bugun qolgan savollar: {n}", "ai_limit": "⏳ Bugungi savollar tugadi (kuniga {n} ta). Ertaga qaytib keling 🤍",
           "ai_disclaimer": "🤖 Sun'iy intellekt javobi — xato bo'lishi mumkin. Muhim masalalarda imomga murojaat qiling.",
           "ai_err": "😔 Hozir javob olib bo'lmadi. Birozdan so'ng qayta urinib ko'ring.",
           "ai_new": "🧹 Yangi suhbat", "ai_exit": "❌ Chiqish", "ai_reset_done": "🧹 Yangi suhbat boshlandi. Savolingizni yozing 👇",
           "ai_blocked": "😔 Bu savolga javob bera olmayman."},
    "tg": {"ai_btn": "🤖 Савол дар бораи ислом",
           "ai_intro": "🤖 <b>Саволҳо дар бораи ислом</b>\n\nСаволи худро нависед — дар бораи намоз, рӯза, зикрҳо, Қуръон, одоб. Саволҳои иловагӣ ҳам додан мумкин.\n\n<i>Ҷавобҳоро зеҳни сунъӣ менависад, метавонад хато кунад. Дар масъалаҳои муҳим ба имом муроҷиат кунед.</i>\n\n💬 Саволҳои боқимондаи имрӯз: <b>{n}</b>",
           "ai_left": "💬 Саволҳои боқимондаи имрӯз: {n}", "ai_limit": "⏳ Саволҳои имрӯза тамом шуданд (рӯзе {n}). Фардо биёед 🤍",
           "ai_disclaimer": "🤖 Ҷавоби зеҳни сунъӣ — метавонад хато бошад. Дар масъалаҳои муҳим ба имом муроҷиат кунед.",
           "ai_err": "😔 Ҳоло ҷавоб гирифта нашуд. Каме баъдтар боз кӯшиш кунед.",
           "ai_new": "🧹 Сӯҳбати нав", "ai_exit": "❌ Баромадан", "ai_reset_done": "🧹 Сӯҳбати нав оғоз шуд. Саволро нависед 👇",
           "ai_blocked": "😔 Ба ин савол ҷавоб дода наметавонам."},
    "ar": {"ai_btn": "🤖 سؤال عن الإسلام",
           "ai_intro": "🤖 <b>أسئلة عن الإسلام</b>\n\nاكتب سؤالك — عن الصلاة والصيام والأذكار والقرآن والآداب. يمكنك طرح أسئلة متابعة.\n\n<i>الإجابات يكتبها الذكاء الاصطناعي وقد تحتوي على أخطاء. في الأمور المهمة اسأل إماماً.</i>\n\n💬 الأسئلة المتبقية اليوم: <b>{n}</b>",
           "ai_left": "💬 الأسئلة المتبقية اليوم: {n}", "ai_limit": "⏳ انتهت أسئلة اليوم ({n} في اليوم). عد غداً 🤍",
           "ai_disclaimer": "🤖 إجابة الذكاء الاصطناعي — قد تحتوي على أخطاء. في الأمور المهمة اسأل إماماً.",
           "ai_err": "😔 تعذر الحصول على إجابة الآن. حاول بعد قليل.",
           "ai_new": "🧹 محادثة جديدة", "ai_exit": "❌ خروج", "ai_reset_done": "🧹 بدأنا محادثة جديدة. اكتب سؤالك 👇",
           "ai_blocked": "😔 لا أستطيع الإجابة عن هذا السؤال."},
}
for _l, _d in EXTRA9.items():
    T[_l].update(_d)


EXTRA10 = {
    "en": {"ai_intro2": "🤖 <b>Questions about Islam</b>\n\nWrite your question — about prayer, fasting, adhkar, the Qur'an, manners. You can ask follow-up questions.\n\n<i>Answers are written by AI and may contain mistakes. For important matters, ask an imam. Admins may read questions to improve the answers.</i>",
           "ai_status_free": "🎁 Free questions today: <b>{n}</b>", "ai_status_cred": "💎 Purchased questions: <b>{n}</b>", "ai_status_unl": "♾ Unlimited until <b>{d}</b>",
           "ai_limit2": "⏳ Your free questions for today are used up. You can get more questions for ⭐ or come back tomorrow 🤍",
           "ai_global": "⏳ Today's free questions are used up for everyone — too many people asked. You can get questions for ⭐ or come back tomorrow 🤍",
           "pack_q": "{q} questions — {s} ⭐", "pack_unl": "♾ Unlimited for {d} days — {s} ⭐",
           "inv_q_title": "{q} AI questions", "inv_unl_title": "Unlimited AI questions for {d} days",
           "inv_desc": "Questions about Islam to the AI helper in the Mawaqit bot",
           "paid_ok": "✅ Payment received! Added: {what}. Thank you 🤍",
           "don_btn": "⭐ Support the project",
           "don_title": "🤍 <b>Support the project</b>\n\nMawaqit is free. If you'd like to support its work, it will be a sadaqah jariyah. May Allah reward you 🤍",
           "don_custom": "✏️ Other amount", "don_card": "💳 To a bank card",
           "don_custom_ask": "Write how many ⭐ you'd like to send (from 1 to 100000):", "don_bad": "Please send a number from 1 to 100000.",
           "don_inv_title": "Support Mawaqit", "don_inv_desc": "A voluntary donation for the bot's work",
           "don_thanks": "🤍 Thank you for your support! May Allah reward you.",
           "don_cards_title": "💳 <b>Transfer to a card</b>\n\nTap a number to copy it:", "don_owner": "👤 Card holder: {name}",
           "don_sent": "✅ I've sent it", "don_sent_ok": "🤍 Thank you! May Allah reward you.",
           "ai_granted": "🎁 You've been given {n} questions to the AI helper. Enjoy 🤍"},
    "ru": {"ai_intro2": "🤖 <b>Вопросы об исламе</b>\n\nНапишите вопрос — о намазе, посте, азкарах, Коране, этике. Можно задавать уточняющие вопросы.\n\n<i>Ответы пишет ИИ, он может ошибаться. По важным вопросам обращайтесь к имаму. Вопросы могут просматривать администраторы для улучшения ответов.</i>",
           "ai_status_free": "🎁 Бесплатных вопросов сегодня: <b>{n}</b>", "ai_status_cred": "💎 Купленных вопросов: <b>{n}</b>", "ai_status_unl": "♾ Безлимит до <b>{d}</b>",
           "ai_limit2": "⏳ Бесплатные вопросы на сегодня закончились. Можно получить вопросы за ⭐ или вернуться завтра 🤍",
           "ai_global": "⏳ Сегодня бесплатные вопросы закончились у всех — слишком много желающих. Можно получить вопросы за ⭐ или вернуться завтра 🤍",
           "pack_q": "{q} вопросов — {s} ⭐", "pack_unl": "♾ Безлимит на {d} дн. — {s} ⭐",
           "inv_q_title": "{q} вопросов к ИИ", "inv_unl_title": "Безлимит вопросов к ИИ на {d} дн.",
           "inv_desc": "Вопросы об исламе к ИИ-помощнику в боте Mawaqit",
           "paid_ok": "✅ Оплата прошла! Начислено: {what}. Спасибо 🤍",
           "don_btn": "⭐ Поддержать проект",
           "don_title": "🤍 <b>Поддержать проект</b>\n\nMawaqit бесплатный. Если хотите поддержать его работу — это будет садака джария. Да вознаградит вас Аллах 🤍",
           "don_custom": "✏️ Своя сумма", "don_card": "💳 На карту",
           "don_custom_ask": "Напишите, сколько ⭐ хотите отправить (от 1 до 100000):", "don_bad": "Пришлите число от 1 до 100000.",
           "don_inv_title": "Поддержка Mawaqit", "don_inv_desc": "Добровольное пожертвование на работу бота",
           "don_thanks": "🤍 Спасибо за поддержку! Да вознаградит вас Аллах.",
           "don_cards_title": "💳 <b>Перевод на карту</b>\n\nНажмите на номер, чтобы скопировать:", "don_owner": "👤 Владелец: {name}",
           "don_sent": "✅ Я отправил(а)", "don_sent_ok": "🤍 Спасибо! Да вознаградит вас Аллах.",
           "ai_granted": "🎁 Вам начислено вопросов к ИИ-помощнику: {n}. Пользуйтесь на здоровье 🤍"},
    "uz": {"ai_intro2": "🤖 <b>Islom haqida savollar</b>\n\nSavolingizni yozing — namoz, ro'za, zikrlar, Qur'on, odob haqida. Qo'shimcha savollar ham berishingiz mumkin.\n\n<i>Javoblarni sun'iy intellekt yozadi, u xato qilishi mumkin. Muhim masalalarda imomga murojaat qiling. Javoblarni yaxshilash uchun savollarni administratorlar ko'rishi mumkin.</i>",
           "ai_status_free": "🎁 Bugungi bepul savollar: <b>{n}</b>", "ai_status_cred": "💎 Sotib olingan savollar: <b>{n}</b>", "ai_status_unl": "♾ <b>{d}</b> gacha cheksiz",
           "ai_limit2": "⏳ Bugungi bepul savollaringiz tugadi. ⭐ evaziga savollar olishingiz yoki ertaga qaytishingiz mumkin 🤍",
           "ai_global": "⏳ Bugun bepul savollar hamma uchun tugadi — so'raganlar juda ko'p. ⭐ evaziga savollar olishingiz yoki ertaga qaytishingiz mumkin 🤍",
           "pack_q": "{q} ta savol — {s} ⭐", "pack_unl": "♾ {d} kunga cheksiz — {s} ⭐",
           "inv_q_title": "Sun'iy intellektga {q} ta savol", "inv_unl_title": "{d} kunga cheksiz savollar",
           "inv_desc": "Mawaqit botidagi sun'iy intellekt yordamchisiga Islom haqida savollar",
           "paid_ok": "✅ To'lov qabul qilindi! Qo'shildi: {what}. Rahmat 🤍",
           "don_btn": "⭐ Loyihani qo'llab-quvvatlash",
           "don_title": "🤍 <b>Loyihani qo'llab-quvvatlash</b>\n\nMawaqit bepul. Uning ishini qo'llab-quvvatlamoqchi bo'lsangiz — bu sadaqai joriya bo'ladi. Alloh sizni mukofotlasin 🤍",
           "don_custom": "✏️ Boshqa summa", "don_card": "💳 Kartaga",
           "don_custom_ask": "Qancha ⭐ yubormoqchisiz, yozing (1 dan 100000 gacha):", "don_bad": "1 dan 100000 gacha son yuboring.",
           "don_inv_title": "Mawaqit'ni qo'llab-quvvatlash", "don_inv_desc": "Bot ishi uchun ixtiyoriy xayriya",
           "don_thanks": "🤍 Qo'llab-quvvatlaganingiz uchun rahmat! Alloh sizni mukofotlasin.",
           "don_cards_title": "💳 <b>Kartaga o'tkazish</b>\n\nNusxa olish uchun raqamni bosing:", "don_owner": "👤 Karta egasi: {name}",
           "don_sent": "✅ Yubordim", "don_sent_ok": "🤍 Rahmat! Alloh sizni mukofotlasin.",
           "ai_granted": "🎁 Sizga sun'iy intellekt yordamchisiga {n} ta savol berildi. Foydalaning 🤍"},
    "tg": {"ai_intro2": "🤖 <b>Саволҳо дар бораи ислом</b>\n\nСаволи худро нависед — дар бораи намоз, рӯза, зикрҳо, Қуръон, одоб. Саволҳои иловагӣ ҳам додан мумкин.\n\n<i>Ҷавобҳоро зеҳни сунъӣ менависад, метавонад хато кунад. Дар масъалаҳои муҳим ба имом муроҷиат кунед. Саволҳоро барои беҳтар кардани ҷавобҳо маъмурон дида метавонанд.</i>",
           "ai_status_free": "🎁 Саволҳои ройгони имрӯз: <b>{n}</b>", "ai_status_cred": "💎 Саволҳои харидашуда: <b>{n}</b>", "ai_status_unl": "♾ Бемаҳдуд то <b>{d}</b>",
           "ai_limit2": "⏳ Саволҳои ройгони имрӯзаи шумо тамом шуданд. Саволҳоро бо ⭐ гирифтан ё фардо баргаштан мумкин 🤍",
           "ai_global": "⏳ Имрӯз саволҳои ройгон барои ҳама тамом шуданд — пурсандагон бисёранд. Саволҳоро бо ⭐ гирифтан ё фардо баргаштан мумкин 🤍",
           "pack_q": "{q} савол — {s} ⭐", "pack_unl": "♾ Бемаҳдуд ба {d} рӯз — {s} ⭐",
           "inv_q_title": "{q} савол ба зеҳни сунъӣ", "inv_unl_title": "Саволҳои бемаҳдуд ба {d} рӯз",
           "inv_desc": "Саволҳо дар бораи ислом ба ёрдамчии зеҳни сунъӣ дар боти Mawaqit",
           "paid_ok": "✅ Пардохт қабул шуд! Илова шуд: {what}. Ташаккур 🤍",
           "don_btn": "⭐ Дастгирии лоиҳа",
           "don_title": "🤍 <b>Дастгирии лоиҳа</b>\n\nMawaqit ройгон аст. Агар хоҳед кори онро дастгирӣ кунед — ин садақаи ҷория мешавад. Аллоҳ шуморо подош диҳад 🤍",
           "don_custom": "✏️ Маблағи дигар", "don_card": "💳 Ба корт",
           "don_custom_ask": "Нависед, чанд ⭐ фиристодан мехоҳед (аз 1 то 100000):", "don_bad": "Рақам аз 1 то 100000 фиристед.",
           "don_inv_title": "Дастгирии Mawaqit", "don_inv_desc": "Хайрияи ихтиёрӣ барои кори бот",
           "don_thanks": "🤍 Ташаккур барои дастгирӣ! Аллоҳ шуморо подош диҳад.",
           "don_cards_title": "💳 <b>Интиқол ба корт</b>\n\nБарои нусха гирифтан рақамро пахш кунед:", "don_owner": "👤 Соҳиби корт: {name}",
           "don_sent": "✅ Фиристодам", "don_sent_ok": "🤍 Ташаккур! Аллоҳ шуморо подош диҳад.",
           "ai_granted": "🎁 Ба шумо {n} савол ба ёрдамчии зеҳни сунъӣ дода шуд. Истифода баред 🤍"},
    "ar": {"ai_intro2": "🤖 <b>أسئلة عن الإسلام</b>\n\nاكتب سؤالك — عن الصلاة والصيام والأذكار والقرآن والآداب. يمكنك طرح أسئلة متابعة.\n\n<i>الإجابات يكتبها الذكاء الاصطناعي وقد تحتوي على أخطاء. في الأمور المهمة اسأل إماماً. قد يطّلع المشرفون على الأسئلة لتحسين الإجابات.</i>",
           "ai_status_free": "🎁 الأسئلة المجانية اليوم: <b>{n}</b>", "ai_status_cred": "💎 الأسئلة المشتراة: <b>{n}</b>", "ai_status_unl": "♾ بلا حد حتى <b>{d}</b>",
           "ai_limit2": "⏳ انتهت أسئلتك المجانية لليوم. يمكنك الحصول على أسئلة مقابل ⭐ أو العودة غداً 🤍",
           "ai_global": "⏳ انتهت الأسئلة المجانية اليوم للجميع — الطلب كبير. يمكنك الحصول على أسئلة مقابل ⭐ أو العودة غداً 🤍",
           "pack_q": "{q} سؤالاً — {s} ⭐", "pack_unl": "♾ بلا حد لمدة {d} يوماً — {s} ⭐",
           "inv_q_title": "{q} سؤالاً للذكاء الاصطناعي", "inv_unl_title": "أسئلة بلا حد لمدة {d} يوماً",
           "inv_desc": "أسئلة عن الإسلام لمساعد الذكاء الاصطناعي في بوت مواقيت",
           "paid_ok": "✅ تم الدفع! أضيف: {what}. شكراً 🤍",
           "don_btn": "⭐ ادعم المشروع",
           "don_title": "🤍 <b>ادعم المشروع</b>\n\nمواقيت مجاني. إن أردت دعم عمله فستكون صدقة جارية. جزاك الله خيراً 🤍",
           "don_custom": "✏️ مبلغ آخر", "don_card": "💳 إلى بطاقة",
           "don_custom_ask": "اكتب عدد ⭐ التي تريد إرسالها (من 1 إلى 100000):", "don_bad": "أرسل رقماً من 1 إلى 100000.",
           "don_inv_title": "دعم مواقيت", "don_inv_desc": "تبرع طوعي لعمل البوت",
           "don_thanks": "🤍 شكراً لدعمك! جزاك الله خيراً.",
           "don_cards_title": "💳 <b>تحويل إلى بطاقة</b>\n\nاضغط على الرقم لنسخه:", "don_owner": "👤 صاحب البطاقة: {name}",
           "don_sent": "✅ أرسلت", "don_sent_ok": "🤍 شكراً! جزاك الله خيراً.",
           "ai_granted": "🎁 أضيف لك {n} سؤالاً لمساعد الذكاء الاصطناعي. بالتوفيق 🤍"},
}
for _l, _d in EXTRA10.items():
    T[_l].update(_d)

EXTRA12 = {
    "en": {"fr_as_photo": "🖼 Send as a photo", "fr_as_video": "🎬 Send as a video", "fr_btn": "🤝 Share with friends", "fr_send": "📤 Send to a friend", "fr_how": "↪️ How to forward",
           "fr_tip": "Tap the ↪️ arrow next to the card (or hold the card → Forward). You can pick several chats at once 🤍",
           "fr_cap": "\"Whoever guides someone to goodness will have a reward like the one who does it\" (Muslim) 🤍\nNever miss a prayer with {bot}"},
    "ru": {"fr_as_photo": "🖼 Прислать как фото", "fr_as_video": "🎬 Прислать как видео", "fr_btn": "🤝 Поделиться с друзьями", "fr_send": "📤 Отправить другу", "fr_how": "↪️ Как переслать",
           "fr_tip": "Нажмите стрелку ↪️ справа от карточки (или зажмите карточку → «Переслать»). Можно выбрать сразу несколько чатов 🤍",
           "fr_cap": "«Кто укажет на благое, тому награда, как и совершившему его» (Муслим) 🤍\nНе пропускай намаз вместе с {bot}"},
    "uz": {"fr_as_photo": "🖼 Rasm qilib yuborish", "fr_as_video": "🎬 Video qilib yuborish", "fr_btn": "🤝 Do‘stlarga ulashish", "fr_send": "📤 Do‘stga yuborish", "fr_how": "↪️ Qanday uzatiladi",
           "fr_tip": "Kartochka yonidagi ↪️ strelkani bosing (yoki kartochkani bosib turing → «Uzatish»). Bir nechta chatni birdan tanlash mumkin 🤍",
           "fr_cap": "«Kim yaxshilikka yo‘l ko‘rsatsa, unga uni qilgan kishining savobicha savob bor» (Muslim) 🤍\n{bot} bilan namozni qoldirmang"},
    "tg": {"fr_as_photo": "🖼 Ҳамчун расм", "fr_as_video": "🎬 Ҳамчун видео", "fr_btn": "🤝 Ба дӯстон фиристодан", "fr_send": "📤 Ба дӯст фиристодан", "fr_how": "↪️ Чӣ тавр фиристодан",
           "fr_tip": "Тирчаи ↪️-ро дар паҳлӯи корт пахш кунед (ё кортро пахш карда нигоҳ доред → «Фиристодан»). Якбора якчанд чатро интихоб кардан мумкин 🤍",
           "fr_cap": "«Ҳар кӣ ба некӣ роҳнамоӣ кунад, барояш мисли подоши иҷрокунандаи он аст» (Муслим) 🤍\nБо {bot} намозро аз даст надиҳед"},
    "ar": {"fr_as_photo": "🖼 أرسلها كصورة", "fr_as_video": "🎬 أرسلها كفيديو", "fr_btn": "🤝 شارك مع الأصدقاء", "fr_send": "📤 أرسل إلى صديق", "fr_how": "↪️ كيف أعيد التوجيه",
           "fr_tip": "اضغط على السهم ↪️ بجانب البطاقة (أو اضغط مطولاً على البطاقة ← «إعادة توجيه»). يمكنك اختيار عدة محادثات معاً 🤍",
           "fr_cap": "«مَن دَلَّ على خيرٍ فله مثلُ أجرِ فاعلِه» (رواه مسلم) 🤍\nلا تفوّت صلاتك مع {bot}"},
}
for _l, _d in EXTRA12.items():
    T[_l].update(_d)

EXTRA11 = {
    "en": {"ayah_btn": "📖 Ayah of the day", "ayah_title": "Ayah of the day", "ayah_hdr": "AYAH OF THE DAY", "quran": "Qur'an",
           "pic_btn": "🖼 Share as a picture", "pic_bg": "🎨 Background {i}/{n}", "pic_done": "✅ Done",
           "pic_tip": "Now tap the picture → Forward. You can pick several chats at once ✨",
           "st_ayah": "📖 Ayah of the day at 9:00: {v}", "sb_ayah_on": "📖 Ayah at 9:00: ON", "sb_ayah_off": "📖 Ayah at 9:00: OFF",
           "ayah_err": "😔 Couldn't load the ayah right now. Please try a little later."},
    "ru": {"ayah_btn": "📖 Аят дня", "ayah_title": "Аят дня", "ayah_hdr": "АЯТ ДНЯ", "quran": "Коран",
           "pic_btn": "🖼 Поделиться картинкой", "pic_bg": "🎨 Фон {i}/{n}", "pic_done": "✅ Готово",
           "pic_tip": "Теперь нажмите на картинку → «Переслать». Можно выбрать сразу несколько чатов ✨",
           "st_ayah": "📖 Аят дня в 9:00: {v}", "sb_ayah_on": "📖 Аят в 9:00: ВКЛ", "sb_ayah_off": "📖 Аят в 9:00: ВЫКЛ",
           "ayah_err": "😔 Сейчас не получилось загрузить аят. Попробуйте чуть позже."},
    "uz": {"ayah_btn": "📖 Kun oyati", "ayah_title": "Kun oyati", "ayah_hdr": "KUN OYATI", "quran": "Qur'on",
           "pic_btn": "🖼 Rasm qilib ulashish", "pic_bg": "🎨 Fon {i}/{n}", "pic_done": "✅ Tayyor",
           "pic_tip": "Endi rasmni bosing → «Uzatish». Bir nechta chatni birdan tanlash mumkin ✨",
           "st_ayah": "📖 Kun oyati soat 9:00 da: {v}", "sb_ayah_on": "📖 Oyat 9:00 da: YOQILGAN", "sb_ayah_off": "📖 Oyat 9:00 da: O'CHIQ",
           "ayah_err": "😔 Hozir oyatni yuklab bo'lmadi. Birozdan so'ng urinib ko'ring."},
    "tg": {"ayah_btn": "📖 Ояти рӯз", "ayah_title": "Ояти рӯз", "ayah_hdr": "ОЯТИ РӮЗ", "quran": "Қуръон",
           "pic_btn": "🖼 Ҳамчун расм фиристодан", "pic_bg": "🎨 Замина {i}/{n}", "pic_done": "✅ Тайёр",
           "pic_tip": "Акнун расмро пахш кунед → «Фиристодан». Якбора якчанд чатро интихоб кардан мумкин ✨",
           "st_ayah": "📖 Ояти рӯз соати 9:00: {v}", "sb_ayah_on": "📖 Оят соати 9:00: ФАЪОЛ", "sb_ayah_off": "📖 Оят соати 9:00: ХОМӮШ",
           "ayah_err": "😔 Ҳоло оятро бор карда нашуд. Каме баъдтар кӯшиш кунед."},
    "ar": {"ayah_btn": "📖 آية اليوم", "ayah_title": "آية اليوم", "ayah_hdr": "آية اليوم", "quran": "القرآن الكريم",
           "pic_btn": "🖼 مشاركة كصورة", "pic_bg": "🎨 الخلفية {i}/{n}", "pic_done": "✅ تم",
           "pic_tip": "الآن اضغط على الصورة ← «إعادة توجيه». يمكنك اختيار عدة محادثات معاً ✨",
           "st_ayah": "📖 آية اليوم الساعة 9:00: {v}", "sb_ayah_on": "📖 الآية 9:00: مفعّلة", "sb_ayah_off": "📖 الآية 9:00: متوقفة",
           "ayah_err": "😔 تعذر تحميل الآية الآن. حاول بعد قليل."},
}
for _l, _d in EXTRA11.items():
    T[_l].update(_d)

# ───────────────────────── Uzbek in Cyrillic ─────────────────────────
# The Cyrillic Uzbek texts are produced from the Latin ones by the official spelling rules,
# so both stay in sync. Words that the rules can't get right are listed in CYR_WORDS.

_APOS = "'ʻʼ’‘`"
_CYR_1 = {"a": "а", "b": "б", "c": "ц", "d": "д", "e": "е", "f": "ф", "g": "г", "h": "ҳ", "i": "и", "j": "ж", "k": "к",
          "l": "л", "m": "м", "n": "н", "o": "о", "p": "п", "q": "қ", "r": "р", "s": "с", "t": "т", "u": "у", "v": "в",
          "w": "в", "x": "х", "y": "й", "z": "з"}
_CYR_VOW = set("aeiouAEIOU")
CYR_WORDS = {  # Latin word (lower case) → Cyrillic
    "sentabr": "сентябр", "oktabr": "октябр", "iyun": "июн", "iyul": "июл", "yanvar": "январ",
    "mawaqit": "Mawaqit", "telegram": "Telegram", "mawaqittimebot": "MawaqitTimeBot",
    "fevral": "феврал", "dekabr": "декабр", "noyabr": "ноябр", "avgust": "август",
}
_CYR_KEEP = re.compile(r"(\{[^}]*\}|<b>N</b>|<[^>]+>|https?://\S+|@\w+|&\w+;)")
_CYR_WORD = re.compile(r"[A-Za-z" + _APOS + r"]+")


def _cyr_word(w):
    low = w.lower().strip(_APOS)
    for k, v in CYR_WORDS.items():  # "Mawaqit'dagi" → "Mawaqit’даги"
        if low.startswith(k) and len(low) > len(k) and low[len(k)] in _APOS:
            return v + "’" + _cyr_word(w[len(k) + 1:])
    if low in CYR_WORDS:
        out = CYR_WORDS[low]
        if w[:1].isupper() and out[:1].islower():
            out = out[:1].upper() + out[1:]
        return out
    res, i, n = [], 0, len(w)
    while i < n:
        c, lc = w[i], w[i].lower()
        nxt = w[i + 1].lower() if i + 1 < n else ""
        up = c.isupper()
        if c in _APOS:  # tutuq belgisi
            res.append("ъ" if res and res[-1] not in "ъ" and i > 0 else "")
            i += 1
            continue
        if lc in "og" and nxt and nxt in _APOS:
            ch = "ў" if lc == "o" else "ғ"
            i += 2
        elif lc == "s" and nxt == "h":
            ch, i = "ш", i + 2
        elif lc == "c" and nxt == "h":
            ch, i = "ч", i + 2
        elif lc == "y" and nxt in ("o", "u", "a", "e") and not (nxt == "o" and i + 2 < n and w[i + 2] in _APOS):
            ch, i = {"o": "ё", "u": "ю", "a": "я", "e": "е"}[nxt], i + 2
        elif lc == "e":
            ch = "э" if i == 0 or w[i - 1] in _CYR_VOW else "е"
            i += 1
        elif lc in _CYR_1:
            ch = _CYR_1[lc]
            i += 1
        else:
            ch, i = c, i + 1
        if up:
            # SH, CH, YO… in an all-caps word stay all caps
            ch = ch.upper()
        res.append(ch)
    out = "".join(res)
    if len(w) > 1 and w.isupper():
        return out.upper()
    if w[:1].isupper():
        return out[:1].upper() + out[1:].lower() if not any(x.isupper() for x in w[1:]) else out
    return out


def to_cyr(text):
    """Latin Uzbek → Cyrillic Uzbek. Placeholders, HTML tags, links and @names are left alone."""
    if not isinstance(text, str):
        if isinstance(text, list):
            return [to_cyr(x) for x in text]
        if isinstance(text, dict):
            return {k: to_cyr(v) for k, v in text.items()}
        return text
    parts = _CYR_KEEP.split(text)
    return "".join(p if i % 2 else _CYR_WORD.sub(lambda m: _cyr_word(m.group(0)), p) for i, p in enumerate(parts))


T["uzc"] = to_cyr(T["uz"])
PN["uzc"] = to_cyr(PN["uz"])
HM["uzc"] = to_cyr(HM["uz"])

GROUP_WELCOME = ("🕌 <b>Assalamu alaikum!</b>\n\n"
                 "I'll post prayer times and reminders here. Group admins, please set me up 👇\n\n" + LANG_PICK_TEXT)


def t(lang, key, **kw):
    s = T.get(lang, EN).get(key) or EN[key]
    return s.format(**kw) if kw else s


def esc(s):
    return html.escape(str(s))


def lead_label(lang, n):
    return t(lang, "lead_none") if n == 0 else t(lang, "lead_n", n=n)


def reminder_phrase(lang, u):
    n, at = u["lead_min"], u["at_time"]
    if n and at:
        return t(lang, "phrase_both", n=n)
    if n:
        return t(lang, "phrase_n", n=n)
    return t(lang, "phrase_0") if at else t(lang, "phrase_off")


def quiet_label(lang, qs, qe):
    return t(lang, "quiet_off") if qs is None else f"{qs:02d}:00–{qe:02d}:00"


def fmt_left(lang, minutes):
    h, m = divmod(minutes, 60)
    return t(lang, "left_hm", h=h, m=m) if h else t(lang, "left_m", m=m)


# ───────────────────────── database ─────────────────────────

SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    user_id       BIGINT PRIMARY KEY,
    lang          TEXT,
    madhab        TEXT,
    city          TEXT,
    lat           DOUBLE PRECISION,
    lon           DOUBLE PRECISION,
    tz            TEXT,
    country       TEXT,
    remind        BOOLEAN NOT NULL DEFAULT FALSE,
    lead_min      INT NOT NULL DEFAULT 10,
    quiet_start   INT,
    quiet_end     INT,
    ramadan       BOOLEAN NOT NULL DEFAULT TRUE,
    onboarded     BOOLEAN NOT NULL DEFAULT FALSE,
    awaiting_city BOOLEAN NOT NULL DEFAULT FALSE,
    created_at    TIMESTAMPTZ NOT NULL DEFAULT now()
);
ALTER TABLE users ADD COLUMN IF NOT EXISTS banned    BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS blocked   BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS last_seen TIMESTAMPTZ;
ALTER TABLE users ADD COLUMN IF NOT EXISTS chat_type TEXT NOT NULL DEFAULT 'private';
ALTER TABLE users ADD COLUMN IF NOT EXISTS title     TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS owner_id  BIGINT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS members   INT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS daily     TEXT NOT NULL DEFAULT 'off';
ALTER TABLE users ADD COLUMN IF NOT EXISTS at_time   BOOLEAN NOT NULL DEFAULT TRUE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS auto_mode INT NOT NULL DEFAULT 5;
ALTER TABLE users ADD COLUMN IF NOT EXISTS full_name TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS username  TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS azkar_rem BOOLEAN NOT NULL DEFAULT TRUE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS weekly    BOOLEAN NOT NULL DEFAULT TRUE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS last_weekly DATE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS last_summary DATE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS referred_by BIGINT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS azan TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS last_screen_msg BIGINT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS rem_msgs BIGINT[];
ALTER TABLE users ADD COLUMN IF NOT EXISTS fast_show BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS tour_sent BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS menu_btn TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS suhoor_rem INT NOT NULL DEFAULT -1;
ALTER TABLE users ADD COLUMN IF NOT EXISTS iftar_rem INT NOT NULL DEFAULT -1;
ALTER TABLE users ADD COLUMN IF NOT EXISTS fast_sound BOOLEAN NOT NULL DEFAULT TRUE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS prayer_modes TEXT NOT NULL DEFAULT 'sssss';
CREATE TABLE IF NOT EXISTS admins (
    user_id  BIGINT PRIMARY KEY,
    perms    TEXT[] NOT NULL DEFAULT '{}',
    added_by BIGINT,
    added_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS mosques (
    osm_id     TEXT PRIMARY KEY,
    lat        DOUBLE PRECISION NOT NULL,
    lon        DOUBLE PRECISION NOT NULL,
    name       TEXT,
    names      TEXT,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX IF NOT EXISTS mosques_geo ON mosques (lat, lon);
CREATE TABLE IF NOT EXISTS kv (
    key   TEXT PRIMARY KEY,
    value TEXT
);
CREATE TABLE IF NOT EXISTS ai_usage (
    user_id BIGINT NOT NULL,
    day     DATE NOT NULL,
    n       INT NOT NULL DEFAULT 0,
    PRIMARY KEY (user_id, day)
);
ALTER TABLE users ADD COLUMN IF NOT EXISTS hidden BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS ayah_rem BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS last_ayah DATE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS share_bg INT NOT NULL DEFAULT 0;
ALTER TABLE users ADD COLUMN IF NOT EXISTS share_font INT NOT NULL DEFAULT 0;
CREATE TABLE IF NOT EXISTS ayah_cache (ref TEXT PRIMARY KEY, data JSONB NOT NULL);
CREATE TABLE IF NOT EXISTS broadcasts (id SERIAL PRIMARY KEY, admin_id BIGINT, audience TEXT, label TEXT, src_chat BIGINT,
    src_msg BIGINT, opts TEXT, status TEXT, run_at TIMESTAMPTZ, created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    started_at TIMESTAMPTZ, finished_at TIMESTAMPTZ, total INT, sent INT, failed INT, blocked INT);
CREATE TABLE IF NOT EXISTS sent_msgs (id SERIAL PRIMARY KEY, bc_id INT, user_id BIGINT NOT NULL, message_id BIGINT NOT NULL,
    kind TEXT, preview TEXT, deleted BOOLEAN NOT NULL DEFAULT FALSE, at TIMESTAMPTZ NOT NULL DEFAULT now());
CREATE INDEX IF NOT EXISTS sent_msgs_user ON sent_msgs (user_id, id);
CREATE INDEX IF NOT EXISTS sent_msgs_bc ON sent_msgs (bc_id);
CREATE TABLE IF NOT EXISTS share_pics (id TEXT PRIMARY KEY, file_id TEXT NOT NULL, at TIMESTAMPTZ NOT NULL DEFAULT now());
CREATE TABLE IF NOT EXISTS ayah_pool (ref TEXT PRIMARY KEY, source TEXT NOT NULL DEFAULT 'base',
                                      removed BOOLEAN NOT NULL DEFAULT FALSE, added_at TIMESTAMPTZ NOT NULL DEFAULT now());
CREATE TABLE IF NOT EXISTS ayah_seen (user_id BIGINT NOT NULL, ref TEXT NOT NULL, PRIMARY KEY (user_id, ref));
ALTER TABLE users ADD COLUMN IF NOT EXISTS ayah_day DATE;
ALTER TABLE users ADD COLUMN IF NOT EXISTS ayah_ref TEXT;
CREATE TABLE IF NOT EXISTS ai_credits (
    user_id         BIGINT PRIMARY KEY,
    credits         INT NOT NULL DEFAULT 0,
    unlimited_until TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS payments (
    id        SERIAL PRIMARY KEY,
    user_id   BIGINT NOT NULL,
    kind      TEXT NOT NULL,
    payload   TEXT,
    stars     INT NOT NULL,
    charge_id TEXT,
    refunded  BOOLEAN NOT NULL DEFAULT FALSE,
    at        TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS ai_log (
    id       SERIAL PRIMARY KEY,
    user_id  BIGINT NOT NULL,
    question TEXT,
    answer   TEXT,
    model    TEXT,
    at       TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX IF NOT EXISTS ai_log_user ON ai_log (user_id, id);
CREATE TABLE IF NOT EXISTS msg_cleanup (
    chat_id BIGINT NOT NULL,
    msg_id  BIGINT NOT NULL,
    at      TIMESTAMPTZ NOT NULL,
    PRIMARY KEY (chat_id, msg_id)
);
CREATE INDEX IF NOT EXISTS msg_cleanup_at ON msg_cleanup (at);
CREATE INDEX IF NOT EXISTS users_referred_by ON users (referred_by);
CREATE TABLE IF NOT EXISTS nv_months (
    slug       TEXT NOT NULL,
    y          INT NOT NULL,
    m          INT NOT NULL,
    data       TEXT NOT NULL,
    fetched_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (slug, y, m)
);
CREATE TABLE IF NOT EXISTS badges (
    user_id BIGINT NOT NULL,
    code    TEXT NOT NULL,
    at      TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (user_id, code)
);
CREATE TABLE IF NOT EXISTS azans (
    id         SERIAL PRIMARY KEY,
    name       TEXT NOT NULL,
    file_id    TEXT NOT NULL,
    kind       TEXT NOT NULL DEFAULT 'audio',
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS tracker (
    user_id BIGINT NOT NULL,
    day     DATE NOT NULL,
    mask    TEXT NOT NULL,
    PRIMARY KEY (user_id, day)
);
CREATE INDEX IF NOT EXISTS tracker_day ON tracker (day);
CREATE TABLE IF NOT EXISTS challenges (
    id         SERIAL PRIMARY KEY,
    code       TEXT UNIQUE NOT NULL,
    owner      BIGINT NOT NULL,
    title      TEXT NOT NULL,
    days       INT NOT NULL,
    start_day  DATE NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS challenge_members (
    challenge_id INT NOT NULL REFERENCES challenges (id) ON DELETE CASCADE,
    user_id      BIGINT NOT NULL,
    joined_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (challenge_id, user_id)
);
CREATE TABLE IF NOT EXISTS daily_active (
    day     DATE NOT NULL,
    user_id BIGINT NOT NULL,
    PRIMARY KEY (day, user_id)
);
CREATE TABLE IF NOT EXISTS times_cards (
    chat_id   BIGINT PRIMARY KEY,
    msg_id    BIGINT NOT NULL,
    data_id   BIGINT NOT NULL,
    sent_at   TIMESTAMPTZ NOT NULL DEFAULT now(),
    edited_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS daily_stats (
    stat_day   DATE NOT NULL,
    stat_key   TEXT NOT NULL,
    stat_value INT NOT NULL DEFAULT 0,
    PRIMARY KEY (stat_day, stat_key)
);
"""


async def get_user(uid):
    row = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    return dict(row) if row else None


async def ensure_user(uid):
    await POOL.execute("INSERT INTO users (user_id, last_seen) VALUES ($1, now()) ON CONFLICT DO NOTHING", uid)
    return await get_user(uid)


async def save(uid, **fields):
    """Update columns of a user (column names come from code, never from user input)."""
    cols = list(fields)
    sets = ", ".join(f"{c} = ${i + 2}" for i, c in enumerate(cols))
    await POOL.execute(f"UPDATE users SET {sets} WHERE user_id = $1", uid, *[fields[c] for c in cols])


# ───────────────────────── external APIs ─────────────────────────

CACHE = {}
SEM = asyncio.Semaphore(6)
NOMI_LOCK = asyncio.Lock()
_nomi_last = 0.0


async def fetch_timings(lat, lon, d, method, school):
    url = f"https://api.aladhan.com/v1/timings/{d.strftime('%d-%m-%Y')}"
    params = {"latitude": lat, "longitude": lon, **method_params(method), "school": school}
    last_exc = None
    for attempt in range(2):
        try:
            r = await HTTP.get(url, params=params)
            r.raise_for_status()
            j = r.json()["data"]
            tm, h = j["timings"], j["date"]["hijri"]
            out = {k: tm[k].split()[0] for k in ("Fajr", "Sunrise", "Dhuhr", "Asr", "Maghrib", "Isha")}
            out.update(hday=int(h["day"]), hmonth=int(h["month"]["number"]), hyear=int(h["year"]),
                       tz=j["meta"]["timezone"])
            return out
        except Exception as e:  # noqa: BLE001
            last_exc = e
            await asyncio.sleep(1)
    raise last_exc


async def get_timings(u, d):
    method = method_for(u["country"])
    school = 1 if u["madhab"] == "hanafi" else 0
    key = (round(u["lat"], 2), round(u["lon"], 2), method, school, d)
    if key in CACHE:
        return await local_times(u, d, CACHE[key])
    async with SEM:
        if key not in CACHE:
            CACHE[key] = await fetch_timings(u["lat"], u["lon"], d, method, school)
    return await local_times(u, d, CACHE[key])


async def nominatim(endpoint, params):
    """OpenStreetMap geocoder. Policy: max 1 request/second + identifying User-Agent."""
    global _nomi_last
    async with NOMI_LOCK:
        wait = 1.1 - (_time.monotonic() - _nomi_last)
        if wait > 0:
            await asyncio.sleep(wait)
        try:
            r = await HTTP.get(
                f"https://nominatim.openstreetmap.org/{endpoint}",
                params={**params, "format": "jsonv2", "addressdetails": 1},
                headers={"User-Agent": f"PrayerTimesTelegramBot/1.0 ({CONTACT})"},
            )
            r.raise_for_status()
            return r.json()
        finally:
            _nomi_last = _time.monotonic()


def place_name(addr):
    city = next((addr[k] for k in ("city", "town", "village", "municipality", "county",
                                   "state_district", "state") if addr.get(k)), None)
    country = addr.get("country")
    if city and country and city != country:
        return f"{city}, {country}"
    return city or country


async def relocalize_city(uid, lang, force_country=False):
    """After a language change: the city and country names in the new language (by the saved coordinates)."""
    u = await get_user(uid)
    if not u or u["lat"] is None or u["lon"] is None:
        return
    try:
        name, cc = await reverse_geocode(u["lat"], u["lon"], lang)
    except Exception:  # noqa: BLE001
        return
    if name and not COORDS_RE.match(name):
        await save(uid, city=name, **({"country": cc} if cc and (force_country or not u["country"]) else {}))


async def geocode(query, lang):
    data = await nominatim("search", {"q": query, "limit": 1, "accept-language": "uz" if lang == "uzc" else lang})
    if not data:
        return None
    d = data[0]
    addr = d.get("address", {})
    name = place_name(addr) or d.get("display_name", query).split(",")[0]
    if lang == "uzc":
        name = to_cyr(name)
    return name, float(d["lat"]), float(d["lon"]), addr.get("country_code", "")


COORDS_RE = re.compile(r"^-?\d+\.\d+, -?\d+\.\d+$")


async def reverse_geocode(lat, lon, lang):
    """City and country for a point: OpenStreetMap's Nominatim (2 tries), then Photon (also OpenStreetMap).
    Only if both fail, the coordinates are returned (and fixed later in the background)."""
    al = "uz" if lang == "uzc" else lang
    fix = (lambda x: to_cyr(x)) if lang == "uzc" else (lambda x: x)
    for attempt in range(2):
        try:
            d = await nominatim("reverse", {"lat": lat, "lon": lon, "zoom": 10, "accept-language": al})
            addr = d.get("address", {})
            name = place_name(addr)
            if name:
                return fix(name), addr.get("country_code", "")
            break
        except Exception as e:  # noqa: BLE001
            log.warning("reverse geocode (nominatim, try %d) failed: %r", attempt + 1, e)
    try:
        r = await HTTP.get("https://photon.komoot.io/reverse", timeout=12,
                           params={"lat": lat, "lon": lon, "limit": 1, **({"lang": al} if al in ("en", "de", "fr") else {})},
                           headers={"User-Agent": f"PrayerTimesTelegramBot/1.0 ({CONTACT})"})
        r.raise_for_status()
        f = (r.json().get("features") or [{}])[0].get("properties") or {}
        city = f.get("city") or f.get("town") or f.get("village") or f.get("county") or f.get("state") or f.get("name")
        country = f.get("country")
        name = f"{city}, {country}" if city and country and city != country else (city or country)
        if name:
            return fix(name), (f.get("countrycode") or "").lower()
    except Exception as e:  # noqa: BLE001
        log.warning("reverse geocode (photon) failed: %r", e)
    return f"{lat:.2f}, {lon:.2f}", ""


def qibla_bearing(lat, lon):
    p1, p2 = math.radians(lat), math.radians(KAABA[0])
    dl = math.radians(KAABA[1] - lon)
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return (math.degrees(math.atan2(y, x)) + 360) % 360


# ───────────────────────── UI helpers ─────────────────────────

BOT_USERNAME = ""  # filled in post_init


def btn(text, data):
    return InlineKeyboardButton(text, callback_data=data)


def kb(*rows):
    return InlineKeyboardMarkup([list(r) for r in rows])


def kind(u):
    return (u or {}).get("chat_type") or "private"


def is_private(u):
    return kind(u) == "private"


async def render(update: Update, text, markup=None, track=True):
    """Edit the message in place for button presses, send a new one otherwise.
    In private chats only one menu/screen message is kept: showing a new one deletes the previous one."""
    q = update.callback_query
    m = None
    if q:
        try:
            await q.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
            m = q.message
        except BadRequest as e:
            if "not modified" in str(e).lower():
                m = q.message
            else:
                log.warning("edit failed (%s), sending new message", e)
        if m is None:
            m = await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    else:
        m = await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    if track and m is not None and update.effective_chat and update.effective_chat.type == "private":
        await swap_screen(update.get_bot(), update.effective_chat.id, m.message_id)
    return m


async def swap_screen(bot, chat_id, msg_id):
    """Remember msg_id as the chat's menu/screen message and delete the previous one."""
    try:
        old = await POOL.fetchval(
            "UPDATE users u SET last_screen_msg = $2 FROM (SELECT last_screen_msg AS old FROM users WHERE user_id = $1) o "
            "WHERE u.user_id = $1 RETURNING o.old", chat_id, msg_id)
        if old and old != msg_id:
            card = await POOL.fetchval("SELECT msg_id FROM times_cards WHERE chat_id = $1", chat_id)
            if old != card:
                await bot.delete_message(chat_id, old)
    except Exception:  # noqa: BLE001  (older than 48 h or already gone)
        pass


async def ensure_chat(chat, ctype, owner_id=None):
    """Create/refresh the record of a group or channel (stored in the same table, id = chat id)."""
    await POOL.execute(
        "INSERT INTO users (user_id, chat_type, title, owner_id, last_seen) VALUES ($1, $2, $3, $4, now()) "
        "ON CONFLICT (user_id) DO UPDATE SET title = EXCLUDED.title, chat_type = EXCLUDED.chat_type, "
        "blocked = FALSE, owner_id = COALESCE(EXCLUDED.owner_id, users.owner_id)",
        chat.id, ctype, chat.title, owner_id)
    return await get_user(chat.id)


async def target_for(update: Update, ctx):
    """Whose settings are we looking at? The user, a group, or a channel the user manages in private."""
    chat = update.effective_chat
    if chat.type == "private":
        tid = ctx.user_data.get("target")
        if tid:
            c = await get_user(tid)
            if c and c["chat_type"] == "channel" and c["owner_id"] == update.effective_user.id and not c["blocked"]:
                return c
            ctx.user_data.pop("target", None)
        return await ensure_user(update.effective_user.id)
    return await ensure_chat(chat, "group")


async def can_manage(update: Update, ctx):
    """In groups only admins may change settings. Results are cached for 2 minutes."""
    chat = update.effective_chat
    if chat.type == "private":
        return True
    msg = update.message
    if msg and msg.sender_chat and msg.sender_chat.id == chat.id:  # anonymous group admin
        return True
    user = update.effective_user
    cache = ctx.chat_data.setdefault("admins", {})
    hit = cache.get(user.id)
    if hit and _time.time() - hit[1] < 120:
        return hit[0]
    try:
        m = await ctx.bot.get_chat_member(chat.id, user.id)
        ok = m.status in ("administrator", "creator")
    except Exception:  # noqa: BLE001
        ok = False
    cache[user.id] = (ok, _time.time())
    return ok


# ───────────────────────── screens ─────────────────────────

def screen_lang(back=False):
    rows = [[btn(LANG_BUTTONS["en"], "lang:en"), btn(LANG_BUTTONS["ru"], "lang:ru")],
            [btn("🇺🇿 Oʻzbekcha / Ўзбекча", "lang:uzpick:" + ("1" if back else "0"))],
            [btn(LANG_BUTTONS["tg"], "lang:tg"), btn(LANG_BUTTONS["ar"], "lang:ar")]]
    if back:
        rows.append([btn("⬅️", "s:settings")])
    return LANG_PICK_TEXT, kb(*rows)


def screen_uz_script(back):
    """Uzbek is written in Latin and in Cyrillic: the second step of the language choice."""
    return ("🇺🇿 <b>Alifboni tanlang · Алифбони танланг</b>",
            kb([btn("🔤 Lotin — Oʻzbekcha", "lang:uz")], [btn("🔤 Кирилл — Ўзбекча", "lang:uzc")],
               [btn("⬅️ Orqaga · Орқага", "lang:all:" + ("1" if back else "0"))]))


def screen_madhab(u):
    lang = u["lang"]
    cur = u["madhab"]
    rows = [[btn(("✅ " if cur == "std" else "") + t(lang, "madhab_std"), "set:madhab:std")],
            [btn(("✅ " if cur == "hanafi" else "") + t(lang, "madhab_hanafi"), "set:madhab:hanafi")]]
    if u["onboarded"]:
        rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "ask_madhab"), kb(*rows)


def screen_city(u):
    lang = u["lang"]
    markup = kb([btn(t(lang, "btn_back"), "s:settings")]) if u["onboarded"] else None
    return t(lang, "ask_city"), markup


async def show_city_prompt(update, ctx, u):
    lang = u["lang"]
    await save(u["user_id"], awaiting_city=True)
    if kind(u) == "group":
        # In groups bots only see replies to their own messages, so we ask for a reply.
        q = update.callback_query
        if q:
            try:
                await q.message.delete()
            except Exception:  # noqa: BLE001
                pass
        m = await update.effective_chat.send_message(
            t(lang, "group_ask_city"), parse_mode=ParseMode.HTML,
            reply_markup=ForceReply(input_field_placeholder=t(lang, "city_ph")))
        await remember_prompt(update, ctx, m)
        return
    # One message: the question with the location button (and "Back" for those who already have a city)
    # under the input field. A reply keyboard can't sit on an edited message, so a new one is sent.
    text, _ = screen_city(u)
    rows = [[KeyboardButton(t(lang, "loc_btn"), request_location=True)]]
    if u["onboarded"]:
        rows.append([KeyboardButton(t(lang, "btn_back"))])
    q = update.callback_query
    if q and q.message:
        try:
            await q.message.delete()
        except Exception:  # noqa: BLE001
            pass
    old_helper = ctx.user_data.pop("loc_msg", None)
    if old_helper:
        await drop_message(update, old_helper)
    m = await update.effective_chat.send_message(
        text, parse_mode=ParseMode.HTML,
        reply_markup=ReplyKeyboardMarkup(rows, resize_keyboard=True, one_time_keyboard=True,
                                         input_field_placeholder=t(lang, "city_ph")))
    await remember_prompt(update, ctx, m)
    ctx.user_data["loc_msg"] = m.message_id


async def remember_prompt(update, ctx, msg):
    """Keep the id of the city question so it can be removed once the city is set."""
    old = ctx.chat_data.get("city_prompt")
    if old and msg is not None and old != msg.message_id:
        await drop_message(update, old)
    if msg is not None:
        ctx.chat_data["city_prompt"] = msg.message_id


async def drop_message(update, mid):
    try:
        await update.effective_chat.delete_message(mid)
    except Exception:  # noqa: BLE001
        pass


async def cleanup_city_prompt(update, ctx):
    mid = ctx.chat_data.pop("city_prompt", None)
    q = update.callback_query
    if mid and not (q and q.message and q.message.message_id == mid):  # never delete the message we edit next
        await drop_message(update, mid)


async def cleanup_loc_kb(update, ctx):
    if update.effective_chat.type != "private":
        return
    mid = ctx.user_data.pop("loc_msg", None)
    if not mid:
        return
    chat = update.effective_chat
    try:
        await chat.delete_message(mid)
    except Exception:  # noqa: BLE001
        pass
    try:  # sending + deleting a message is the way to remove a reply keyboard
        m = await chat.send_message("✅", reply_markup=ReplyKeyboardRemove())
        await m.delete()
    except Exception:  # noqa: BLE001
        pass


def add_group_btn(lang):
    return InlineKeyboardButton(t(lang, "btn_add_group"), url=f"https://t.me/{BOT_USERNAME}?startgroup=start")


def add_channel_btn(lang):
    return InlineKeyboardButton(t(lang, "btn_add_channel"),
                                url=f"https://t.me/{BOT_USERNAME}?startchannel&admin=post_messages")


def qibla_btn(u):
    lang = u["lang"]
    if is_private(u) and WEBAPP_URL:
        return webapp_btn(t(lang, "btn_qibla"), "qibla")  # live compass
    return btn(t(lang, "btn_qibla"), "m:qibla")  # compass picture


def screen_menu(u):
    lang = u["lang"]
    rows = [
        [InlineKeyboardButton(t(lang, "btn_times"), callback_data="m:times", style="success")],
        [qibla_btn(u), btn(t(lang, "btn_rem_s_on" if u["remind"] else "btn_rem_s_off"), "m:toggle")],
        [btn(t(lang, "btn_settings"), "m:settings")],
    ]
    if is_private(u) and WEBAPP_URL:  # quick ways into the app: ayah, qibla
        rows[1:2] = [[btn(t(lang, "ayah_btn"), "ay:show"), qibla_btn(u)],
                     [btn(t(lang, "btn_rem_s_on" if u["remind"] else "btn_rem_s_off"), "m:toggle"),
                      btn(t(lang, "btn_settings"), "m:settings")]]
        rows = rows[:3]
    if kind(u) == "channel":
        rows.append([btn(t(lang, "btn_my_channels"), "ch:list"), btn(t(lang, "btn_my_menu"), "ch:exit")])
        return t(lang, "channel_menu_title", title=esc(u["title"] or "—"), city=esc(u["city"] or "—")), kb(*rows)
    if is_private(u):
        rows = private_menu_rows(u)  # the main admin arranges it in the bot settings
        if is_admin(u["user_id"]):
            rows.append([btn("🛠 Админка", "a:home")])
    return t(lang, "menu_title", city=esc(u["city"])), kb(*rows)


def daily_label(lang, v):
    return t(lang, {"fajr": "daily_fajr", "sunrise": "daily_sunrise"}.get(v, "daily_off"))


def screen_settings(u):
    lang = u["lang"]
    madhab = t(lang, "madhab_hanafi" if u["madhab"] == "hanafi" else "madhab_std")
    lines = [t(lang, "settings_title"), "",
             f"📍 {esc(u['city'])}",
             f"🌐 {LANG_BUTTONS[lang]}",
             f"🕌 {madhab}",
             f"⏰ {lead_label(lang, u['lead_min'])}",
             f"🔕 {quiet_label(lang, u['quiet_start'], u['quiet_end'])}",
             t(lang, "st_at", v=t(lang, "on" if u["at_time"] else "off")),
             f"🔄 {auto_label(lang, u['auto_mode'])}",
             t(lang, "st_ram", v=t(lang, "on" if u["ramadan"] else "off"))]
    rows = [
        [btn(t(lang, "btn_city"), "s:city")],
        [btn(t(lang, "btn_lang"), "s:lang"), btn(t(lang, "btn_madhab"), "s:madhab")],
        [btn(t(lang, "sb_lead"), "s:lead"), btn(t(lang, "sb_at_on" if u["at_time"] else "sb_at_off"), "s:attime")],
        [btn(t(lang, "sb_auto"), "s:auto"), btn(t(lang, "btn_quiet"), "s:quiet")],
    ]
    ram = btn(t(lang, "sb_ram_on" if u["ramadan"] else "sb_ram_off"), "s:ramadan")
    if not is_private(u):
        lines.append(f"📅 {daily_label(lang, u['daily'])}")
        rows.append([ram, btn(t(lang, "btn_daily"), "s:daily")])
    else:
        lines.append(t(lang, "st_wk", v=t(lang, "on" if u["weekly"] else "off")))
        lines.append(t(lang, "st_ayah", v=t(lang, "on" if u["ayah_rem"] else "off")))
        rows.append([ram, btn(t(lang, "sb_wk_on" if u["weekly"] else "sb_wk_off"), "s:wk")])
        rows.append([btn(t(lang, "sb_ayah_on" if u["ayah_rem"] else "sb_ayah_off"), "s:ayah")])
        if AZANS:
            lines.append(t(lang, "st_azan", v=esc(azan_label(lang, u))))
            rows.append([btn(t(lang, "sb_azan", v=azan_label(lang, u)), "s:azan")])
        rows.append([btn(t(lang, "btn_fast"), "s:fast"), btn(t(lang, "btn_snd"), "s:snd")])
        if feat("groups"):
            rows.append([btn(t(lang, "btn_groups"), "s:groups")])
        if feat("donate"):
            rows.append([btn(t(lang, "don_btn"), "don:menu")])
        if ADMINS and feat("support"):
            rows.append([btn(t(lang, "btn_support"), "s:support")])
    rows.append([btn(t(lang, "btn_back"), "m:home")])
    return "\n".join(lines), kb(*rows)


def screen_lead(u):
    lang = u["lang"]
    opts = [btn(("✅ " if u["lead_min"] == n else "") + lead_label(lang, n), f"set:lead:{n}") for n in LEAD_OPTIONS]
    rows = [opts[i:i + 2] for i in range(0, len(opts), 2)]
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "lead_title"), kb(*rows)


async def screen_fast(u):
    lang = u["lang"]
    d = await get_timings(u, datetime.now(ZoneInfo(u["tz"])).date())
    def opt(v, cur, cb, label):
        return btn(("✅ " if v == cur else "") + label, cb)
    off = t(lang, "off").capitalize()
    suh = [opt(v, u["suhoor_rem"], f"set:suh:{v}", off if v < 0 else f"{v}′") for v in SUH_OPTS]
    ift = [opt(v, u["iftar_rem"], f"set:ift:{v}", off if v < 0 else (t(lang, "fast_at") if v == 0 else f"{v}′")) for v in IFT_OPTS]
    rows = [[btn(t(lang, "fast_show_on" if u["fast_show"] else "fast_show_off"), "s:fs")],
            [btn(t(lang, "fast_suh"), "s:fast")], suh,
            [btn(t(lang, "fast_ift"), "s:fast")], ift[:3], ift[3:],
            [btn(t(lang, "fast_snd_on" if u["fast_sound"] else "fast_snd_off"), "s:fsnd")],
            [btn(t(lang, "btn_back"), "s:settings")]]
    return t(lang, "fast_title", s=d["Fajr"], i=d["Maghrib"]), kb(*rows)


def screen_sound(u):
    lang = u["lang"]
    modes = (u["prayer_modes"] or "sssss").ljust(5, "s")
    icons = dict(ROWS)
    rows = [[btn(f"{icons[k]} {PN[lang][k.lower()]} — {t(lang, 'mode_' + modes[i])}", f"set:pm:{i}")] for i, k in enumerate(EVENTS)]
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "snd_title"), kb(*rows)


def screen_quiet(u):
    lang = u["lang"]
    cur = (u["quiet_start"], u["quiet_end"])
    rows = [[btn(("✅ " if cur[0] is None else "") + "🔔 " + t(lang, "quiet_off"), "set:quiet:off")]]
    for a, b in QUIET_PRESETS:
        rows.append([btn(("✅ " if cur == (a, b) else "") + f"🔕 {a:02d}:00–{b:02d}:00", f"set:quiet:{a}-{b}")])
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "quiet_title"), kb(*rows)


def screen_daily(u):
    lang = u["lang"]
    rows = [[btn(("✅ " if u["daily"] == v else "") + daily_label(lang, v), f"set:daily:{v}")]
            for v in ("off", "fajr", "sunrise")]
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "daily_title"), kb(*rows)


async def screen_times(u, onboarding=False):
    lang = u["lang"]
    tz = ZoneInfo(u["tz"])
    now = datetime.now(tz)
    today = now.date()
    d = await get_timings(u, today)
    names = PN[lang]
    ram = u["ramadan"] and d["hmonth"] == 9

    lines = [t(lang, "times_title"),
             f"📍 {esc(u['city'])}",
             f"📅 {today.strftime('%d.%m.%Y')}",
             f"🗓 {d['hday']} {HM[lang][d['hmonth'] - 1]} {d['hyear']}"]
    if ram:
        lines.append(t(lang, "ram_banner"))
    lines.append("")
    for key, emoji in ROWS:
        lines.append(f"{emoji} {names[key.lower()]} — <b>{d[key]}</b>")
    if ram or (u.get("fast_show") if hasattr(u, "get") else False):
        lines += ["", f"🥣 {t(lang, 'suhoor')} — <b>{d['Fajr']}</b>", f"🍽 {t(lang, 'iftar')} — <b>{d['Maghrib']}</b>"]

    nxt = None
    for key in EVENTS:
        hh, mm = map(int, d[key].split(":"))
        ev = datetime.combine(today, dtime(hh, mm), tzinfo=tz)
        if ev > now:
            nxt = (key, ev)
            break
    if nxt is None:
        d2 = await get_timings(u, today + timedelta(days=1))
        hh, mm = map(int, d2["Fajr"].split(":"))
        nxt = ("Fajr", datetime.combine(today + timedelta(days=1), dtime(hh, mm), tzinfo=tz))
    minutes = max(1, math.ceil((nxt[1] - now).total_seconds() / 60))
    lines += ["", t(lang, "next_line", name=names[nxt[0].lower()], left=fmt_left(lang, minutes))]

    markup = None if onboarding else kb(
        [qibla_btn(u)],
        [btn(t(lang, "btn_menu"), "m:home")],
    )
    return "\n".join(lines), markup


async def ask_remind(update, u):
    lang = u["lang"]
    await update.effective_chat.send_message(
        t(lang, "ask_remind", phrase=reminder_phrase(lang, u)),
        parse_mode=ParseMode.HTML,
        reply_markup=kb([btn(t(lang, "btn_yes"), "rem:yes")], [btn(t(lang, "btn_no"), "rem:no")]),
    )



# ───────────────────────── live prayer-times card ─────────────────────────
# Opening "prayer times" sends a separate card. The menu stays where it is, the previous card is
# deleted, and the newest card keeps itself up to date (countdown, current prayer, new day).

AUTO_OPTIONS = [0, 1, 5, 15]


def auto_label(lang, n):
    return t(lang, "auto_off") if not n else (t(lang, "auto_1") if n == 1 else t(lang, "auto_n", n=n))


async def card_markup(u):
    lang = u["lang"]
    if is_private(u):
        share = None
        try:
            share = await share_times_btn(u)
        except Exception:  # noqa: BLE001
            log.exception("share button failed")
        rows = ([[share]] if share else []) + [[btn(t(lang, "btn_menu"), "m:new")]]
        return kb(*rows)
    return kb([btn(t(lang, "btn_menu"), "m:new")])


async def card_text(u):
    text, _ = await screen_times(u, onboarding=True)
    if u["auto_mode"]:
        now = datetime.now(ZoneInfo(u["tz"]))
        text += "\n<i>" + t(u["lang"], "updated_at", time=now.strftime("%H:%M")) + "</i>"
    return text


async def remember_card(chat_id, msg_id, data_id, bot=None):
    """Make this message the chat's live card; delete the previous one."""
    old = await POOL.fetchval("SELECT msg_id FROM times_cards WHERE chat_id = $1", chat_id)
    await POOL.execute(
        "INSERT INTO times_cards (chat_id, msg_id, data_id, sent_at, edited_at) VALUES ($1, $2, $3, now(), now()) "
        "ON CONFLICT (chat_id) DO UPDATE SET msg_id = EXCLUDED.msg_id, data_id = EXCLUDED.data_id, "
        "sent_at = now(), edited_at = now()", chat_id, msg_id, data_id)
    if bot and old and old != msg_id:
        try:
            await bot.delete_message(chat_id, old)
        except Exception:  # noqa: BLE001  (older than 48 h or already gone)
            pass


async def send_times_card(update, ctx, u):
    chat = update.effective_chat
    try:
        text = await card_text(u)
    except Exception:  # noqa: BLE001
        log.exception("times failed")
        return await chat.send_message(t(u["lang"], "error"))
    try:
        m = await chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=await card_markup(u))
    except BadRequest:  # just in case Telegram refuses the share link: send the card without it
        log.exception("card with share link refused")
        m = await chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=kb(
            [btn(t(u["lang"], "btn_menu"), "m:new")]))
    await remember_card(chat.id, m.message_id, u["user_id"], ctx.bot)


async def refresh_cards(context: ContextTypes.DEFAULT_TYPE):
    if bot_off() or not feat("auto"):
        return
    try:
        rows = await POOL.fetch(
            "SELECT c.chat_id AS card_chat, c.msg_id AS card_msg, u.* FROM times_cards c "
            "JOIN users u ON u.user_id = c.data_id "
            "WHERE u.auto_mode > 0 AND u.tz IS NOT NULL AND u.lang IS NOT NULL AND u.city IS NOT NULL "
            "AND NOT u.banned AND c.sent_at > now() - interval '14 days' "
            "AND c.edited_at <= now() - make_interval(mins => u.auto_mode) + interval '10 seconds'")
    except Exception:  # noqa: BLE001
        log.exception("refresh_cards: db error")
        return
    for r in rows:
        u = dict(r)
        chat_id, msg_id = u.pop("card_chat"), u.pop("card_msg")
        drop = False
        try:
            await context.bot.edit_message_text(await card_text(u), chat_id=chat_id, message_id=msg_id,
                                                parse_mode=ParseMode.HTML, reply_markup=await card_markup(u))
        except RetryAfter as e:
            log.warning("card refresh slowed down by Telegram for %ss", e.retry_after)
            return
        except BadRequest as e:
            drop = "not modified" not in str(e).lower()
        except Forbidden:
            drop = True
        except Exception:  # noqa: BLE001
            log.exception("card refresh failed for %s", chat_id)
        if drop:
            await POOL.execute("DELETE FROM times_cards WHERE chat_id = $1 AND msg_id = $2", chat_id, msg_id)
        else:
            await POOL.execute("UPDATE times_cards SET edited_at = now() WHERE chat_id = $1", chat_id)
        await asyncio.sleep(0.04)


def screen_auto(u):
    lang = u["lang"]
    opts = [btn(("✅ " if u["auto_mode"] == n else "") + auto_label(lang, n), f"set:auto:{n}") for n in AUTO_OPTIONS]
    return t(lang, "auto_title"), kb(opts[:2], opts[2:], [btn(t(lang, "btn_back"), "s:settings")])


# ───────────────────────── flow ─────────────────────────

async def resume(update, ctx, u):
    """Continue wherever the setup stopped, or show the main menu."""
    if not u["lang"]:
        text, markup = screen_lang()
        if not is_private(u):
            text = GROUP_WELCOME
        return await render(update, text, markup)
    if not u["madhab"]:
        text, markup = screen_madhab(u)
        return await render(update, text, markup)
    if not u["city"]:
        return await show_city_prompt(update, ctx, u)
    if not u["onboarded"]:
        text, markup = await screen_times(u, onboarding=True)
        await render(update, text, markup)
        return await ask_remind(update, u)
    text, markup = screen_menu(u)
    await render(update, text, markup)


async def apply_location(update, ctx, u, name, lat, lon, cc, drop_ids=()):
    tid, lang = u["user_id"], u["lang"]
    school = 1 if u["madhab"] == "hanafi" else 0
    try:
        data = await fetch_timings(lat, lon, datetime.utcnow().date(), method_for(cc), school)
    except Exception:  # noqa: BLE001
        log.exception("timings failed")
        await update.effective_chat.send_message(t(lang, "error"))
        return
    if COORDS_RE.match(name or "") and data.get("tz") and "/" in data["tz"]:
        name = data["tz"].split("/")[-1].replace("_", " ")  # e.g. "Tashkent"; the real name is filled in later
    await save(tid, city=name, lat=lat, lon=lon, country=cc, tz=data["tz"], awaiting_city=False)
    u = await get_user(tid)
    await cleanup_loc_kb(update, ctx)
    await cleanup_city_prompt(update, ctx)
    for mid in drop_ids:  # the user's own message with the city / location
        await drop_message(update, mid)
    onboarding = not u["onboarded"]
    if onboarding:
        shown = await render(update, await card_text(u), None, track=False)
        if shown is not None:
            await remember_card(update.effective_chat.id, shown.message_id, tid, ctx.bot)
        return await ask_remind(update, u)
    shown = await render(update, await card_text(u), await card_markup(u), track=False)
    if shown is not None:
        await remember_card(update.effective_chat.id, shown.message_id, tid, ctx.bot)


async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "channel":
        return
    if chat.type == "private":
        for k in ("admin_state", "support_mode", "reply_to", "target"):
            ctx.user_data.pop(k, None)
    elif _time.time() - ctx.chat_data.get("welcomed", 0) < 20:
        return  # the bot was just added and already greeted the group
    if chat.type == "private" and ctx.args:
        arg = ctx.args[0]
        if arg.startswith("r_") and arg[2:].isdigit():
            await credit_referral(ctx.bot, update.effective_user.id, int(arg[2:]))
        elif arg.startswith("ch_"):
            owner = await POOL.fetchval("SELECT owner FROM challenges WHERE code = $1", arg[3:20])
            await credit_referral(ctx.bot, update.effective_user.id, owner)
            await join_challenge(update, ctx, arg[3:])
    u = await target_for(update, ctx)
    await resume(update, ctx, u)
    if chat.type == "private":
        try:  # keep the chat clean: the user's /start disappears
            await update.message.delete()
        except Exception:  # noqa: BLE001
            pass


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.message
    if chat.type == "private":
        if is_admin(update.effective_user.id) and ctx.user_data.get("admin_state"):
            if await admin_text(update, ctx):
                return
        u = await target_for(update, ctx)
        if ctx.user_data.get("don_custom") and u["lang"]:
            return await don_custom_amount(update, ctx, u)
        if ctx.user_data.get("ai_mode") and u["onboarded"] and not u["awaiting_city"]:
            return await ai_message(update, ctx, u)
    else:
        reply = msg.reply_to_message
        if not (reply and reply.from_user and reply.from_user.id == ctx.bot.id):
            return
        u = await target_for(update, ctx)
        if not (u["lang"] and u["madhab"] and u["awaiting_city"]):
            return
        if not await can_manage(update, ctx):
            return await msg.reply_text(t(u["lang"], "only_admins"))
    if not (u["lang"] and u["madhab"]) or not (u["awaiting_city"] or not u["city"]):
        return await resume(update, ctx, u)
    lang = u["lang"]
    if chat.type == "private" and u["city"] and msg.text.strip() == t(lang, "btn_back"):  # "Back" under the input field
        await save(u["user_id"], awaiting_city=False)
        await drop_message(update, msg.message_id)
        await cleanup_city_prompt(update, ctx)
        await cleanup_loc_kb(update, ctx)
        text, markup = screen_settings(await get_user(u["user_id"]))
        return await render(update, text, markup)
    try:
        res = await geocode(msg.text.strip()[:100], lang)
    except Exception:  # noqa: BLE001
        log.exception("geocode failed")
        return await msg.reply_text(t(lang, "error"))
    if not res:
        return await msg.reply_text(t(lang, "city_not_found"), parse_mode=ParseMode.HTML)
    name, lat, lon, cc = res
    ctx.chat_data["pending_city"] = (u["user_id"], name, lat, lon, cc, msg.message_id)
    place = f"{esc(name)} {flag(cc)}" if cc else esc(name)
    await msg.reply_text(
        t(lang, "city_confirm", place=place),
        parse_mode=ParseMode.HTML,
        reply_markup=kb([btn(t(lang, "btn_city_yes"), "cc:yes")], [btn(t(lang, "btn_city_no"), "cc:no")]),
    )


async def on_location(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    u = await target_for(update, ctx)
    if not (u["lang"] and u["madhab"]):
        return await resume(update, ctx, u)
    ctx.chat_data.pop("pending_city", None)
    loc = update.message.location
    name, cc = await reverse_geocode(loc.latitude, loc.longitude, u["lang"])
    await apply_location(update, ctx, u, name, loc.latitude, loc.longitude, cc, drop_ids=(update.message.message_id,))


async def channel_button(update: Update, ctx, parts):
    """Channels are managed from the owner's private chat."""
    uid = update.effective_user.id
    me = await ensure_user(uid)
    lang = me["lang"] or "en"
    sub = parts[1] if len(parts) > 1 else "list"
    if sub == "open" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        c = await get_user(int(parts[2]))
        if c and c["chat_type"] == "channel" and c["owner_id"] == uid and not c["blocked"]:
            ctx.user_data["target"] = c["user_id"]
            if not c["lang"]:
                await save(c["user_id"], lang=lang)  # start with the owner's language
                c = await get_user(c["user_id"])
            return await resume(update, ctx, c)
        sub = "list"
    if sub == "exit":
        ctx.user_data.pop("target", None)
        return await resume(update, ctx, me)
    ctx.user_data.pop("target", None)
    rows = await POOL.fetch(
        "SELECT user_id, title FROM users WHERE chat_type = 'channel' AND owner_id = $1 AND NOT blocked "
        "ORDER BY title", uid)
    back = [btn(t(lang, "btn_menu"), "m:home")]
    if not rows:
        return await render(update, t(lang, "no_channels"), kb([add_channel_btn(lang)], back))
    buttons = [[btn("📢 " + (r["title"] or str(r["user_id"])), f"ch:open:{r['user_id']}")] for r in rows]
    await render(update, t(lang, "my_channels_title"), kb(*buttons, [add_channel_btn(lang)], back))


async def on_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    chat = update.effective_chat
    uid = q.from_user.id
    parts = q.data.split(":")
    act = parts[0]

    if act == "a":  # admin panel
        await q.answer()
        if is_admin(uid) and chat.type == "private":
            ctx.user_data.pop("reply_to", None)
            return await admin_router(update, ctx, parts)
        return
    if act == "sup":
        return await support_button(update, ctx, parts)
    if act == "ai" and chat.type == "private":
        return await ai_button(update, ctx, parts)
    if (act == "don" and not feat("donate")) or (act == "fr" and not feat("share")) \
            or (act == "ay" and not feat("ayah")):
        return await q.answer()
    if act == "don" and chat.type == "private":
        return await don_button(update, ctx, parts)
    if act == "buy" and chat.type == "private":
        return await buy_button(update, ctx, parts)
    if act == "fr" and chat.type == "private":
        if len(parts) > 1 and parts[1] == "how":
            fu = await get_user(uid)
            return await q.answer(t((fu or {}).get("lang") or "en", "fr_tip"), show_alert=True)
        if len(parts) > 2 and parts[1] == "as" and parts[2] in ("photo", "video"):
            await q.answer()
            return await share_card_send(ctx.bot, uid, parts[2])
        return await share_card_button(update, ctx)
    if act in ("pic", "ay") and chat.type == "private":
        return await pic_button(update, ctx, parts)
    if chat.type == "private":
        ctx.user_data.pop("ai_mode", None)  # any other button leaves the AI conversation
    if chat.type == "private":
        ctx.user_data.pop("support_mode", None)
        ctx.user_data.pop("reply_to", None)
    if act == "ch":
        await q.answer()
        if chat.type == "private":
            return await channel_button(update, ctx, parts)
        return
    if act == "pr":
        return await on_prayed(update, ctx, parts)

    u = await target_for(update, ctx)
    public = act == "tc" or (act == "m" and len(parts) > 1 and parts[1] in ("home", "times", "qibla", "new"))
    if chat.type != "private" and not public and not await can_manage(update, ctx):
        return await q.answer(t(u["lang"] or "en", "only_admins"), show_alert=True)
    await q.answer()
    tid = u["user_id"]

    # language can always be picked (Uzbek: first the language, then Latin or Cyrillic)
    if act == "lang" and len(parts) > 1 and parts[1] in ("uzpick", "all"):
        back = len(parts) > 2 and parts[2] == "1"
        text, markup = screen_uz_script(back) if parts[1] == "uzpick" else screen_lang(back=back)
        return await render(update, text, markup)
    if act == "lang" and len(parts) > 1 and parts[1] in LANGS:
        changed = u["lang"] != parts[1]
        await save(tid, lang=parts[1])
        if changed:
            await relocalize_city(tid, parts[1])
        u = await get_user(tid)
        if is_private(u) and u["onboarded"]:
            await sync_menu_button(ctx.bot, u)
        if u["onboarded"]:
            text, markup = screen_settings(u)
            return await render(update, text, markup)
        return await resume(update, ctx, u)

    if not u["lang"]:
        return await resume(update, ctx, u)
    lang = u["lang"]

    if act == "set" and parts[1] == "azan" and len(parts) > 2 and is_private(u):
        if parts[2] == "off" or azan_by_id(parts[2]):
            await save(tid, azan=None if parts[2] == "off" else parts[2])
            u = await get_user(tid)
            a = azan_by_id(u["azan"])
            if a:  # let them hear it
                try:
                    await send_azan_file(ctx.bot, tid, a, caption="🔊 " + a["name"], disable_notification=True)
                except Exception:  # noqa: BLE001
                    log.exception("adhan preview failed")
        text, markup = screen_settings(await get_user(tid))
        return await render(update, text, markup)

    if act == "set" and parts[1] == "madhab" and parts[2] in ("std", "hanafi"):
        await save(tid, madhab=parts[2])
        u = await get_user(tid)
        if not u["city"]:
            return await show_city_prompt(update, ctx, u)
        text, markup = screen_settings(u)
        return await render(update, text, markup)

    if act == "cc" and parts[1] in ("yes", "no"):
        pending = ctx.chat_data.pop("pending_city", None)
        if not u["madhab"]:
            return await resume(update, ctx, u)
        if pending:
            await drop_message(update, pending[-1])  # the user's "Tashkent" message
        if parts[1] == "yes" and pending and pending[0] == tid:
            _, name, lat, lon, cc, _ = pending
            return await apply_location(update, ctx, u, name, lat, lon, cc)
        return await show_city_prompt(update, ctx, u)  # "type again" (or an old, expired button)

    if act == "rem" and parts[1] in ("yes", "no"):
        on = parts[1] == "yes"
        await save(tid, remind=on, onboarded=True)
        u = await get_user(tid)
        _, markup = screen_menu(u)
        text = t(lang, "remind_on", phrase=reminder_phrase(lang, u)) if on else t(lang, "remind_off")
        shown = await render(update, text, markup)
        if is_private(u):
            await sync_menu_button(ctx.bot, u)
            await send_tour(ctx.bot, u)
        return shown

    # everything below needs a finished setup
    if not (u["madhab"] and u["city"] and u["tz"]):
        return await resume(update, ctx, u)

    if act == "tc":  # refresh this card now
        try:
            text = await card_text(u)
            await render(update, text, await card_markup(u), track=False)
            await POOL.execute("UPDATE times_cards SET edited_at = now() WHERE chat_id = $1 AND msg_id = $2",
                               update.effective_chat.id, q.message.message_id)
        except Exception:  # noqa: BLE001
            log.exception("card refresh failed")
        return

    if act == "m":
        sub = parts[1]
        if sub == "times":  # the menu closes and the card takes its place
            await send_times_card(update, ctx, u)
            try:
                await q.message.delete()
            except Exception:  # noqa: BLE001  (older than 48 h: leave it)
                pass
            return
        if sub == "new":
            text, markup = screen_menu(u)
            m = await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
            if update.effective_chat.type == "private":
                await swap_screen(ctx.bot, update.effective_chat.id, m.message_id)
            return
        elif sub == "qibla":
            return await send_qibla_image(update, u)
        elif sub == "toggle":
            await save(tid, remind=not u["remind"], onboarded=True)
            text, markup = screen_menu(await get_user(tid))
        elif sub == "settings":
            text, markup = screen_settings(u)
        else:
            text, markup = screen_menu(u)
        return await render(update, text, markup)

    if act == "s":
        sub = parts[1]
        if sub == "city":
            return await show_city_prompt(update, ctx, u)
        if sub == "support" and is_private(u) and ADMINS:
            ctx.user_data["support_mode"] = True
            ctx.user_data.pop("sup_last_mg", None)
            return await render(update, t(lang, "support_prompt"), kb([btn(t(lang, "btn_cancel"), "sup:cancel")]))
        if sub == "lang":
            text, markup = screen_lang(back=True)
        elif sub == "madhab":
            text, markup = screen_madhab(u)
        elif sub == "lead":
            text, markup = screen_lead(u)
        elif sub == "quiet":
            text, markup = screen_quiet(u)
        elif sub == "daily" and not is_private(u):
            text, markup = screen_daily(u)
        elif sub == "auto":
            text, markup = screen_auto(u)
        elif sub == "fast" and is_private(u):
            text, markup = await screen_fast(u)
        elif sub in ("fs", "fsnd") and is_private(u):
            col = "fast_show" if sub == "fs" else "fast_sound"
            await save(tid, **{col: not u[col]})
            text, markup = await screen_fast(await get_user(tid))
        elif sub == "snd" and is_private(u):
            text, markup = screen_sound(u)
        elif sub == "groups" and is_private(u):
            text, markup = screen_groups(u)
        elif sub == "azan" and is_private(u):
            text, markup = screen_azan(u)
        elif sub == "wk" and is_private(u):
            await save(tid, weekly=not u["weekly"])
            text, markup = screen_settings(await get_user(tid))
        elif sub == "ayah" and is_private(u):
            await save(tid, ayah_rem=not u["ayah_rem"])
            text, markup = screen_settings(await get_user(tid))
        elif sub == "attime":
            await save(tid, at_time=not u["at_time"])
            text, markup = screen_settings(await get_user(tid))
        elif sub == "ramadan":
            await save(tid, ramadan=not u["ramadan"])
            text, markup = screen_settings(await get_user(tid))
        else:
            text, markup = screen_settings(u)
        return await render(update, text, markup)

    if act == "set" and parts[1] in ("suh", "ift", "pm") and len(parts) > 2 and is_private(u):
        v = int(parts[2]) if parts[2].lstrip("-").isdigit() else None
        if parts[1] == "suh" and v in SUH_OPTS:
            await save(tid, suhoor_rem=v)
        elif parts[1] == "ift" and v in IFT_OPTS:
            await save(tid, iftar_rem=v)
        elif parts[1] == "pm" and v is not None and 0 <= v < 5:
            modes = list((u["prayer_modes"] or "sssss").ljust(5, "s"))
            modes[v] = PRAYER_MODES[(PRAYER_MODES.index(modes[v]) + 1) % 3]
            await save(tid, prayer_modes="".join(modes))
            text, markup = screen_sound(await get_user(tid))
            return await render(update, text, markup)
        text, markup = await screen_fast(await get_user(tid))
        return await render(update, text, markup)

    if act == "set":
        what = parts[1]
        if what == "lead" and parts[2].isdigit() and int(parts[2]) in LEAD_OPTIONS:
            await save(tid, lead_min=int(parts[2]))
        elif what == "auto" and parts[2].isdigit() and int(parts[2]) in AUTO_OPTIONS:
            await save(tid, auto_mode=int(parts[2]))
            card = await POOL.fetchrow("SELECT chat_id, msg_id FROM times_cards WHERE data_id = $1", tid)
            if card:  # show the change on the card right away
                try:
                    await ctx.bot.edit_message_text(await card_text(await get_user(tid)), chat_id=card["chat_id"],
                                                    message_id=card["msg_id"], parse_mode=ParseMode.HTML,
                                                    reply_markup=await card_markup(await get_user(tid)))
                except Exception:  # noqa: BLE001
                    pass
        elif what == "daily" and parts[2] in ("off", "fajr", "sunrise"):
            await save(tid, daily=parts[2])
        elif what == "quiet":
            if parts[2] == "off":
                await save(tid, quiet_start=None, quiet_end=None)
            else:
                a, b = (int(x) for x in parts[2].split("-"))
                if (a, b) in QUIET_PRESETS:
                    await save(tid, quiet_start=a, quiet_end=b)
        text, markup = screen_settings(await get_user(tid))
        return await render(update, text, markup)

    text, markup = screen_menu(u)
    await render(update, text, markup)


# ───────────────────────── groups & channels ─────────────────────────

async def on_my_member(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """The bot was added to / removed from a chat, or its rights changed."""
    cm = update.my_chat_member
    chat, new, old = cm.chat, cm.new_chat_member, cm.old_chat_member
    if chat.type == "private":
        await POOL.execute("UPDATE users SET blocked = $2 WHERE user_id = $1", chat.id,
                           new.status in ("kicked", "left"))
        return
    present = new.status in ("member", "administrator", "creator") or \
        (new.status == "restricted" and getattr(new, "is_member", False))
    if not present:
        await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", chat.id)
        return
    was = old.status in ("member", "administrator", "creator") or \
        (old.status == "restricted" and getattr(old, "is_member", False))
    adder = cm.from_user.id if cm.from_user else None

    if chat.type == "channel":
        c = await ensure_chat(chat, "channel", owner_id=None if was else adder)
        try:
            await save(chat.id, members=await ctx.bot.get_chat_member_count(chat.id))
        except Exception:  # noqa: BLE001
            pass
        can_post = new.status == "administrator" and getattr(new, "can_post_messages", False)
        could_post = old.status == "administrator" and getattr(old, "can_post_messages", False)
        owner = c["owner_id"]
        if not owner:
            return
        olang = ((await get_user(owner)) or {}).get("lang") or "en"
        try:
            if not can_post:
                await ctx.bot.send_message(owner, t(olang, "channel_no_rights", title=esc(chat.title)),
                                           parse_mode=ParseMode.HTML)
            elif not could_post:
                await ctx.bot.send_message(
                    owner, t(olang, "channel_added", title=esc(chat.title)), parse_mode=ParseMode.HTML,
                    reply_markup=kb([btn(t(olang, "btn_setup"), f"ch:open:{chat.id}")]))
        except Exception:  # noqa: BLE001
            log.info("could not message channel owner %s", owner)
        return

    # group / supergroup
    c = await ensure_chat(chat, "group", owner_id=None if was else adder)
    try:
        await save(chat.id, members=await ctx.bot.get_chat_member_count(chat.id))
    except Exception:  # noqa: BLE001
        pass
    if was:
        return
    ctx.chat_data["welcomed"] = _time.time()
    try:
        if c["onboarded"] and c["lang"]:
            text, markup = screen_menu(c)
        else:
            text, markup = GROUP_WELCOME, screen_lang()[1]
        await ctx.bot.send_message(chat.id, text, parse_mode=ParseMode.HTML, reply_markup=markup)
    except Exception:  # noqa: BLE001
        log.exception("group welcome failed")


async def on_migrate(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """A group became a supergroup: Telegram changes its id."""
    m = update.message
    if m and m.migrate_to_chat_id:
        try:
            await POOL.execute(
                "UPDATE users SET user_id = $2 WHERE user_id = $1 "
                "AND NOT EXISTS (SELECT 1 FROM users WHERE user_id = $2)", m.chat.id, m.migrate_to_chat_id)
        except Exception:  # noqa: BLE001
            log.exception("migrate failed")


# ───────────────────────── support ─────────────────────────

async def support_button(update: Update, ctx, parts):
    q = update.callback_query
    uid = q.from_user.id
    sub = parts[1] if len(parts) > 1 else ""
    if sub == "cancel":
        await q.answer()
        ctx.user_data.pop("support_mode", None)
        u = await target_for(update, ctx)
        if not (u["lang"] and u["city"]):
            return await resume(update, ctx, u)
        text, markup = screen_settings(u)
        return await render(update, text, markup)
    await q.answer()
    if not is_admin(uid) or update.effective_chat.type != "private":
        return
    if sub == "reply" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        if not has_perm(uid, "support"):
            return await update.effective_chat.send_message("🔒 У вас нет права «Поддержка».")
        target = int(parts[2])
        ctx.user_data["reply_to"] = target
        ctx.user_data["reply_kind"] = "w" if len(parts) > 3 and parts[3] == "w" else "r"
        ctx.user_data.pop("rep_last_mg", None)
        await update.effective_chat.send_message(
            f"↩️ <b>Ответ пользователю</b> <code>{target}</code>\n\n"
            f"Отправьте ответ: текст, фото, видео, голосовое, файл — что угодно.",
            parse_mode=ParseMode.HTML, reply_markup=kb([btn("❌ Отмена", "sup:rdone")]))
        return
    if sub == "rdone":
        ctx.user_data.pop("reply_to", None)
        return await render(update, "✅ Готово. Режим ответа выключен.", kb(ADMIN_BACK))


async def support_msg(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Private messages while in support mode (user) or reply mode (admin). Any message type."""
    if not update.message:
        return
    uid = update.effective_user.id
    if is_admin(uid) and ctx.user_data.get("admin_state") == "azan" and not (update.message.text or "").startswith("/"):
        await admin_azan_upload(update, ctx)
        raise ApplicationHandlerStop
    if is_admin(uid) and ctx.user_data.get("admin_state") == "bc_text" and ctx.user_data.get("bc") \
            and not (update.message.text or "").startswith("/"):
        await bc_got_message(update, ctx)
        raise ApplicationHandlerStop
    if is_main(uid) and ctx.user_data.get("admin_state") == "inv_up":
        m = update.message
        got = ("photo", m.photo[-1].file_id) if m.photo else ("video", m.video.file_id) if m.video else \
            ("animation", m.animation.file_id) if m.animation else None
        if got:
            ctx.user_data.pop("admin_state", None)
            invite_cfg()["custom"]["all"] = {"type": got[0], "file_id": got[1]}
            await save_bot_cfg()
            await m.reply_text("✅ Своя карточка сохранена. Теперь по кнопке «Поделиться» уходит она.",
                               reply_markup=kb([btn("🤝 Карточка приглашения", "a:bset:inv")]))
        else:
            await m.reply_text("❗ Нужно фото, видео или GIF.")
        raise ApplicationHandlerStop
    if is_admin(uid) and ctx.user_data.get("reply_to"):
        await admin_reply(update, ctx)
        raise ApplicationHandlerStop
    if ctx.user_data.get("support_mode") and ADMINS and feat("support"):
        await user_support(update, ctx)
        raise ApplicationHandlerStop


async def user_support(update: Update, ctx):
    msg = update.message
    user = update.effective_user
    u = await ensure_user(user.id)
    lang = u["lang"] or "en"
    mg = msg.media_group_id
    first = not mg or ctx.user_data.get("sup_last_mg") != mg
    now = _time.time()
    stamps = [x for x in ctx.user_data.get("sup_ts", []) if now - x < 60]
    if first and len(stamps) >= 10:
        await msg.reply_text(t(lang, "support_slow"))
        return
    if first:
        stamps.append(now)
    ctx.user_data["sup_ts"] = stamps
    ctx.user_data["sup_last_mg"] = mg

    markup = kb([btn("↩️ Ответить", f"sup:reply:{user.id}"), btn("👤 Карточка", f"a:card:{user.id}")])
    try:
        if first:
            uname = f"@{user.username}" if user.username else "—"
            where = f"📍 {esc(u['city'])} {flag(u['country']) if u['country'] else ''} · " if u["city"] else ""
            header = (f"📩 <b>Новое сообщение в поддержку</b>\n"
                      f"👤 Имя: <a href=\"tg://user?id={user.id}\">{esc(user.full_name)}</a>\n"
                      f"🔗 Username: {esc(uname)}\n"
                      f"🆔 ID: <code>{user.id}</code>\n"
                      f"{where}🌐 {LANG_BUTTONS.get(lang, lang)}")
        delivered = 0
        hidden = u["hidden"] if "hidden" in u.keys() else False
        for admin in sorted(a for a in ADMINS if has_perm(a, "support") and (not hidden or is_main(a))):  # any can reply
            try:
                if first:
                    await ctx.bot.send_message(admin, header, parse_mode=ParseMode.HTML)
                try:
                    await msg.copy(admin, reply_markup=markup)
                except BadRequest:  # some messages (e.g. polls) can't be copied with buttons
                    await msg.forward(admin)
                    await ctx.bot.send_message(admin, "👆", reply_markup=markup)
                delivered += 1
            except Exception:  # noqa: BLE001
                log.exception("support forward to admin %s failed (has this admin started the bot?)", admin)
        if not delivered:
            raise RuntimeError("no admin reachable")
    except Exception:  # noqa: BLE001
        log.exception("support forward failed")
        await msg.reply_text(t(lang, "error"))
        return
    if first:
        await bump("support_msgs")
        await msg.reply_text(t(lang, "support_sent"), reply_markup=kb([btn(t(lang, "btn_menu"), "m:home")]))
        if BOT_CFG.get("sup_auto"):
            await msg.reply_text(BOT_CFG["sup_auto"], disable_web_page_preview=True)


async def admin_reply(update: Update, ctx):
    msg = update.message
    target = ctx.user_data["reply_to"]
    tu = await get_user(target)
    tlang = (tu or {}).get("lang") or "en"
    mg = msg.media_group_id
    first = not mg or ctx.user_data.get("rep_last_mg") != mg
    ctx.user_data["rep_last_mg"] = mg
    logged = []
    try:
        if first:
            head = "admin_msg_header" if ctx.user_data.get("reply_kind") == "w" else "support_reply_header"
            hm = await ctx.bot.send_message(target, t(tlang, head), parse_mode=ParseMode.HTML)
            logged.append(await log_sent(target, hm.message_id, "admin", "заголовок сообщения от админа"))
        cm = await msg.copy(target)
        preview = (msg.text or msg.caption or "")[:60] or ("[фото]" if msg.photo else "[видео]" if msg.video else
                                                              "[голосовое]" if msg.voice else "[файл]")
        logged.append(await log_sent(target, cm.message_id, "admin", "от админа: " + preview))
    except Forbidden:
        await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", target)
        ctx.user_data.pop("reply_to", None)
        await msg.reply_text("❌ Пользователь заблокировал бота, ответ не доставлен.", reply_markup=kb(ADMIN_BACK))
        return
    except Exception as e:  # noqa: BLE001
        log.exception("admin reply failed")
        await msg.reply_text(f"⚠️ Не удалось отправить: {esc(e)}")
        return
    if first:
        dl = ":".join(str(x) for x in logged if x)
        await msg.reply_text(f"✅ Доставлено пользователю <code>{target}</code>.\nМожно отправить ещё или завершить 👇",
                             parse_mode=ParseMode.HTML,
                             reply_markup=kb([btn("✅ Готово", "sup:rdone"), btn("🗑 Удалить у него", f"a:umdelp:{target}:{dl}")]
                                             if dl and len(dl) < 40 else [btn("✅ Готово", "sup:rdone")]))


# ───────────────────────── reminders ─────────────────────────

SENT = {}  # (chat_id, date, event) -> unix time


def in_quiet(hour, qs, qe):
    if qs is None or qe is None:
        return False
    return (qs <= hour < qe) if qs <= qe else (hour >= qs or hour < qe)


async def send_reminder(bot, u, text, markup=None, silent=False):
    lang = u["lang"]
    if markup is None:
        markup = kb([btn(t(lang, "btn_menu"), "m:new")]) if is_private(u) else None
    for attempt in range(2):
        try:
            m = await bot.send_message(u["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=markup,
                                       disable_notification=silent)
            await bump("reminders_sent")
            if is_private(u):
                await swap_reminders(bot, u["user_id"], m.message_id)
                await schedule_delete(u["user_id"], m.message_id)
            break
        except Forbidden:  # blocked / removed from the chat (cleared automatically when they come back)
            await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", u["user_id"])
            await bump("reminders_failed")
            break
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception:  # noqa: BLE001
            log.exception("send failed for %s", u["user_id"])
            await bump("reminders_failed")
            break
    await asyncio.sleep(0.05)  # stay well under Telegram's broadcast limits


async def swap_reminders(bot, uid, msg_id):
    """Only the latest reminder stays in a private chat: the previous one (and its adhan) is deleted."""
    try:
        old = await POOL.fetchval(
            "UPDATE users u SET rem_msgs = ARRAY[$2::bigint] FROM (SELECT rem_msgs AS old FROM users WHERE user_id = $1) o "
            "WHERE u.user_id = $1 RETURNING o.old", uid, msg_id)
        for mid in old or []:
            try:
                await bot.delete_message(uid, mid)
            except Exception:  # noqa: BLE001  (already deleted or older than 48 h)
                pass
    except Exception:  # noqa: BLE001
        log.exception("could not clean old reminders for %s", uid)


def due(now, when):
    return 0 <= (now - when).total_seconds() < 60


async def process_user(bot, u):
    tz = ZoneInfo(u["tz"])
    now = datetime.now(tz)
    d = now.date()
    data = await get_timings(u, d)
    lang = u["lang"]

    # daily schedule for groups and channels
    if not is_private(u) and u["daily"] in ("fajr", "sunrise"):
        hh, mm = map(int, data["Fajr" if u["daily"] == "fajr" else "Sunrise"].split(":"))
        sk = (u["user_id"], d.isoformat(), "daily")
        if due(now, datetime.combine(d, dtime(hh, mm), tzinfo=tz)) and sk not in SENT:
            SENT[sk] = _time.time()
            text, _ = await screen_times(u, onboarding=True)
            await send_reminder(bot, u, text)

    ramadan = u["ramadan"] and data["hmonth"] == 9
    modes = ((u.get("prayer_modes") if hasattr(u, "get") else None) or "sssss").ljust(5, "s")
    if is_private(u) and (u["suhoor_rem"] >= 0 or u["iftar_rem"] >= 0):
        await fasting_reminders(bot, u, data, now, d, tz, ramadan, modes)

    if not u["remind"]:
        return
    for key in EVENTS:
        mode = modes[EVENTS.index(key)] if is_private(u) else "s"
        if mode == "o":
            continue
        hh, mm = map(int, data[key].split(":"))
        event_time = datetime.combine(d, dtime(hh, mm), tzinfo=tz)
        plan = []  # two reminders: "b" = before, "n" = now
        if u["lead_min"] > 0:
            plan.append(("b", event_time - timedelta(minutes=u["lead_min"])))
        if u["at_time"]:
            plan.append(("n", event_time))
        for suffix, when in plan:
            if not due(now, when):
                continue
            sk = (u["user_id"], d.isoformat(), key, suffix)
            if sk in SENT:
                continue
            SENT[sk] = _time.time()
            if in_quiet(when.hour, u["quiet_start"], u["quiet_end"]):
                continue
            if key == "Dhuhr" and d.weekday() == 4:
                kind_ = "jumah"
            elif ramadan and key == "Fajr":
                kind_ = "fajr_ram"
            elif ramadan and key == "Maghrib":
                kind_ = "iftar"
            else:
                kind_ = "std"
            text = t(lang, f"rem_{kind_}_{suffix}", name=PN[lang][key.lower()], n=u["lead_min"], time=data[key])
            markup = None
            if is_private(u) and (suffix == "n" or not u["at_time"]):
                markup = prayed_markup(lang, d.isoformat(), EVENTS.index(key))
            await send_reminder(bot, u, text, markup, silent=mode == "q")
            if suffix == "n" and is_private(u) and u["azan"]:
                await send_azan(bot, u)


async def fasting_reminders(bot, u, data, now, d, tz, ramadan, modes):
    """Suhoor (before Fajr) and iftar (before / at Maghrib) reminders chosen in the settings."""
    lang = u["lang"]
    plan = []
    if u["suhoor_rem"] > 0:
        plan.append(("suh", "Fajr", u["suhoor_rem"]))
    if u["iftar_rem"] >= 0:
        plan.append(("ift", "Maghrib", u["iftar_rem"]))
    for tag, key, n in plan:
        hh, mm = map(int, data[key].split(":"))
        when = datetime.combine(d, dtime(hh, mm), tzinfo=tz) - timedelta(minutes=n)
        if not due(now, when):
            continue
        sk = (u["user_id"], d.isoformat(), tag)
        if sk in SENT:
            continue
        SENT[sk] = _time.time()
        if in_quiet(when.hour, u["quiet_start"], u["quiet_end"]):
            continue
        # in Ramadan the prayer reminder already says this at the same moment: don't send it twice
        idx = EVENTS.index(key)
        same = u["remind"] and modes[idx] != "o" and ((n > 0 and n == u["lead_min"]) or (n == 0 and u["at_time"]))
        if ramadan and same:
            continue
        if tag == "suh":
            text = t(lang, "suh_rem", n=n, time=data[key])
        else:
            text = t(lang, "rem_iftar_n" if n == 0 else "rem_iftar_b", n=n, time=data[key])
        await send_reminder(bot, u, text, silent=not u["fast_sound"])


async def tick(context: ContextTypes.DEFAULT_TYPE):
    if bot_off() or not feat("remind"):
        return
    try:
        rows = await POOL.fetch(
            "SELECT * FROM users WHERE (remind OR daily <> 'off' OR suhoor_rem >= 0 OR iftar_rem >= 0) "
            "AND NOT banned AND NOT blocked "
            "AND lat IS NOT NULL AND tz IS NOT NULL AND lang IS NOT NULL")
    except Exception:  # noqa: BLE001
        log.exception("tick: db error")
        return
    users = [dict(r) for r in rows]

    # purge old caches
    now_ts = _time.time()
    for k in [k for k, v in SENT.items() if now_ts - v > 600]:
        SENT.pop(k, None)
    today_utc = datetime.utcnow().date()
    for k in [k for k in CACHE if k[4] < today_utc - timedelta(days=2)]:
        CACHE.pop(k, None)

    # fetch each location once, in parallel
    jobs = [get_timings(u, datetime.now(ZoneInfo(u["tz"])).date()) for u in users]
    await asyncio.gather(*jobs, return_exceptions=True)

    for u in users:
        try:
            await process_user(context.bot, u)
        except Exception:  # noqa: BLE001
            log.exception("process_user failed for %s", u["user_id"])


# ───────────────────────── admin panel ─────────────────────────
# Admins: ADMIN_ID plus ADMIN_IDS. The admin UI is in Russian and fully button-driven.

ADMIN_BACK = [btn("⬅️ Назад", "a:home")]
CSV_COLUMNS = ("user_id", "full_name", "username", "chat_type", "title", "owner_id", "members", "lang", "madhab", "city", "country", "tz", "remind", "lead_min", "at_time", "quiet_start",
               "quiet_end", "ramadan", "onboarded", "banned", "blocked", "created_at", "last_seen")
MADHAB_RU = {"std": "Шафиитский / Маликитский / Ханбалитский", "hanafi": "Ханафитский"}


def is_admin(uid):
    return uid in ADMINS


def flag(cc):
    cc = (cc or "").upper()
    if len(cc) == 2 and cc.isalpha():
        return "".join(chr(0x1F1E6 + ord(c) - 65) for c in cc)
    return "🏳️"


def bar(n, mx, width=8):
    k = round(width * n / mx) if mx else 0
    return "▰" * k + "▱" * (width - k)


def fdt(dt):
    return dt.strftime("%d.%m.%Y %H:%M") if dt else "—"


def yn(v):
    return "да" if v else "нет"


async def bump(key, n=1):
    """Daily counters shown in the admin panel (UTC day)."""
    try:
        await POOL.execute(
            "INSERT INTO daily_stats (stat_day, stat_key, stat_value) VALUES (CURRENT_DATE, $1, $2) "
            "ON CONFLICT (stat_day, stat_key) DO UPDATE SET stat_value = daily_stats.stat_value + EXCLUDED.stat_value",
            key, n)
    except Exception:  # noqa: BLE001
        log.exception("bump failed")


async def gate(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Runs before every handler: records activity and silently ignores banned users."""
    user = update.effective_user
    if not user:
        return
    chat = update.effective_chat
    try:
        if chat and chat.type == "private":
            row = await POOL.fetchrow(
                "INSERT INTO users (user_id, last_seen, full_name, username) VALUES ($1, now(), $2, $3) "
                "ON CONFLICT (user_id) DO UPDATE SET last_seen = now(), blocked = FALSE, "
                "full_name = EXCLUDED.full_name, username = EXCLUDED.username RETURNING banned, lang, (xmax = 0) AS inserted",
                user.id, user.full_name, user.username)
            await POOL.execute("INSERT INTO daily_active (day, user_id) VALUES (CURRENT_DATE, $1) ON CONFLICT DO NOTHING",
                               user.id)
        else:
            row = await POOL.fetchrow(
                "UPDATE users SET last_seen = now(), full_name = $2, username = $3 WHERE user_id = $1 "
                "RETURNING banned, lang, FALSE AS inserted", user.id, user.full_name, user.username)
    except Exception:  # noqa: BLE001
        log.exception("gate failed")
        return
    if row and row["banned"] and not is_admin(user.id):
        if update.callback_query:
            try:
                await update.callback_query.answer()
            except Exception:  # noqa: BLE001
                pass
        raise ApplicationHandlerStop
    inserted = bool(row and row["inserted"])
    code = (row["lang"] if row and row["lang"] else str(user.language_code or "en")[:2])
    await gate_rules(update, ctx, user, code if code in LANGS else "en", inserted)
    if inserted and chat and chat.type == "private":
        try:
            await apply_defaults(user.id)
        except Exception:  # noqa: BLE001
            log.exception("defaults failed")
        if BOT_CFG.get("welcome"):
            asyncio.get_running_loop().create_task(send_welcome(ctx.bot, user.id))


# ── screens ──

async def screen_admin_home(uid=None):
    r = await POOL.fetchrow(
        "SELECT count(*) AS total, count(*) FILTER (WHERE remind AND NOT blocked AND NOT banned) AS rem "
        "FROM users WHERE chat_type = 'private'")
    text = (f"🛠 <b>Админка</b>\n\n"
            f"👥 Пользователей: <b>{r['total']}</b>\n"
            f"🔔 С напоминаниями: <b>{r['rem']}</b>\n\n"
            f"Выберите раздел 👇")
    can = (lambda p: True) if uid is None else (lambda p: has_perm(uid, p))
    items = [("stats", btn("📈 Статистика", "a:stats")), ("stats", btn("🌍 География", "a:geo")),
             ("users", btn("👥 Пользователи", "a:users:0")), ("users", btn("📢 Группы и каналы", "a:chats:0")),
             ("bc", btn("📣 Рассылка", "a:bc")), ("users", btn("🔎 Поиск", "a:user")),
             ("health", btn("✉️ Тест напоминания", "a:test")), ("bans", btn("🚫 Баны", "a:bans")),
             ("export", btn("📤 Экспорт CSV", "a:export")), ("health", btn("🩺 Здоровье", "a:health")),
             ("azan", btn("🔊 Азаны", "a:azan")), ("ai", btn("🤖 ИИ-помощник", "a:ai"))]
    shown = [b for p, b in items if can(p)]
    rows = [shown[i:i + 2] for i in range(0, len(shown), 2)]
    if uid is not None and is_main(uid):
        rows.append([btn("👮 Админы", "a:adm"), btn("🙈 Скрытые", "a:hidden")])
        rows.append([btn("⚙️ Настройки бота", "a:bset")])
    rows.append([btn("🏠 В меню бота", "m:home")])
    return text, kb(*rows)


async def today_counters():
    rows = await POOL.fetch("SELECT stat_key, stat_value FROM daily_stats WHERE stat_day = CURRENT_DATE")
    return {r["stat_key"]: r["stat_value"] for r in rows}


async def screen_admin_stats():
    r = await POOL.fetchrow("""
        SELECT count(*) AS total,
               count(*) FILTER (WHERE onboarded) AS setup,
               count(*) FILTER (WHERE remind AND NOT blocked AND NOT banned) AS reminders,
               count(*) FILTER (WHERE created_at >= date_trunc('day', now())) AS new_today,
               count(*) FILTER (WHERE created_at >= now() - interval '7 days') AS new_week,
               count(*) FILTER (WHERE last_seen >= now() - interval '7 days') AS active_week,
               count(*) FILTER (WHERE banned) AS banned,
               count(*) FILTER (WHERE blocked) AS blocked
        FROM users WHERE chat_type = 'private'""")
    ch = await POOL.fetchrow("""
        SELECT count(*) FILTER (WHERE chat_type = 'group') AS groups,
               count(*) FILTER (WHERE chat_type = 'channel') AS channels,
               coalesce(sum(members), 0) AS members
        FROM users WHERE chat_type <> 'private' AND NOT blocked""")
    c = await today_counters()
    text = (f"📈 <b>Статистика</b>\n\n"
            f"👥 Всего: <b>{r['total']}</b>\n"
            f"✅ Завершили настройку: <b>{r['setup']}</b>\n"
            f"🔔 С напоминаниями: <b>{r['reminders']}</b>\n\n"
            f"🆕 Новых сегодня: <b>{r['new_today']}</b>\n"
            f"🆕 Новых за 7 дней: <b>{r['new_week']}</b>\n"
            f"👁 Активных за 7 дней: <b>{r['active_week']}</b>\n\n"
            f"🚫 В бане: <b>{r['banned']}</b>\n"
            f"🧱 Заблокировали бота: <b>{r['blocked']}</b>\n\n"
            f"👥 Групп: <b>{ch['groups']}</b> · 📢 Каналов: <b>{ch['channels']}</b>\n"
            f"👤 Участников в них: <b>{ch['members']}</b>\n\n"
            f"📩 Сообщений в поддержку сегодня: <b>{c.get('support_msgs', 0)}</b>\n"
            f"📬 Напоминаний сегодня (UTC): отправлено <b>{c.get('reminders_sent', 0)}</b>, "
            f"ошибок <b>{c.get('reminders_failed', 0)}</b>")
    return text, kb([btn("🔄 Обновить", "a:stats")], ADMIN_BACK)


def top_lines(rows, label):
    if not rows:
        return "— пока нет данных"
    mx = max(r["c"] for r in rows)
    return "\n".join(f"{label(r)}  {bar(r['c'], mx)} <b>{r['c']}</b>" for r in rows)


def km_between(a1, o1, a2, o2):
    r = math.radians
    h = math.sin(r(a2 - a1) / 2) ** 2 + math.cos(r(a1)) * math.cos(r(a2)) * math.sin(r(o2 - o1) / 2) ** 2
    return 12742 * math.asin(math.sqrt(h))


async def city_clusters(radius_km=30, top=10):
    """One city = every point within ~30 km, whatever language its name was saved in."""
    rows = await POOL.fetch("SELECT city, lat, lon, lang FROM users WHERE lat IS NOT NULL AND city IS NOT NULL")
    groups = []
    for r in rows:
        for g in groups:
            if km_between(g["lat"], g["lon"], r["lat"], r["lon"]) <= radius_km:
                g["c"] += 1
                g["names"][r["city"]] = g["names"].get(r["city"], 0) + 1
                if r["lang"] == "ru":
                    g["ru"] = r["city"]
                break
        else:
            groups.append({"lat": r["lat"], "lon": r["lon"], "c": 1, "names": {r["city"]: 1},
                           "ru": r["city"] if r["lang"] == "ru" else None})
    for g in groups:
        g["name"] = g["ru"] or max(g["names"], key=g["names"].get)
    groups.sort(key=lambda g: -g["c"])
    return groups[:top]


async def screen_admin_geo():
    cities = await city_clusters()
    countries = await POOL.fetch(
        "SELECT lower(country) AS cc, count(*) AS c FROM users WHERE coalesce(country, '') <> '' "
        "GROUP BY lower(country) ORDER BY c DESC LIMIT 10")
    langs = await POOL.fetch(
        "SELECT lang, count(*) AS c FROM users WHERE lang IS NOT NULL GROUP BY lang ORDER BY c DESC")
    madh = await POOL.fetch(
        "SELECT madhab, count(*) AS c FROM users WHERE madhab IS NOT NULL GROUP BY madhab ORDER BY c DESC")
    text = (f"🌍 <b>География и языки</b>\n\n"
            f"<b>Города (топ-10)</b>\n{top_lines(cities, lambda r: '📍 ' + esc(r['name']))}\n\n"
            f"<b>Страны (топ-10)</b>\n{top_lines(countries, lambda r: flag(r['cc']) + ' ' + r['cc'].upper())}\n\n"
            f"<b>Языки</b>\n{top_lines(langs, lambda r: LANG_BUTTONS.get(r['lang'], r['lang']))}\n\n"
            f"<b>Мазхабы</b>\n{top_lines(madh, lambda r: '🕌 ' + MADHAB_RU.get(r['madhab'], r['madhab']))}")
    return text, kb([btn("🔄 Обновить", "a:geo")], ADMIN_BACK)


PAGE = 8


def back_cb(token):
    """Where the "back" button of a profile leads: users list, search, chats list or the admin home."""
    if token and token[0] in "usc" and token[1:].isdigit():
        return {"u": "a:users:", "s": "a:usearch:", "c": "a:chats:"}[token[0]] + token[1:]
    if token == "h":
        return "a:hidden"
    return "a:home"


def short(s, n):
    s = str(s or "")
    return s if len(s) <= n else s[: n - 1] + "…"


def person_label(r):
    name = r["full_name"] or (f"@{r['username']}" if r["username"] else str(r["user_id"]))
    bits = [("🚫 " if r["banned"] else "") + short(name, 22)]
    if r["username"] and r["full_name"]:
        bits.append("@" + short(r["username"], 16))
    if r["city"]:
        bits.append(short(r["city"].split(",")[0], 14))
    return " · ".join(bits)


async def user_card(uid, back=None, viewer=None):
    r = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    if not r or (r["hidden"] and not is_main(viewer)):
        return None
    u = dict(r)
    lead = (f"за {u['lead_min']} мин" if u["lead_min"] else "без заранее") + (" + в момент азана" if u["at_time"] else "")
    quiet = "выкл" if u["quiet_start"] is None else f"{u['quiet_start']:02d}:00–{u['quiet_end']:02d}:00"
    where = f"{esc(u['city'] or '—')} {flag(u['country']) if u['country'] else ''}"
    common = (f"🌐 {LANG_BUTTONS.get(u['lang'], '—')} · 🕌 {MADHAB_RU.get(u['madhab'], '—')}\n"
              f"📍 {where}\n"
              f"🔔 {'вкл: ' + lead if u['remind'] else 'выкл'} · 🔕 {quiet}\n"
              f"🔄 Автообновление: {auto_label('ru', u['auto_mode'])} · 🌙 Рамадан: {yn(u['ramadan'])}\n")
    rows = []
    if u["chat_type"] == "private":
        name = esc(u["full_name"] or "Без имени")
        owned = await POOL.fetchrow(
            "SELECT count(*) FILTER (WHERE chat_type = 'group') AS g, count(*) FILTER (WHERE chat_type = 'channel') AS c "
            "FROM users WHERE owner_id = $1 AND NOT blocked", uid)
        status = ("🚫 В бане" if u["banned"] else "") + (" · " if u["banned"] and u["blocked"] else "") + \
                 ("🧱 Заблокировал бота" if u["blocked"] else "")
        text = (f"👤 <b><a href=\"tg://user?id={uid}\">{name}</a></b>\n"
                f"🔗 {('@' + esc(u['username'])) if u['username'] else 'нет username'} · 🆔 <code>{uid}</code>\n\n"
                f"{common}"
                f"📢 Каналов: {owned['c']} · 👥 Групп: {owned['g']}\n\n"
                f"📅 С нами с {fdt(u['created_at'])} UTC\n"
                f"👁 Был(а): {fdt(u['last_seen'])} UTC\n"
                f"{('⚠️ ' + status) if status else '✅ Активен'}")
        if not is_admin(uid):
            rows.append([btn("✉️ Написать", f"sup:reply:{uid}:w"),
                         btn("✅ Разбанить", f"a:unban:{uid}:{back or ''}") if u["banned"]
                         else btn("🚫 Забанить", f"a:ban:{uid}:{back or ''}")])
        if u["username"]:
            rows.append([InlineKeyboardButton("💬 Открыть в Telegram", url=f"https://t.me/{u['username']}")])
        if viewer is not None and has_perm(viewer, "ai"):
            credits, unl = await ai_wallet(uid)
            text += f"\n🤖 ИИ: куплено {credits}" + (f", безлимит до {unl:%d.%m.%Y}" if unl and unl > datetime.now(ZoneInfo('UTC')) else "")
            rows.append([btn("🎁 Начислить вопросы", f"a:grant:{uid}"), btn("📜 Его вопросы", f"a:ai:log:0:{uid}")])
        tools = []
        if viewer is not None and has_perm(viewer, "users"):
            rows.append([btn("⚙️ Его настройки", f"a:us:{uid}:{back or ''}")])
        if viewer is not None and has_perm(viewer, "bc"):
            tools.append(btn("✅ В рассылке" if uid in await bc_picks(viewer) else "📌 В рассылку", f"a:bpick:{uid}:{back or ''}"))
        if viewer is not None and has_perm(viewer, "users"):
            tools.append(btn("🗑 Сообщения бота", f"a:umsg:{uid}:{back or ''}"))
        if tools:
            rows.append(tools)
        if viewer is not None and has_perm(viewer, "bans") and not is_admin(uid):
            rows.append([btn("❌ Удалить пользователя", f"a:udel:{uid}:{back or ''}")])
        if is_main(viewer):
            if not is_admin(uid):
                rows.append([btn("👮 Сделать админом", f"a:adm:mk:{uid}")])
            rows.append([btn("👁 Показать всем админам" if u["hidden"] else "🙈 Скрыть от других админов", f"a:hide:{uid}:{back or ''}")])
        if u["hidden"]:
            text = "🙈 <i>Скрыт: видите только вы</i>\n" + text
    else:
        kind_ru = "👥 Группа" if u["chat_type"] == "group" else "📢 Канал"
        owner = await POOL.fetchrow("SELECT full_name, username FROM users WHERE user_id = $1", u["owner_id"]) \
            if u["owner_id"] else None
        who = (esc(owner["full_name"] or "") + (f" @{esc(owner['username'])}" if owner and owner["username"] else "")) \
            if owner else "—"
        text = (f"<b>{kind_ru}: {esc(u['title'] or '—')}</b>\n🆔 <code>{uid}</code> · 👤 участников: {u['members'] or '—'}\n"
                f"🙋 Добавил: {who} (<code>{u['owner_id'] or '—'}</code>)\n"
                f"📅 Ежедневное расписание: {u['daily']}\n\n{common}\n"
                f"📅 Добавлен {fdt(u['created_at'])} UTC\n"
                f"{'🧱 Бот удалён из чата' if u['blocked'] else '✅ Бот в чате'}")
        if u["owner_id"]:
            rows.append([btn("👤 Кто добавил", f"a:card:{u['owner_id']}:{back or ''}")])
        if viewer is not None and has_perm(viewer, "users"):
            rows.append([btn("⚙️ Настройки чата", f"a:us:{uid}:{back or ''}")])
        if viewer is not None and has_perm(viewer, "bans"):
            rows.append([btn("❌ Удалить и выйти из чата", f"a:udel:{uid}:{back or ''}")])
    rows.append([btn("⬅️ Назад", back_cb(back))])
    return text, kb(*rows)


def search_where(query):
    q = query.strip()
    if q.lstrip("-").isdigit():
        return "user_id = $1", [int(q)]
    if q.startswith("@"):
        return "username ILIKE $1", [q[1:] + "%"]
    return "(full_name ILIKE $1 OR username ILIKE $1 OR city ILIKE $1 OR title ILIKE $1)", [f"%{q}%"]


async def screen_people(page, kind="users", query=None, viewer=None):
    """kind: users | search | chats"""
    if kind == "chats":
        where, args, title = "chat_type <> 'private'", [], "📢 <b>Группы и каналы</b>"
    elif kind == "search":
        w, args = search_where(query or "")
        where, title = w, f"🔎 <b>Поиск:</b> «{esc(query)}»"
    else:
        where, args, title = "chat_type = 'private'", [], "👥 <b>Пользователи</b>"
    if not is_main(viewer):
        where = f"({where}) AND NOT hidden"
    total = await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)
    pages = max(1, math.ceil(total / PAGE))
    page = max(0, min(page, pages - 1))
    rows = await POOL.fetch(
        f"SELECT user_id, full_name, username, city, banned, chat_type, title, members FROM users WHERE {where} "
        f"ORDER BY last_seen DESC NULLS LAST, created_at DESC LIMIT {PAGE} OFFSET {page * PAGE}", *args)
    token = {"users": "u", "search": "s", "chats": "c"}[kind] + str(page)
    buttons = []
    for r in rows:
        if r["chat_type"] == "private":
            label = "👤 " + person_label(r)
        else:
            label = ("👥 " if r["chat_type"] == "group" else "📢 ") + short(r["title"] or r["user_id"], 28) + \
                    (f" · {r['members']} уч." if r["members"] else "")
        buttons.append([btn(label, f"a:card:{r['user_id']}:{token}")])
    cb = {"users": "a:users:", "search": "a:usearch:", "chats": "a:chats:"}[kind]
    nav = []
    if page > 0:
        nav.append(btn("◀️", f"{cb}{page - 1}"))
    nav.append(btn(f"{page + 1} / {pages}", f"{cb}{page}"))
    if page < pages - 1:
        nav.append(btn("▶️", f"{cb}{page + 1}"))
    buttons.append(nav)
    buttons.append([btn("🔎 Поиск", "a:user"), btn("⬅️ Назад", "a:home")])
    text = f"{title}\nНайдено: <b>{total}</b>" + ("" if rows else "\n\nНичего не найдено.") + \
        ("\n\nНовые и активные — сверху. Нажмите, чтобы открыть профиль 👇" if rows else "")
    return text, kb(*buttons)


async def screen_admin_bans(viewer=None):
    rows = await POOL.fetch("SELECT user_id, city FROM users WHERE banned AND (NOT hidden OR $1) ORDER BY user_id LIMIT 20",
                            is_main(viewer))
    if not rows:
        text = "🚫 <b>Баны</b>\n\nСписок пуст.\n\nЧтобы забанить пользователя, найдите его через 🔎 Пользователь."
        return text, kb(ADMIN_BACK)
    text = "🚫 <b>Забаненные</b> (до 20)\n\nНажмите, чтобы разбанить 👇"
    buttons = [[btn(f"✅ {r['user_id']} · {r['city'] or '—'}", f"a:unban:{r['user_id']}")] for r in rows]
    return text, kb(*buttons, ADMIN_BACK)


async def screen_admin_health():
    t0 = _time.perf_counter()
    await POOL.fetchval("SELECT 1")
    db_ms = round((_time.perf_counter() - t0) * 1000)
    t1 = _time.perf_counter()
    try:
        await fetch_timings(KAABA[0], KAABA[1], datetime.utcnow().date(), 4, 0)
        api = f"✅ {round((_time.perf_counter() - t1) * 1000)} мс"
    except Exception as e:  # noqa: BLE001
        api = f"❌ {type(e).__name__}"
    c = await today_counters()
    active = await POOL.fetchval(
        "SELECT count(*) FROM users WHERE remind AND NOT blocked AND NOT banned AND tz IS NOT NULL")
    up = int(_time.time() - START_TS)
    d, rem = divmod(up, 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    errs = "\n".join(f"• <code>{e[0].strftime('%d.%m %H:%M')}</code> {esc(e[1])}" for e in list(ERRBUF)[-5:]) \
        or "— ошибок нет 🎉"
    text = (f"🩺 <b>Здоровье бота</b>\n\n"
            f"🗄 База данных: ✅ {db_ms} мс\n"
            f"🕌 API времён (Aladhan): {api}\n"
            f"⏱ Работает: {d} д {h} ч {m} мин\n"
            f"👥 Получают напоминания: {active}\n"
            f"🧠 Кэш времён: {len(CACHE)} записей\n"
            f"📬 Сегодня (UTC): отправлено {c.get('reminders_sent', 0)}, ошибок {c.get('reminders_failed', 0)}\n\n"
            f"<b>Последние ошибки</b>\n{errs}")
    return text, kb([btn("🔄 Обновить", "a:health")], ADMIN_BACK)


# ── broadcast ──

async def send_one(bot, uid, text, photo=None, markup=None):
    for _ in range(2):
        try:
            if photo is not None:
                m = await bot.send_photo(uid, photo, caption=text or None, parse_mode=ParseMode.HTML, reply_markup=markup)
            else:
                m = await bot.send_message(uid, text, parse_mode=ParseMode.HTML, reply_markup=markup)
            return "ok", m
        except Forbidden:
            await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", uid)
            return "blocked", None
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception:  # noqa: BLE001
            log.exception("broadcast send failed for %s", uid)
            return "fail", None
    return "fail", None


async def run_broadcast(app, chat_id, text, bc):
    app.bot_data["bc_running"] = True
    started = _time.time()
    sent = failed = blocked = 0
    try:
        where, args = bc_where(bc)
        rows = await POOL.fetch(f"SELECT user_id FROM users WHERE {where}", *args)
        ids = [r["user_id"] for r in rows]
        total = len(ids)
        progress = await app.bot.send_message(chat_id, f"📣 Отправка… 0 / {total}")
        photo = bc.get("photo")
        markup = InlineKeyboardMarkup([[InlineKeyboardButton(bc["button"][0], url=bc["button"][1])]]) \
            if bc.get("button") else None
        for i, uid in enumerate(ids, 1):
            res, sent_msg = await send_one(app.bot, uid, text, photo, markup)
            if res == "ok" and isinstance(photo, bytes) and sent_msg is not None and sent_msg.photo:
                photo = sent_msg.photo[-1].file_id  # upload once, then reuse
            if res == "ok":
                sent += 1
            elif res == "blocked":
                blocked += 1
                failed += 1
            else:
                failed += 1
            await asyncio.sleep(0.05)  # ~20 messages/second, under Telegram's limits
            if i % 100 == 0:
                try:
                    await progress.edit_text(f"📣 Отправка… {i} / {total}")
                except Exception:  # noqa: BLE001
                    pass
        secs = round(_time.time() - started)
        report = (f"✅ <b>Рассылка завершена</b>\n\n"
                  f"Кому: {bc_label(bc)}\n"
                  f"📬 Доставлено: <b>{sent}</b>\n"
                  f"❌ Не доставлено: <b>{failed}</b> (заблокировали бота: {blocked})\n"
                  f"⏱ Время: {secs} сек")
        await app.bot.send_message(chat_id, report, parse_mode=ParseMode.HTML, reply_markup=kb(ADMIN_BACK))
    except Exception:  # noqa: BLE001
        log.exception("broadcast crashed")
        await app.bot.send_message(chat_id, f"⚠️ Рассылка прервана. Отправлено: {sent}, ошибок: {failed}.")
    finally:
        app.bot_data["bc_running"] = False


# ── broadcast v2: any message, audiences, buttons, schedule, progress/stop, history, delete everywhere ──

BC_DAYS = {"active": "активные за {} дн.", "inactive": "неактивные {}+ дн.", "new": "новички за {} дн."}


def bc_where(bc):
    base = "lang IS NOT NULL AND NOT banned AND NOT blocked"
    k, v = bc["kind"], bc.get("value")
    if k == "everything":
        return base, []
    if k == "chats":
        return base + " AND chat_type <> 'private'", []
    base += " AND chat_type = 'private'"
    if k == "lang":
        return base + " AND lang = $1", [v]
    if k == "country":
        return base + " AND lower(country) = $1", [v]
    if k == "city":
        return base + " AND city ILIKE $1", [f"%{v}%"]
    if k == "active":
        return base + " AND last_seen > now() - make_interval(days => $1)", [int(v)]
    if k == "inactive":
        return base + " AND (last_seen IS NULL OR last_seen < now() - make_interval(days => $1))", [int(v)]
    if k == "new":
        return base + " AND created_at > now() - make_interval(days => $1)", [int(v)]
    if k == "remind":
        return base + " AND remind", []
    if k == "picked":
        return "user_id = ANY($1::bigint[]) AND NOT banned AND NOT blocked", [[int(x) for x in v]]
    return base, []


def bc_label(bc):
    k, v = bc["kind"], bc.get("value")
    if k == "lang":
        return f"язык {LANG_BUTTONS.get(v, v)}"
    if k == "country":
        return f"страна {flag(v)} {v.upper()}"
    if k == "city":
        return f"город «{v}»"
    if k in BC_DAYS:
        return BC_DAYS[k].format(v)
    return {"everything": "пользователи + группы и каналы", "chats": "только группы и каналы",
            "remind": "с включёнными напоминаниями", "picked": f"выбранные люди ({len(v or [])})"}.get(k, "все пользователи")


async def bc_count(bc):
    where, args = bc_where(bc)
    return await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)


async def bc_picks(admin):
    try:
        return [int(x) for x in json.loads(await kv_get(f"bcpick:{admin}", "[]") or "[]")]
    except ValueError:
        return []


async def screen_bc_menu(admin):
    n = len(await bc_picks(admin))
    sched = await POOL.fetchval("SELECT count(*) FROM broadcasts WHERE status = 'scheduled'")
    return "📣 <b>Рассылка</b>\n\nКому отправить?", kb(
        [btn("👥 Всем пользователям", "a:bc:all"), btn("👥📢 Всем + группы", "a:bc:everything")],
        [btn("📢 Только группы и каналы", "a:bc:chats")],
        [btn("🌐 По языку", "a:bc:lang"), btn("🌍 По стране", "a:bc:country"), btn("🏙 По городу", "a:bc:city")],
        [btn("🟢 Активные 7 дн.", "a:bc:active:7"), btn("🟢 Активные 30 дн.", "a:bc:active:30")],
        [btn("💤 Неактивные 30+ дн.", "a:bc:inactive:30"), btn("🆕 Новички 7 дн.", "a:bc:new:7")],
        [btn("🔔 С напоминаниями", "a:bc:remind"), btn(f"👤 Выбранным ({n})", "a:bc:picked")],
        [btn("📜 История", "a:bc:hist"), btn(f"🕓 Запланированные ({sched})", "a:bc:sched")],
        ADMIN_BACK)


async def ask_bc_text(update, ctx):
    bc = ctx.user_data["bc"]
    n = await bc_count(bc)
    ctx.user_data["admin_state"] = "bc_text"
    text = (f"✍️ <b>Сообщение для рассылки</b>\n\nКому: <b>{bc_label(bc)}</b> (получателей: <b>{n}</b>)\n\n"
            "Отправьте сюда любое сообщение: текст с оформлением, фото, видео, GIF, голосовое, кружок, документ. "
            "Оно уйдёт людям точно в таком виде.")
    await render(update, text, kb([btn("❌ Отмена", "a:bc")]))


def bc_markup(opts, lang):
    rows = [[InlineKeyboardButton(b[0], url=b[1])] for b in opts.get("buttons", [])]
    extra = []
    if opts.get("app") and WEBAPP_URL:
        extra.append(webapp_btn(t(lang, "btn_app"), "today"))
    if opts.get("times"):
        extra.append(btn(t(lang, "btn_times"), "m:times"))
    if extra:
        rows.append(extra)
    return InlineKeyboardMarkup(rows) if rows else None


async def screen_bc_builder(ctx):
    bc = ctx.user_data["bc"]
    o = bc.setdefault("opts", {})
    n = await bc_count(bc)
    btns = [f"🔗 {esc(b[0])}" for b in o.get("buttons", [])] + (["📱 Открыть приложение"] if o.get("app") else []) + \
           (["🕌 Время намаза"] if o.get("times") else [])
    text = (f"📣 <b>Рассылка готова</b>\n\n👥 Кому: <b>{bc_label(bc)}</b> — {n}\n"
            f"🔘 Кнопки: {', '.join(btns) if btns else 'нет'}\n"
            f"🔕 Без звука: {'да' if o.get('silent') else 'нет'} · 📌 Закрепить: {'да' if o.get('pin') else 'нет'}\n\n"
            "Сначала можно отправить превью себе 👇")
    rows = [[btn("🔗 + Кнопка-ссылка", "a:bcd:url"), btn(("✅ " if o.get("app") else "➕ ") + "Приложение", "a:bcd:app")],
            [btn(("✅ " if o.get("times") else "➕ ") + "Время намаза", "a:bcd:times")]
            + ([btn("🧹 Убрать кнопки", "a:bcd:clr")] if btns else []),
            [btn(("🔕 Без звука ✅" if o.get("silent") else "🔔 Со звуком"), "a:bcd:silent"),
             btn(("📌 Закрепить ✅" if o.get("pin") else "📌 Не закреплять"), "a:bcd:pin")],
            [btn("👁 Превью себе", "a:bcd:test"), btn("✏️ Другое сообщение", "a:bcd:msg")],
            [btn("🕓 Запланировать", "a:bcd:when"), btn(f"✅ Отправить ({n})", "a:bcd:go")],
            [btn("❌ Отмена", "a:bc")]]
    return text, kb(*rows)


async def bc_got_message(update, ctx):
    """The admin sent the message to broadcast (any type)."""
    msg = update.message
    if msg.media_group_id:
        if ctx.user_data.get("bc_mg") == msg.media_group_id:
            return
        ctx.user_data["bc_mg"] = msg.media_group_id
        await msg.reply_text("ℹ️ Альбомы рассылаются только первым файлом. Лучше отправьте одно фото или видео с подписью.")
    ctx.user_data.pop("admin_state", None)
    ctx.user_data["bc"]["src"] = [msg.chat_id, msg.message_id]
    text, markup = await screen_bc_builder(ctx)
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)


def bc_parse_when(raw, tz):
    """"18:30" (today, or tomorrow if passed) or "17.11 18:30" / "17.11.2026 18:30", in the admin's time."""
    now = datetime.now(ZoneInfo(tz))
    m = re.match(r"^\s*(?:(\d{1,2})\.(\d{1,2})(?:\.(\d{2,4}))?\s+)?(\d{1,2})[:.](\d{2})\s*$", raw)
    if not m:
        return None
    d, mo, y, h, mi = m.groups()
    try:
        if d:
            y = int(y) + (2000 if y and len(y) == 2 else 0) if y else now.year
            when = datetime(y, int(mo), int(d), int(h), int(mi), tzinfo=ZoneInfo(tz))
        else:
            when = now.replace(hour=int(h), minute=int(mi), second=0, microsecond=0)
            if when <= now:
                when += timedelta(days=1)
    except ValueError:
        return None
    return when if when > now else None


async def bc_save(admin, bc, status, run_at=None):
    return await POOL.fetchval(
        "INSERT INTO broadcasts (admin_id, audience, label, src_chat, src_msg, opts, status, run_at) "
        "VALUES ($1, $2, $3, $4, $5, $6, $7, $8) RETURNING id",
        admin, json.dumps({"kind": bc["kind"], "value": bc.get("value")}), bc_label(bc), bc["src"][0], bc["src"][1],
        json.dumps(bc.get("opts", {}), ensure_ascii=False), status, run_at)


def bc_start(app, bc_id):
    task = asyncio.create_task(run_bc(app, bc_id))
    tasks = app.bot_data.setdefault("tasks", set())
    tasks.add(task)
    task.add_done_callback(tasks.discard)


async def log_sent(user_id, message_id, kind, preview="", bc_id=None):
    try:
        return await POOL.fetchval("INSERT INTO sent_msgs (bc_id, user_id, message_id, kind, preview) VALUES ($1, $2, $3, $4, $5) "
                                   "RETURNING id", bc_id, user_id, message_id, kind, preview[:80])
    except Exception:  # noqa: BLE001
        log.exception("log sent failed")


async def run_bc(app, bc_id):
    if app.bot_data.get("bc_running"):
        return
    app.bot_data["bc_running"] = bc_id
    app.bot_data.pop("bc_stop", None)
    row = await POOL.fetchrow("SELECT * FROM broadcasts WHERE id = $1", bc_id)
    admin = row["admin_id"]
    aud, opts = json.loads(row["audience"]), json.loads(row["opts"] or "{}")
    sent = failed = blocked = 0
    status = "done"
    try:
        where, args = bc_where(aud)
        people = await POOL.fetch(f"SELECT user_id, lang FROM users WHERE {where}", *args)
        total = len(people)
        await POOL.execute("UPDATE broadcasts SET status = 'running', total = $2, started_at = now() WHERE id = $1", bc_id, total)
        stop_kb = kb([btn("⏹ Остановить", f"a:bcx:stop:{bc_id}")])
        progress = await app.bot.send_message(admin, f"📣 Рассылка #{bc_id}: 0 / {total}", reply_markup=stop_kb)
        markups = {}
        for i, p in enumerate(people, 1):
            if app.bot_data.get("bc_stop") == bc_id:
                status = "stopped"
                break
            lang = p["lang"] or "en"
            if lang not in markups:
                markups[lang] = bc_markup(opts, lang)
            for attempt in range(2):
                try:
                    m = await app.bot.copy_message(p["user_id"], row["src_chat"], row["src_msg"], reply_markup=markups[lang],
                                                   disable_notification=bool(opts.get("silent")))
                    sent += 1
                    await log_sent(p["user_id"], m.message_id, "bc", f"рассылка #{bc_id}", bc_id)
                    if opts.get("pin"):
                        try:
                            await app.bot.pin_chat_message(p["user_id"], m.message_id, disable_notification=True)
                        except Exception:  # noqa: BLE001
                            pass
                    break
                except Forbidden:
                    blocked += 1
                    failed += 1
                    await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", p["user_id"])
                    break
                except RetryAfter as e:
                    await asyncio.sleep(e.retry_after + 1)
                except BadRequest as e:
                    if "not found" in str(e).lower() and "message" in str(e).lower() and sent == 0:
                        raise RuntimeError("исходное сообщение удалено — рассылка невозможна") from e
                    failed += 1
                    break
                except Exception:  # noqa: BLE001
                    log.exception("broadcast copy failed for %s", p["user_id"])
                    failed += 1
                    break
            await asyncio.sleep(0.045)
            if i % 50 == 0:
                await POOL.execute("UPDATE broadcasts SET sent = $2, failed = $3, blocked = $4 WHERE id = $1",
                                   bc_id, sent, failed, blocked)
                try:
                    await progress.edit_text(f"📣 Рассылка #{bc_id}: {i} / {total}", reply_markup=stop_kb)
                except Exception:  # noqa: BLE001
                    pass
        try:
            await progress.delete()
        except Exception:  # noqa: BLE001
            pass
        report = (f"{'⏹ Остановлена' if status == 'stopped' else '✅ Завершена'} <b>рассылка #{bc_id}</b>\n\n"
                  f"Кому: {esc(row['label'])}\n📬 Доставлено: <b>{sent}</b>\n"
                  f"❌ Не доставлено: <b>{failed}</b> (заблокировали бота: {blocked})")
        await app.bot.send_message(admin, report, parse_mode=ParseMode.HTML,
                                   reply_markup=kb([btn("🗑 Удалить у всех", f"a:bcx:del:{bc_id}"), btn("📜 История", "a:bc:hist")],
                                                   ADMIN_BACK))
    except Exception as e:  # noqa: BLE001
        status = "failed"
        log.exception("broadcast %s crashed", bc_id)
        try:
            await app.bot.send_message(admin, f"⚠️ Рассылка #{bc_id} прервана: {esc(e)}\nОтправлено: {sent}.", parse_mode=ParseMode.HTML)
        except Exception:  # noqa: BLE001
            pass
    finally:
        await POOL.execute("UPDATE broadcasts SET status = $2, sent = $3, failed = $4, blocked = $5, finished_at = now() "
                           "WHERE id = $1", bc_id, status, sent, failed, blocked)
        app.bot_data["bc_running"] = False


async def delete_sent(bot, rows):
    ok = gone = 0
    for r in rows:
        try:
            await bot.delete_message(r["user_id"], r["message_id"])
            ok += 1
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception:  # noqa: BLE001
            gone += 1
        await POOL.execute("UPDATE sent_msgs SET deleted = TRUE WHERE id = $1", r["id"])
        await asyncio.sleep(0.04)
    return ok, gone


async def run_bc_delete(app, bc_id, admin):
    rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE bc_id = $1 AND NOT deleted "
                            "AND at > now() - interval '48 hours'", bc_id)
    note = await app.bot.send_message(admin, f"🗑 Удаляю рассылку #{bc_id} у {len(rows)} получателей…")
    ok, gone = await delete_sent(app.bot, rows)
    await POOL.execute("UPDATE broadcasts SET status = 'deleted' WHERE id = $1", bc_id)
    try:
        await note.edit_text(f"🗑 Рассылка #{bc_id} удалена у <b>{ok}</b> получателей." + (f" Не удалось: {gone}." if gone else ""),
                             parse_mode=ParseMode.HTML, reply_markup=kb(ADMIN_BACK))
    except Exception:  # noqa: BLE001
        pass


async def bc_scheduler(context):
    """Starts scheduled broadcasts when their time comes."""
    app = context.application
    if app.bot_data.get("bc_running"):
        return
    bc_id = await POOL.fetchval("SELECT id FROM broadcasts WHERE status = 'scheduled' AND run_at <= now() ORDER BY run_at LIMIT 1")
    if bc_id:
        await POOL.execute("UPDATE broadcasts SET status = 'queued' WHERE id = $1", bc_id)
        bc_start(app, bc_id)


BC_ST = {"done": "✅", "stopped": "⏹", "failed": "⚠️", "deleted": "🗑", "running": "⏳", "scheduled": "🕓", "queued": "⏳",
         "cancelled": "✖️"}


async def admin_bc(update, ctx, parts):
    """a:bc:… (audience and lists), a:bcd:… (draft), a:bcx:… (running/history actions)."""
    admin = update.effective_user.id
    sub = parts[1]
    what = parts[2] if len(parts) > 2 else "menu"
    app = ctx.application
    if sub == "bc":
        if what == "menu":
            text, markup = await screen_bc_menu(admin)
            return await render(update, text, markup)
        if what in ("all", "everything", "chats", "remind"):
            ctx.user_data["bc"] = {"kind": what, "value": None}
            return await ask_bc_text(update, ctx)
        if what in BC_DAYS and len(parts) > 3 and parts[3].isdigit():
            ctx.user_data["bc"] = {"kind": what, "value": int(parts[3])}
            return await ask_bc_text(update, ctx)
        if what == "lang":
            rows = [[btn(LANG_BUTTONS["en"], "a:bcl:en"), btn(LANG_BUTTONS["ru"], "a:bcl:ru")],
                    [btn(LANG_BUTTONS["uz"], "a:bcl:uz"), btn(LANG_BUTTONS["uzc"], "a:bcl:uzc")],
                    [btn(LANG_BUTTONS["tg"], "a:bcl:tg"), btn(LANG_BUTTONS["ar"], "a:bcl:ar")], [btn("⬅️ Назад", "a:bc")]]
            return await render(update, "🌐 <b>Выберите язык получателей</b>", kb(*rows))
        if what == "country":
            ctx.user_data["admin_state"] = "bc_country"
            return await render(update, "🌍 <b>Страна получателей</b>\n\nОтправьте двухбуквенный код страны, например: "
                                        "<code>uz</code>, <code>ru</code>, <code>tj</code>, <code>sa</code>.", kb([btn("⬅️ Назад", "a:bc")]))
        if what == "city":
            ctx.user_data["admin_state"] = "bc_city"
            return await render(update, "🏙 <b>Город получателей</b>\n\nОтправьте название города (или его часть), "
                                        "например: <code>Ташкент</code> или <code>Toshkent</code>.", kb([btn("⬅️ Назад", "a:bc")]))
        if what == "picked":
            if len(parts) > 3 and parts[3] == "use":
                picks = await bc_picks(admin)
                if not picks:
                    return await update.callback_query.answer("Список пуст", show_alert=True)
                ctx.user_data["bc"] = {"kind": "picked", "value": picks}
                return await ask_bc_text(update, ctx)
            if len(parts) > 3 and parts[3] == "clr":
                await kv_set(f"bcpick:{admin}", "[]")
            picks = await bc_picks(admin)
            ctx.user_data["admin_state"] = "bc_pick"
            names = [esc(await admin_name(x)) for x in picks[:15]]
            text = ("👤 <b>Рассылка выбранным людям</b>\n\n"
                    "Отправьте список ID или @username — через пробел или каждый с новой строки.\n"
                    "Или отмечайте людей кнопкой «📌 В рассылку» в их карточке (Пользователи → человек).\n\n"
                    f"Сейчас отмечено: <b>{len(picks)}</b>" + (("\n" + "\n".join("• " + x for x in names)) if names else "")
                    + ("\n…" if len(picks) > 15 else ""))
            rows = ([[btn(f"✅ Отправить отмеченным ({len(picks)})", "a:bc:picked:use")], [btn("🧹 Очистить", "a:bc:picked:clr")]]
                    if picks else []) + [[btn("⬅️ Назад", "a:bc")]]
            return await render(update, text, kb(*rows))
        if what == "hist":
            rows = await POOL.fetch("SELECT * FROM broadcasts ORDER BY id DESC LIMIT 10")
            lines = ["📜 <b>История рассылок</b>", ""]
            kbrows = []
            for r in rows:
                when = r["finished_at"] or r["run_at"] or r["created_at"]
                lines.append(f"{BC_ST.get(r['status'], '•')} <b>#{r['id']}</b> · {fdt(when)} UTC · {esc(r['label'])}\n"
                             f"    📬 {r['sent'] or 0} / {r['total'] or '—'} · ❌ {r['failed'] or 0}")
                if r["status"] in ("done", "stopped") and r["sent"] and r["finished_at"] and \
                        r["finished_at"] > datetime.now(ZoneInfo("UTC")) - timedelta(hours=48):
                    kbrows.append([btn(f"🗑 Удалить #{r['id']} у всех", f"a:bcx:del:{r['id']}")])
            if not rows:
                lines.append("Пока пусто.")
            return await render(update, "\n".join(lines), kb(*kbrows, [btn("⬅️ Назад", "a:bc")]))
        if what == "sched":
            rows = await POOL.fetch("SELECT * FROM broadcasts WHERE status = 'scheduled' ORDER BY run_at")
            me = await get_user(admin)
            tz = (me or {}).get("tz") or "Asia/Tashkent"
            lines = ["🕓 <b>Запланированные рассылки</b>", ""] + \
                [f"• <b>#{r['id']}</b> · {r['run_at'].astimezone(ZoneInfo(tz)):%d.%m %H:%M} · {esc(r['label'])}" for r in rows]
            if not rows:
                lines.append("Нет запланированных.")
            kbrows = [[btn(f"👁 #{r['id']}", f"a:bcx:show:{r['id']}"), btn(f"✖️ Отменить #{r['id']}", f"a:bcx:cancel:{r['id']}")]
                      for r in rows]
            return await render(update, "\n".join(lines), kb(*kbrows, [btn("⬅️ Назад", "a:bc")]))
        text, markup = await screen_bc_menu(admin)
        return await render(update, text, markup)

    if sub == "bcd":
        bc = ctx.user_data.get("bc")
        if not bc or not bc.get("src"):
            return await render(update, "⚠️ Черновик рассылки не найден. Начните заново.", kb([btn("📣 Рассылка", "a:bc")]))
        o = bc.setdefault("opts", {})
        if what in ("app", "times", "silent", "pin"):
            o[what] = not o.get(what)
        elif what == "clr":
            o.update(buttons=[], app=False, times=False)
        elif what == "url":
            ctx.user_data["admin_state"] = "bc_btn"
            return await render(update, "🔗 <b>Кнопки-ссылки</b>\n\nОтправьте кнопки, каждую с новой строки, в виде:\n"
                                        "<code>Текст кнопки | https://ссылка</code>\n\nНапример:\n"
                                        "<code>📖 Читать статью | https://example.com</code>", kb([btn("⬅️ Назад", "a:bcd:back")]))
        elif what == "msg":
            return await ask_bc_text(update, ctx)
        elif what == "test":
            try:
                await ctx.bot.copy_message(admin, bc["src"][0], bc["src"][1], reply_markup=bc_markup(o, "ru"),
                                           disable_notification=bool(o.get("silent")))
            except Exception as e:  # noqa: BLE001
                await update.effective_chat.send_message(f"⚠️ Не получилось: {esc(e)}", parse_mode=ParseMode.HTML)
            text, markup = await screen_bc_builder(ctx)
            return await update.effective_chat.send_message("👆 Так увидят люди.\n\n" + text, parse_mode=ParseMode.HTML,
                                                            reply_markup=markup)
        elif what == "when":
            ctx.user_data["admin_state"] = "bc_when"
            me = await get_user(admin)
            tz = (me or {}).get("tz") or "Asia/Tashkent"
            return await render(update, f"🕓 <b>Когда отправить?</b>\n\nВремя по {esc(tz)}. Отправьте:\n"
                                        "<code>18:30</code> — сегодня (или завтра, если время прошло)\n"
                                        "<code>20.11 09:00</code> — в конкретный день", kb([btn("⬅️ Назад", "a:bcd:back")]))
        elif what == "go":
            if app.bot_data.get("bc_running"):
                return await update.callback_query.answer("⏳ Сейчас идёт другая рассылка. Подождите или остановите её.",
                                                          show_alert=True)
            bc_id = await bc_save(admin, bc, "queued")
            ctx.user_data.pop("bc", None)
            await render(update, f"🚀 Рассылка #{bc_id} запущена. Прогресс и кнопка «Остановить» — в следующем сообщении.",
                         kb(ADMIN_BACK))
            return bc_start(app, bc_id)
        text, markup = await screen_bc_builder(ctx)
        return await render(update, text, markup)

    if sub == "bcx" and len(parts) > 3 and parts[3].isdigit():
        bc_id = int(parts[3])
        if what == "stop":
            app.bot_data["bc_stop"] = bc_id
            return await update.callback_query.answer("⏹ Останавливаю…")
        if what == "cancel":
            await POOL.execute("UPDATE broadcasts SET status = 'cancelled' WHERE id = $1 AND status = 'scheduled'", bc_id)
            return await admin_bc(update, ctx, ["a", "bc", "sched"])
        if what == "show":
            r = await POOL.fetchrow("SELECT * FROM broadcasts WHERE id = $1", bc_id)
            if r:
                try:
                    await ctx.bot.copy_message(admin, r["src_chat"], r["src_msg"], reply_markup=bc_markup(json.loads(r["opts"]), "ru"))
                except Exception as e:  # noqa: BLE001
                    await update.effective_chat.send_message(f"⚠️ {esc(e)}", parse_mode=ParseMode.HTML)
            return
        if what == "del":
            n = await POOL.fetchval("SELECT count(*) FROM sent_msgs WHERE bc_id = $1 AND NOT deleted AND at > now() - interval '48 hours'",
                                    bc_id)
            return await render(update, f"🗑 Удалить рассылку #{bc_id} у всех получателей ({n})?\n\n"
                                        "Telegram позволяет удалять сообщения не старше 48 часов.",
                                kb([btn("🗑 Да, удалить", f"a:bcx:delok:{bc_id}"), btn("⬅️ Нет", "a:bc:hist")]))
        if what == "delok":
            task = asyncio.create_task(run_bc_delete(app, bc_id, admin))
            app.bot_data.setdefault("tasks", set()).add(task)
            return await render(update, f"🗑 Удаляю рассылку #{bc_id}…", kb(ADMIN_BACK))
    text, markup = await screen_bc_menu(admin)
    return await render(update, text, markup)


async def admin_bc_text(update, ctx, state):
    """Typed answers for the broadcast. Returns True if consumed."""
    msg = update.message
    raw = (msg.text or "").strip()
    admin = update.effective_user.id
    back = kb([btn("📣 Рассылка", "a:bc")])
    if state == "bc_city":
        ctx.user_data.pop("admin_state", None)
        ctx.user_data["bc"] = {"kind": "city", "value": raw[:60]}
        await ask_bc_text(update, ctx)
        return True
    if state == "bc_pick":
        ids, missing = [], []
        for tok in re.split(r"[\s,;]+", raw):
            if not tok:
                continue
            who = await find_user_id(tok)
            if who and await get_user(who):
                ids.append(who)
            else:
                missing.append(tok)
        ids = list(dict.fromkeys(ids))
        if not ids:
            await msg.reply_text("🤷 Никого не нашёл. Проверьте ID или @username.", reply_markup=back)
            return True
        ctx.user_data.pop("admin_state", None)
        ctx.user_data["bc"] = {"kind": "picked", "value": ids}
        if missing:
            await msg.reply_text("⚠️ Не найдены: " + ", ".join(missing[:20]))
        await ask_bc_text(update, ctx)
        return True
    if state == "bc_btn":
        bc = ctx.user_data.get("bc")
        if not bc:
            return False
        good = []
        for line in raw.splitlines():
            if "|" in line:
                a, b = (x.strip() for x in line.split("|", 1))
                if a and re.match(r"^(https?://|tg://)\S+$", b):
                    good.append([a[:60], b[:500]])
        if not good:
            await msg.reply_text("❗ Не понял. Пример: <code>Открыть | https://example.com</code>", parse_mode=ParseMode.HTML)
            return True
        ctx.user_data.pop("admin_state", None)
        bc.setdefault("opts", {}).setdefault("buttons", []).extend(good[:6])
        text, markup = await screen_bc_builder(ctx)
        await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        return True
    if state == "bc_when":
        bc = ctx.user_data.get("bc")
        if not bc:
            return False
        me = await get_user(admin)
        tz = (me or {}).get("tz") or "Asia/Tashkent"
        when = bc_parse_when(raw, tz)
        if not when:
            await msg.reply_text("❗ Не понял время. Пример: <code>18:30</code> или <code>20.11 09:00</code>", parse_mode=ParseMode.HTML)
            return True
        ctx.user_data.pop("admin_state", None)
        bc_id = await bc_save(admin, bc, "scheduled", when)
        ctx.user_data.pop("bc", None)
        await msg.reply_text(f"🕓 Рассылка #{bc_id} запланирована на <b>{when:%d.%m.%Y %H:%M}</b> ({esc(tz)}).\n"
                             "Отменить можно в «📣 Рассылка → 🕓 Запланированные».", parse_mode=ParseMode.HTML,
                             reply_markup=kb([btn("🕓 Запланированные", "a:bc:sched")], ADMIN_BACK))
        return True
    return False


# ── deleting a bot message for a person, deleting a person ──

async def screen_user_msgs(uid, back):
    rows = await POOL.fetch("SELECT * FROM sent_msgs WHERE user_id = $1 AND NOT deleted AND at > now() - interval '7 days' "
                            "ORDER BY id DESC LIMIT 10", uid)
    lines = [f"🗑 <b>Сообщения бота для</b> {esc(await admin_name(uid))}", "",
             "Последние рассылки и сообщения от админов. Удалить можно сообщения не старше 48 часов.", ""]
    kbrows, cur = [], []
    fresh = datetime.now(ZoneInfo("UTC")) - timedelta(hours=48)
    for k, r in enumerate(rows, 1):
        ok = r["at"] > fresh
        lines.append(f"{k}. {fdt(r['at'])} UTC · {esc(r['preview'] or r['kind'])}" + ("" if ok else " · ⌛ старше 48 ч"))
        if ok:
            cur.append(btn(f"🗑 {k}", f"a:umdel:{uid}:{r['id']}:{back or ''}"))
            if len(cur) == 5:
                kbrows.append(cur)
                cur = []
    if cur:
        kbrows.append(cur)
    if not rows:
        lines.append("Пока нет сообщений.")
    elif any(r["at"] > fresh for r in rows):
        kbrows.append([btn("🗑 Удалить все (до 48 ч)", f"a:umdelall:{uid}:{back or ''}")])
    kbrows.append([btn("⬅️ К карточке", f"a:card:{uid}:{back or ''}")])
    return "\n".join(lines), kb(*kbrows)


async def wipe_user(bot, uid, ban):
    """Deletes everything the bot keeps about a person (sales stay in the sales log). With ban: keeps a banned stub."""
    tables = await POOL.fetch("SELECT table_name FROM information_schema.columns WHERE column_name = 'user_id' "
                              "AND table_schema = current_schema() AND table_name NOT IN ('users', 'payments', 'admins', 'sent_msgs')")
    for r in tables:
        try:
            await POOL.execute(f'DELETE FROM "{r["table_name"]}" WHERE user_id = $1', uid)
        except Exception:  # noqa: BLE001
            log.exception("wipe %s failed", r["table_name"])
    await POOL.execute("DELETE FROM sent_msgs WHERE user_id = $1", uid)
    u = await get_user(uid)
    if u and u["chat_type"] != "private":
        try:
            await bot.leave_chat(uid)
        except Exception:  # noqa: BLE001
            pass
    if ban:
        await POOL.execute("UPDATE users SET banned = TRUE, remind = FALSE, city = NULL, lat = NULL, lon = NULL, tz = NULL, "
                           "country = NULL, onboarded = FALSE WHERE user_id = $1", uid)
    else:
        await POOL.execute("DELETE FROM users WHERE user_id = $1", uid)


async def admin_people_tools(update, ctx, parts):
    """a:bpick / a:umsg / a:umdel / a:umdelall / a:umdelp / a:udel / a:udelok."""
    admin = update.effective_user.id
    sub = parts[1]
    uid = int(parts[2]) if len(parts) > 2 and parts[2].lstrip("-").isdigit() else 0
    if not uid:
        return
    if sub == "bpick":
        picks = await bc_picks(admin)
        picks = [x for x in picks if x != uid] if uid in picks else picks + [uid]
        await kv_set(f"bcpick:{admin}", json.dumps(picks))
        await update.callback_query.answer(("📌 Добавлен в рассылку" if uid in picks else "Убран из рассылки") + f" ({len(picks)})")
        card = await user_card(uid, parts[3] if len(parts) > 3 and parts[3] else None, viewer=admin)
        if card:
            return await render(update, card[0], card[1])
        return
    if sub == "umsg":
        text, markup = await screen_user_msgs(uid, parts[3] if len(parts) > 3 else "")
        return await render(update, text, markup)
    if sub in ("umdel", "umdelall", "umdelp"):
        if sub == "umdel" and len(parts) > 3 and parts[3].isdigit():
            rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE id = $1 AND user_id = $2", int(parts[3]), uid)
            bk = parts[4] if len(parts) > 4 else ""
        elif sub == "umdelp":  # right after an admin's message: both the header and the message
            ids = [int(x) for x in parts[3:] if x.isdigit()]
            rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE id = ANY($1::int[]) AND user_id = $2", ids, uid)
            bk = None
        elif sub == "umdelall":
            rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE user_id = $1 AND NOT deleted "
                                    "AND at > now() - interval '48 hours'", uid)
            bk = parts[3] if len(parts) > 3 else ""
        else:
            text, markup = await screen_user_msgs(uid, "")
            return await render(update, text, markup)
        ok, gone = await delete_sent(ctx.bot, rows)
        await update.callback_query.answer(f"🗑 Удалено: {ok}" + (f", не удалось: {gone}" if gone else ""), show_alert=bool(gone))
        if bk is None:
            try:
                await update.callback_query.edit_message_reply_markup(None)
            except Exception:  # noqa: BLE001
                pass
            return
        text, markup = await screen_user_msgs(uid, bk)
        return await render(update, text, markup)
    if sub == "udel":
        if is_admin(uid):
            return await update.callback_query.answer("Админа удалить нельзя — сначала снимите права.", show_alert=True)
        bk = parts[3] if len(parts) > 3 else ""
        return await render(update, f"❌ <b>Удалить {esc(await admin_name(uid))}?</b>\n\n"
                                    "Сотрутся все данные: настройки, город, трекер, история ИИ, купленные вопросы. "
                                    "Журнал продаж останется.\n\n"
                                    "• <b>Удалить</b> — если он снова нажмёт /start, начнёт с нуля.\n"
                                    "• <b>Удалить и забанить</b> — бот больше не будет ему отвечать.",
                            kb([btn("🗑 Удалить", f"a:udelok:{uid}:d")], [btn("🗑🚫 Удалить и забанить", f"a:udelok:{uid}:b")],
                               [btn("⬅️ Отмена", f"a:card:{uid}:{bk}")]))
    if sub == "udelok" and len(parts) > 3 and not is_admin(uid):
        name = await admin_name(uid)
        await wipe_user(ctx.bot, uid, parts[3] == "b")
        return await render(update, f"✅ {esc(name)} удалён" + (" и забанен." if parts[3] == "b" else "."), kb(ADMIN_BACK))


# ── router ──

ADMIN_PERM_OF = {"stats": "stats", "geo": "stats", "health": "health", "test": "health", "bans": "bans", "ban": "bans",
                 "unban": "bans", "azan": "azan", "card": "users", "users": "users", "usearch": "users", "chats": "users",
                 "user": "users", "export": "export", "bc": "bc", "bcl": "bc", "adm": "main", "ai": "ai",
                 "grant": "ai", "hide": "main", "hidden": "main", "ayrm": "main", "bcd": "bc", "bcx": "bc", "bpick": "bc",
                 "umsg": "users", "umdel": "users", "umdelall": "users", "umdelp": "users", "udel": "bans", "udelok": "bans",
                 "bset": "main", "us": "users", "uso": "users", "usset": "users", "uspm": "users", "usc": "users"}


async def admin_router(update: Update, ctx: ContextTypes.DEFAULT_TYPE, parts):
    ctx.user_data.pop("admin_state", None)
    sub = parts[1] if len(parts) > 1 else "home"
    uid = update.effective_user.id

    need = ADMIN_PERM_OF.get(sub)
    if need == "main" and not is_main(uid) or need not in (None, "main") and not has_perm(uid, need):
        text, markup = await screen_admin_home(uid)
        return await render(update, "🔒 <b>Нет доступа к этому разделу.</b>\n\n" + text, markup)
    if sub == "adm":
        return await admin_admins(update, ctx, parts)
    if sub == "ai":
        return await admin_ai(update, ctx, parts)
    if sub == "grant" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        ctx.user_data["admin_state"] = f"ai_grant:{parts[2]}"
        return await render(update, AI_ASK["grant"], kb([btn("⬅️ Назад", f"a:card:{parts[2]}")]))
    if sub == "ayrm" and len(parts) > 2:  # remove an ayah added automatically
        ref = parts[2].replace(".", ":")
        await POOL.execute("UPDATE ayah_pool SET removed = TRUE WHERE ref = $1", ref)
        await load_ayah_pool()
        return await update.effective_chat.send_message(f"🗑 Аят {esc(ref)} убран. Осталось аятов: {len(AYAH_POOL)}.")
    if sub == "hide" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        await POOL.execute("UPDATE users SET hidden = NOT hidden WHERE user_id = $1", int(parts[2]))
        card = await user_card(int(parts[2]), parts[3] if len(parts) > 3 and parts[3] else None, viewer=uid)
        if card:
            return await render(update, card[0], card[1])
    if sub == "hidden":
        rows = await POOL.fetch("SELECT user_id, full_name, username, title, chat_type FROM users WHERE hidden ORDER BY user_id LIMIT 40")
        text = "🙈 <b>Скрытые</b>\n\nИх видите только вы. Другие админы не видят их нигде." + ("" if rows else "\n\nПока никого.")
        return await render(update, text, kb(*[[btn("🙈 " + (r["full_name"] or r["title"] or str(r["user_id"]))[:40],
                                                    f"a:card:{r['user_id']}:h")] for r in rows], ADMIN_BACK))
    if sub == "home":
        ctx.user_data.pop("bc", None)
        text, markup = await screen_admin_home(uid)
        return await render(update, text, markup)
    if sub == "stats":
        text, markup = await screen_admin_stats()
        return await render(update, text, markup)
    if sub == "geo":
        text, markup = await screen_admin_geo()
        return await render(update, text, markup)
    if sub == "health":
        text, markup = await screen_admin_health()
        return await render(update, text, markup)
    if sub == "bans":
        text, markup = await screen_admin_bans(uid)
        return await render(update, text, markup)
    if sub == "azan":
        if len(parts) > 2 and parts[2] == "add":
            await admin_azan(update, ctx, parts)
            ctx.user_data["admin_state"] = "azan"  # set after the router's reset above
            return
        return await admin_azan(update, ctx, parts)

    if sub == "card" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        back = parts[3] if len(parts) > 3 else None
        card = await user_card(int(parts[2]), back, viewer=uid)
        if not card:
            return await update.effective_chat.send_message("🤷 Такого пользователя нет в базе.")
        if back:  # opened from a list: show in place
            return await render(update, card[0], card[1])
        return await update.effective_chat.send_message(card[0], parse_mode=ParseMode.HTML, reply_markup=card[1])

    if sub in ("users", "usearch", "chats"):
        page = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
        kind = {"users": "users", "usearch": "search", "chats": "chats"}[sub]
        text, markup = await screen_people(page, kind, ctx.user_data.get("user_q"), viewer=uid)
        return await render(update, text, markup)

    if sub == "user":
        ctx.user_data["admin_state"] = "search"
        return await render(update, "🔎 <b>Поиск</b>\n\nОтправьте имя, @username, Telegram ID, город или название группы.",
                            kb(ADMIN_BACK))

    if sub in ("ban", "unban") and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        target = int(parts[2])
        if is_admin(target):
            return await render(update, "😅 Себя забанить нельзя.", kb(ADMIN_BACK))
        await POOL.execute("UPDATE users SET banned = $2 WHERE user_id = $1", target, sub == "ban")
        card = await user_card(target, parts[3] if len(parts) > 3 else None, viewer=uid)
        if card:
            return await render(update, card[0], card[1])
        return await render(update, "Пользователь не найден.", kb(ADMIN_BACK))

    if sub == "test":
        u = await get_user(uid) or {}
        lang = u.get("lang") or "ru"
        lead = u.get("lead_min", DEFAULT_LEAD)
        tz = ZoneInfo(u["tz"]) if u.get("tz") else ZoneInfo("UTC")
        when = (datetime.now(tz) + timedelta(minutes=lead)).strftime("%H:%M")
        body = t(lang, "rem_std_n" if lead == 0 else "rem_std_b", name=PN[lang]["fajr"], n=lead, time=when)
        await update.effective_chat.send_message(
            "🧪 <i>Тестовое напоминание</i>\n\n" + body, parse_mode=ParseMode.HTML,
            reply_markup=kb([btn(t(lang, "btn_menu"), "m:home")]))
        return

    if sub == "export":
        rows = await POOL.fetch(f"SELECT {', '.join(CSV_COLUMNS)} FROM users WHERE NOT hidden OR $1 ORDER BY created_at", is_main(uid))
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(CSV_COLUMNS)
        for r in rows:
            w.writerow([r[c] for c in CSV_COLUMNS])
        data = io.BytesIO(buf.getvalue().encode("utf-8-sig"))  # BOM so Excel opens Cyrillic/Arabic correctly
        name = f"users_{datetime.utcnow():%Y%m%d_%H%M}.csv"
        await update.effective_chat.send_document(document=data, filename=name,
                                                  caption=f"📤 Пользователей: {len(rows)}")
        return

    if sub in ("bc", "bcd", "bcx"):
        return await admin_bc(update, ctx, parts)
    if sub in ("bpick", "umsg", "umdel", "umdelall", "umdelp", "udel", "udelok"):
        return await admin_people_tools(update, ctx, parts)
    if sub == "bset":
        return await admin_bset(update, ctx, parts)
    if sub in ("us", "uso", "usset", "uspm", "usc"):
        return await admin_user_settings(update, ctx, parts)

    if sub == "bcl" and len(parts) > 2 and parts[2] in LANGS:
        ctx.user_data["bc"] = {"kind": "lang", "value": parts[2], "text": None}
        return await ask_bc_text(update, ctx)

    text, markup = await screen_admin_home(uid)
    await render(update, text, markup)


async def admin_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handles the admin's typed answers. Returns True if the message was consumed."""
    state = ctx.user_data.get("admin_state")
    msg = update.message

    if state == "adm_add" and is_main(update.effective_user.id):
        return await admin_add_from_message(update, ctx)
    if state and state.startswith("ai_") and has_perm(update.effective_user.id, "ai"):
        await admin_ai_text(update, ctx, state)
        return True

    if state == "search":
        raw = msg.text.strip()[:64]
        ctx.user_data.pop("admin_state", None)
        ctx.user_data["user_q"] = raw
        text, markup = await screen_people(0, "search", raw, viewer=update.effective_user.id)
        await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        return True

    if state in ("bc_city", "bc_pick", "bc_btn", "bc_when"):
        return await admin_bc_text(update, ctx, state)
    if state.startswith("bs_text:") and is_main(update.effective_user.id):
        return await admin_bset_text(update, ctx, state)
    if state.startswith("us_city:") and has_perm(update.effective_user.id, "users"):
        return await admin_user_city(update, ctx, state)

    if state == "bc_country":
        code = msg.text.strip().lower()
        if len(code) != 2 or not code.isalpha():
            await msg.reply_text("❗ Нужен двухбуквенный код страны, например uz. Попробуйте ещё раз.")
            return True
        ctx.user_data["bc"] = {"kind": "country", "value": code, "text": None}
        await ask_bc_text(update, ctx)
        return True

    if state == "bc_text":
        bc = ctx.user_data.get("bc")
        if not bc:
            ctx.user_data.pop("admin_state", None)
            return False
        text = msg.text_html
        try:  # preview exactly as users will see it
            await msg.reply_text(text, parse_mode=ParseMode.HTML)
        except BadRequest as e:
            await msg.reply_text(f"⚠️ Не удалось показать предпросмотр: {e}\nПопробуйте отправить текст ещё раз.")
            return True
        bc["text"] = text
        where, args = bc_where(bc)
        n = await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)
        ctx.user_data.pop("admin_state", None)
        await msg.reply_text(
            f"👆 Так увидят сообщение.\n\n👥 Получателей: <b>{n}</b> ({bc_label(bc)})\n\nОтправить?",
            parse_mode=ParseMode.HTML,
            reply_markup=kb([btn("✅ Отправить", "a:bc:go"), btn("❌ Отмена", "a:home")]))
        return True

    return False


async def cmd_admin(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return  # silently ignore for everyone else
    ctx.user_data.pop("admin_state", None)
    text, markup = await screen_admin_home(update.effective_user.id)
    await render(update, text, markup)


# ───────────────────────── mini app: web server + API ─────────────────────────
# Railway gives the service a public address when you press "Generate Domain" and passes it
# to the bot as RAILWAY_PUBLIC_DOMAIN. WEBAPP_URL can override it. Without either, the bot
# simply hides the app buttons and shows the compass picture instead.

PUBLIC_DOMAIN = os.getenv("RAILWAY_PUBLIC_DOMAIN", "")
WEBAPP_URL = (os.getenv("WEBAPP_URL") or (f"https://{PUBLIC_DOMAIN}" if PUBLIC_DOMAIN else "")).rstrip("/")
WEBAPP_FILE = Path(__file__).with_name("webapp.html")
WEB_RUNNER = None
MONTH_CACHE = {}
TIMING_KEYS = ("Fajr", "Sunrise", "Dhuhr", "Asr", "Maghrib", "Isha")


def webapp_btn(text, tab="today"):
    return InlineKeyboardButton(text, web_app=WebAppInfo(url=f"{WEBAPP_URL}/?tab={tab}"))


def check_init_data(init_data):
    """Validate Telegram Mini App initData (HMAC signed with the bot token). Returns the user dict."""
    if not init_data:
        return None
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True, strict_parsing=True))
    except ValueError:
        return None
    their = pairs.pop("hash", None)
    if not their:
        return None
    check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    ours = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(ours, their):
        return None
    try:
        if _time.time() - int(pairs.get("auth_date", "0")) > 7 * 86400:
            return None
        user = json.loads(pairs.get("user", "{}"))
    except (ValueError, TypeError):
        return None
    return user if isinstance(user, dict) and "id" in user else None


async def api_auth(request):
    tg_user = check_init_data(request.headers.get("X-Init-Data", ""))
    if not tg_user:
        raise web.HTTPUnauthorized(text="bad initData")
    u = await get_user(int(tg_user["id"]))
    lang = (u or {}).get("lang") or str(tg_user.get("language_code") or "en")[:2]
    return tg_user, u, (lang if lang in LANGS else "en")


async def _calc_month(u, y, m):
    method, school = method_for(u["country"]), (1 if u["madhab"] == "hanafi" else 0)
    key = (round(u["lat"], 2), round(u["lon"], 2), method, school, y, m)
    if key in MONTH_CACHE:
        return MONTH_CACHE[key]
    async with SEM:
        r = await HTTP.get(f"https://api.aladhan.com/v1/calendar/{y}/{m}",
                           params={"latitude": u["lat"], "longitude": u["lon"], **method_params(method), "school": school})
    r.raise_for_status()
    days = []
    for item in r.json()["data"]:
        g, h, tm = item["date"]["gregorian"], item["date"]["hijri"], item["timings"]
        days.append({"date": g["date"], "day": int(g["day"]), "wd": g["weekday"]["en"][:3],
                     "hday": int(h["day"]), "hmonth": int(h["month"]["number"]), "hyear": int(h["year"]),
                     "t": {k: tm[k].split()[0] for k in TIMING_KEYS}})
    if len(MONTH_CACHE) > 400:
        MONTH_CACHE.clear()
    MONTH_CACHE[key] = days
    return days


async def _calc_hijri_month(u, hy, hm):
    method, school = method_for(u["country"]), (1 if u["madhab"] == "hanafi" else 0)
    key = ("h", round(u["lat"], 2), round(u["lon"], 2), method, school, hy, hm)
    if key in MONTH_CACHE:
        return MONTH_CACHE[key]
    async with SEM:
        r = await HTTP.get(f"https://api.aladhan.com/v1/hijriCalendar/{hy}/{hm}",
                           params={"latitude": u["lat"], "longitude": u["lon"], **method_params(method), "school": school})
    r.raise_for_status()
    days = []
    for item in r.json()["data"]:
        g, h, tm = item["date"]["gregorian"], item["date"]["hijri"], item["timings"]
        days.append({"date": g["date"], "hday": int(h["day"]),
                     "t": {k: tm[k].split()[0] for k in TIMING_KEYS}})
    MONTH_CACHE[key] = days
    return days


async def _local_days(u, days):
    if not nv_city(u):
        return days
    out = []
    for x in days:
        dd, mm, yy = (int(v) for v in x["date"].split("-"))
        out.append(dict(x, t=await local_times(u, date(yy, mm, dd), x["t"])))
    return out


async def fetch_month(u, y, m):
    return await _local_days(u, await _calc_month(u, y, m))


async def fetch_hijri_month(u, hy, hm):
    return await _local_days(u, await _calc_hijri_month(u, hy, hm))


def profile_json(u, lang):
    quiet = "off" if u["quiet_start"] is None else f"{u['quiet_start']}-{u['quiet_end']}"
    return {"lang": lang, "city": u["city"], "lat": u["lat"], "lon": u["lon"], "tz": u["tz"],
            "madhab": u["madhab"], "country": u["country"], "lead": u["lead_min"], "at_time": u["at_time"],
            "remind": u["remind"], "auto": u["auto_mode"], "ramadan": u["ramadan"], "quiet": quiet,
            "weekly": u["weekly"], "azan": u["azan"] if azan_by_id(u["azan"]) else "off",
            "fast_show": u["fast_show"], "suhoor_rem": u["suhoor_rem"], "iftar_rem": u["iftar_rem"],
            "fast_sound": u["fast_sound"], "modes": (u["prayer_modes"] or "sssss").ljust(5, "s"),
            "suh_options": SUH_OPTS, "ift_options": IFT_OPTS,
            "azan_options": [[str(a["id"]), a["name"]] for a in AZANS],
            "lead_options": LEAD_OPTIONS, "auto_options": AUTO_OPTIONS,
            "quiet_options": ["off"] + [f"{a}-{b}" for a, b in QUIET_PRESETS]}


async def read_json(request):
    try:
        body = await request.json()
    except Exception:  # noqa: BLE001
        raise web.HTTPBadRequest(text="bad json")
    if not isinstance(body, dict):
        raise web.HTTPBadRequest(text="bad json")
    return body


async def api_settings(request):
    """Change the user's settings from the mini app. Only known fields with allowed values are accepted."""
    tg_user, u, _ = await api_auth(request)
    if not u:
        raise web.HTTPBadRequest(text="no user")
    old_lang = u["lang"]
    body = await read_json(request)
    fields = {}
    if body.get("lang") in LANGS:
        fields["lang"] = body["lang"]
    if body.get("madhab") in ("std", "hanafi"):
        fields["madhab"] = body["madhab"]
    if isinstance(body.get("lead"), int) and body["lead"] in LEAD_OPTIONS:
        fields["lead_min"] = body["lead"]
    if isinstance(body.get("auto"), int) and body["auto"] in AUTO_OPTIONS:
        fields["auto_mode"] = body["auto"]
    for key, col in (("at_time", "at_time"), ("remind", "remind"), ("ramadan", "ramadan"),
                     ("weekly", "weekly"), ("fast_show", "fast_show"), ("fast_sound", "fast_sound")):
        if isinstance(body.get(key), bool):
            fields[col] = body[key]
    if body.get("suhoor_rem") in SUH_OPTS:
        fields["suhoor_rem"] = body["suhoor_rem"]
    if body.get("iftar_rem") in IFT_OPTS:
        fields["iftar_rem"] = body["iftar_rem"]
    pm = body.get("modes")
    if isinstance(pm, str) and len(pm) == 5 and set(pm) <= set(PRAYER_MODES):
        fields["prayer_modes"] = pm
    az = body.get("azan")
    if az == "off" or (az is not None and azan_by_id(az)):
        fields["azan"] = None if az == "off" else str(az)
    q = body.get("quiet")
    if q == "off":
        fields["quiet_start"], fields["quiet_end"] = None, None
    elif isinstance(q, str) and "-" in q:
        try:
            a, b = (int(x) for x in q.split("-"))
            if (a, b) in QUIET_PRESETS:
                fields["quiet_start"], fields["quiet_end"] = a, b
        except ValueError:
            pass
    if not fields:
        raise web.HTTPBadRequest(text="nothing to change")
    if "remind" in fields:
        fields["onboarded"] = True
    await save(u["user_id"], **fields)
    u = await get_user(u["user_id"])
    if "lang" in fields and fields["lang"] != old_lang:
        await relocalize_city(u["user_id"], fields["lang"])
        u = await get_user(u["user_id"])
    return web.json_response({"ok": True, "profile": profile_json(u, u["lang"] or "en")})


async def api_geocode(request):
    _, u, lang = await api_auth(request)
    q = (request.query.get("q") or "").strip()[:100]
    if len(q) < 2:
        raise web.HTTPBadRequest(text="short query")
    try:
        res = await geocode(q, lang)
    except Exception:  # noqa: BLE001
        log.exception("api geocode failed")
        return web.json_response({"ok": False}, status=502)
    if not res:
        return web.json_response({"ok": True, "found": False})
    name, lat, lon, cc = res
    return web.json_response({"ok": True, "found": True, "name": name, "lat": lat, "lon": lon, "cc": cc,
                              "flag": flag(cc) if cc else ""})


async def api_city(request):
    tg_user, u, _ = await api_auth(request)
    if not u:
        raise web.HTTPBadRequest(text="no user")
    body = await read_json(request)
    try:
        name = str(body["name"])[:120]
        lat, lon = float(body["lat"]), float(body["lon"])
        cc = str(body.get("cc") or "")[:2].lower()
        if not (-90 <= lat <= 90 and -180 <= lon <= 180) or not name:
            raise ValueError
    except (KeyError, ValueError, TypeError):
        raise web.HTTPBadRequest(text="bad city")
    school = 1 if u["madhab"] == "hanafi" else 0
    try:
        data = await fetch_timings(lat, lon, datetime.utcnow().date(), method_for(cc), school)
    except Exception:  # noqa: BLE001
        log.exception("api city timings failed")
        return web.json_response({"ok": False}, status=502)
    await save(u["user_id"], city=name, lat=lat, lon=lon, country=cc, tz=data["tz"], awaiting_city=False)
    return web.json_response({"ok": True})


async def api_me(request):
    tg_user, u, lang = await api_auth(request)
    try:
        await POOL.execute("INSERT INTO daily_active (day, user_id) VALUES (CURRENT_DATE, $1) ON CONFLICT DO NOTHING",
                           int(tg_user["id"]))
    except Exception:  # noqa: BLE001
        pass
    if not u or not (u["city"] and u["tz"] and u["madhab"]):
        return web.json_response({"ok": True, "need_setup": True, "lang": lang, "bot": BOT_USERNAME})
    try:
        now = datetime.now(ZoneInfo(u["tz"]))
        today = await get_timings(u, now.date())
        tomorrow = await get_timings(u, now.date() + timedelta(days=1))
        month = await fetch_month(u, now.year, now.month)
    except Exception:  # noqa: BLE001
        log.exception("api_me failed")
        return web.json_response({"ok": False, "error": "timings"}, status=502)
    return web.json_response({
        "ok": True, "need_setup": False, "bot": BOT_USERNAME, "profile": profile_json(u, lang),
        "share_url": share_url(u["user_id"], now.date().isoformat()), "is_admin": is_admin(u["user_id"]),
        "pic": {"bg": u["share_bg"] % art.N_BG, "fs": u["share_font"] % art.N_FONT, "n_bg": art.N_BG,
                "fonts": art.FONT_NAMES.get(u["lang"], art.FONT_NAMES["en"])},
        "admin": {"perms": admin_perms(u["user_id"]), "main": is_main(u["user_id"])} if is_admin(u["user_id"]) else None,
        "ref": {"count": await POOL.fetchval("SELECT count(*) FROM users WHERE referred_by = $1", u["user_id"]),
                "link": ref_link(u["user_id"])},
        "dev": DEV_CONTACT,
        "ai": {"enabled": ai_allowed_now(u["user_id"]), "status": ai_status_text(lang, await ai_quota(u)),
               "unlimited": is_admin(u["user_id"])},
        "money": money_json(lang),
        "today": {"date": now.date().isoformat(), "t": {k: today[k] for k in TIMING_KEYS},
                  "hday": today["hday"], "hmonth": today["hmonth"], "hyear": today["hyear"]},
        "tomorrow": {"t": {k: tomorrow[k] for k in TIMING_KEYS}},
        "month": {"y": now.year, "m": now.month, "days": month},
    })


async def api_month(request):
    _, u, _ = await api_auth(request)
    if not u or not u["city"]:
        raise web.HTTPBadRequest(text="no city")
    try:
        y, m = int(request.query["y"]), int(request.query["m"])
        if not (2000 <= y <= 2100 and 1 <= m <= 12):
            raise ValueError
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad month")
    try:
        days = await fetch_month(u, y, m)
    except Exception:  # noqa: BLE001
        log.exception("api_month failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True, "y": y, "m": m, "days": days})


async def api_ramadan(request):
    _, u, _ = await api_auth(request)
    if not u or not u["city"]:
        raise web.HTTPBadRequest(text="no city")
    try:
        now = datetime.now(ZoneInfo(u["tz"]))
        today = await get_timings(u, now.date())
        hy = today["hyear"] if today["hmonth"] <= 9 else today["hyear"] + 1
        days = await fetch_hijri_month(u, hy, 9)
    except Exception:  # noqa: BLE001
        log.exception("api_ramadan failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True, "hyear": hy, "today": now.date().isoformat(), "days": days})


async def page_index(request):
    try:
        body = WEBAPP_FILE.read_text(encoding="utf-8")
    except FileNotFoundError:
        return web.Response(text="webapp.html is missing next to bot.py", status=500)
    return web.Response(text=body, content_type="text/html", headers={"Cache-Control": "no-cache"})


async def page_health(request):
    return web.Response(text="ok")


async def start_web(application=None):
    global WEB_RUNNER
    app = web.Application(client_max_size=30 * 1024 * 1024)  # broadcast photos and videos (base64)
    app["ptb"] = application
    app["bot"] = application.bot if application else None
    app.add_routes([web.get("/", page_index), web.get("/health", page_health),
                    web.get("/api/me", api_me), web.get("/api/month", api_month),
                    web.get("/api/ramadan", api_ramadan), web.post("/api/settings", api_settings),
                    web.get("/api/geocode", api_geocode), web.post("/api/city", api_city),
                    web.get("/api/city_times", api_city_times), web.post("/api/share_send", api_share_send),
                    web.get("/share/{uid}/{day}/{sig}.png", page_share),
                    web.get("/api/mosques", api_mosques), web.get("/api/reverse", api_reverse),
                    web.get("/api/admin/summary", api_admin_summary), web.get("/api/admin/people", api_admin_people),
                    web.get("/api/admin/person", api_admin_person), web.post("/api/admin/ban", api_admin_ban),
                    web.post("/api/admin/message", api_admin_message), web.get("/api/admin/bc_count", api_admin_bc_count),
                    web.post("/api/admin/broadcast", api_admin_broadcast), web.get("/api/admin/health", api_admin_health),
                    web.post("/api/admin/export", api_admin_export),
                    web.get("/api/admin/admins", api_admin_admins), web.post("/api/admin/admins", api_admin_admins),
                    web.get("/api/tracker", api_tracker), web.post("/api/tracker", api_tracker_set),
                    web.post("/api/tracker_bulk", api_tracker_bulk), web.get("/api/community", api_community),
                    web.get("/api/challenges", api_challenges), web.post("/api/challenges", api_challenge_new),
                    web.post("/api/challenges/leave", api_challenge_leave),
                    web.post("/api/share_prepare", api_share_prepare), web.post("/api/ai", api_ai),
                    web.get("/api/ayah", api_ayah), web.get("/api/pic", api_pic), web.post("/api/pic_prepare", api_pic_prepare),
                    web.get("/pic/{kind}/{uid}/{key}/{bg}/{fs}/{sig}.jpg", page_pic),
                    web.post("/api/invoice", api_invoice), web.post("/api/donate/sent", api_donate_sent),
                    web.get("/api/admin/ai", api_admin_ai), web.post("/api/admin/ai", api_admin_ai),
                    web.post("/api/admin/hide", api_admin_hide),
                    web.get("/card/{name}", page_card), web.get("/api/invite", api_invite),
                    web.post("/api/invite_prepare", api_invite_prepare), web.post("/api/invite_send", api_invite_send),
                    web.get("/api/admin/botcfg", api_admin_botcfg), web.post("/api/admin/botcfg", api_admin_botcfg),
                    web.get("/api/admin/bc2", api_admin_bc2), web.post("/api/admin/bc2", api_admin_bc2),
                    web.get("/api/admin/person_tools", api_admin_person_tools), web.post("/api/admin/person_tools", api_admin_person_tools)])
    WEB_RUNNER = web.AppRunner(app, access_log=None)
    await WEB_RUNNER.setup()
    port = int(os.getenv("PORT", "8080"))
    await web.TCPSite(WEB_RUNNER, "0.0.0.0", port).start()
    log.info("Mini app server on port %s (%s)", port, WEBAPP_URL or "no public domain yet")


# ───────────────────────── mini app: other cities ─────────────────────────

async def api_city_times(request):
    """Prayer times for any place (the "other city" screen). Uses the user's madhab."""
    _, u, lang = await api_auth(request)
    try:
        lat, lon = float(request.query["lat"]), float(request.query["lon"])
        cc = (request.query.get("cc") or "")[:2].lower()
        if not (-90 <= lat <= 90 and -180 <= lon <= 180):
            raise ValueError
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad place")
    place = {"lat": lat, "lon": lon, "country": cc, "madhab": (u or {}).get("madhab") or "std"}
    try:
        first = await get_timings(place, datetime.utcnow().date())
        local = datetime.now(ZoneInfo(first["tz"]))
        day = await get_timings(place, local.date())
        tomorrow = await get_timings(place, local.date() + timedelta(days=1))
    except Exception:  # noqa: BLE001
        log.exception("city times failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({
        "ok": True, "tz": day["tz"], "date": local.date().isoformat(), "now": local.strftime("%H:%M"),
        "t": {k: day[k] for k in TIMING_KEYS}, "tomorrow": {k: tomorrow[k] for k in TIMING_KEYS},
        "hday": day["hday"], "hmonth": day["hmonth"], "hyear": day["hyear"],
        "qibla": round(qibla_bearing(lat, lon)),
    })


# ───────────────────────── share: a picture of today's schedule ─────────────────────────
# The picture has a public but signed address (Telegram downloads it for stories), valid for its day.

FONT_DIR = Path(__file__).with_name("fonts")
SHARE_CACHE = {}


def share_sig(uid, day):
    return hmac.new(BOT_TOKEN.encode(), f"share:{uid}:{day}".encode(), hashlib.sha256).hexdigest()[:20]


def share_url(uid, day):
    return f"{WEBAPP_URL}/share/{uid}/{day}/{share_sig(uid, day)}.png" if WEBAPP_URL else ""


FONTS = {}


def _font(size, bold=False):
    """Bundled DejaVu Sans: Latin, Cyrillic (incl. Uzbek/Tajik letters) and Arabic."""
    key = (size, bold)
    if key not in FONTS:
        from PIL import ImageFont, features
        path = FONT_DIR / ("DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf")
        try:
            engine = ImageFont.Layout.RAQM if features.check("raqm") else ImageFont.Layout.BASIC
            FONTS[key] = ImageFont.truetype(str(path), size, layout_engine=engine)
        except Exception:  # noqa: BLE001
            FONTS[key] = ImageFont.load_default(size=size)
    return FONTS[key]


async def share_png_for(u, day_iso):
    return await pic_bytes(u, "t", day_iso, u["share_bg"], u["share_font"])


# ───────────────────────── ayah of the day, share pictures ─────────────────────────

QURAN_API = "https://api.alquran.cloud/v1/ayah/{ref}/editions/{eds}"
AYAH_EDITIONS = {"ar": "quran-simple", "en": "en.sahih", "ru": "ru.kuliev", "uz": "uz.sodik", "tg": "tg.ayati"}
AYAH_CACHE = {}
PIC_CACHE = {}
_LAT = {"а": "a", "б": "b", "в": "v", "г": "g", "д": "d", "е": "e", "ё": "yo", "ж": "j", "з": "z", "и": "i", "й": "y",
        "к": "k", "л": "l", "м": "m", "н": "n", "о": "o", "п": "p", "р": "r", "с": "s", "т": "t", "у": "u", "ф": "f",
        "х": "x", "ц": "ts", "ч": "ch", "ш": "sh", "щ": "sh", "ъ": "ʼ", "ы": "i", "ь": "", "э": "e", "ю": "yu", "я": "ya",
        "ў": "oʻ", "қ": "q", "ғ": "gʻ", "ҳ": "h"}


def to_lat(text):
    """Cyrillic Uzbek → Latin Uzbek (for translations that come in Cyrillic)."""
    out = []
    for i, ch in enumerate(text):
        low = ch.lower()
        if low not in _LAT:
            out.append(ch)
            continue
        v = _LAT[low]
        if low == "е" and (i == 0 or not text[i - 1].isalpha() or text[i - 1].lower() in "аеёиоуўэюя"):
            v = "ye"
        if ch.isupper() and v:
            v = v[0].upper() + v[1:]
        out.append(v)
    return "".join(out)


def name_cyr(name):
    """"Al-Baqara" → "Аль-Бакара" (sura names come in Latin)."""
    parts = []
    for w in name.replace("'", "").replace("`", "").split("-"):
        low = w.lower()
        if low == "al":
            parts.append("аль" if w[:1].islower() else "Аль")
            continue
        for a, b in (("kh", "х"), ("sh", "ш"), ("th", "с"), ("dh", "з"), ("gh", "г"), ("ch", "ч"), ("aa", "а"), ("ee", "и"),
                     ("oo", "у"), ("ii", "и"), ("uu", "у"), ("j", "дж")):
            low = low.replace(a, b)
        low = "".join({"a": "а", "b": "б", "c": "к", "d": "д", "e": "е", "f": "ф", "g": "г", "h": "х", "i": "и", "k": "к",
                       "l": "л", "m": "м", "n": "н", "o": "о", "p": "п", "q": "к", "r": "р", "s": "с", "t": "т", "u": "у",
                       "v": "в", "w": "в", "y": "й", "z": "з"}.get(c, c) for c in low)
        parts.append(low[:1].upper() + low[1:] if w[:1].isupper() else low)
    return "-".join(parts)


async def fetch_ayah(ref):
    """Arabic text + translations for "s:a" or "s:a-b" (alquran.cloud), kept in the database."""
    if ref in AYAH_CACHE:
        return AYAH_CACHE[ref]
    row = await POOL.fetchval("SELECT data FROM ayah_cache WHERE ref = $1", ref)
    if row:
        AYAH_CACHE[ref] = json.loads(row) if isinstance(row, str) else row
        return AYAH_CACHE[ref]
    s_no, rng = ref.split(":")
    a0, a1 = (int(x) for x in rng.split("-")) if "-" in rng else (int(rng), int(rng))
    out = {"s": int(s_no), "a": f"{a0}" if a0 == a1 else f"{a0}–{a1}"}
    texts = {k: [] for k in AYAH_EDITIONS}
    for n in range(a0, a1 + 1):
        got = {}
        r = await HTTP.get(QURAN_API.format(ref=f"{s_no}:{n}", eds=",".join(AYAH_EDITIONS.values())), timeout=20)
        if r.status_code == 200:
            for item in r.json().get("data") or []:
                got[item["edition"]["identifier"]] = item
        else:  # one edition name may be wrong: ask for them one by one
            for ed in AYAH_EDITIONS.values():
                rr = await HTTP.get(QURAN_API.format(ref=f"{s_no}:{n}", eds=ed), timeout=20)
                if rr.status_code == 200:
                    for item in rr.json().get("data") or []:
                        got[item["edition"]["identifier"]] = item
        ar = got.get(AYAH_EDITIONS["ar"])
        if not ar:
            raise RuntimeError(f"no arabic text for {s_no}:{n}")
        out["name"], out["ar_name"] = ar["surah"]["englishName"], ar["surah"]["name"]
        for k, ed in AYAH_EDITIONS.items():
            txt = (got.get(ed) or {}).get("text", "").strip()
            if k == "ar" and n == 1 and int(s_no) not in (1, 9):
                words = txt.split()
                if len(words) > 4 and words[0].startswith("بِسْمِ"):
                    txt = " ".join(words[4:])
            if txt:
                texts[k].append(txt)
    for k, v in texts.items():
        out[k] = (" ۝ " if k == "ar" else " ").join(v)
    await POOL.execute("INSERT INTO ayah_cache (ref, data) VALUES ($1, $2) ON CONFLICT (ref) DO UPDATE SET data = EXCLUDED.data",
                       ref, json.dumps(out, ensure_ascii=False))
    AYAH_CACHE[ref] = out
    return out


async def prefetch_ayahs(context):
    """Load all ayahs into the database slowly, so the first person each day doesn't wait."""
    await load_ayah_pool()
    have = {r["ref"] for r in await POOL.fetch("SELECT ref FROM ayah_cache")}
    todo = [x for x in AYAH_POOL if x not in have]
    ok = 0
    for ref in todo:
        try:
            await fetch_ayah(ref)
            ok += 1
        except Exception as e:  # noqa: BLE001
            log.warning("ayah %s: %r", ref, e)
        await asyncio.sleep(1.5)
    if todo:
        log.info("ayahs loaded: %d of %d", ok, len(todo))


AYAH_POOL = list(AYAHS)  # base list + ayahs added every week (from the ayah_pool table)
SURA_AYAHS = [7, 286, 200, 176, 120, 165, 206, 75, 129, 109, 123, 111, 43, 52, 99, 128, 111, 110, 98, 135, 112, 78, 118, 64,
              77, 227, 93, 88, 69, 60, 34, 30, 73, 54, 45, 83, 182, 88, 75, 85, 54, 53, 89, 59, 37, 35, 38, 29, 18, 45, 60,
              49, 62, 55, 78, 96, 29, 22, 24, 13, 14, 11, 11, 18, 12, 12, 30, 52, 52, 44, 28, 28, 20, 56, 40, 31, 50, 40, 46,
              42, 29, 19, 36, 25, 22, 17, 19, 26, 30, 20, 15, 21, 11, 8, 8, 19, 5, 8, 8, 11, 11, 8, 3, 9, 5, 4, 7, 3, 6, 3, 5,
              4, 5, 6]


async def load_ayah_pool():
    await POOL.executemany("INSERT INTO ayah_pool (ref) VALUES ($1) ON CONFLICT DO NOTHING", [(x,) for x in AYAHS])
    rows = await POOL.fetch("SELECT ref FROM ayah_pool WHERE NOT removed ORDER BY added_at, ref")
    AYAH_POOL[:] = [r["ref"] for r in rows] or list(AYAHS)


async def today_ayah_ref(u, day):
    """Each person gets an ayah they haven't seen yet; it stays the same all day. After all of them — from the start."""
    import random
    uid = u["user_id"]
    if u.get("ayah_day") == day and u.get("ayah_ref"):
        return u["ayah_ref"]
    seen = {r["ref"] for r in await POOL.fetch("SELECT ref FROM ayah_seen WHERE user_id = $1", uid)}
    left = [x for x in AYAH_POOL if x not in seen]
    if not left:
        await POOL.execute("DELETE FROM ayah_seen WHERE user_id = $1", uid)
        left = list(AYAH_POOL)
    ref = random.Random(uid * 7919 + day.toordinal()).choice(left)
    await save(uid, ayah_day=day, ayah_ref=ref)
    await POOL.execute("INSERT INTO ayah_seen (user_id, ref) VALUES ($1, $2) ON CONFLICT DO NOTHING", uid, ref)
    u["ayah_day"], u["ayah_ref"] = day, ref
    return ref


AYAH_PICK = """You help choose verses for an "Ayah of the day" card in a Muslim app. Below are Qur'an verses (id | English meaning).
Pick up to {n} that read well ON THEIR OWN for an ordinary Muslim: guidance, mercy, hope, patience, gratitude, prayer, duas,
reminders of Allah and the Hereafter, good character. Skip verses that are fragments of a story, need the previous verse to make
sense, are detailed legal rulings (inheritance, divorce, debts, war), or are about punishment only.
Answer with JSON only: a list of the chosen ids, e.g. ["2:153", "39:53"]."""


async def add_weekly_ayahs(bot, n=7):
    """Every week: random short verses not in the list yet → the AI picks the good ones → added for everyone."""
    import random
    have = {r["ref"] for r in await POOL.fetch("SELECT ref FROM ayah_pool")}
    covered = set()
    for x in have:
        sno, rng = x.split(":")
        a0, a1 = (int(v) for v in rng.split("-")) if "-" in rng else (int(rng), int(rng))
        covered |= {f"{sno}:{k}" for k in range(a0, a1 + 1)}
    rnd = random.Random()
    cands = []
    for _ in range(400):
        if len(cands) >= 40:
            break
        sno = rnd.randint(1, 114)
        ref = f"{sno}:{rnd.randint(1, SURA_AYAHS[sno - 1])}"
        if ref in covered or ref in [c[0] for c in cands] or ref in ("9:1",):
            continue
        try:
            r = await HTTP.get(QURAN_API.format(ref=ref, eds="quran-simple,en.sahih"), timeout=20)
            data = {i["edition"]["identifier"]: i["text"] for i in r.json().get("data") or []} if r.status_code == 200 else {}
        except Exception:  # noqa: BLE001
            data = {}
        ar, en = data.get("quran-simple", ""), data.get("en.sahih", "")
        if 20 <= len(ar) <= 260 and en:
            cands.append((ref, en))
        await asyncio.sleep(0.4)
    if not cands:
        return []
    prompt = "\n".join(f"{ref} | {en}" for ref, en in cands)
    system = AYAH_PICK.format(n=n)
    text = None
    if AI["key"]:
        text, _, _ = await gemini_answer(system, [{"role": "user", "parts": [{"text": prompt}]}], False, AI["cfg"])
    if not text:
        for p in PROVIDERS:
            if AI["pkeys"].get(p):
                text, _ = await backup_answer(p, [{"role": "system", "content": system}, {"role": "user", "content": prompt}],
                                              AI["cfg"])
                if text:
                    break
    if not text:
        return None  # no AI right now: try again later
    ids = re.findall(r"\d{1,3}:\d{1,3}", text)
    ok = {c[0] for c in cands}
    chosen = []
    for ref in ids:
        if ref in ok and ref not in chosen:
            chosen.append(ref)
        if len(chosen) >= n:
            break
    added = []
    for ref in chosen:
        try:
            await fetch_ayah(ref)
            await POOL.execute("INSERT INTO ayah_pool (ref, source) VALUES ($1, 'auto') ON CONFLICT DO NOTHING", ref)
            added.append(ref)
        except Exception as e:  # noqa: BLE001
            log.warning("weekly ayah %s: %r", ref, e)
        await asyncio.sleep(1)
    await load_ayah_pool()
    log.info("weekly ayahs added: %s", ", ".join(added) or "none")
    if added and ADMIN_ID:
        en = dict(cands)
        lines = [f"📖 <b>Добавлено {len(added)} новых аятов</b> (всего {len(AYAH_POOL)})", ""]
        lines += [f"• <b>{r}</b> — {esc(en.get(r, '')[:160])}" for r in added]
        lines += ["", "Если какой-то не подходит — нажмите ❌, он больше не будет показываться."]
        rows = [[btn(f"❌ {r}", f"a:ayrm:{r.replace(':', '.')}") for r in added[i:i + 3]] for i in range(0, len(added), 3)]
        try:
            await bot.send_message(ADMIN_ID, "\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=kb(*rows),
                                   disable_notification=True)
        except Exception:  # noqa: BLE001
            log.exception("weekly ayahs: admin message failed")
    return added


async def weekly_ayahs_job(bot):
    """Once a week (Monday night in Tashkent): add new ayahs. Retries next run if the AI was busy."""
    now = datetime.now(ZoneInfo("Asia/Tashkent"))
    week = f"{now.isocalendar()[0]}-{now.isocalendar()[1]}"
    if now.weekday() != 0 or now.hour < 22 or await kv_get("ayah_week", "") == week:
        return
    await kv_set("ayah_week", week)
    try:
        if await add_weekly_ayahs(bot) is None:
            await kv_set("ayah_week", "")
    except Exception:  # noqa: BLE001
        log.exception("weekly ayahs failed")
        await kv_set("ayah_week", "")


def ayah_parts(a, lang):
    """(arabic, translation, reference line) in the person's language."""
    tr = ""
    if lang != "ar":
        tr = a.get("uz" if lang in ("uz", "uzc") else lang) or a.get("ru" if lang in ("tg", "uz", "uzc") else "en") or a.get("en", "")
        is_cyr = bool(re.search("[а-яА-ЯёЁ]", tr))
        if lang == "uz" and is_cyr:
            tr = to_lat(tr)
        elif lang == "uzc" and not is_cyr:
            tr = to_cyr(tr)
    num = f"{a['s']}:{a['a']}"
    ar = a["ar"]
    if "۝" in ar:  # between verses: the verse number in ornate brackets (the ۝ sign is missing in many fonts)
        first = int(str(a["a"]).split("–")[0])
        digits = str.maketrans("0123456789", "٠١٢٣٤٥٦٧٨٩")
        bits = [x.strip() for x in ar.split("۝")]
        ar = " ".join(f"{b} ﴿{str(first + k).translate(digits)}﴾" if k < len(bits) - 1 else b for k, b in enumerate(bits))
    if lang == "ar":
        ref = f"{a['ar_name']} · {num}"
    elif lang in ("ru", "tg", "uzc"):
        ref = f"{t(lang, 'quran')} · {name_cyr(a['name'])} {num}"
    else:
        ref = f"{t(lang, 'quran')} · {a['name']} {num}"
    return ar, tr, ref


async def screen_ayah(u, day=None):
    lang = u["lang"]
    u = dict(u)
    day = day or datetime.now(ZoneInfo(u["tz"] or "UTC")).date()
    aref = await today_ayah_ref(u, day)
    a = await fetch_ayah(aref)
    ar, tr, ref = ayah_parts(a, lang)
    text = f"📖 <b>{t(lang, 'ayah_title')}</b>\n\n{esc(ar)}\n\n" + (f"<i>{esc(tr)}</i>\n\n" if tr else "") + f"— {esc(ref)}"
    share = InlineKeyboardButton(t(lang, "btn_share"), url="https://t.me/share/url?url=" + quote(ayah_share_text(lang, ar, tr, ref), safe=""))
    return text, kb([share], [btn(t(lang, "btn_menu"), "m:new")])


def ayah_share_text(lang, ar, tr, ref):
    return f"📖 {t(lang, 'ayah_title')}\n\n{ar}\n\n" + (f"{tr}\n\n" if tr else "") + f"— {ref}\n\n@{BOT_USERNAME}"


def times_rows(lang, data):
    kinds = {"Fajr": "moon", "Sunrise": "half", "Dhuhr": "sun", "Asr": "sun", "Maghrib": "half", "Isha": "moon"}
    return [(kinds[k], PN[lang][k.lower()], data[k], k == "Sunrise") for k, _ in ROWS]


async def pic_bytes(u, kind, day_iso, bg, fs):
    lang = u["lang"]
    key = (kind, u["user_id"], day_iso, lang, u["city"], u["madhab"], bg, fs)
    if key in PIC_CACHE:
        return PIC_CACHE[key]
    loop = asyncio.get_running_loop()
    label = f"@{BOT_USERNAME}" if BOT_USERNAME else "Mawaqit"
    if kind == "a":  # day_iso is the ayah reference here
        ar, tr, ref = ayah_parts(await fetch_ayah(day_iso), lang)
        jpg = await loop.run_in_executor(None, art.render_ayah, ar, tr, ref, t(lang, "ayah_hdr"), label, bg, fs)
    else:
        y, m, dd = (int(x) for x in day_iso.split("-"))
        data = await get_timings(u, date(y, m, dd))
        title = strip_tags(t(lang, "times_title")).replace("🕌 ", "")
        date_line = f"{dd:02d}.{m:02d}.{y}  ·  {data['hday']} {HM[lang][data['hmonth'] - 1]} {data['hyear']}"
        jpg = await loop.run_in_executor(None, lambda: art.render_times(title, u["city"] or "", date_line, times_rows(lang, data),
                                                                        label, bg, fs, rtl=lang == "ar"))
    if len(PIC_CACHE) > 120:
        PIC_CACHE.clear()
    PIC_CACHE[key] = jpg
    return jpg


def pic_markup(lang, kind, day_iso, bg, fs):
    names = art.FONT_NAMES.get(lang, art.FONT_NAMES["en"])
    cb = f"pic:{kind}:{{}}:{day_iso.replace(':', '.')}"
    return kb([btn("◀️", cb.format("b-")), btn(t(lang, "pic_bg", i=bg % art.N_BG + 1, n=art.N_BG), cb.format("b+")), btn("▶️", cb.format("b+"))],
              [btn("◀️", cb.format("f-")), btn("🔤 " + names[fs % art.N_FONT], cb.format("f+")), btn("▶️", cb.format("f+"))],
              [btn(t(lang, "pic_done"), cb.format("ok"))])


async def pic_button(update, ctx, parts):
    """ay:show — the ayah of the day; pic:<a|t>:<new|b+|b-|f+|f-|ok>:<day> — the share picture and its picker."""
    q = update.callback_query
    u = await get_user(q.from_user.id)
    if not u or not u["lang"] or not u["tz"]:
        return await q.answer()
    lang = u["lang"]
    if parts[0] == "ay":
        await q.answer()
        try:
            text, markup = await screen_ayah(u)
        except Exception:  # noqa: BLE001
            log.exception("ayah failed")
            return await update.effective_chat.send_message(t(lang, "ayah_err"))
        return await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    kind = parts[1] if len(parts) > 1 and parts[1] in ("a", "t") else "t"
    op = parts[2] if len(parts) > 2 else "new"
    day_iso = parts[3] if len(parts) > 3 and re.match(r"^\d{4}-\d\d-\d\d$", parts[3]) else \
        datetime.now(ZoneInfo(u["tz"])).date().isoformat()
    if kind == "a":  # the ayah reference ("94.5-6"); older buttons carry a day
        if len(parts) > 3 and re.match(r"^\d{1,3}\.\d{1,3}(-\d{1,3})?$", parts[3]):
            day_iso = parts[3].replace(".", ":")
        else:
            day_iso = await today_ayah_ref(dict(u), date.fromisoformat(day_iso))
    if op == "ok":  # the finished picture: @bot under it and a share button
        await q.answer()
        msg = q.message
        photo = msg.photo[-1].file_id if msg and msg.photo else None
        if not photo:
            return
        pid = hashlib.md5(f"{photo}:{_time.time()}".encode()).hexdigest()[:12]
        await POOL.execute("INSERT INTO share_pics (id, file_id) VALUES ($1, $2) ON CONFLICT DO NOTHING", pid, photo)
        caption = f"@{BOT_USERNAME}" if BOT_USERNAME else None
        share = InlineKeyboardButton(t(lang, "btn_share"), switch_inline_query=f"pic {pid}")
        await update.effective_chat.send_photo(photo, caption=caption, reply_markup=kb([share]))
        try:
            await msg.delete()
        except Exception:  # noqa: BLE001
            pass
        return
    bg, fs = u["share_bg"] % art.N_BG, u["share_font"] % art.N_FONT
    if op in ("b+", "b-"):
        bg = (bg + (1 if op == "b+" else -1)) % art.N_BG
    elif op in ("f+", "f-"):
        fs = (fs + (1 if op == "f+" else -1)) % art.N_FONT
    if (bg, fs) != (u["share_bg"], u["share_font"]):
        await save(u["user_id"], share_bg=bg, share_font=fs)
    await q.answer()
    try:
        jpg = await pic_bytes(u, kind, day_iso, bg, fs)
    except Exception:  # noqa: BLE001
        log.exception("share picture failed")
        return await update.effective_chat.send_message(t(lang, "ayah_err" if kind == "a" else "error"))
    markup = pic_markup(lang, kind, day_iso, bg, fs)
    if op == "new":
        await update.effective_chat.send_action("upload_photo")
        return await update.effective_chat.send_photo(jpg, reply_markup=markup)
    try:
        await q.edit_message_media(InputMediaPhoto(jpg), reply_markup=markup)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise


# mini app: ayah of the day and the picture studio

def pic_sig(kind, uid, key, bg, fs):
    return hmac.new(BOT_TOKEN.encode(), f"pic:{kind}:{uid}:{key}:{bg}:{fs}".encode(), hashlib.sha256).hexdigest()[:20]


def pic_args(request, u):
    """kind, key (ayah ref "94:5-6" or day), background, font from the query/body."""
    q = request.query
    kind = q.get("kind") if q.get("kind") in ("a", "t") else "t"
    try:
        bg, fs = int(q.get("bg", u["share_bg"])) % art.N_BG, int(q.get("fs", u["share_font"])) % art.N_FONT
    except ValueError:
        bg, fs = u["share_bg"] % art.N_BG, u["share_font"] % art.N_FONT
    return kind, bg, fs


async def pic_key(u, kind):
    day = datetime.now(ZoneInfo(u["tz"])).date()
    return await today_ayah_ref(dict(u), day) if kind == "a" else day.isoformat()


async def api_ayah(request):
    tg_user, u, lang = await api_auth(request)
    if not feat("ayah"):
        raise web.HTTPNotFound()
    if not u or not u["tz"]:
        raise web.HTTPBadRequest(text="no city")
    ref_id = await pic_key(u, "a")
    try:
        ar, tr, ref = ayah_parts(await fetch_ayah(ref_id), u["lang"])
    except Exception:  # noqa: BLE001
        log.exception("ayah for the mini app failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True, "ar": ar, "tr": tr, "ref": ref, "share": ayah_share_text(u["lang"], ar, tr, ref)})


async def api_pic(request):
    tg_user, u, lang = await api_auth(request)
    if not u or not u["tz"] or not u["city"]:
        raise web.HTTPBadRequest(text="no city")
    kind, bg, fs = pic_args(request, u)
    if (bg, fs) != (u["share_bg"], u["share_font"]):
        await save(u["user_id"], share_bg=bg, share_font=fs)
    try:
        jpg = await pic_bytes(u, kind, await pic_key(u, kind), bg, fs)
    except Exception:  # noqa: BLE001
        log.exception("picture failed")
        raise web.HTTPServiceUnavailable()
    return web.Response(body=jpg, content_type="image/jpeg", headers={"Cache-Control": "private, max-age=600"})


async def api_pic_prepare(request):
    """A ready photo message (@bot under it) for Telegram's share window, and a link to save the picture."""
    tg_user, u, lang = await api_auth(request)
    if not u or not u["tz"] or not u["city"]:
        raise web.HTTPBadRequest(text="no city")
    body = await read_json(request)
    kind = body.get("kind") if body.get("kind") in ("a", "t") else "t"
    bg, fs = int(body.get("bg") or 0) % art.N_BG, int(body.get("fs") or 0) % art.N_FONT
    key = (await pic_key(u, kind)).replace(":", ".")
    uid = u["user_id"]
    url = f"{WEBAPP_URL}/pic/{kind}/{uid}/{key}/{bg}/{fs}/{pic_sig(kind, uid, key, bg, fs)}.jpg"
    try:
        await pic_bytes(u, kind, key.replace(".", ":"), bg, fs)  # ready before Telegram comes for it
        res = InlineQueryResultPhoto(id=hashlib.md5(url.encode()).hexdigest(), photo_url=url, thumbnail_url=url,
                                     caption=f"@{BOT_USERNAME}")
        pm = await request.app["bot"].save_prepared_inline_message(uid, res, allow_user_chats=True, allow_bot_chats=True,
                                                                   allow_group_chats=True, allow_channel_chats=True)
    except Exception:  # noqa: BLE001
        log.exception("picture prepare failed")
        return web.json_response({"ok": False, "url": url}, status=502)
    return web.json_response({"ok": True, "id": pm.id, "url": url})


async def page_pic(request):
    m = request.match_info
    try:
        kind, uid, key, bg, fs = m["kind"], int(m["uid"]), m["key"], int(m["bg"]), int(m["fs"])
    except ValueError:
        raise web.HTTPNotFound()
    if kind not in ("a", "t") or not hmac.compare_digest(pic_sig(kind, uid, key, bg, fs), m["sig"]):
        raise web.HTTPNotFound()
    u = await get_user(uid)
    if not u or not u["city"] or not u["tz"]:
        raise web.HTTPNotFound()
    try:
        jpg = await pic_bytes(u, kind, key.replace(".", ":"), bg % art.N_BG, fs % art.N_FONT)
    except Exception:  # noqa: BLE001
        log.exception("picture failed")
        raise web.HTTPServiceUnavailable()
    return web.Response(body=jpg, content_type="image/jpeg", headers={"Cache-Control": "public, max-age=86400"})


# ───────────────────────── "Share with friends": an animated card (assets/share/mawaqit_card_<lang>.mp4) ─────────────────────────

SHARE_CARD_DIR = Path(__file__).with_name("assets") / "share"
SHARE_CARD_LANGS = ("en", "ru", "uz", "uzc", "tg", "ar")


SHARE_LOCKS = {}  # user_id -> lock, so quick repeated presses run one after another


async def share_sent(uid):
    try:
        return [x for x in json.loads(await kv_get(f"sharemsg:{uid}", "[]") or "[]") if isinstance(x, list)]
    except ValueError:
        return []


async def share_cards_forget(bot, uid, kind=None):
    """Removes the cards sent before: all of them (a new "Share"), or only those of one kind (no duplicates)."""
    keep, gone = [], []
    for mid, k in await share_sent(uid):
        (gone if kind is None or k == kind else keep).append([mid, k])
    for mid, _ in gone:
        try:
            await bot.delete_message(uid, mid)
        except Exception:  # noqa: BLE001
            pass
    await kv_set(f"sharemsg:{uid}", json.dumps(keep))


async def share_cards_remember(uid, msg, kind):
    if msg:
        await kv_set(f"sharemsg:{uid}", json.dumps((await share_sent(uid) + [[msg.message_id, kind]])[-10:]))


async def share_card_send(bot, uid, kind=None, fresh=False):
    """fresh: a new press of "Share" (everything old goes); otherwise only an older card of the same kind goes."""
    lock = SHARE_LOCKS.setdefault(uid, asyncio.Lock())
    async with lock:
        u = await get_user(uid)
        kind = kind or invite_cfg()["mode"]
        await share_cards_forget(bot, uid, None if fresh else kind)
        await share_cards_remember(uid, await send_share_card(bot, u, kind), kind)


async def share_card_button(update, ctx):
    q = update.callback_query
    await q.answer()
    try:
        await update.effective_chat.send_action("upload_photo" if invite_cfg()["mode"] == "photo" else "upload_video")
    except Exception:  # noqa: BLE001
        pass
    await share_card_send(ctx.bot, q.from_user.id, fresh=True)


async def page_share(request):
    try:
        uid = int(request.match_info["uid"])
        day_iso = request.match_info["day"]
        datetime.strptime(day_iso, "%Y-%m-%d")
    except ValueError:
        raise web.HTTPNotFound()
    if not hmac.compare_digest(share_sig(uid, day_iso), request.match_info["sig"]):
        raise web.HTTPNotFound()
    u = await get_user(uid)
    if not u or not u["city"] or not u["tz"]:
        raise web.HTTPNotFound()
    try:
        png = await share_png_for(u, day_iso)
    except Exception:  # noqa: BLE001
        log.exception("share image failed")
        raise web.HTTPServiceUnavailable()
    return web.Response(body=png, content_type="image/jpeg", headers={"Cache-Control": "public, max-age=3600"})


async def api_share_send(request):
    """Send the picture to the user's chat with the bot, so they can keep or forward it."""
    tg_user, u, lang = await api_auth(request)
    if not u or not u["city"] or not u["tz"]:
        raise web.HTTPBadRequest(text="no city")
    day_iso = datetime.now(ZoneInfo(u["tz"])).date().isoformat()
    try:
        png = await pic_bytes(u, "t", day_iso, u["share_bg"], u["share_font"])
        await request.app["bot"].send_photo(u["user_id"], png, caption=f"@{BOT_USERNAME}")
    except Exception:  # noqa: BLE001
        log.exception("share send failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True})


# ───────────────────────── compass picture (groups, desktop, no domain) ─────────────────────────

COMPASS_CACHE = {}


def compass_png(bearing):
    """A clean compass card with a gold arrow pointing to the Qibla."""
    key = round(bearing)
    if key in COMPASS_CACHE:
        return COMPASS_CACHE[key]
    from PIL import Image, ImageDraw, ImageFont

    S = 1600  # draw big, then shrink for smooth edges
    c = S // 2
    img = Image.new("RGB", (S, S), (14, 24, 41))
    d = ImageDraw.Draw(img)
    gold, soft, white, red = (212, 175, 55), (70, 86, 112), (236, 240, 246), (230, 92, 92)

    def font(size):
        try:
            return ImageFont.load_default(size=size)
        except TypeError:  # very old Pillow
            return ImageFont.load_default()

    def pt(angle, r):
        a = math.radians(angle)
        return c + r * math.sin(a), c - r * math.cos(a)

    R = 640
    d.ellipse([c - R - 18, c - R - 18, c + R + 18, c + R + 18], fill=(20, 33, 56))
    d.ellipse([c - R, c - R, c + R, c + R], outline=gold, width=10)
    for a in range(0, 360, 5):
        long_ = a % 30 == 0
        d.line([pt(a, R - (70 if long_ else 36)), pt(a, R - 12)], fill=white if long_ else soft,
               width=8 if long_ else 4)
    f_big = font(120)
    for a, label in ((0, "N"), (90, "E"), (180, "S"), (270, "W")):
        x, y = pt(a, R - 150)
        d.text((x, y), label, fill=red if label == "N" else white, font=f_big, anchor="mm")

    # arrow
    tip, tail = pt(key, R - 120), pt(key + 180, 170)
    left, right = pt(key - 90, 46), pt(key + 90, 46)
    d.line([tail, tip], fill=gold, width=30)
    hb1, hb2 = pt(key - 7, R - 300), pt(key + 7, R - 300)
    d.polygon([tip, hb1, hb2], fill=gold)
    d.polygon([pt(key, 120), left, pt(key + 180, 60), right], fill=gold)
    d.ellipse([c - 34, c - 34, c + 34, c + 34], fill=(14, 24, 41), outline=gold, width=10)

    # Kaaba at the tip
    kx, ky = pt(key, R + 2)
    k = 70
    d.rectangle([kx - k, ky - k, kx + k, ky + k], fill=(18, 18, 18), outline=gold, width=8)
    d.rectangle([kx - k, ky - k + 34, kx + k, ky - k + 54], fill=gold)

    img = img.resize((800, 800), Image.LANCZOS)
    d = ImageDraw.Draw(img)
    d.text((400, 760), f"{key}°", fill=gold, font=font(44), anchor="mm")
    buf = io.BytesIO()
    img.save(buf, "PNG", optimize=True)
    COMPASS_CACHE[key] = buf.getvalue()
    return COMPASS_CACHE[key]


async def send_qibla_image(update, u):
    lang = u["lang"]
    deg = qibla_bearing(u["lat"], u["lon"])
    arrow = ARROWS[int((deg + 22.5) // 45) % 8]
    caption = t(lang, "qibla", city=esc(u["city"]), arrow=arrow, deg=round(deg)) + "\n\n" + t(lang, "qibla_img_hint")
    rows = []
    if is_private(u) and WEBAPP_URL:
        rows.append([webapp_btn(t(lang, "btn_compass"), "qibla")])
    rows.append([btn(t(lang, "btn_menu"), "m:home")])
    photo = await asyncio.get_running_loop().run_in_executor(None, compass_png, deg)
    await update.effective_chat.send_photo(photo, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb(*rows))


# ───────────────────────── mini app: mosques & places ─────────────────────────

OVERPASS = (  # free OpenStreetMap servers; each is tried in turn
    "https://overpass-api.de/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.osm.jp/api/interpreter",
)
MOSQUE_CACHE = {}
MOSQUE_RADII = (3000, 10000, 25000)


async def overpass(query):
    last = None
    for url in OVERPASS:  # the free servers are often busy, so try the mirrors in turn (short wait each)
        try:
            r = await HTTP.post(url, data={"data": query}, timeout=httpx.Timeout(14, connect=5),
                                headers={"User-Agent": f"PrayerTimesTelegramBot/1.0 ({CONTACT})"})
            r.raise_for_status()
            return r.json().get("elements", [])
        except Exception as e:  # noqa: BLE001
            last = e
            log.warning("overpass %s failed: %r", url, e)
    raise last or RuntimeError("overpass unavailable")


def _mosque_item(osm_id, la, lo, name, names):
    return {"id": osm_id, "lat": la, "lon": lo, "name": name or "", "names": names or {}}


async def mosques_overpass(lat, lon, radius):
    q = (f'[out:json][timeout:20];(nwr["amenity"="place_of_worship"]["religion"="muslim"](around:{radius},{lat},{lon});'
         f'nwr["building"="mosque"](around:{radius},{lat},{lon}););out center 300;')
    items = []
    for e in await overpass(q):
        la = e.get("lat") or (e.get("center") or {}).get("lat")
        lo = e.get("lon") or (e.get("center") or {}).get("lon")
        if la is None or lo is None:
            continue
        tags = e.get("tags") or {}
        names = {k[5:]: v for k, v in tags.items() if k.startswith("name:") and len(k) == 7}
        items.append(_mosque_item(f"{e.get('type', 'n')[0]}{e.get('id')}", la, lo, tags.get("name"), names))
    return items


async def mosques_nominatim(lat, lon, radius):
    """Backup when every Overpass server is down: OpenStreetMap's geocoder knows mosques too."""
    dlat = radius / 111000
    dlon = radius / (111000 * max(0.2, math.cos(math.radians(lat))))
    items = []
    for q in ("mosque", "masjid"):
        data = await nominatim("search", {"q": q, "limit": 50, "bounded": 1, "extratags": 1, "namedetails": 1,
                                          "viewbox": f"{lon - dlon},{lat + dlat},{lon + dlon},{lat - dlat}"})
        for d in data or []:
            cat, typ = d.get("category") or d.get("class"), d.get("type")
            if not ((cat == "amenity" and typ == "place_of_worship") or (cat == "building" and typ == "mosque")):
                continue  # streets or shops that are only called "masjid"
            nd = d.get("namedetails") or {}
            names = {k[5:]: v for k, v in nd.items() if k.startswith("name:") and len(k) == 7}
            items.append(_mosque_item(f"{(d.get('osm_type') or 'n')[0]}{d.get('osm_id')}", float(d["lat"]), float(d["lon"]),
                                      nd.get("name") or d.get("name"), names))
    uniq = {i["id"]: i for i in items}
    return list(uniq.values())


async def mosques_saved(lat, lon, radius):
    dlat = radius / 111000
    dlon = radius / (111000 * max(0.2, math.cos(math.radians(lat))))
    rows = await POOL.fetch("SELECT * FROM mosques WHERE lat BETWEEN $1 AND $2 AND lon BETWEEN $3 AND $4 LIMIT 500",
                            lat - dlat, lat + dlat, lon - dlon, lon + dlon)
    return [_mosque_item(r["osm_id"], r["lat"], r["lon"], r["name"], json.loads(r["names"] or "{}")) for r in rows
            if km(lat, lon, r["lat"], r["lon"]) * 1000 <= radius]


async def save_mosques(items):
    if not items:
        return
    try:
        await POOL.executemany(
            "INSERT INTO mosques (osm_id, lat, lon, name, names) VALUES ($1, $2, $3, $4, $5) "
            "ON CONFLICT (osm_id) DO UPDATE SET lat = EXCLUDED.lat, lon = EXCLUDED.lon, name = EXCLUDED.name, "
            "names = EXCLUDED.names, updated_at = now()",
            [(i["id"], i["lat"], i["lon"], i["name"], json.dumps(i["names"], ensure_ascii=False)) for i in items])
    except Exception:  # noqa: BLE001
        log.exception("could not save mosques")


async def find_mosques(lat, lon):
    """Overpass mirrors → saved mosques → Nominatim; the search widens 3 → 10 → 25 km while nothing is found."""
    source = "osm"
    for radius in MOSQUE_RADII:
        items = []
        try:
            items = await mosques_overpass(lat, lon, radius)
            await save_mosques(items)
        except Exception:  # noqa: BLE001
            items = await mosques_saved(lat, lon, radius)
            source = "saved"
            if not items:
                try:
                    items = await mosques_nominatim(lat, lon, radius)
                    await save_mosques(items)
                    source = "nominatim"
                except Exception:  # noqa: BLE001
                    log.exception("nominatim mosques failed")
        if items:
            return items, radius, source
    return [], MOSQUE_RADII[-1], source


async def api_mosques(request):
    _, u, lang = await api_auth(request)
    try:
        lat, lon = float(request.query["lat"]), float(request.query["lon"])
        if not (-90 <= lat <= 90 and -180 <= lon <= 180):
            raise ValueError
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad place")
    key = (round(lat, 2), round(lon, 2))
    hit = MOSQUE_CACHE.get(key)
    if hit and _time.time() - hit[0] < 6 * 3600:
        return web.json_response(hit[1])
    items, radius, source = await find_mosques(lat, lon)
    out = {"ok": True, "radius": radius, "items": items, "source": source}
    if items and source == "osm":  # only cache fresh results; after a failure try the servers again next time
        if len(MOSQUE_CACHE) > 300:
            MOSQUE_CACHE.clear()
        MOSQUE_CACHE[key] = (_time.time(), out)
    log.info("mosques %.2f,%.2f: %d within %d m (%s)", lat, lon, len(items), radius, source)
    return web.json_response(out)


async def api_reverse(request):
    _, u, lang = await api_auth(request)
    try:
        lat, lon = float(request.query["lat"]), float(request.query["lon"])
        if not (-90 <= lat <= 90 and -180 <= lon <= 180):
            raise ValueError
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad place")
    name, cc = await reverse_geocode(lat, lon, lang)
    return web.json_response({"ok": True, "name": name, "cc": cc, "flag": flag(cc) if cc else "",
                              "lat": lat, "lon": lon})


# ───────────────────────── mini app: admin panel ─────────────────────────
# Every call checks the signed Telegram data and that the caller is one of ADMINS.

async def admin_auth(request, perm=None):
    tg_user = check_init_data(request.headers.get("X-Init-Data", ""))
    if not tg_user or not is_admin(int(tg_user["id"])):
        raise web.HTTPForbidden(text="admins only")
    if perm and not has_perm(int(tg_user["id"]), perm):
        raise web.HTTPForbidden(text="no right: " + perm)
    return int(tg_user["id"])


def series(rows, days=30):
    have = {r["d"].isoformat(): r["c"] for r in rows}
    today = datetime.utcnow().date()
    return [{"d": (today - timedelta(days=i)).isoformat(), "c": have.get((today - timedelta(days=i)).isoformat(), 0)}
            for i in range(days - 1, -1, -1)]


async def api_admin_summary(request):
    await admin_auth(request, "stats")
    r = await POOL.fetchrow("""
        SELECT count(*) AS total,
               count(*) FILTER (WHERE onboarded) AS setup,
               count(*) FILTER (WHERE remind AND NOT blocked AND NOT banned) AS reminders,
               count(*) FILTER (WHERE created_at >= date_trunc('day', now())) AS new_today,
               count(*) FILTER (WHERE created_at >= now() - interval '7 days') AS new_week,
               count(*) FILTER (WHERE last_seen >= now() - interval '7 days') AS active_week,
               count(*) FILTER (WHERE banned) AS banned,
               count(*) FILTER (WHERE blocked) AS blocked
        FROM users WHERE chat_type = 'private'""")
    ch = await POOL.fetchrow("""
        SELECT count(*) FILTER (WHERE chat_type = 'group') AS groups,
               count(*) FILTER (WHERE chat_type = 'channel') AS channels,
               coalesce(sum(members), 0) AS members
        FROM users WHERE chat_type <> 'private' AND NOT blocked""")
    c = await today_counters()
    new = await POOL.fetch("SELECT created_at::date AS d, count(*) AS c FROM users WHERE chat_type = 'private' "
                           "AND created_at > now() - interval '31 days' GROUP BY 1")
    act = await POOL.fetch("SELECT day AS d, count(*) AS c FROM daily_active WHERE day > CURRENT_DATE - 31 GROUP BY 1")
    rem = await POOL.fetch("SELECT stat_day AS d, stat_value AS c FROM daily_stats "
                           "WHERE stat_key = 'reminders_sent' AND stat_day > CURRENT_DATE - 31")
    langs = await POOL.fetch("SELECT lang AS k, count(*) AS c FROM users WHERE lang IS NOT NULL AND chat_type = 'private' "
                             "GROUP BY lang ORDER BY c DESC")
    madh = await POOL.fetch("SELECT madhab AS k, count(*) AS c FROM users WHERE madhab IS NOT NULL GROUP BY madhab ORDER BY c DESC")
    countries = await POOL.fetch("SELECT lower(country) AS k, count(*) AS c FROM users WHERE coalesce(country, '') <> '' "
                                 "GROUP BY lower(country) ORDER BY c DESC LIMIT 10")
    cities = await city_clusters()
    return web.json_response({
        "ok": True, "users": dict(r), "chats": dict(ch),
        "today": {"support": c.get("support_msgs", 0), "sent": c.get("reminders_sent", 0), "failed": c.get("reminders_failed", 0)},
        "new": series(new), "active": series(act), "reminders": series(rem),
        "langs": [{"k": x["k"], "label": LANG_BUTTONS.get(x["k"], x["k"]), "c": x["c"]} for x in langs],
        "madhabs": [{"k": x["k"], "label": MADHAB_RU.get(x["k"], x["k"]), "c": x["c"]} for x in madh],
        "countries": [{"k": x["k"], "label": f"{flag(x['k'])} {x['k'].upper()}", "c": x["c"]} for x in countries],
        "cities": [{"label": g["name"], "c": g["c"]} for g in cities],
    })


def person_json(r):
    return {"id": r["user_id"], "name": r["full_name"], "username": r["username"], "city": r["city"],
            "flag": flag(r["country"]) if r["country"] else "", "lang": r["lang"], "banned": r["banned"],
            "blocked": r["blocked"], "type": r["chat_type"], "title": r["title"], "members": r["members"],
            "last_seen": r["last_seen"].isoformat() if r["last_seen"] else None,
            "created": r["created_at"].isoformat() if r["created_at"] else None}


async def api_admin_people(request):
    viewer = await admin_auth(request, "users")
    kind = request.query.get("kind", "users")
    flt = request.query.get("filter", "all")
    q = (request.query.get("q") or "").strip()[:64]
    try:
        page = max(0, int(request.query.get("page", "0")))
    except ValueError:
        page = 0
    where, args = ("chat_type = 'private'" if kind == "users" else "chat_type <> 'private'"), []
    if q:
        w, args = search_where(q)
        where += " AND " + w
    where += {"active": " AND last_seen >= now() - interval '7 days'", "banned": " AND banned",
              "blocked": " AND blocked"}.get(flt, "")
    if not is_main(viewer):
        where += " AND NOT hidden"
    total = await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)
    rows = await POOL.fetch(f"SELECT * FROM users WHERE {where} ORDER BY last_seen DESC NULLS LAST, created_at DESC "
                            f"LIMIT 20 OFFSET {page * 20}", *args)
    return web.json_response({"ok": True, "total": total, "page": page, "items": [person_json(r) for r in rows]})


async def api_admin_person(request):
    viewer = await admin_auth(request, "users")
    try:
        uid = int(request.query["id"])
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad id")
    r = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    if not r or (r["hidden"] and not is_main(viewer)):
        raise web.HTTPNotFound()
    u = dict(r)
    out = person_json(r)
    out["hidden"] = r["hidden"]
    out["can_hide"] = is_main(viewer)
    owned = await POOL.fetchrow(
        "SELECT count(*) FILTER (WHERE chat_type = 'group') AS g, count(*) FILTER (WHERE chat_type = 'channel') AS c "
        "FROM users WHERE owner_id = $1 AND NOT blocked", uid)
    owner = await POOL.fetchrow("SELECT user_id, full_name, username FROM users WHERE user_id = $1", u["owner_id"]) \
        if u["owner_id"] else None
    lead = (f"за {u['lead_min']} мин" if u["lead_min"] else "без заранее") + (" + в момент азана" if u["at_time"] else "")
    out.update({
        "madhab": MADHAB_RU.get(u["madhab"], "—"), "lang_label": LANG_BUTTONS.get(u["lang"], "—"), "tz": u["tz"],
        "reminders": ("вкл: " + lead) if u["remind"] else "выкл",
        "quiet": "выкл" if u["quiet_start"] is None else f"{u['quiet_start']:02d}:00–{u['quiet_end']:02d}:00",
        "auto": auto_label("ru", u["auto_mode"]), "ramadan": u["ramadan"], "daily": u["daily"],
        "owned_groups": owned["g"], "owned_channels": owned["c"], "is_admin": is_admin(uid),
        "owner": {"id": owner["user_id"], "name": owner["full_name"], "username": owner["username"]} if owner else None,
    })
    return web.json_response({"ok": True, "person": out})


async def api_admin_ban(request):
    await admin_auth(request, "bans")
    body = await read_json(request)
    try:
        uid, ban = int(body["id"]), bool(body["ban"])
    except (KeyError, ValueError, TypeError):
        raise web.HTTPBadRequest(text="bad request")
    if is_admin(uid):
        raise web.HTTPBadRequest(text="cannot ban an admin")
    await POOL.execute("UPDATE users SET banned = $2 WHERE user_id = $1", uid, ban)
    return web.json_response({"ok": True})


def admin_markup_text(text):
    """Plain text from the app, with **bold** and __italic__, made safe for Telegram HTML."""
    import re
    s = esc(text)
    s = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", s, flags=re.S)
    return re.sub(r"__(.+?)__", r"<i>\1</i>", s, flags=re.S)


async def api_admin_hide(request):
    viewer = await admin_auth(request)
    if not is_main(viewer):
        raise web.HTTPForbidden(text="main admin only")
    body = await read_json(request)
    try:
        uid = int(body["id"])
    except (KeyError, TypeError, ValueError):
        raise web.HTTPBadRequest(text="bad id")
    hidden = await POOL.fetchval("UPDATE users SET hidden = NOT hidden WHERE user_id = $1 RETURNING hidden", uid)
    return web.json_response({"ok": True, "hidden": hidden})


async def api_admin_message(request):
    await admin_auth(request, "support")
    body = await read_json(request)
    try:
        uid, text = int(body["id"]), str(body["text"]).strip()[:3500]
    except (KeyError, ValueError, TypeError):
        raise web.HTTPBadRequest(text="bad request")
    if not text:
        raise web.HTTPBadRequest(text="empty")
    u = await get_user(uid)
    lang = (u or {}).get("lang") or "en"
    try:
        m = await request.app["bot"].send_message(uid, t(lang, "admin_msg_header") + "\n\n" + admin_markup_text(text),
                                                  parse_mode=ParseMode.HTML)
        await log_sent(uid, m.message_id, "admin", "от админа: " + text[:60])
    except Forbidden:
        await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", uid)
        return web.json_response({"ok": False, "error": "blocked"})
    except Exception:  # noqa: BLE001
        log.exception("admin message failed")
        return web.json_response({"ok": False, "error": "failed"})
    return web.json_response({"ok": True})


def bc_from_body(body):
    kind = body.get("kind") if body.get("kind") in ("all", "everything", "lang", "country") else "all"
    value = None
    if kind == "lang":
        value = body.get("value") if body.get("value") in LANGS else "ru"
    elif kind == "country":
        value = str(body.get("value") or "").strip().lower()[:2]
        if len(value) != 2 or not value.isalpha():
            raise web.HTTPBadRequest(text="bad country")
    return {"kind": kind, "value": value, "text": None}


async def api_admin_bc_count(request):
    await admin_auth(request, "bc")
    bc = bc_from_body(dict(request.query))
    where, args = bc_where(bc)
    return web.json_response({"ok": True, "count": await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args),
                              "label": bc_label(bc)})


async def api_admin_broadcast(request):
    admin = await admin_auth(request, "bc")
    body = await read_json(request)
    bc = bc_from_body(body)
    text = admin_markup_text(str(body.get("text") or "").strip()[:3500])
    photo = None
    if body.get("photo"):
        import base64
        try:
            raw = str(body["photo"]).split(",", 1)[-1]
            photo = base64.b64decode(raw, validate=True)
            if len(photo) > 8 * 1024 * 1024:
                raise ValueError
        except Exception:  # noqa: BLE001
            raise web.HTTPBadRequest(text="bad photo")
    if not text and not photo:
        raise web.HTTPBadRequest(text="empty")
    if photo and len(text) > 1024:
        raise web.HTTPBadRequest(text="caption too long")
    btn_text, btn_url = str(body.get("button_text") or "").strip()[:60], str(body.get("button_url") or "").strip()[:500]
    if btn_text or btn_url:
        if not (btn_text and (btn_url.startswith("https://") or btn_url.startswith("http://"))):
            raise web.HTTPBadRequest(text="bad button")
        bc["button"] = (btn_text, btn_url)
    bc["photo"] = photo
    ptb = request.app["ptb"]
    if ptb.bot_data.get("bc_running"):
        return web.json_response({"ok": False, "error": "running"}, status=409)
    task = asyncio.create_task(run_broadcast(ptb, admin, text, bc))
    tasks = ptb.bot_data.setdefault("tasks", set())
    tasks.add(task)
    task.add_done_callback(tasks.discard)
    return web.json_response({"ok": True})


async def api_admin_health(request):
    await admin_auth(request, "health")
    t0 = _time.perf_counter()
    await POOL.fetchval("SELECT 1")
    db_ms = round((_time.perf_counter() - t0) * 1000)
    t1 = _time.perf_counter()
    try:
        await fetch_timings(KAABA[0], KAABA[1], datetime.utcnow().date(), 4, 0)
        api = {"ok": True, "ms": round((_time.perf_counter() - t1) * 1000)}
    except Exception as e:  # noqa: BLE001
        api = {"ok": False, "error": type(e).__name__}
    c = await today_counters()
    active = await POOL.fetchval("SELECT count(*) FROM users WHERE remind AND NOT blocked AND NOT banned AND tz IS NOT NULL")
    cards = await POOL.fetchval("SELECT count(*) FROM times_cards")
    return web.json_response({
        "ok": True, "db_ms": db_ms, "api": api, "uptime": int(_time.time() - START_TS), "reminder_users": active,
        "cache": len(CACHE), "live_cards": cards, "sent": c.get("reminders_sent", 0), "failed": c.get("reminders_failed", 0),
        "errors": [{"at": e[0].strftime("%d.%m %H:%M"), "msg": e[1]} for e in list(ERRBUF)[-8:]],
        "admins": sorted(ADMINS),
    })


async def api_admin_export(request):
    admin = await admin_auth(request, "export")
    rows = await POOL.fetch(f"SELECT {', '.join(CSV_COLUMNS)} FROM users WHERE NOT hidden OR $1 ORDER BY created_at", is_main(admin))
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(CSV_COLUMNS)
    for r in rows:
        w.writerow([r[c] for c in CSV_COLUMNS])
    data = io.BytesIO(buf.getvalue().encode("utf-8-sig"))
    try:
        await request.app["bot"].send_document(admin, document=data, filename=f"users_{datetime.utcnow():%Y%m%d_%H%M}.csv",
                                               caption=f"📤 Пользователей: {len(rows)}")
    except Exception:  # noqa: BLE001
        log.exception("export failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True, "rows": len(rows)})


# ───────────────────────── prayer times in any chat (inline mode) ─────────────────────────
# Needs inline mode switched on once in @BotFather (/setinline).

INLINE_GEO = {}


async def on_inline(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    iq = update.inline_query
    u = await get_user(iq.from_user.id)
    lang = (u or {}).get("lang") or str(iq.from_user.language_code or "en")[:2]
    lang = lang if lang in LANGS else "en"
    q = iq.query.strip()[:80]
    if q in ("card", "card " + lang) or q.startswith("card "):  # "Send to a friend" under the animated card
        cl = q.split()[1] if len(q.split()) > 1 and q.split()[1] in SHARE_CARD_LANGS else lang
        fid = await kv_get("share_card_" + cl)
        res = [InlineQueryResultCachedMpeg4Gif(id="card2_" + cl, mpeg4_file_id=fid,
                                               caption=t(cl, "fr_cap", bot=f"@{BOT_USERNAME}"))] if fid else []
        try:
            await iq.answer(res, cache_time=600, is_personal=False)
        except BadRequest as e:
            log.info("inline answer skipped: %s", e)
        return
    m = re.match(r"^pic ([0-9a-f]{12})$", q)
    if m:  # the "Share" button under a finished picture
        fid = await POOL.fetchval("SELECT file_id FROM share_pics WHERE id = $1", m.group(1))
        res = [InlineQueryResultCachedPhoto(id=m.group(1), photo_file_id=fid, caption=f"@{BOT_USERNAME}")] if fid else []
        try:
            await iq.answer(res, cache_time=3600, is_personal=False)
        except BadRequest as e:
            log.info("inline answer skipped: %s", e)
        return
    hint = InlineQueryResultsButton(text=t(lang, "in_hint"), start_parameter="inline")
    place = None
    try:
        if not q and u and u["city"] and u["lat"] is not None:
            place = (u["city"], u["lat"], u["lon"], u["country"] or "")
        elif len(q) >= 3:
            key = (q.lower(), lang)
            if key not in INLINE_GEO:
                if len(INLINE_GEO) > 2000:
                    INLINE_GEO.clear()
                INLINE_GEO[key] = await geocode(q, lang)
            place = INLINE_GEO[key]
        if not place:
            return await iq.answer([], cache_time=5, is_personal=True, button=hint)
        result = await times_share_result(place, lang, (u or {}).get("madhab"), iq.from_user.id)
        await iq.answer([result], cache_time=120, is_personal=True, button=hint)
    except BadRequest as e:
        log.info("inline answer skipped: %s", e)  # the query expired while the user kept typing
    except Exception:  # noqa: BLE001
        log.exception("inline query failed")


# ───────────────────────── tracker on the server, community, challenges ─────────────────────────

def mask_ok(m):
    return isinstance(m, str) and len(m) == 5 and set(m) <= {"0", "1"}


def iso_day(s):
    try:
        return datetime.strptime(str(s), "%Y-%m-%d").date()
    except ValueError:
        raise web.HTTPBadRequest(text="bad day")


async def api_tracker(request):
    tg_user, u, _ = await api_auth(request)
    uid = int(tg_user["id"])
    since = iso_day(request.query.get("from") or (datetime.utcnow().date() - timedelta(days=130)).isoformat())
    rows = await POOL.fetch("SELECT day, mask FROM tracker WHERE user_id = $1 AND day >= $2", uid, since)
    total = await POOL.fetchval("SELECT coalesce(sum(length(replace(mask, '0', ''))), 0) FROM tracker WHERE user_id = $1", uid)
    return web.json_response({"ok": True, "days": {r["day"].isoformat(): r["mask"] for r in rows}, "total": total})


async def api_tracker_set(request):
    tg_user, u, _ = await api_auth(request)
    body = await read_json(request)
    day, mask = iso_day(body.get("day")), body.get("mask")
    if not mask_ok(mask) or abs((day - datetime.utcnow().date()).days) > 400:
        raise web.HTTPBadRequest(text="bad mark")
    await POOL.execute("INSERT INTO tracker (user_id, day, mask) VALUES ($1, $2, $3) "
                       "ON CONFLICT (user_id, day) DO UPDATE SET mask = EXCLUDED.mask", int(tg_user["id"]), day, mask)
    if "1" in mask:
        asyncio.get_running_loop().create_task(check_badges(request.app["bot"], int(tg_user["id"])))
    return web.json_response({"ok": True})


async def api_tracker_bulk(request):
    """One-time move of old marks from Telegram cloud storage. Never overwrites marks already on the server."""
    tg_user, u, _ = await api_auth(request)
    body = await read_json(request)
    days = body.get("days") if isinstance(body.get("days"), dict) else {}
    rows = []
    for k, v in list(days.items())[:400]:
        try:
            d = iso_day(k)
        except web.HTTPBadRequest:
            continue
        if mask_ok(v) and v != "00000":
            rows.append((int(tg_user["id"]), d, v))
    if rows:
        await POOL.executemany("INSERT INTO tracker (user_id, day, mask) VALUES ($1, $2, $3) ON CONFLICT DO NOTHING", rows)
    return web.json_response({"ok": True, "saved": len(rows)})


async def api_community(request):
    await api_auth(request)
    day = iso_day(request.query.get("day") or datetime.utcnow().date().isoformat())
    r = await POOL.fetchrow("SELECT count(*) FILTER (WHERE mask = '11111') AS full, "
                            "count(*) FILTER (WHERE mask <> '00000') AS marked FROM tracker WHERE day = $1", day)
    return web.json_response({"ok": True, "full": r["full"], "marked": r["marked"]})


CH_MAX_MEMBERS = 50


async def challenge_view(ch, today):
    members = await POOL.fetch(
        "SELECT m.user_id, u.full_name, u.username FROM challenge_members m LEFT JOIN users u ON u.user_id = m.user_id "
        "WHERE m.challenge_id = $1 ORDER BY m.joined_at", ch["id"])
    end = ch["start_day"] + timedelta(days=ch["days"] - 1)
    upto = min(today, end)
    marks = await POOL.fetch("SELECT user_id, day, mask FROM tracker WHERE day >= $1 AND day <= $2 AND user_id = ANY($3::bigint[])",
                             ch["start_day"], upto, [m["user_id"] for m in members])
    by = {}
    for r in marks:
        by.setdefault(r["user_id"], {})[r["day"]] = r["mask"]
    out = []
    for m in members:
        mine = by.get(m["user_id"], {})
        out.append({"id": m["user_id"], "name": m["full_name"] or (("@" + m["username"]) if m["username"] else "👤"),
                    "full_days": sum(1 for v in mine.values() if v == "11111"),
                    "today": mine.get(today, "00000") if today <= end else None})
    out.sort(key=lambda x: (-x["full_days"], x["name"] or ""))
    return {"id": ch["id"], "code": ch["code"], "title": ch["title"], "days": ch["days"], "owner": ch["owner"],
            "start": ch["start_day"].isoformat(), "end": end.isoformat(),
            "day_no": max(0, min(ch["days"], (today - ch["start_day"]).days + 1)), "ended": today > end,
            "invite": f"https://t.me/{BOT_USERNAME}?start=ch_{ch['code']}", "members": out}


def user_today(u):
    try:
        return datetime.now(ZoneInfo(u["tz"])).date() if u and u["tz"] else datetime.utcnow().date()
    except Exception:  # noqa: BLE001
        return datetime.utcnow().date()


async def api_challenges(request):
    tg_user, u, _ = await api_auth(request)
    uid, today = int(tg_user["id"]), user_today(u)
    rows = await POOL.fetch("SELECT c.* FROM challenges c JOIN challenge_members m ON m.challenge_id = c.id "
                            "WHERE m.user_id = $1 AND c.start_day + c.days > $2::date - 30 ORDER BY c.created_at DESC", uid, today)
    return web.json_response({"ok": True, "items": [await challenge_view(r, today) for r in rows]})


async def api_challenge_new(request):
    import secrets
    tg_user, u, _ = await api_auth(request)
    uid = int(tg_user["id"])
    body = await read_json(request)
    days = body.get("days") if body.get("days") in (7, 14, 30, 40) else 7
    title = str(body.get("title") or "").strip()[:40] or f"{days} 🤝"
    today = user_today(u)
    active = await POOL.fetchval("SELECT count(*) FROM challenges WHERE owner = $1 AND start_day + days > $2", uid, today)
    if active >= 5:
        return web.json_response({"ok": False, "error": "limit"}, status=409)
    code = secrets.token_urlsafe(6).replace("-", "x").replace("_", "y")
    cid = await POOL.fetchval("INSERT INTO challenges (code, owner, title, days, start_day) VALUES ($1, $2, $3, $4, $5) RETURNING id",
                              code, uid, title, days, today)
    await POOL.execute("INSERT INTO challenge_members (challenge_id, user_id) VALUES ($1, $2)", cid, uid)
    ch = await POOL.fetchrow("SELECT * FROM challenges WHERE id = $1", cid)
    return web.json_response({"ok": True, "item": await challenge_view(ch, today)})


async def api_challenge_leave(request):
    tg_user, u, _ = await api_auth(request)
    body = await read_json(request)
    try:
        cid = int(body["id"])
    except (KeyError, ValueError, TypeError):
        raise web.HTTPBadRequest(text="bad id")
    await POOL.execute("DELETE FROM challenge_members WHERE challenge_id = $1 AND user_id = $2", cid, int(tg_user["id"]))
    await POOL.execute("DELETE FROM challenges c WHERE id = $1 AND NOT EXISTS "
                       "(SELECT 1 FROM challenge_members m WHERE m.challenge_id = c.id)", cid)
    return web.json_response({"ok": True})


async def join_challenge(update, ctx, code):
    """/start ch_<code> — join a friend's challenge."""
    uid = update.effective_user.id
    u = await ensure_user(uid)
    lang = u["lang"] or (update.effective_user.language_code or "en")[:2]
    lang = lang if lang in LANGS else "en"
    ch = await POOL.fetchrow("SELECT * FROM challenges WHERE code = $1", code[:20])
    if not ch or user_today(u) > ch["start_day"] + timedelta(days=ch["days"] - 1):
        return await update.effective_message.reply_text(t(lang, "ch_nf"))
    n = await POOL.fetchval("SELECT count(*) FROM challenge_members WHERE challenge_id = $1", ch["id"])
    already = await POOL.fetchval("SELECT 1 FROM challenge_members WHERE challenge_id = $1 AND user_id = $2", ch["id"], uid)
    if not already and n >= CH_MAX_MEMBERS:
        return await update.effective_message.reply_text(t(lang, "ch_full"))
    await POOL.execute("INSERT INTO challenge_members (challenge_id, user_id) VALUES ($1, $2) ON CONFLICT DO NOTHING", ch["id"], uid)
    markup = kb([webapp_btn(t(lang, "btn_open_ch"), "more&sub=challenges")]) if WEBAPP_URL else None
    await update.effective_message.reply_text(t(lang, "ch_joined", t=esc(ch["title"]), d=ch["days"]),
                                              parse_mode=ParseMode.HTML, reply_markup=markup)


# ───────────────────────── weekly report & admin summary ─────────────────────────

def week_squares(masks, days):
    return "".join("🟩" if masks.get(d) == "11111" else ("🟨" if masks.get(d, "00000") != "00000" else "⬜") for d in days)


async def send_weekly(bot, u, today):
    days = [today - timedelta(days=i) for i in range(7, 0, -1)]  # last Monday … Sunday
    rows = await POOL.fetch("SELECT day, mask FROM tracker WHERE user_id = $1 AND day >= $2", u["user_id"], today - timedelta(days=400))
    masks = {r["day"]: r["mask"] for r in rows}
    n = sum(masks.get(d, "").count("1") for d in days)
    full = sum(1 for d in days if masks.get(d) == "11111")
    streak, d = 0, today - timedelta(days=1)
    while masks.get(d) == "11111":
        streak += 1
        d -= timedelta(days=1)
    lang = u["lang"]
    p = round(100 * n / 35)
    text = "\n".join([
        t(lang, "wk_title", range=f"{days[0]:%d.%m}–{days[-1]:%d.%m}"), "",
        week_squares(masks, days), "",
        t(lang, "wk_prayers", n=n, p=p), t(lang, "wk_full", d=full), t(lang, "wk_streak", s=streak), "",
        t(lang, "wk_great" if p >= 85 else ("wk_good" if p >= 50 else "wk_start"))])
    markup = kb([webapp_btn(t(lang, "btn_open_tracker"), "more&sub=tracker")]) if WEBAPP_URL else None
    try:
        await bot.send_message(u["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=markup,
                               disable_notification=True)
    except Forbidden:
        await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", u["user_id"])
    except Exception:  # noqa: BLE001
        log.exception("weekly report failed for %s", u["user_id"])


async def admin_summary_text():
    y = datetime.utcnow().date() - timedelta(days=1)
    r = await POOL.fetchrow(
        "SELECT count(*) FILTER (WHERE chat_type = 'private') AS users, "
        "count(*) FILTER (WHERE chat_type = 'private' AND created_at::date = $1) AS new_users, "
        "count(*) FILTER (WHERE chat_type <> 'private' AND created_at::date = $1) AS new_chats, "
        "count(*) FILTER (WHERE chat_type = 'private' AND blocked) AS blocked FROM users", y)
    active = await POOL.fetchval("SELECT count(*) FROM daily_active WHERE day = $1", y)
    stats = {x["stat_key"]: x["stat_value"] for x in await POOL.fetch("SELECT stat_key, stat_value FROM daily_stats WHERE stat_day = $1", y)}
    full = await POOL.fetchval("SELECT count(*) FROM tracker WHERE day = $1 AND mask = '11111'", y)
    return (f"📬 <b>Сводка за {y:%d.%m.%Y}</b>\n\n"
            f"👥 Всего пользователей: <b>{r['users']}</b>\n"
            f"🆕 Новых: <b>{r['new_users']}</b> · 👥📢 новых групп и каналов: <b>{r['new_chats']}</b>\n"
            f"👁 Активных: <b>{active}</b>\n"
            f"📬 Напоминаний: <b>{stats.get('reminders_sent', 0)}</b> (ошибок {stats.get('reminders_failed', 0)})\n"
            f"📩 Сообщений в поддержку: <b>{stats.get('support_msgs', 0)}</b>\n"
            f"✅ Отметили все 5 намазов: <b>{full}</b>\n"
            f"🧱 Заблокировали бота (всего): {r['blocked']}")


async def periodic(context: ContextTypes.DEFAULT_TYPE):
    """Every 10 minutes: Monday 09:00 weekly reports (user's own time), 09:00 summary for admins."""
    bot = context.bot
    if bot_off():
        return
    try:
        rows = await POOL.fetch(
            "SELECT u.* FROM users u WHERE chat_type = 'private' AND weekly AND NOT banned AND NOT blocked "
            "AND tz IS NOT NULL AND lang IS NOT NULL "
            "AND EXISTS (SELECT 1 FROM tracker t WHERE t.user_id = u.user_id AND t.day > CURRENT_DATE - 14)")
        for r in rows:
            u = dict(r)
            now = datetime.now(ZoneInfo(u["tz"]))
            if now.weekday() == 0 and now.hour == 9 and u["last_weekly"] != now.date() and feat("weekly"):
                await POOL.execute("UPDATE users SET last_weekly = $2 WHERE user_id = $1", u["user_id"], now.date())
                await send_weekly(bot, u, now.date())
                await asyncio.sleep(0.05)
    except Exception:  # noqa: BLE001
        log.exception("weekly reports failed")
    try:  # ayah of the day at 09:00 local time
        rows = await POOL.fetch("SELECT * FROM users WHERE chat_type = 'private' AND ayah_rem AND NOT banned AND NOT blocked "
                                "AND tz IS NOT NULL AND lang IS NOT NULL")
        for r in rows:
            u = dict(r)
            now = datetime.now(ZoneInfo(u["tz"]))
            if now.hour == 9 and u["last_ayah"] != now.date() and feat("ayah"):
                await POOL.execute("UPDATE users SET last_ayah = $2 WHERE user_id = $1", u["user_id"], now.date())
                try:
                    text, markup = await screen_ayah(u, now.date())
                    await bot.send_message(u["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=markup,
                                           disable_notification=True)
                except Forbidden:
                    await save(u["user_id"], blocked=True)
                except Exception:  # noqa: BLE001
                    log.exception("ayah of the day failed for %s", u["user_id"])
                await asyncio.sleep(0.05)
    except Exception:  # noqa: BLE001
        log.exception("ayah of the day failed")
    try:
        await weekly_ayahs_job(bot)
    except Exception:  # noqa: BLE001
        log.exception("weekly ayahs failed")
    try:  # places saved while the geocoder was down: get the real city name and country
        rows = await POOL.fetch("SELECT user_id, lang, tz, city FROM users WHERE lat IS NOT NULL AND lang IS NOT NULL "
                                "AND (country IS NULL OR country = '' OR city ~ '^-?[0-9]+[.][0-9]+, -?[0-9]+[.][0-9]+$') LIMIT 5")
        for r in rows:
            await relocalize_city(r["user_id"], r["lang"], force_country=True)
    except Exception:  # noqa: BLE001
        log.exception("place fix failed")
    try:
        await POOL.execute("DELETE FROM ai_log WHERE at < now() - interval '90 days'")
        await POOL.execute("DELETE FROM share_pics WHERE at < now() - interval '60 days'")
    except Exception:  # noqa: BLE001
        pass
    try:
        await periodic_summaries(bot)
    except Exception:  # noqa: BLE001
        log.exception("summaries failed")
    try:
        for admin in sorted(a for a in ADMINS if has_perm(a, "summary")):
            a = await get_user(admin)
            tz = (a or {}).get("tz") or "Asia/Tashkent"
            now = datetime.now(ZoneInfo(tz))
            if now.hour != 9:
                continue
            done = await POOL.fetchval("SELECT 1 FROM daily_stats WHERE stat_day = $1 AND stat_key = $2",
                                       now.date(), f"admin_summary_{admin}")
            if done:
                continue
            await POOL.execute("INSERT INTO daily_stats (stat_day, stat_key, stat_value) VALUES ($1, $2, 1) "
                               "ON CONFLICT DO NOTHING", now.date(), f"admin_summary_{admin}")
            markup = kb([webapp_btn("🛠 Админка", "admin")]) if WEBAPP_URL else None
            try:
                await bot.send_message(admin, await admin_summary_text(), parse_mode=ParseMode.HTML, reply_markup=markup)
            except Exception:  # noqa: BLE001
                log.exception("admin summary to %s failed (has this admin started the bot?)", admin)
    except Exception:  # noqa: BLE001
        log.exception("admin summary failed")



# ───────────────────────── developer, share, groups screen ─────────────────────────

DEV_CONTACT = (os.environ.get("DEV_CONTACT") or "bdurrokhman").lstrip("@").strip()


def dev_btn(lang):
    return InlineKeyboardButton(t(lang, "btn_dev"), url=f"https://t.me/{DEV_CONTACT}")


async def share_times_text(u):
    """Plain prayer times for today with the bot link at the bottom (for Telegram's own "share" window)."""
    lang = u["lang"]
    today = datetime.now(ZoneInfo(u["tz"])).date()
    d = await get_timings(u, today)
    lines = [f"🕌 {strip_tags(t(lang, 'times_title')).replace('🕌', '').strip()} · {u['city']}", f"📅 {today:%d.%m.%Y}", ""]
    lines += [f"{emoji} {PN[lang][key.lower()]} — {d[key]}" for key, emoji in ROWS]
    lines += ["", t(lang, "share_footer", bot=f"@{BOT_USERNAME}")]
    return "\n".join(lines)


async def share_times_btn(u):
    """Telegram's own share window: pick a chat, the ready text is put in (with @bot at the bottom). Pictures: in the mini app."""
    text = await share_times_text(u)
    return InlineKeyboardButton(t(u["lang"], "btn_share"), url="https://t.me/share/url?url=" + quote(text, safe=""))


def strip_tags(x):
    return re.sub(r"<[^>]+>", "", x)


async def times_share_result(place, lang, madhab, sharer_id):
    """The message people share: today's prayer times and a link to the bot at the bottom."""
    name, lat, lon, cc = place
    pu = {"user_id": 0, "chat_type": "private", "lat": lat, "lon": lon, "country": cc, "lang": lang, "city": name,
          "madhab": madhab or "std", "ramadan": True, "tz": None}
    first = await get_timings(pu, datetime.utcnow().date())
    pu["tz"] = first["tz"]
    day = await get_timings(pu, datetime.now(ZoneInfo(pu["tz"])).date())
    text, _ = await screen_times(pu, onboarding=True)
    text = text.rsplit("\n\n", 1)[0]  # "next prayer in …" would be stale for whoever reads it later
    text += "\n\n" + t(lang, "share_footer", bot=f"@{BOT_USERNAME}")
    desc = " · ".join(f"{PN[lang][k.lower()]} {day[k]}" for k in EVENTS)
    return InlineQueryResultArticle(
        id=hashlib.md5(f"{lat:.3f},{lon:.3f},{lang},{pu['madhab']},{sharer_id}".encode()).hexdigest(),
        title=f"🕌 {name}", description=desc,
        input_message_content=InputTextMessageContent(text, parse_mode=ParseMode.HTML,
                                                      link_preview_options=LinkPreviewOptions(is_disabled=True)))


async def api_share_prepare(request):
    """Prepares the prayer-times message; the mini app then opens Telegram's share sheet with it."""
    tg_user, u, lang = await api_auth(request)
    if not u or not u["city"] or u["lat"] is None:
        raise web.HTTPBadRequest(text="no city")
    try:
        res = await times_share_result((u["city"], u["lat"], u["lon"], u["country"] or ""), u["lang"] or lang,
                                       u["madhab"], u["user_id"])
        pm = await request.app["bot"].save_prepared_inline_message(u["user_id"], res, allow_user_chats=True,
                                                                   allow_group_chats=True, allow_channel_chats=True)
    except Exception:  # noqa: BLE001
        log.exception("share prepare failed")
        return web.json_response({"ok": False}, status=502)
    return web.json_response({"ok": True, "id": pm.id})


def ref_link(uid):
    return f"https://t.me/{BOT_USERNAME}?start=r_{uid}"


def share_url_for(text, url):
    return f"https://t.me/share/url?url={quote(url, safe='')}&text={quote(text, safe='')}"


def screen_groups(u):
    lang = u["lang"]
    return t(lang, "groups_title"), kb([add_group_btn(lang)], [add_channel_btn(lang)],
                                       [btn(t(lang, "btn_my_channels"), "ch:list")],
                                       [btn(t(lang, "btn_back"), "s:settings")])


# ───────────────────────── adhan recordings (uploaded by admins) ─────────────────────────

AZANS = []  # [{"id", "name", "file_id", "kind"}]


async def load_azans():
    global AZANS
    AZANS = [dict(r) for r in await POOL.fetch("SELECT id, name, file_id, kind FROM azans ORDER BY id")]


def azan_by_id(v):
    return next((a for a in AZANS if str(a["id"]) == str(v or "")), None)


def azan_label(lang, u):
    a = azan_by_id(u.get("azan"))
    return a["name"] if a else t(lang, "off")


def screen_azan(u):
    lang = u["lang"]
    cur = azan_by_id(u.get("azan"))
    rows = [[btn(("✅ " if cur and cur["id"] == a["id"] else "") + "🔊 " + a["name"], f"set:azan:{a['id']}")] for a in AZANS]
    rows.append([btn(("✅ " if not cur else "") + "🔇 " + t(lang, "off").capitalize(), "set:azan:off")])
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "azan_title"), kb(*rows)


async def send_azan_file(bot, chat_id, a, **kw):
    if a["kind"] == "voice":
        return await bot.send_voice(chat_id, a["file_id"], **kw)
    if a["kind"] == "document":
        return await bot.send_document(chat_id, a["file_id"], **kw)
    return await bot.send_audio(chat_id, a["file_id"], **kw)


async def send_azan(bot, u):
    a = azan_by_id(u.get("azan"))
    if not a:
        return
    try:
        m = await send_azan_file(bot, u["user_id"], a, disable_notification=True)
        await POOL.execute("UPDATE users SET rem_msgs = array_append(rem_msgs, $2::bigint) WHERE user_id = $1",
                           u["user_id"], m.message_id)
        await schedule_delete(u["user_id"], m.message_id)
    except Exception:  # noqa: BLE001
        log.exception("adhan send failed for %s", u["user_id"])


async def screen_admin_azans():
    lines = ["🔊 <b>Азаны</b>", "",
             "Пользователи выбирают муэдзина в настройках. Запись приходит тихо сразу после напоминания в момент намаза.", ""]
    if AZANS:
        for a in AZANS:
            n = await POOL.fetchval("SELECT count(*) FROM users WHERE azan = $1", str(a["id"]))
            lines.append(f"• <b>{esc(a['name'])}</b> — выбрали {n}")
    else:
        lines.append("Пока нет ни одной записи. Пока их нет, кнопка азана у пользователей скрыта.")
    rows = [[btn("▶️ " + a["name"], f"a:azan:play:{a['id']}"), btn("🗑", f"a:azan:del:{a['id']}")] for a in AZANS]
    rows.append([btn("➕ Добавить азан", "a:azan:add")])
    rows.append(ADMIN_BACK)
    return "\n".join(lines), kb(*rows)


async def admin_azan(update, ctx, parts):
    op = parts[2] if len(parts) > 2 else ""
    if op == "add":
        ctx.user_data["admin_state"] = "azan"
        return await render(update, "➕ <b>Новый азан</b>\n\nОтправьте аудиофайл (mp3/m4a) или голосовое сообщение. "
                                    "В подписи к файлу напишите имя муэдзина — так его увидят пользователи.",
                            kb([btn("⬅️ Назад", "a:azan")]))
    if op == "play" and len(parts) > 3:
        a = azan_by_id(parts[3])
        if a:
            await send_azan_file(update.get_bot(), update.effective_chat.id, a, caption=a["name"])
        return
    if op == "del" and len(parts) > 3 and parts[3].isdigit():
        await POOL.execute("DELETE FROM azans WHERE id = $1", int(parts[3]))
        await POOL.execute("UPDATE users SET azan = NULL WHERE azan = $1", parts[3])
        await load_azans()
    text, markup = await screen_admin_azans()
    return await render(update, text, markup)


async def admin_azan_upload(update, ctx):
    """While the admin is adding an adhan: takes the audio file. Returns True if consumed."""
    msg = update.message
    f, kind_ = None, None
    if msg.audio:
        f, kind_ = msg.audio, "audio"
    elif msg.voice:
        f, kind_ = msg.voice, "voice"
    elif msg.document and (msg.document.mime_type or "").startswith("audio/"):
        f, kind_ = msg.document, "document"
    if not f:
        await msg.reply_text("Нужен аудиофайл или голосовое сообщение. Или нажмите «Назад».")
        return True
    name = (msg.caption or getattr(f, "title", None) or getattr(f, "performer", None) or "Азан").strip()[:40]
    await POOL.execute("INSERT INTO azans (name, file_id, kind) VALUES ($1, $2, $3)", name, f.file_id, kind_)
    await load_azans()
    ctx.user_data.pop("admin_state", None)
    text, markup = await screen_admin_azans()
    await msg.reply_text("✅ Добавлено: " + esc(name) + "\n\n" + text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return True


# ───────────────────────── "I prayed" from the reminder, achievements ─────────────────────────

BADGES = [("s7", "streak", 7), ("s30", "streak", 30), ("s100", "streak", 100),
          ("t100", "total", 100), ("t500", "total", 500), ("t1000", "total", 1000)]


APP_HINT = {0: ("rb_morning", "more&sub=azkar&az=m"), 2: ("rb_evening", "more&sub=azkar&az=e"), 4: ("rb_tracker", "more&sub=tracker")}


def prayed_markup(lang, day, idx, done=False):
    first = btn(t(lang, "btn_prayed_done"), "pr:ok") if done else btn(t(lang, "btn_prayed"), f"pr:{day}:{idx}")
    rows = [[first]]
    if WEBAPP_URL and idx in APP_HINT:  # Fajr → morning adhkar, Asr → evening adhkar, Isha → tracker
        key, tab = APP_HINT[idx]
        rows.append([webapp_btn(t(lang, key), tab)])
    rows.append([btn(t(lang, "btn_menu"), "m:new")])
    return kb(*rows)


TOUR_DIR = Path(__file__).with_name("assets")
TOUR_FILE_IDS = {}


async def send_tour(bot, u):
    """Once, right after the setup: what else is in the mini app, with buttons straight into each part."""
    if not WEBAPP_URL or not is_private(u) or u["tour_sent"] or not feat("tour"):
        return
    lang = u["lang"]
    await save(u["user_id"], tour_sent=True)
    b = lambda k, tab: webapp_btn(t(lang, k), tab)  # noqa: E731
    markup = kb([b("tb_qibla", "qibla"), b("tb_tasbih", "tasbih")],
                [b("tb_azkar", "more&sub=azkar"), b("tb_tracker", "more&sub=tracker")],
                [b("tb_cal", "cal"), b("tb_duas", "more&sub=duas")])
    try:
        img = TOUR_DIR / f"tour_{lang}.jpg"
        if img.exists():
            m = await bot.send_photo(u["user_id"], TOUR_FILE_IDS.get(lang) or img.read_bytes(), caption=t(lang, "tour_text"),
                                     parse_mode=ParseMode.HTML, reply_markup=markup)
            TOUR_FILE_IDS[lang] = m.photo[-1].file_id
        else:
            await bot.send_message(u["user_id"], t(lang, "tour_text"), parse_mode=ParseMode.HTML, reply_markup=markup)
    except Exception:  # noqa: BLE001
        log.exception("tour failed for %s", u["user_id"])


async def sync_menu_button(bot, u):
    """The button next to the message field is the same English "🕌 App" for everyone (set once for the whole bot)."""
    return


async def menu_buttons_job(context: ContextTypes.DEFAULT_TYPE):
    """Puts back the common "🕌 App" button for chats that got a per-language one earlier."""
    try:
        rows = await POOL.fetch("SELECT user_id FROM users WHERE menu_btn IS NOT NULL AND menu_btn <> 'default' LIMIT 25")
    except Exception:  # noqa: BLE001
        return
    for r in rows:
        try:
            await context.bot.set_chat_menu_button(chat_id=r["user_id"], menu_button=MenuButtonDefault())
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
            return
        except Exception:  # noqa: BLE001
            pass
        await POOL.execute("UPDATE users SET menu_btn = 'default' WHERE user_id = $1", r["user_id"])
        await asyncio.sleep(0.2)


async def on_prayed(update, ctx, parts):
    q = update.callback_query
    uid = q.from_user.id
    u = await get_user(uid)
    lang = (u or {}).get("lang") or "en"
    if len(parts) < 3:
        return await q.answer(t(lang, "prayed_toast"))
    try:
        day = datetime.strptime(parts[1], "%Y-%m-%d").date()
        idx = int(parts[2])
        assert 0 <= idx < 5
    except (ValueError, AssertionError):
        return await q.answer()
    mask = await POOL.fetchval("SELECT mask FROM tracker WHERE user_id = $1 AND day = $2", uid, day) or "00000"
    mask = mask[:idx] + "1" + mask[idx + 1:]
    await POOL.execute("INSERT INTO tracker (user_id, day, mask) VALUES ($1, $2, $3) "
                       "ON CONFLICT (user_id, day) DO UPDATE SET mask = EXCLUDED.mask", uid, day, mask)
    await q.answer(t(lang, "prayed_toast"))
    try:
        await q.edit_message_reply_markup(prayed_markup(lang, parts[1], idx, done=True))
    except Exception:  # noqa: BLE001
        pass
    await check_badges(update.get_bot(), uid)


async def tracker_stats(uid, today):
    rows = await POOL.fetch("SELECT day, mask FROM tracker WHERE user_id = $1 AND day > $2", uid, today - timedelta(days=400))
    masks = {r["day"]: r["mask"] for r in rows}
    total = await POOL.fetchval("SELECT coalesce(sum(length(replace(mask, '0', ''))), 0) FROM tracker WHERE user_id = $1", uid)
    d = today if masks.get(today) == "11111" else today - timedelta(days=1)
    streak = 0
    while masks.get(d) == "11111":
        streak += 1
        d -= timedelta(days=1)
    return streak, total


async def check_badges(bot, uid):
    """Sends one silent message when new achievements are earned."""
    try:
        u = await get_user(uid)
        if not u or not u["lang"] or u["banned"]:
            return
        lang = u["lang"]
        streak, total = await tracker_stats(uid, user_today(u))
        have = {r["code"] for r in await POOL.fetch("SELECT code FROM badges WHERE user_id = $1", uid)}
        new = [code for code, kind_, need in BADGES if code not in have and (streak if kind_ == "streak" else total) >= need]
        if not new:
            return
        got = []
        for code in new:
            if await POOL.fetchval("INSERT INTO badges (user_id, code) VALUES ($1, $2) ON CONFLICT DO NOTHING RETURNING 1", uid, code):
                got.append(code)
        if not got:
            return
        best = t(lang, "b_" + got[-1])
        rows = [[InlineKeyboardButton(t(lang, "btn_share"), url=share_url_for(t(lang, "badge_share", name=best), ref_link(uid)))]]
        if WEBAPP_URL:
            rows.append([webapp_btn(t(lang, "btn_open_tracker2"), "more&sub=tracker")])
        await bot.send_message(uid, t(lang, "badge_new", list="\n".join(t(lang, "b_" + c) for c in got)),
                               parse_mode=ParseMode.HTML, reply_markup=kb(*rows), disable_notification=True)
    except Forbidden:
        pass
    except Exception:  # noqa: BLE001
        log.exception("badges failed for %s", uid)


# ───────────────────────── sadaqah jariyah: invitations ─────────────────────────

async def credit_referral(bot, uid, ref_id):
    """Counts a newcomer for the person whose link brought them (only once, only for new users)."""
    if not ref_id or ref_id == uid:
        return
    try:
        row = await POOL.fetchrow("SELECT onboarded, referred_by, created_at > now() - interval '15 minutes' AS fresh "
                                  "FROM users WHERE user_id = $1", uid)
        ref = await get_user(ref_id)
        if not row or not ref or row["onboarded"] or row["referred_by"] or not row["fresh"] or ref["chat_type"] != "private":
            return
        await POOL.execute("UPDATE users SET referred_by = $2 WHERE user_id = $1", uid, ref_id)
        n = await POOL.fetchval("SELECT count(*) FROM users WHERE referred_by = $1", ref_id)
        if ref["lang"] and not ref["banned"] and not ref["blocked"]:
            await bot.send_message(ref_id, t(ref["lang"], "ref_joined", n=n), parse_mode=ParseMode.HTML, disable_notification=True)
    except Forbidden:
        pass
    except Exception:  # noqa: BLE001
        log.exception("referral failed")


# ───────────────────────── monthly and yearly summary ─────────────────────────

def period_stats(masks, start, end):
    days = [start + timedelta(days=i) for i in range((end - start).days + 1)]
    n = sum(masks.get(d, "").count("1") for d in days)
    full = sum(1 for d in days if masks.get(d) == "11111")
    best = cur = 0
    for d in days:
        cur = cur + 1 if masks.get(d) == "11111" else 0
        best = max(best, cur)
    per = [sum(1 for d in days if masks.get(d, "00000")[i] == "1") for i in range(5)]
    top = max(range(5), key=lambda i: per[i]) if any(per) else None
    return {"n": n, "m": len(days) * 5, "full": full, "best": best, "top": top}


def render_summary(u, title, period, st):
    """A 1080×1350 card with the period's numbers."""
    from PIL import Image, ImageDraw
    lang = u["lang"] or "en"
    rtl = lang == "ar"
    W, H = 1080, 1350
    img = Image.new("RGB", (W, H), (12, 21, 38))
    d = ImageDraw.Draw(img)
    for y in range(H):
        k = y / H
        d.line([(0, y), (W, y)], fill=(int(14 + 30 * k), int(24 + 12 * k), int(44 + 30 * k)))
    gold, white, hint, card, green = (212, 175, 55), (238, 242, 248), (160, 172, 194), (30, 44, 72), (34, 163, 122)

    def text(xy, s, font, fill, anchor="mm"):
        kw = {"direction": "rtl"} if rtl and any("؀" <= ch <= "ۿ" for ch in s) else {}
        try:
            d.text(xy, s, font=font, fill=fill, anchor=anchor, **kw)
        except Exception:  # noqa: BLE001
            d.text(xy, s, font=font, fill=fill, anchor=anchor)

    d.ellipse([W // 2 - 60, 90, W // 2 + 60, 210], fill=gold)
    d.ellipse([W // 2 - 32, 74, W // 2 + 80, 186], fill=(14, 24, 44))
    text((W // 2, 280), title, _font(64, True), white)
    text((W // 2, 350), u["city"] or "", _font(36), hint)
    pct = round(100 * st["n"] / st["m"]) if st["m"] else 0
    # big ring
    cx, cy, r = W // 2, 600, 190
    d.ellipse([cx - r, cy - r, cx + r, cy + r], outline=card, width=34)
    if pct:
        d.arc([cx - r, cy - r, cx + r, cy + r], start=-90, end=-90 + 360 * pct / 100, fill=gold, width=34)
    text((cx, cy - 20), str(st["n"]), _font(110, True), white)
    text((cx, cy + 70), f"{t(lang, 'img_prayers')} · {pct}%", _font(36), hint)
    boxes = [(str(st["full"]), t(lang, "img_full"), green), (str(st["best"]), t(lang, "img_best"), gold)]
    if st["top"] is not None:
        boxes.append((PN[lang][EVENTS[st["top"]].lower()], t(lang, "img_top"), white))
    bw = (W - 180 - 30 * (len(boxes) - 1)) // len(boxes)
    for i, (big, small, col) in enumerate(boxes):
        x = 90 + i * (bw + 30)
        d.rounded_rectangle([x, 880, x + bw, 1080], radius=36, fill=card)
        text((x + bw // 2, 955), big, _font(64 if len(big) < 6 else 44, True), col)
        text((x + bw // 2, 1035), small, _font(30), hint)
    if BOT_USERNAME:
        text((W // 2, H - 110), f"@{BOT_USERNAME}", _font(40, True), hint)
    buf = io.BytesIO()
    img.save(buf, "PNG", optimize=True)
    return buf.getvalue()


async def send_summary(bot, u, today):
    """1st of the month: last month's summary; on January 1st: the whole last year."""
    lang = u["lang"]
    yearly = today.month == 1
    end = today - timedelta(days=1)
    start = date(end.year, 1, 1) if yearly else end.replace(day=1)
    rows = await POOL.fetch("SELECT day, mask FROM tracker WHERE user_id = $1 AND day >= $2 AND day <= $3",
                            u["user_id"], start, end)
    masks = {r["day"]: r["mask"] for r in rows}
    if not any(m != "00000" for m in masks.values()):
        return
    st = period_stats(masks, start, end)
    period = str(end.year) if yearly else f"{T[lang]['months'][end.month - 1]} {end.year}"
    title = t(lang, "sum_y_title" if yearly else "sum_m_title", period=period)
    lines = [title, "", t(lang, "sum_prayers", n=st["n"], m=st["m"], p=round(100 * st["n"] / st["m"])),
             t(lang, "sum_full", d=st["full"]), t(lang, "sum_best", s=st["best"])]
    if st["top"] is not None:
        lines.append(t(lang, "sum_top", name=PN[lang][EVENTS[st["top"]].lower()]))
    lines += ["", t(lang, "sum_end"), "", f'<a href="{ref_link(u["user_id"])}">@{BOT_USERNAME}</a>']
    plain = title.replace("<b>", "").replace("</b>", "").replace("🎁 ", "")
    png = await asyncio.get_running_loop().run_in_executor(None, render_summary, u, plain, period, st)
    rows = [[InlineKeyboardButton(t(lang, "btn_share"),
                                  url=share_url_for(t(lang, "sum_share", period=period, n=st["n"]), ref_link(u["user_id"])))]]
    if WEBAPP_URL:
        rows.append([webapp_btn(t(lang, "btn_open_tracker2"), "more&sub=tracker")])
    try:
        await bot.send_photo(u["user_id"], png, caption="\n".join(lines), parse_mode=ParseMode.HTML,
                             reply_markup=kb(*rows), disable_notification=True)
    except Forbidden:
        await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", u["user_id"])
    except Exception:  # noqa: BLE001
        log.exception("summary failed for %s", u["user_id"])


async def periodic_summaries(bot):
    rows = await POOL.fetch(
        "SELECT u.* FROM users u WHERE chat_type = 'private' AND NOT banned AND NOT blocked "
        "AND tz IS NOT NULL AND lang IS NOT NULL "
        "AND EXISTS (SELECT 1 FROM tracker t WHERE t.user_id = u.user_id AND t.day > CURRENT_DATE - 400)")
    for r in rows:
        u = dict(r)
        now = datetime.now(ZoneInfo(u["tz"]))
        if now.day == 1 and now.hour == 10 and u["last_summary"] != now.date():
            await POOL.execute("UPDATE users SET last_summary = $2 WHERE user_id = $1", u["user_id"], now.date())
            await send_summary(bot, u, now.date())
            await asyncio.sleep(0.05)



# ───────────────────────── official local calendars ─────────────────────────
# Uzbekistan: the official calendar published on namozvaqti.uz (monthly tables for ~75 towns).
# Each user gets the table of the nearest town. If the site can't be read, the bot falls back to its own
# calculation tuned to the same calendar ("ca" method below), so reminders never stop.

NV_CITIES = [  # slug, lat, lon
    ("toshkent", 41.311, 69.280), ("angren", 41.017, 70.144), ("bekobod", 40.221, 69.270), ("olmaliq", 40.845, 69.598),
    ("yangiyol", 41.112, 69.047), ("gazalkent", 41.558, 69.771), ("parkent", 41.294, 69.677), ("piskent", 40.897, 69.350),
    ("boka", 40.811, 69.198), ("nurafshon", 41.040, 69.358),
    ("andijon", 40.783, 72.344), ("asaka", 40.641, 72.239), ("shahrixon", 40.712, 72.057), ("xojaobod", 40.668, 72.562),
    ("marhamat", 40.500, 72.333), ("paytug", 40.897, 72.245), ("xonobod", 40.802, 72.973),
    ("fargona", 40.384, 71.786), ("qoqon", 40.529, 70.943), ("margilon", 40.471, 71.725), ("quva", 40.522, 72.072),
    ("rishton", 40.357, 71.284), ("bogdod", 40.502, 71.217), ("oltiariq", 40.391, 71.474),
    ("samarqand", 39.654, 66.975), ("kattaqorgon", 39.899, 66.257), ("urgut", 39.402, 67.243), ("ishtixon", 39.966, 66.486),
    ("buxoro", 39.768, 64.421), ("gijduvon", 40.100, 64.683), ("qorakol", 39.500, 63.853), ("gazli", 40.133, 63.450),
    ("guliston", 40.490, 68.784), ("sirdaryo", 40.844, 68.661),
    ("jizzax", 40.116, 67.842), ("zomin", 39.960, 68.396), ("gallaorol", 40.022, 67.592), ("dostlik", 40.524, 68.036),
    ("navoiy", 40.084, 65.379), ("zarafshon", 41.573, 64.204), ("konimex", 40.267, 65.155), ("nurota", 40.565, 65.689),
    ("uchquduq", 42.157, 63.556),
    ("nukus", 42.460, 59.603), ("moynoq", 43.768, 59.022), ("taxtakopir", 43.017, 60.367), ("tortkol", 41.550, 61.000),
    ("qongirot", 43.043, 58.844),
    ("termiz", 37.224, 67.278), ("boysun", 38.206, 67.199), ("denov", 38.267, 67.900), ("sherobod", 37.667, 67.000),
    ("shorchi", 38.000, 67.783),
    ("qarshi", 38.861, 65.790), ("muborak", 39.255, 65.153), ("shahrisabz", 39.058, 66.834), ("guzor", 38.621, 66.248),
    ("namangan", 40.998, 71.672), ("chortoq", 41.069, 71.824), ("chust", 41.003, 71.238), ("pop1", 40.874, 71.110),
    ("uchqorgon", 41.114, 72.079),
    ("urganch", 41.550, 60.631), ("hazorasp", 41.320, 61.074), ("xonqa", 41.474, 60.787), ("shovot", 41.653, 60.304),
    ("xiva", 41.378, 60.364),
]
NV_MAX_KM = 150
NV_DATA = {}   # (slug, y, m) -> {day: {Fajr…Isha}} or None (not available)
NV_FAIL = {}   # (slug, y, m) -> time of the last failed attempt
NV_LOCK = asyncio.Lock()
_NV_ROW = re.compile(r"(?<![\d:])(\d{1,2})\s+(?:[^\d\s]{1,12}\s+){0,2}((?:\d{1,2}:\d{2}\s+){5}\d{1,2}:\d{2})")


def km(lat1, lon1, lat2, lon2):
    p = math.pi / 180
    a = (math.sin((lat2 - lat1) * p / 2) ** 2 + math.cos(lat1 * p) * math.cos(lat2 * p) * math.sin((lon2 - lon1) * p / 2) ** 2)
    return 12742 * math.asin(math.sqrt(a))


def nv_city(u):
    if (u.get("country") or "").lower() != "uz" or u.get("lat") is None:
        return None
    dist, slug = min((km(u["lat"], u["lon"], la, lo), s) for s, la, lo in NV_CITIES)
    return slug if dist <= NV_MAX_KM else None


def nv_parse(page, y, m):
    """Monthly table → {day: {Fajr, Sunrise, Dhuhr, Asr, Maghrib, Isha}}. None if it doesn't look right."""
    text = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", page)))
    n = (date(y + (m == 12), m % 12 + 1, 1) - timedelta(days=1)).day
    out = {}
    for mt in _NV_ROW.finditer(text):
        day = int(mt.group(1))
        times = [f"{int(x.split(':')[0]):02d}:{x.split(':')[1]}" for x in mt.group(2).split()]
        if 1 <= day <= n and day not in out and times == sorted(times):
            out[day] = dict(zip(TIMING_KEYS, times))
    return out if len(out) == n else None


async def nv_month(slug, y, m):
    key = (slug, y, m)
    if key in NV_DATA:
        return NV_DATA[key]
    if _time.time() - NV_FAIL.get(key, 0) < 1800:
        return None
    async with NV_LOCK:
        if key in NV_DATA:
            return NV_DATA[key]
        try:
            row = await POOL.fetchval("SELECT data FROM nv_months WHERE slug = $1 AND y = $2 AND m = $3", slug, y, m)
            if row:
                NV_DATA[key] = {int(k): v for k, v in json.loads(row).items()}
                return NV_DATA[key]
            r = await HTTP.get(f"https://namozvaqti.uz/oylik/{m}/{slug}", follow_redirects=True,
                               headers={"User-Agent": "MawaqitTimeBot/1.0 (+https://t.me/MawaqitTimeBot)"})
            r.raise_for_status()
            data = nv_parse(r.text, y, m)
            if not data:
                raise ValueError("table not recognised")
            await POOL.execute("INSERT INTO nv_months (slug, y, m, data) VALUES ($1, $2, $3, $4) ON CONFLICT DO NOTHING",
                               slug, y, m, json.dumps(data))
            NV_DATA[key] = data
            log.info("namozvaqti.uz: %s %d-%02d loaded (%d days)", slug, y, m, len(data))
            return data
        except Exception as e:  # noqa: BLE001
            NV_FAIL[key] = _time.time()
            log.warning("namozvaqti.uz: %s %d-%02d not available (%s), using own calculation", slug, y, m, e)
            return None


def _mins(hhmm):
    h, mm = hhmm.split(":")
    return int(h) * 60 + int(mm)


async def local_times(u, d, calc):
    """Times for day d from the official local calendar, merged over the calculated ones (calc)."""
    slug = nv_city(u)
    if not slug:
        return calc
    data = await nv_month(slug, d.year, d.month)
    day = data and data.get(d.day)
    if not day:
        return calc
    # sanity check against the calculation: the official table never differs by more than ~25 min
    if any(abs(_mins(day[k]) - _mins(calc[k])) > 25 for k in TIMING_KEYS if k != "Asr"):
        log.warning("namozvaqti.uz: %s %s looks wrong, ignored", slug, d)
        return calc
    out = dict(calc)
    for k in TIMING_KEYS:
        if k == "Asr" and u.get("madhab") != "hanafi":
            continue  # the official table gives the Hanafi Asr
        out[k] = day[k]
    return out


# ───────────────────────── admins and their rights ─────────────────────────
# ADMIN_ID is the main admin; ADMIN_ID and ADMIN_IDS are permanent and have every right.
# Only the main admin adds/removes other admins and picks their rights (stored in the "admins" table).

PERMANENT_ADMINS = set(ADMINS)
DB_ADMINS = {}  # user_id -> set of rights
PERMS = [("stats", "📈 Статистика и география"), ("users", "👥 Пользователи и поиск"), ("support", "💬 Поддержка"),
         ("bans", "🚫 Баны"), ("bc", "📣 Рассылки"), ("export", "📤 Экспорт CSV"), ("azan", "🔊 Азаны"),
         ("health", "🩺 Здоровье и тест"), ("summary", "📬 Ежедневная сводка"), ("ai", "🤖 ИИ-помощник")]
PERM_KEYS = [k for k, _ in PERMS]
DEFAULT_PERMS = ["stats", "support"]


def is_main(uid):
    return bool(ADMIN_ID) and uid == ADMIN_ID


def has_perm(uid, perm):
    if uid in PERMANENT_ADMINS:
        return True
    return perm in DB_ADMINS.get(uid, ())


def admin_perms(uid):
    return PERM_KEYS if uid in PERMANENT_ADMINS else [k for k in PERM_KEYS if k in DB_ADMINS.get(uid, ())]


async def load_admins():
    rows = await POOL.fetch("SELECT user_id, perms FROM admins")
    DB_ADMINS.clear()
    DB_ADMINS.update({r["user_id"]: set(r["perms"] or []) for r in rows if r["user_id"] not in PERMANENT_ADMINS})
    ADMINS.clear()
    ADMINS.update(PERMANENT_ADMINS | set(DB_ADMINS))


async def add_admin(bot, target, by):
    await POOL.execute("INSERT INTO admins (user_id, perms, added_by) VALUES ($1, $2, $3) ON CONFLICT DO NOTHING",
                       target, DEFAULT_PERMS, by)
    await load_admins()
    try:
        await bot.send_message(target, "🛠 <b>Вас назначили администратором бота Mawaqit</b>\n\n"
                                        "Админка открывается кнопкой ниже или командой /admin.",
                               parse_mode=ParseMode.HTML, reply_markup=kb([btn("🛠 Открыть админку", "a:home")]))
    except Exception:  # noqa: BLE001
        pass


async def remove_admin(bot, target):
    await POOL.execute("DELETE FROM admins WHERE user_id = $1", target)
    await load_admins()
    try:
        await bot.send_message(target, "ℹ️ Вы больше не администратор бота Mawaqit.")
    except Exception:  # noqa: BLE001
        pass


async def set_perms(target, perms):
    await POOL.execute("UPDATE admins SET perms = $2 WHERE user_id = $1", target, [p for p in PERM_KEYS if p in perms])
    await load_admins()


async def admin_name(uid):
    u = await get_user(uid)
    if not u:
        return str(uid)
    return (u["full_name"] or "—") + (f" @{u['username']}" if u["username"] else "")


async def screen_admins():
    lines = ["👮 <b>Админы</b>", ""]
    for uid in sorted(PERMANENT_ADMINS):
        lines.append(f"👑 {esc(await admin_name(uid))} · <code>{uid}</code> — {'главный' if is_main(uid) else 'постоянный'}, все права")
    rows = []
    for uid in sorted(DB_ADMINS):
        n = len(DB_ADMINS[uid])
        rows.append([btn(f"🛠 {await admin_name(uid)} · {n}/{len(PERMS)}", f"a:adm:u:{uid}")])
    if not DB_ADMINS:
        lines += ["", "Других админов пока нет."]
    lines += ["", "Нажмите на админа, чтобы изменить права или удалить."]
    rows.append([btn("➕ Добавить админа", "a:adm:add")])
    rows.append(ADMIN_BACK)
    return "\n".join(lines), kb(*rows)


async def screen_admin_perms(target):
    have = DB_ADMINS.get(target, set())
    row = await POOL.fetchrow("SELECT added_at, added_by FROM admins WHERE user_id = $1", target)
    text = (f"🛠 <b>{esc(await admin_name(target))}</b>\n🆔 <code>{target}</code>\n"
            + (f"Добавлен {fdt(row['added_at'])} UTC\n" if row else "")
            + "\nВключите права галочками 👇")
    btns = [btn(("✅ " if k in have else "⬜ ") + label, f"a:adm:t:{target}:{k}") for k, label in PERMS]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    rows.append([btn("✅ Все права", f"a:adm:all:{target}"), btn("⬜ Снять все", f"a:adm:none:{target}")])
    rows.append([btn("🗑 Удалить из админов", f"a:adm:del:{target}")])
    rows.append([btn("⬅️ К списку админов", "a:adm")])
    return text, kb(*rows)


async def admin_admins(update, ctx, parts):
    """a:adm[:op:…] — only the main admin gets here."""
    op = parts[2] if len(parts) > 2 else ""
    target = int(parts[3]) if len(parts) > 3 and parts[3].lstrip("-").isdigit() else None
    if op == "add":
        ctx.user_data["admin_state"] = "adm_add"
        return await render(update, "➕ <b>Новый админ</b>\n\nОтправьте Telegram ID или @username человека, "
                                    "или перешлите сюда любое его сообщение.\n\n"
                                    "<i>Человек должен хотя бы раз запустить бота.</i>", kb([btn("⬅️ Назад", "a:adm")]))
    if op == "mk" and target:
        if target in ADMINS:
            text, markup = await screen_admin_perms(target) if target in DB_ADMINS else await screen_admins()
            return await render(update, text, markup)
        await add_admin(ctx.bot, target, update.effective_user.id)
        text, markup = await screen_admin_perms(target)
        return await render(update, "✅ Добавлен. " + text, markup)
    if target and target in DB_ADMINS:
        if op == "t" and len(parts) > 4 and parts[4] in PERM_KEYS:
            await set_perms(target, DB_ADMINS[target] ^ {parts[4]})
        elif op == "all":
            await set_perms(target, PERM_KEYS)
        elif op == "none":
            await set_perms(target, [])
        elif op == "del":
            return await render(update, f"🗑 Удалить <b>{esc(await admin_name(target))}</b> из админов?",
                                kb([btn("✅ Да, удалить", f"a:adm:delok:{target}"), btn("❌ Отмена", f"a:adm:u:{target}")]))
        elif op == "delok":
            await remove_admin(ctx.bot, target)
            text, markup = await screen_admins()
            return await render(update, "🗑 Удалён.\n\n" + text, markup)
        text, markup = await screen_admin_perms(target)
        return await render(update, text, markup)
    text, markup = await screen_admins()
    return await render(update, text, markup)


async def admin_add_from_message(update, ctx):
    """State adm_add: ID, @username or a forwarded message."""
    msg = update.message
    target = None
    origin = getattr(msg, "forward_origin", None)
    if origin is not None:
        user = getattr(origin, "sender_user", None)
        if not user:
            await msg.reply_text("🙈 У этого человека скрыт аккаунт при пересылке. Отправьте его ID или @username.")
            return True
        target = user.id
    else:
        raw = (msg.text or "").strip()
        if raw.lstrip("-").isdigit():
            target = int(raw)
        elif raw:
            target = await POOL.fetchval("SELECT user_id FROM users WHERE lower(username) = lower($1) AND chat_type = 'private'",
                                         raw.lstrip("@").split("/")[-1])
    u = await get_user(target) if target else None
    if not u or u["chat_type"] != "private":
        await msg.reply_text("🤷 Такого человека нет в базе. Он должен сначала запустить бота. Попробуйте ещё раз.",
                             reply_markup=kb([btn("⬅️ Назад", "a:adm")]))
        return True
    ctx.user_data.pop("admin_state", None)
    if target in ADMINS:
        text, markup = await screen_admins()
        await msg.reply_text("ℹ️ Он уже админ.\n\n" + text, parse_mode=ParseMode.HTML, reply_markup=markup)
        return True
    await add_admin(ctx.bot, target, update.effective_user.id)
    text, markup = await screen_admin_perms(target)
    await msg.reply_text("✅ Добавлен. " + text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return True


# mini app: admins management (main admin only)

async def api_admin_admins(request):
    uid = await admin_auth(request)
    if not is_main(uid):
        raise web.HTTPForbidden(text="main admin only")
    if request.method == "POST":
        body = await read_json(request)
        op = body.get("op")
        if op == "add":
            q = str(body.get("query") or "").strip()
            target = int(q) if q.lstrip("-").isdigit() else await POOL.fetchval(
                "SELECT user_id FROM users WHERE lower(username) = lower($1) AND chat_type = 'private'", q.lstrip("@"))
            u = await get_user(target) if target else None
            if not u or u["chat_type"] != "private":
                return web.json_response({"ok": False, "error": "not_found"})
            if target not in ADMINS:
                await add_admin(request.app["bot"], target, uid)
        else:
            try:
                target = int(body.get("id"))
            except (TypeError, ValueError):
                raise web.HTTPBadRequest(text="bad id")
            if target not in DB_ADMINS:
                raise web.HTTPBadRequest(text="not an editable admin")
            if op == "del":
                await remove_admin(request.app["bot"], target)
            elif op == "perms" and isinstance(body.get("perms"), list):
                await set_perms(target, set(body["perms"]))
            else:
                raise web.HTTPBadRequest(text="bad op")
    items = []
    for a in sorted(PERMANENT_ADMINS) + sorted(DB_ADMINS):
        u = await get_user(a)
        items.append({"id": a, "name": (u or {}).get("full_name") or str(a), "username": (u or {}).get("username"),
                      "permanent": a in PERMANENT_ADMINS, "main": is_main(a), "perms": admin_perms(a)})
    return web.json_response({"ok": True, "items": items, "perms": [{"key": k, "label": l} for k, l in PERMS]})


# ───────────────────────── tidy chat: reminders disappear after an hour ─────────────────────────

REMINDER_TTL_MIN = 60


async def schedule_delete(chat_id, msg_id, minutes=REMINDER_TTL_MIN):
    try:
        await POOL.execute("INSERT INTO msg_cleanup (chat_id, msg_id, at) VALUES ($1, $2, now() + make_interval(mins => $3)) "
                           "ON CONFLICT DO NOTHING", chat_id, msg_id, minutes)
    except Exception:  # noqa: BLE001
        log.exception("could not schedule deletion")


async def cleanup_job(context: ContextTypes.DEFAULT_TYPE):
    try:
        rows = await POOL.fetch("DELETE FROM msg_cleanup WHERE (chat_id, msg_id) IN "
                                "(SELECT chat_id, msg_id FROM msg_cleanup WHERE at <= now() LIMIT 200) RETURNING chat_id, msg_id")
    except Exception:  # noqa: BLE001
        log.exception("cleanup: db error")
        return
    for r in rows:
        try:
            await context.bot.delete_message(r["chat_id"], r["msg_id"])
        except Exception:  # noqa: BLE001  (already deleted by the user or by the next reminder)
            pass
        await asyncio.sleep(0.03)


# ───────────────────────── AI helper: questions about Islam (Google Gemini) ─────────────────────────
# Settings live in the kv table (ai_cfg) and are changed from the admin panel. Free questions per person
# and for everyone per day; questions bought for Telegram Stars go first in the queue.

GEMINI_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GEMINI_PREFER = ("gemini-3-flash", "gemini-3-flash-preview", "gemini-flash-latest", "gemini-2.5-flash",
                 "gemini-flash-lite-latest", "gemini-2.5-flash-lite", "gemini-2.0-flash", "gemini-2.0-flash-lite")
AI_CFG_DEFAULT = {"enabled": True, "access": "admins", "selected": [], "banned": [], "daily_free": 20,
                  "global_free": 350, "model": "auto", "length": "medium", "memory": 8, "extra": "",
                  "disc_on": True, "disc": "", "prov": {"groq": True, "cerebras": True, "openrouter": True},
                  "gem_limit": 550, "reserve": 200}
# Backup AI providers (OpenAI-style API). They answer Russian/English/Arabic when Gemini's free quota runs low;
# Uzbek and Tajik are always answered by Gemini (the backups write those languages poorly).
PROVIDERS = {
    "groq": {"name": "Groq", "base": "https://api.groq.com/openai/v1", "env": "GROQ_API_KEY", "site": "console.groq.com/keys",
             "prefer": ("openai/gpt-oss-120b", "llama-3.3-70b-versatile", "meta-llama/llama-4-maverick-17b-128e-instruct")},
    "cerebras": {"name": "Cerebras", "base": "https://api.cerebras.ai/v1", "env": "CEREBRAS_API_KEY", "site": "cloud.cerebras.ai",
                 "prefer": ("gpt-oss-120b", "llama-3.3-70b", "qwen-3-235b-a22b-instruct-2507", "llama3.1-8b")},
    "openrouter": {"name": "OpenRouter", "base": "https://openrouter.ai/api/v1", "env": "OPENROUTER_API_KEY",
                   "site": "openrouter.ai/keys",
                   "prefer": ("openai/gpt-oss-120b:free", "meta-llama/llama-3.3-70b-instruct:free",
                              "deepseek/deepseek-chat-v3-0324:free", "qwen/qwen3-235b-a22b:free")},
}
GEMINI_ONLY_LANGS = ("uz", "uzc", "tg")
DEFAULT_PACKS = [{"id": "q50", "q": 50, "stars": 50}, {"id": "q200", "q": 200, "stars": 150},
                 {"id": "u30", "days": 30, "stars": 300}]
DEFAULT_CARDS = {"owner": "",
                 "cards": [{"label": "VISA", "number": "4466 1369 0003 3243"},
                           {"label": "VISA", "number": "4097 8402 1478 0988"},
                           {"label": "HUMO", "number": "9860 3501 4472 5404"}]}
AI = {"cfg": dict(AI_CFG_DEFAULT), "key": GEMINI_KEY, "models": [], "cool": {}, "packs": list(DEFAULT_PACKS),
      "cards": json.loads(json.dumps(DEFAULT_CARDS)), "pkeys": {}, "pmodel": {}}
AI_HISTORY = {}  # user_id -> list of (role, text)
LANG_NAMES = {"en": "English", "ru": "Russian", "uz": "Uzbek (Latin script)", "uzc": "Uzbek (Cyrillic script)",
              "tg": "Tajik (Cyrillic script)", "ar": "Arabic"}
AI_LENGTH = {"short": "Keep every answer short: 2–4 sentences or a short list.",
             "medium": "Be concise: usually 3–8 short paragraphs or a short list.",
             "long": "Give detailed, well-structured answers with explanations and, where you are sure of them, sources."}
AI_SYSTEM = """You are a gentle, knowledgeable assistant inside "Mawaqit", a Muslim prayer-times app.
You answer questions about Islam: prayer (salah), wudu, fasting, zakat, hajj, adhkar and duas, the Qur'an, the Prophet's life ﷺ,
Islamic history, manners (adab) and everyday Muslim life.

Rules:
- Answer in {lang}. Be warm and clear. No long introductions. {length}
- The user follows the {madhab} madhab: give that school's position first; if the schools differ, say so briefly.
- Rely on the mainstream Sunni understanding. Where scholars genuinely differ, say that there are different opinions.
- Never invent hadiths, quotes, verse numbers or sources. Quote a verse or hadith only if you are sure of it, and name
  the source (e.g. "Sahih al-Bukhari", "Qur'an 2:255"). If unsure, explain the meaning without a reference.
- Do not issue fatwas. For personal or serious matters (divorce, inheritance, debts, medical, legal), give general
  guidance only and advise asking a local imam or the official muftiate.
- If the question is not about Islam or Muslim life, politely say you only help with questions about Islam.
- Be respectful to all people and other schools of thought; never mock or call anyone a disbeliever.
- Format with plain text. You may use **bold** for key words and "- " for list items. No tables, no headings."""


async def kv_get(key, default=None):
    try:
        v = await POOL.fetchval("SELECT value FROM kv WHERE key = $1", key)
        return default if v is None else v
    except Exception:  # noqa: BLE001
        return default


async def kv_set(key, value):
    await POOL.execute("INSERT INTO kv (key, value) VALUES ($1, $2) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value",
                       key, value)


async def load_ai():
    try:
        cfg = json.loads(await kv_get("ai_cfg", "{}") or "{}")
    except ValueError:
        cfg = {}
    if not cfg and await kv_get("ai_public") == "1":  # the earlier on/off switch
        cfg["access"] = "all"
    AI["cfg"] = {**AI_CFG_DEFAULT, **cfg}
    AI["key"] = (await kv_get("gemini_key", "") or "").strip() or GEMINI_KEY
    AI["cfg"]["prov"] = {**AI_CFG_DEFAULT["prov"], **(AI["cfg"].get("prov") or {})}
    try:
        saved = json.loads(await kv_get("ai_pkeys", "{}") or "{}")
    except ValueError:
        saved = {}
    AI["pkeys"] = {p: (saved.get(p) or os.getenv(v["env"], "")).strip() for p, v in PROVIDERS.items()}
    for k, default in (("packs", DEFAULT_PACKS), ("cards", DEFAULT_CARDS)):
        try:
            v = json.loads(await kv_get("ai_" + k, "") or "null")
            AI[k] = v if v else json.loads(json.dumps(default))
        except ValueError:
            AI[k] = json.loads(json.dumps(default))


async def save_ai_cfg(**changes):
    AI["cfg"].update(changes)
    await kv_set("ai_cfg", json.dumps(AI["cfg"], ensure_ascii=False))


def ai_allowed_now(uid):
    c = AI["cfg"]
    if not (AI["key"] or any(AI["pkeys"].values())) or not c["enabled"] or uid in c["banned"]:
        return False
    if is_admin(uid) or c["access"] == "all":
        return True
    return c["access"] == "selected" and uid in c["selected"]


async def ai_allowed(uid):
    return ai_allowed_now(uid)


async def ai_wallet(uid):
    r = await POOL.fetchrow("SELECT credits, unlimited_until FROM ai_credits WHERE user_id = $1", uid)
    return (r["credits"] if r else 0), (r["unlimited_until"] if r else None)


async def ai_quota(u):
    """What this question would be paid with: admin / unl / free / credit, or None + the reason."""
    uid = u["user_id"]
    if is_admin(uid):
        return {"kind": "admin"}
    credits, unl = await ai_wallet(uid)
    now = datetime.now(ZoneInfo("UTC"))
    info = {"credits": credits, "unl": unl if unl and unl > now else None}
    used = await POOL.fetchval("SELECT n FROM ai_usage WHERE user_id = $1 AND day = $2", uid, user_today(u)) or 0
    c = AI["cfg"]
    info["free_left"] = max(0, c["daily_free"] - used) if c["daily_free"] else 10 ** 6
    if info["unl"]:
        return {**info, "kind": "unl"}
    everyone = await POOL.fetchval("SELECT stat_value FROM daily_stats WHERE stat_day = CURRENT_DATE AND stat_key = 'ai_free'") or 0
    global_ok = not c["global_free"] or everyone < c["global_free"]
    if info["free_left"] > 0 and global_ok:
        return {**info, "kind": "free"}
    if credits > 0:
        return {**info, "kind": "credit"}
    return {**info, "kind": None, "reason": "global" if info["free_left"] > 0 else "personal"}


def ai_status_text(lang, q):
    if q.get("kind") == "admin":
        return ""
    parts = []
    if q.get("unl"):
        parts.append(t(lang, "ai_status_unl", d=q["unl"].strftime("%d.%m.%Y")))
    else:
        parts.append(t(lang, "ai_status_free", n=min(q.get("free_left", 0), 999)))
        if q.get("credits"):
            parts.append(t(lang, "ai_status_cred", n=q["credits"]))
    return "\n".join(parts)


async def ai_left(u):  # kept for the mini app: free questions left today (admins: the daily limit)
    q = await ai_quota(u)
    return AI["cfg"]["daily_free"] if q["kind"] == "admin" else q.get("free_left", 0) + q.get("credits", 0)


async def ai_models():
    if AI["models"]:
        return AI["models"]
    try:
        r = await HTTP.get("https://generativelanguage.googleapis.com/v1beta/models", params={"pageSize": 200},
                           headers={"x-goog-api-key": AI["key"]}, timeout=15)
        r.raise_for_status()
        have = [m["name"].split("/")[-1] for m in r.json().get("models", [])
                if "generateContent" in (m.get("supportedGenerationMethods") or [])]
        found = [m for m in GEMINI_PREFER if m in have]
        found += [m for m in have if "flash" in m and not any(x in m for x in ("image", "tts", "live", "audio", "exp"))
                  and m not in found]
        AI["models"] = found
        log.info("gemini models: %s", ", ".join(found[:6]))
    except Exception:  # noqa: BLE001
        log.exception("gemini: could not list models")
    return AI["models"] or ["gemini-2.5-flash", "gemini-2.5-flash-lite"]


def ai_order(models, cheap):
    """Free questions go to Flash-Lite first (much bigger free quota), paid ones and admins to Flash first."""
    chosen = AI["cfg"]["model"]
    lite = [m for m in models if "lite" in m]
    full = [m for m in models if "lite" not in m]
    order = (lite + full) if cheap else (full + lite)
    if chosen != "auto":
        order = [chosen] + [m for m in order if m != chosen]
    return order


async def ai_answer(u, question, cheap=False, keep=True):
    """Returns (answer, model, error_key)."""
    lang = u["lang"] or "en"
    c = AI["cfg"]
    hist = AI_HISTORY.setdefault(u["user_id"], []) if keep else []
    mem = int(c["memory"])
    contents = [{"role": r, "parts": [{"text": x}]} for r, x in (hist[-mem:] if mem else [])]
    contents = contents + [{"role": "user", "parts": [{"text": question[:2000]}]}]
    system = AI_SYSTEM.format(lang=LANG_NAMES.get(lang, "English"), length=AI_LENGTH.get(c["length"], AI_LENGTH["medium"]),
                              madhab="Hanafi" if u["madhab"] == "hanafi" else "Shafi'i/Maliki/Hanbali")
    if c["extra"].strip():
        system += ("\n\nAdditional instructions from the app owner (follow them unless they conflict with the rules above):\n"
                   + c["extra"].strip()[:3000])
    msgs = [{"role": "system", "content": system}] + \
        [{"role": "assistant" if r == "model" else "user", "content": x} for r, x in (hist[-mem:] if mem else [])] + \
        [{"role": "user", "content": question[:2000]}]

    def remember(text):
        if keep:
            hist.extend([("user", question[:2000]), ("model", text[:4000])])
            del hist[:-12]

    backups = [p for p in PROVIDERS if c["prov"].get(p) and AI["pkeys"].get(p)] if lang not in GEMINI_ONLY_LANGS else []
    gem_used = await gemini_used_today()
    # Russian/English/Arabic leave the last part of Gemini's free quota to Uzbek and Tajik questions
    gemini_first = bool(AI["key"]) and (not backups or gem_used < max(0, c["gem_limit"] - c["reserve"]))
    if gemini_first:
        text, model, err = await gemini_answer(system, contents, cheap, c)
        if text or err == "ai_blocked":
            if text:
                remember(text)
            return text, model, err
    for p in backups:
        text, model = await backup_answer(p, msgs, c)
        if text:
            remember(text)
            return text, model, None
    if not gemini_first and AI["key"]:  # backups are down: Gemini after all
        text, model, err = await gemini_answer(system, contents, cheap, c)
        if text or err == "ai_blocked":
            if text:
                remember(text)
            return text, model, err
    await bump("ai_errors")
    return None, None, "ai_err"


def gemini_day():
    """Gemini's free quota resets at midnight Pacific time."""
    return datetime.now(ZoneInfo("America/Los_Angeles")).strftime("%Y%m%d")


async def gemini_used_today():
    try:
        return await POOL.fetchval("SELECT coalesce(sum(stat_value), 0) FROM daily_stats WHERE stat_key = $1 "
                                   "AND stat_day >= CURRENT_DATE - 1", "ai_gem_" + gemini_day()) or 0
    except Exception:  # noqa: BLE001
        return 0


async def provider_models(p, key=None):
    """The provider's model to use: the first of our preferred ones it has (asked once)."""
    if not key and AI["pmodel"].get(p):
        return AI["pmodel"][p]
    v = PROVIDERS[p]
    r = await HTTP.get(v["base"] + "/models", headers={"Authorization": f"Bearer {key or AI['pkeys'][p]}"}, timeout=15)
    r.raise_for_status()
    have = [m.get("id") for m in r.json().get("data", [])]
    model = next((m for m in v["prefer"] if m in have), None)
    if not model and p == "openrouter":  # free models change often: take the strongest family that is there
        free = [m for m in have if m and m.endswith(":free")]
        for fam in ("gpt-oss-120b", "deepseek-chat", "deepseek-v3", "llama-3.3-70b", "qwen3-235b", "llama-4-maverick",
                    "gemma-3-27b", "mistral-small", "gpt-oss-20b"):
            model = next((m for m in free if fam in m), None)
            if model:
                break
        model = model or (free[0] if free else None)
    model = model or v["prefer"][0]
    if not key:
        AI["pmodel"][p] = model
    return model


async def check_backup_ai(context):
    """On start: does each backup provider accept its key, and which model will it use."""
    for p, v in PROVIDERS.items():
        if not AI["pkeys"].get(p):
            continue
        try:
            log.info("backup AI %s: key ok, model %s", v["name"], await provider_models(p))
        except Exception as e:  # noqa: BLE001
            log.warning("backup AI %s: key check failed: %r", v["name"], e)


async def backup_answer(p, msgs, c):
    v = PROVIDERS[p]
    if AI["cool"].get("p:" + p, 0) > _time.time():
        return None, None
    try:
        model = await provider_models(p)
        r = await HTTP.post(v["base"] + "/chat/completions", timeout=60,
                            headers={"Authorization": f"Bearer {AI['pkeys'][p]}",
                                     **({"HTTP-Referer": f"https://t.me/{BOT_USERNAME}", "X-Title": "Mawaqit"} if p == "openrouter" else {})},
                            json={"model": model, "messages": msgs, "temperature": 0.4,
                                  "max_tokens": 4096 if c["length"] == "long" else 2048})
        if r.status_code in (401, 403, 404, 429) or r.status_code >= 500:
            log.warning("%s %s: HTTP %s %s", p, model, r.status_code, r.text[:200])
            if r.status_code == 404:
                AI["pmodel"].pop(p, None)
            AI["cool"]["p:" + p] = _time.time() + (3600 if r.status_code in (401, 403) else 600)
            return None, None
        r.raise_for_status()
        text = ((r.json().get("choices") or [{}])[0].get("message") or {}).get("content") or ""
        text = re.sub(r"(?s)<think>.*?</think>", "", text).strip()
        if not text:
            return None, None
        await bump("ai_p_" + p)
        return text, f"{p}:{model.split('/')[-1]}"
    except Exception:  # noqa: BLE001
        log.exception("%s failed", p)
        AI["cool"]["p:" + p] = _time.time() + 120
        return None, None


async def gemini_answer(system, contents, cheap, c):
    """Returns (answer, model, error_key)."""
    body = {"systemInstruction": {"parts": [{"text": system}]}, "contents": contents,
            "generationConfig": {"temperature": 0.4, "maxOutputTokens": 8192 if c["length"] == "long" else 4096}}
    models = ai_order(await ai_models(), cheap)
    ready = [m for m in models if AI["cool"].get(m, 0) < _time.time()] or models
    for model in ready:
        try:
            r = await HTTP.post(f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
                                json=body, headers={"x-goog-api-key": AI["key"]}, timeout=60)
            if r.status_code in (404, 429, 500, 503):
                log.warning("gemini %s: HTTP %s %s", model, r.status_code, r.text[:200])
                if r.status_code == 429:
                    await bump("ai_quota")
                # out of free quota → rest this model for 10 min; unknown model → for a day
                AI["cool"][model] = _time.time() + (86400 if r.status_code == 404 else 600)
                continue
            r.raise_for_status()
            j = r.json()
            if (j.get("promptFeedback") or {}).get("blockReason"):
                return None, model, "ai_blocked"
            parts = ((j.get("candidates") or [{}])[0].get("content") or {}).get("parts") or []
            text = "".join(p.get("text", "") for p in parts if not p.get("thought")).strip()
            if not text:
                log.warning("gemini %s: empty answer %s", model, str(j)[:300])
                continue
            await bump("ai_gem_" + gemini_day())
            return text, model, None
        except Exception:  # noqa: BLE001
            log.exception("gemini %s failed", model)
    return None, None, "ai_err"


async def ai_count(u, kind, model, question, answer):
    await bump("ai_questions")
    await bump("ai_" + (kind or "admin"))
    if model:
        await bump("ai_m_" + model[:40])
    uid = u["user_id"]
    if kind == "free":
        await POOL.execute("INSERT INTO ai_usage (user_id, day, n) VALUES ($1, $2, 1) "
                           "ON CONFLICT (user_id, day) DO UPDATE SET n = ai_usage.n + 1", uid, user_today(u))
    elif kind == "credit":
        await POOL.execute("UPDATE ai_credits SET credits = greatest(0, credits - 1) WHERE user_id = $1", uid)
    try:
        await POOL.execute("INSERT INTO ai_log (user_id, question, answer, model) VALUES ($1, $2, $3, $4)",
                           uid, question[:2000], answer[:6000], model)
    except Exception:  # noqa: BLE001
        log.exception("ai log failed")


def ai_markup_html(text):
    """Model text (light markdown) → safe Telegram HTML."""
    out = esc(text.strip())
    out = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", out)
    out = re.sub(r"(?m)^\s*[\*\-•]\s+", "• ", out)
    out = re.sub(r"(?m)^#{1,6}\s*(.+)$", r"<b>\1</b>", out)
    out = re.sub(r"(?<![\w*])\*(?!\s)([^*\n]+?)\*(?!\w)", r"<i>\1</i>", out)
    return out


def ai_disclaimer(lang):
    c = AI["cfg"]
    if not c["disc_on"]:
        return ""
    return c["disc"].strip() or t(lang, "ai_disclaimer")


def pack_label(lang, p):
    return t(lang, "pack_unl", d=p["days"], s=p["stars"]) if p.get("days") else t(lang, "pack_q", q=p["q"], s=p["stars"])


def ai_buttons(lang, buy=False):
    rows = [[btn(pack_label(lang, p), f"buy:{p['id']}")] for p in AI["packs"]] if buy else []
    rows.append([btn(t(lang, "ai_new"), "ai:reset"), btn(t(lang, "ai_exit"), "ai:exit")])
    rows.append([btn(t(lang, "don_btn"), "don:menu")])
    return kb(*rows)


async def ai_button(update, ctx, parts):
    q = update.callback_query
    uid = q.from_user.id
    u = await get_user(uid)
    lang = (u or {}).get("lang") or "en"
    await q.answer()
    if not u or not ai_allowed_now(uid):
        return
    sub = parts[1] if len(parts) > 1 else "start"
    if sub == "exit":
        ctx.user_data.pop("ai_mode", None)
        text, markup = screen_menu(u)
        return await render(update, text, markup)
    if sub == "reset":
        AI_HISTORY.pop(uid, None)
        ctx.user_data["ai_mode"] = True
        return await update.effective_chat.send_message(t(lang, "ai_reset_done"), reply_markup=ai_buttons(lang))
    ctx.user_data["ai_mode"] = True
    status = ai_status_text(lang, await ai_quota(u))
    await render(update, t(lang, "ai_intro2") + ("\n\n" + status if status else ""), ai_buttons(lang))


async def ai_message(update, ctx, u):
    """A question typed while the AI mode is on."""
    msg = update.message
    lang = u["lang"] or "en"
    if not ai_allowed_now(u["user_id"]):
        ctx.user_data.pop("ai_mode", None)
        return
    quota = await ai_quota(u)
    if not quota["kind"]:
        return await msg.reply_text(t(lang, "ai_global" if quota.get("reason") == "global" else "ai_limit2"),
                                    reply_markup=ai_buttons(lang, buy=True))
    try:
        await update.effective_chat.send_action("typing")
    except Exception:  # noqa: BLE001
        pass
    answer, model, err = await ai_answer(u, msg.text or "", cheap=quota["kind"] == "free")
    if not answer:
        return await msg.reply_text(t(lang, err), reply_markup=ai_buttons(lang))
    await ai_count(u, quota["kind"], model, msg.text or "", answer)
    body = ai_markup_html(answer)
    disc = ai_disclaimer(lang)
    tail = f"\n\n<i>{esc(disc)}</i>" if disc else ""
    status = ai_status_text(lang, await ai_quota(u))
    if status:
        tail += "\n" + status
    chunks = [body[i:i + 3600] for i in range(0, len(body), 3600)] or [""]
    for i, ch in enumerate(chunks):
        last = i == len(chunks) - 1
        try:
            await msg.reply_text(ch + (tail if last else ""), parse_mode=ParseMode.HTML,
                                 reply_markup=ai_buttons(lang) if last else None)
        except BadRequest:  # a tag got cut between chunks: send plain text instead
            await msg.reply_text(re.sub(r"<[^>]+>", "", ch + (tail if last else "")),
                                 reply_markup=ai_buttons(lang) if last else None)


# ───────────────────────── Telegram Stars: question packs and donations; card donations ─────────────────────────

def find_pack(pid):
    return next((p for p in AI["packs"] if p["id"] == pid), None)


def pack_invoice(lang, p):
    title = t(lang, "inv_unl_title", d=p["days"]) if p.get("days") else t(lang, "inv_q_title", q=p["q"])
    return title[:32], t(lang, "inv_desc")


async def send_pack_invoice(bot, chat_id, lang, p, uid):
    title, desc = pack_invoice(lang, p)
    await bot.send_invoice(chat_id, title, desc, f"pack:{p['id']}:{p['stars']}:{uid}", currency="XTR",
                           prices=[LabeledPrice(title, p["stars"])])


async def send_donate_invoice(bot, chat_id, lang, stars, uid):
    await bot.send_invoice(chat_id, t(lang, "don_inv_title")[:32], t(lang, "don_inv_desc"), f"don:{stars}:{uid}",
                           currency="XTR", prices=[LabeledPrice(t(lang, "don_inv_title")[:32], stars)])


def screen_donate(lang):
    amounts = [btn(f"⭐ {n}", f"don:{n}") for n in (50, 100, 250, 500)]
    return t(lang, "don_title"), kb(amounts[:2], amounts[2:], [btn(t(lang, "don_custom"), "don:custom")],
                                    [btn(t(lang, "don_card"), "don:card")], [btn(t(lang, "btn_menu"), "m:home")])


def screen_cards(lang):
    cards = AI["cards"]
    lines = [t(lang, "don_cards_title"), ""]
    for c in cards.get("cards", []):
        lines.append(f"💳 <b>{esc(c['label'])}</b>\n<code>{esc(c['number'])}</code>")
    if cards.get("owner"):
        lines += ["", t(lang, "don_owner", name=esc(cards["owner"]))]
    rows = [[InlineKeyboardButton(f"📋 {c['label']} •{c['number'].replace(' ', '')[-4:]}",
                                  copy_text=CopyTextButton(c["number"].replace(" ", "")))] for c in cards.get("cards", [])]
    rows.append([btn(t(lang, "don_sent"), "don:sent")])
    rows.append([btn(t(lang, "btn_back"), "don:menu")])
    return "\n".join(lines), kb(*rows)


async def notify_card_sent(bot, user):
    """Someone says they sent money to the card: tell the admins who handle support."""
    u = await get_user(user.id)
    hidden = u and u["hidden"]
    text = (f"💳 <b>Перевод на карту</b>\n\n<a href=\"tg://user?id={user.id}\">{esc(user.full_name)}</a>"
            f"{(' @' + esc(user.username)) if user.username else ''} · <code>{user.id}</code>\n"
            f"сообщил(а), что отправил(а) пожертвование на карту. Проверьте поступление 🤍")
    for admin in sorted(a for a in ADMINS if has_perm(a, "support") and (not hidden or is_main(a))):
        try:
            await bot.send_message(admin, text, parse_mode=ParseMode.HTML,
                                   reply_markup=kb([btn("✉️ Поблагодарить", f"sup:reply:{user.id}:w")]))
        except Exception:  # noqa: BLE001
            pass


async def don_button(update, ctx, parts):
    q = update.callback_query
    uid = q.from_user.id
    u = await get_user(uid)
    lang = (u or {}).get("lang") or "en"
    sub = parts[1] if len(parts) > 1 else "menu"
    if sub == "sent":
        last = ctx.user_data.get("don_sent_at", 0)
        await q.answer(t(lang, "don_sent_ok"), show_alert=True)
        if _time.time() - last > 3600:
            ctx.user_data["don_sent_at"] = _time.time()
            await notify_card_sent(ctx.bot, q.from_user)
        return
    await q.answer()
    if sub == "card":
        text, markup = screen_cards(lang)
        return await render(update, text, markup)
    if sub == "custom":
        ctx.user_data["don_custom"] = True
        return await update.effective_chat.send_message(t(lang, "don_custom_ask"), reply_markup=ForceReply())
    if sub.isdigit():
        return await send_donate_invoice(ctx.bot, update.effective_chat.id, lang, int(sub), uid)
    text, markup = screen_donate(lang)
    return await render(update, text, markup)


async def don_custom_amount(update, ctx, u):
    msg = update.message
    lang = u["lang"] or "en"
    raw = (msg.text or "").strip().replace(" ", "")
    if not raw.isdigit() or not 1 <= int(raw) <= 100000:
        return await msg.reply_text(t(lang, "don_bad"))
    ctx.user_data.pop("don_custom", None)
    await send_donate_invoice(ctx.bot, update.effective_chat.id, lang, int(raw), u["user_id"])


async def buy_button(update, ctx, parts):
    q = update.callback_query
    u = await get_user(q.from_user.id)
    lang = (u or {}).get("lang") or "en"
    await q.answer()
    p = find_pack(parts[1]) if len(parts) > 1 else None
    if p and u:
        await send_pack_invoice(ctx.bot, update.effective_chat.id, lang, p, u["user_id"])


async def on_precheckout(update, ctx):
    pq = update.pre_checkout_query
    parts = (pq.invoice_payload or "").split(":")
    ok = False
    if parts[0] == "pack" and len(parts) == 4:
        p = find_pack(parts[1])
        ok = bool(p) and p["stars"] == pq.total_amount and pq.currency == "XTR"
    elif parts[0] == "don" and len(parts) == 3:
        ok = pq.currency == "XTR" and pq.total_amount == int(parts[1])
    if ok:
        await pq.answer(ok=True)
    else:
        await pq.answer(ok=False, error_message="This offer has changed. Please open it again.")


async def grant(uid, questions=0, days=0):
    await POOL.execute("INSERT INTO ai_credits (user_id) VALUES ($1) ON CONFLICT DO NOTHING", uid)
    if questions:
        await POOL.execute("UPDATE ai_credits SET credits = credits + $2 WHERE user_id = $1", uid, questions)
    if days:
        await POOL.execute("UPDATE ai_credits SET unlimited_until = greatest(coalesce(unlimited_until, now()), now()) "
                           "+ make_interval(days => $2) WHERE user_id = $1", uid, days)


async def on_paid(update, ctx):
    msg = update.message
    sp = msg.successful_payment
    uid = update.effective_user.id
    u = await get_user(uid)
    lang = (u or {}).get("lang") or "en"
    parts = (sp.invoice_payload or "").split(":")
    kind = parts[0]
    await POOL.execute("INSERT INTO payments (user_id, kind, payload, stars, charge_id) VALUES ($1, $2, $3, $4, $5)",
                       uid, kind, sp.invoice_payload, sp.total_amount, sp.telegram_payment_charge_id)
    await bump("stars_" + kind, sp.total_amount)
    if kind == "pack":
        p = find_pack(parts[1]) or {"q": 0, "stars": sp.total_amount, "id": parts[1]}
        await grant(uid, questions=p.get("q", 0), days=p.get("days", 0))
        what = pack_label(lang, p).split(" — ")[0]
        await msg.reply_text(t(lang, "paid_ok", what=what), reply_markup=ai_buttons(lang) if ai_allowed_now(uid) else None)
        note = f"⭐ <b>Покупка</b>: {esc(what)} за {sp.total_amount} ⭐"
    else:
        await msg.reply_text(t(lang, "don_thanks"))
        note = f"🤍 <b>Пожертвование</b>: {sp.total_amount} ⭐"
    hidden = u and u["hidden"]
    for admin in sorted(a for a in ADMINS if has_perm(a, "ai") and (not hidden or is_main(a))):
        try:
            await ctx.bot.send_message(admin, f"{note}\n👤 {esc(update.effective_user.full_name)} · <code>{uid}</code>",
                                       parse_mode=ParseMode.HTML, disable_notification=True)
        except Exception:  # noqa: BLE001
            pass


# mini app: AI chat, purchases, donations

async def api_ai(request):
    tg_user, u, lang = await api_auth(request)
    if not u or not ai_allowed_now(u["user_id"]):
        raise web.HTTPForbidden(text="ai is off")
    body = await read_json(request)
    if body.get("reset"):
        AI_HISTORY.pop(u["user_id"], None)
        return web.json_response({"ok": True, "status": ai_status_text(lang, await ai_quota(u))})
    question = str(body.get("text") or "").strip()[:2000]
    if not question:
        raise web.HTTPBadRequest(text="empty")
    quota = await ai_quota(u)
    if not quota["kind"]:
        return web.json_response({"ok": False, "error": "limit", "reason": quota.get("reason"),
                                  "status": ai_status_text(lang, quota)})
    answer, model, err = await ai_answer(u, question, cheap=quota["kind"] == "free")
    if not answer:
        return web.json_response({"ok": False, "error": err})
    await ai_count(u, quota["kind"], model, question, answer)
    return web.json_response({"ok": True, "html": ai_markup_html(answer), "disc": ai_disclaimer(u["lang"] or lang),
                              "status": ai_status_text(lang, await ai_quota(u))})


async def api_invoice(request):
    """Invoice link for the mini app: {pack: id} or {donate: stars}."""
    tg_user, u, lang = await api_auth(request)
    if not u:
        raise web.HTTPBadRequest(text="no user")
    body = await read_json(request)
    bot = request.app["bot"]
    if body.get("pack"):
        p = find_pack(str(body["pack"]))
        if not p:
            raise web.HTTPBadRequest(text="no pack")
        title, desc = pack_invoice(lang, p)
        link = await bot.create_invoice_link(title, desc, f"pack:{p['id']}:{p['stars']}:{u['user_id']}", currency="XTR",
                                             prices=[LabeledPrice(title, p["stars"])])
    else:
        try:
            stars = int(body.get("donate"))
            assert 1 <= stars <= 100000
        except (TypeError, ValueError, AssertionError):
            raise web.HTTPBadRequest(text="bad amount")
        link = await bot.create_invoice_link(t(lang, "don_inv_title")[:32], t(lang, "don_inv_desc"), f"don:{stars}:{u['user_id']}",
                                             currency="XTR", prices=[LabeledPrice(t(lang, "don_inv_title")[:32], stars)])
    return web.json_response({"ok": True, "link": link})


async def api_donate_sent(request):
    tg_user, u, lang = await api_auth(request)
    key = ("don_sent", int(tg_user["id"]))
    if _time.time() - SENT.get(key, 0) > 3600:
        SENT[key] = _time.time()
        user = NS_User(int(tg_user["id"]), " ".join(x for x in (tg_user.get("first_name"), tg_user.get("last_name")) if x),
                       tg_user.get("username"))
        await notify_card_sent(request.app["bot"], user)
    return web.json_response({"ok": True})


class NS_User:
    def __init__(self, uid, full_name, username):
        self.id, self.full_name, self.username = uid, full_name or str(uid), username


def money_json(lang):
    return {"packs": [{"id": p["id"], "label": pack_label(lang, p), "stars": p["stars"]} for p in AI["packs"]],
            "cards": AI["cards"]}


# ───────────────────────── admin: AI settings, journal, sales ─────────────────────────

AI_ACCESS_RU = {"admins": "только админы 🔒", "all": "все ✅", "selected": "избранные 👥"}
AI_LEN_RU = {"short": "коротко", "medium": "средне", "long": "подробно"}


async def ai_stats(days):
    rows = await POOL.fetch("SELECT stat_key, sum(stat_value) AS v FROM daily_stats WHERE stat_day > CURRENT_DATE - $1::int "
                            "AND (stat_key LIKE 'ai_%' OR stat_key LIKE 'stars_%') GROUP BY stat_key", days)
    return {r["stat_key"]: r["v"] for r in rows}


async def screen_admin_ai():
    c = AI["cfg"]
    today = await ai_stats(1)
    key = AI["key"]
    lines = ["🤖 <b>ИИ-помощник</b>", "",
             f"Статус: {'✅ включён' if c['enabled'] else '⛔ выключен'} · ключ: {'…' + key[-4:] if key else 'нет ❗'}",
             f"Доступ: {AI_ACCESS_RU[c['access']]}" + (f" ({len(c['selected'])})" if c["access"] == "selected" else "")
             + (f" · в бане: {len(c['banned'])}" if c["banned"] else ""),
             f"Бесплатно: {c['daily_free'] or '∞'} в день на человека · {c['global_free'] or '∞'} в день на всех",
             f"Модель: {c['model'] if c['model'] != 'auto' else 'авто'} · ответы: {AI_LEN_RU[c['length']]} · память: {c['memory']}",
             "", f"📊 Сегодня: <b>{today.get('ai_questions', 0)}</b> вопросов "
             f"(бесплатных {today.get('ai_free', 0)}, купленных {today.get('ai_credit', 0) + today.get('ai_unl', 0)}, "
             f"админов {today.get('ai_admin', 0)}) · квота Google: {today.get('ai_quota', 0)} · ошибок: {today.get('ai_errors', 0)}",
             f"♊ Gemini сегодня: {await gemini_used_today()} из ~{c['gem_limit']} · запас для uz/tg: {c['reserve']}",
             "🔌 Запасные: " + (", ".join(f"{v['name']} {today.get('ai_p_' + k, 0)}" for k, v in PROVIDERS.items()
                                         if c["prov"].get(k) and AI["pkeys"].get(k)) or "нет (добавьте ключи)")]
    rows = [[btn("⛔ Выключить" if c["enabled"] else "✅ Включить", "a:ai:on"), btn("🔐 Доступ", "a:ai:acc")],
            [btn(f"👥 Избранные ({len(c['selected'])})", "a:ai:list:selected"), btn(f"🚫 Бан ({len(c['banned'])})", "a:ai:list:banned")],
            [btn(f"🎁 На человека: {c['daily_free'] or '∞'}", "a:ai:opt:daily_free"), btn(f"🌍 На всех: {c['global_free'] or '∞'}", "a:ai:opt:global_free")],
            [btn("🧠 Модель", "a:ai:opt:model"), btn(f"📏 {AI_LEN_RU[c['length']]}", "a:ai:opt:length"), btn(f"💭 {c['memory']}", "a:ai:opt:memory")],
            [btn("✍️ Свои инструкции", "a:ai:ask:extra"), btn(("🏷 Пометка ✅" if c["disc_on"] else "🏷 Пометка ❌"), "a:ai:dsc")],
            [btn("✏️ Текст пометки", "a:ai:ask:disc"), btn("🧪 Тест", "a:ai:ask:test")],
            [btn("📊 Статистика", "a:ai:st"), btn("📜 Журнал", "a:ai:log:0")],
            [btn("⭐ Пакеты", "a:ai:packs"), btn("💳 Карты", "a:ai:cards"), btn("💰 Продажи", "a:ai:pay:0")],
            [btn("🔑 Ключ Gemini", "a:ai:ask:key"), btn("🔌 Запасные ИИ", "a:ai:prov")],
            ADMIN_BACK]
    return "\n".join(lines), kb(*rows)


AI_OPTIONS = {"daily_free": [3, 5, 10, 20, 30, 50, 0], "global_free": [100, 200, 350, 450, 1000, 0],
              "length": ["short", "medium", "long"], "memory": [0, 4, 8, 12],
              "gem_limit": [300, 450, 550, 800, 1000, 1500], "reserve": [50, 100, 200, 300, 400]}
AI_ASK = {"extra": "✍️ <b>Свои инструкции</b>\n\nОтправьте текст — дополнительные правила для ответов. Например: «опирайся на позицию "
                   "Духовного управления мусульман Узбекистана», «в конце предлагай дуа по теме».\n\nОтправьте «-», чтобы очистить.",
          "disc": "✏️ <b>Текст пометки под ответом</b>\n\nОтправьте свой текст. Отправьте «-», чтобы вернуть стандартный (на языке человека).",
          "test": "🧪 <b>Тест</b>\n\nОтправьте вопрос — ответ придёт с текущими настройками (вопрос не считается в лимитах).",
          "key": "🔑 <b>Ключ Gemini</b>\n\nОтправьте новый ключ (начинается с AIza…). Бот сначала проверит его.",
          "selected": "👥 Отправьте ID или @username человека, чтобы добавить его в избранные.",
          "banned": "🚫 Отправьте ID или @username человека, чтобы закрыть ему ИИ-помощника.",
          "packs": "⭐ <b>Пакеты</b>\n\nОтправьте список, каждый пакет с новой строки:\n<code>50 50</code> — 50 вопросов за 50 ⭐\n"
                   "<code>200 150</code> — 200 вопросов за 150 ⭐\n<code>30д 300</code> — безлимит на 30 дней за 300 ⭐",
          "cards": "💳 <b>Карты</b>\n\nОтправьте список, каждая карта с новой строки: <code>VISA 4466 1369 0003 3243</code>\n"
                   "Последней строкой можно указать владельца: <code>Владелец: Имя Фамилия</code>",
          "grant": "🎁 Сколько вопросов начислить? Отправьте число (или <code>30д</code> — безлимит на 30 дней)."}


async def find_user_id(raw):
    raw = (raw or "").strip()
    if raw.lstrip("-").isdigit():
        return int(raw)
    return await POOL.fetchval("SELECT user_id FROM users WHERE lower(username) = lower($1) AND chat_type = 'private'",
                               raw.lstrip("@").split("/")[-1])


async def admin_ai(update, ctx, parts):
    uid = update.effective_user.id
    c = AI["cfg"]
    op = parts[2] if len(parts) > 2 else ""
    back = kb([btn("⬅️ Назад", "a:ai")])
    if op == "on":
        await save_ai_cfg(enabled=not c["enabled"])
    elif op == "acc":
        order = ["admins", "all", "selected"]
        await save_ai_cfg(access=order[(order.index(c["access"]) + 1) % 3])
    elif op == "dsc":
        await save_ai_cfg(disc_on=not c["disc_on"])
    elif op == "opt" and len(parts) > 3:
        field = parts[3]
        if len(parts) > 4:  # a:ai:opt:field:value
            v = parts[4]
            if field == "model":
                await save_ai_cfg(model=v)
            elif field in AI_OPTIONS:
                await save_ai_cfg(**{field: v if field == "length" else int(v)})
        else:
            if field == "model":
                ms = await ai_models()
                opts = [("auto", "🪄 Авто (бесплатные → Lite, платные → Flash)")] + [(m, m) for m in ms[:10]]
            else:
                lab = {"short": "коротко", "medium": "средне", "long": "подробно"}
                opts = [(v, (lab.get(v) if field == "length" else ("∞ без лимита" if v == 0 else str(v)))) for v in AI_OPTIONS[field]]
            cur = c[field]
            rows = [[btn(("✅ " if str(v) == str(cur) else "") + label, f"a:ai:opt:{field}:{v}")] for v, label in opts]
            rows.append([btn("⬅️ Назад", "a:ai")])
            return await render(update, "Выберите значение 👇", kb(*rows))
    elif op == "ask" and len(parts) > 3:
        ctx.user_data["admin_state"] = "ai_" + parts[3]
        cur = ""
        if parts[3] == "extra" and c["extra"]:
            cur = "\n\nСейчас:\n<i>" + esc(c["extra"][:1500]) + "</i>"
        if parts[3] == "disc":
            cur = "\n\nСейчас: <i>" + esc(c["disc"] or "стандартная") + "</i>"
        return await render(update, AI_ASK[parts[3]] + cur, back)
    elif op == "list" and len(parts) > 3:
        field = parts[3]
        if len(parts) > 5 and parts[4] == "rm":
            await save_ai_cfg(**{field: [x for x in c[field] if str(x) != parts[5]]})
        if len(parts) > 4 and parts[4] == "add":
            ctx.user_data["admin_state"] = "ai_" + field
            return await render(update, AI_ASK[field], back)
        rows = [[btn(f"❌ {await admin_name(x)}", f"a:ai:list:{field}:rm:{x}")] for x in AI["cfg"][field][:30]]
        rows.append([btn("➕ Добавить", f"a:ai:list:{field}:add")])
        rows.append([btn("⬅️ Назад", "a:ai")])
        title = "👥 <b>Избранные</b> — им доступен ИИ, когда доступ «избранные»." if field == "selected" else \
            "🚫 <b>Бан в ИИ</b> — им помощник закрыт (остальной бот работает)."
        return await render(update, title + "\n\nНажмите на человека, чтобы убрать его из списка.", kb(*rows))
    elif op == "prov":
        if len(parts) > 4 and parts[3] == "tog" and parts[4] in PROVIDERS:
            await save_ai_cfg(prov={**c["prov"], parts[4]: not c["prov"].get(parts[4])})
        if len(parts) > 4 and parts[3] == "key" and parts[4] in PROVIDERS:
            ctx.user_data["admin_state"] = "ai_pkey:" + parts[4]
            v = PROVIDERS[parts[4]]
            return await render(update, f"🔑 <b>Ключ {v['name']}</b>\n\nСоздайте бесплатный ключ на <b>{v['site']}</b> и отправьте его сюда. "
                                        "Бот сначала проверит его, а сообщение с ключом удалит.\n\nОтправьте «-», чтобы удалить ключ.",
                                kb([btn("⬅️ Назад", "a:ai:prov")]))
        today = await ai_stats(1)
        lines = ["🔌 <b>Запасные ИИ</b>", "",
                 "Отвечают на русском, английском и арабском, когда у Gemini подходит к концу бесплатный лимит. "
                 "На узбекском и таджикском всегда отвечает только Gemini.", "",
                 f"♊ Gemini сегодня: <b>{await gemini_used_today()}</b> из ~{c['gem_limit']} (сброс в 13:00 по Ташкенту)",
                 f"🛡 Запас для uz/tg: {c['reserve']} — после {max(0, c['gem_limit'] - c['reserve'])} ответов Gemini "
                 "остальные языки уходят к запасным", ""]
        rows = []
        for k, v in PROVIDERS.items():
            key = AI["pkeys"].get(k)
            on = c["prov"].get(k)
            state = ("✅" if on else "⏸") if key else "🔑 нет ключа"
            lines.append(f"<b>{v['name']}</b>: {state} · сегодня {today.get('ai_p_' + k, 0)}"
                         + (f" · <code>{esc(AI['pmodel'].get(k, ''))}</code>" if AI["pmodel"].get(k) else "")
                         + (" · ⏳ пауза" if AI["cool"].get("p:" + k, 0) > _time.time() else ""))
            rows.append([btn(f"{'⏸ Выкл' if on else '▶️ Вкл'} {v['name']}", f"a:ai:prov:tog:{k}"),
                         btn(f"🔑 {v['name']}" + (f" …{key[-4:]}" if key else ""), f"a:ai:prov:key:{k}")])
        rows.append([btn(f"♊ Лимит Gemini: {c['gem_limit']}", "a:ai:opt:gem_limit"), btn(f"🛡 Запас: {c['reserve']}", "a:ai:opt:reserve")])
        rows.append([btn("⬅️ Назад", "a:ai")])
        return await render(update, "\n".join(lines), kb(*rows))
    elif op == "st":
        lines = ["📊 <b>Статистика ИИ</b>", ""]
        for days, name in ((1, "Сегодня"), (7, "7 дней"), (30, "30 дней")):
            s = await ai_stats(days)
            people = await POOL.fetchval("SELECT count(DISTINCT user_id) FROM ai_log WHERE at > now() - make_interval(days => $1)", days)
            lines.append(f"<b>{name}</b>: {s.get('ai_questions', 0)} вопросов · {people} чел. · бесплатных {s.get('ai_free', 0)} · "
                         f"купленных {s.get('ai_credit', 0) + s.get('ai_unl', 0)} · квота {s.get('ai_quota', 0)} · ошибок {s.get('ai_errors', 0)} · "
                         f"⭐ продажи {s.get('stars_pack', 0)} · ⭐ пожертвования {s.get('stars_don', 0)}")
        today = await ai_stats(1)
        per_model = [(k[5:], v) for k, v in today.items() if k.startswith("ai_m_")]
        if per_model:
            lines += ["", "<b>Модели сегодня:</b>"] + [f"• {esc(m)}: {v}" for m, v in sorted(per_model, key=lambda x: -x[1])]
        main = is_main(uid)
        top = await POOL.fetch("SELECT l.user_id, count(*) AS n FROM ai_log l JOIN users u ON u.user_id = l.user_id "
                               "WHERE l.at > now() - interval '30 days' AND (NOT u.hidden OR $1) GROUP BY l.user_id ORDER BY n DESC LIMIT 10", main)
        if top:
            lines += ["", "<b>Чаще всех спрашивают (30 дн.):</b>"] + [f"• {esc(await admin_name(r['user_id']))} — {r['n']}" for r in top]
        return await render(update, "\n".join(lines), back)
    elif op == "log":
        page = int(parts[3]) if len(parts) > 3 and parts[3].isdigit() else 0
        who = int(parts[4]) if len(parts) > 4 and parts[4].lstrip("-").isdigit() else None
        main = is_main(uid)
        rows = await POOL.fetch("SELECT l.* FROM ai_log l JOIN users u ON u.user_id = l.user_id WHERE (NOT u.hidden OR $1) "
                                "AND ($2::bigint IS NULL OR l.user_id = $2) ORDER BY l.id DESC LIMIT 5 OFFSET $3", main, who, page * 5)
        lines = ["📜 <b>Журнал вопросов</b>" + (f" · <code>{who}</code>" if who else ""), ""]
        for r in rows:
            lines.append(f"👤 {esc(await admin_name(r['user_id']))} · {r['at']:%d.%m %H:%M} UTC · {esc(r['model'] or '')}\n"
                         f"❓ {esc(r['question'][:300])}\n💬 {esc(r['answer'][:400])}{'…' if len(r['answer']) > 400 else ''}\n")
        if not rows:
            lines.append("Пусто.")
        tail = f":{who}" if who else ""
        nav = ([btn("◀️", f"a:ai:log:{page - 1}{tail}")] if page else []) + ([btn("▶️", f"a:ai:log:{page + 1}{tail}")] if len(rows) == 5 else [])
        rows_kb = ([nav] if nav else []) + [[btn("🔎 По человеку", "a:ai:ask:logwho"), btn("⬅️ Назад", "a:ai")]]
        return await render(update, "\n".join(lines)[:4000], kb(*rows_kb))
    elif op == "packs":
        lines = ["⭐ <b>Пакеты вопросов</b>", ""] + [f"• {esc(pack_label('ru', p))}" for p in AI["packs"]]
        return await render(update, "\n".join(lines), kb([btn("✏️ Изменить", "a:ai:ask:packs")], [btn("⬅️ Назад", "a:ai")]))
    elif op == "cards":
        text, _ = screen_cards("ru")
        return await render(update, text, kb([btn("✏️ Изменить", "a:ai:ask:cards")], [btn("⬅️ Назад", "a:ai")]))
    elif op == "pay":
        page = int(parts[3]) if len(parts) > 3 and parts[3].isdigit() else 0
        if len(parts) > 4 and parts[3] in ("ref", "refok"):
            pid = int(parts[4])
            p = await POOL.fetchrow("SELECT * FROM payments WHERE id = $1", pid)
            if p and parts[3] == "ref" and not p["refunded"]:
                return await render(update, f"↩️ Вернуть {p['stars']} ⭐ пользователю <code>{p['user_id']}</code>?\n"
                                            "Купленные вопросы (или безлимит) будут сняты.",
                                    kb([btn("✅ Да, вернуть", f"a:ai:pay:refok:{pid}"), btn("❌ Нет", "a:ai:pay:0")]))
            if p and parts[3] == "refok" and not p["refunded"]:
                try:
                    await ctx.bot.refund_star_payment(p["user_id"], p["charge_id"])
                    await POOL.execute("UPDATE payments SET refunded = TRUE WHERE id = $1", pid)
                    pk = find_pack(p["payload"].split(":")[1]) if p["kind"] == "pack" else None
                    if pk and pk.get("q"):
                        await POOL.execute("UPDATE ai_credits SET credits = greatest(0, credits - $2) WHERE user_id = $1",
                                           p["user_id"], pk["q"])
                    elif pk and pk.get("days"):
                        await POOL.execute("UPDATE ai_credits SET unlimited_until = unlimited_until - make_interval(days => $2) "
                                           "WHERE user_id = $1", p["user_id"], pk["days"])
                    await bump("stars_refund", p["stars"])
                    note = "✅ Возвращено."
                except Exception as e:  # noqa: BLE001
                    note = f"⚠️ Не получилось: {esc(e)}"
                await update.effective_chat.send_message(note, parse_mode=ParseMode.HTML)
        main = is_main(uid)
        rows = await POOL.fetch("SELECT p.* FROM payments p LEFT JOIN users u ON u.user_id = p.user_id "
                                "WHERE (u.hidden IS NOT TRUE OR $1) ORDER BY p.id DESC LIMIT 8 OFFSET $2", main, page * 8)
        total = await POOL.fetchrow("SELECT coalesce(sum(stars) FILTER (WHERE kind = 'pack' AND NOT refunded), 0) AS packs, "
                                    "coalesce(sum(stars) FILTER (WHERE kind = 'don' AND NOT refunded), 0) AS don, "
                                    "coalesce(sum(stars) FILTER (WHERE at > now() - interval '30 days' AND NOT refunded), 0) AS m "
                                    "FROM payments")
        lines = ["💰 <b>Продажи и пожертвования</b>",
                 f"Всего: пакеты {total['packs']} ⭐ · пожертвования {total['don']} ⭐ · за 30 дней {total['m']} ⭐", ""]
        kbrows = []
        for p in rows:
            what = "пожертвование" if p["kind"] == "don" else "пакет " + p["payload"].split(":")[1]
            lines.append(f"{'↩️' if p['refunded'] else '⭐'} {p['at']:%d.%m %H:%M} · {p['stars']} ⭐ · {what} · "
                         f"{esc(await admin_name(p['user_id']))}")
            if not p["refunded"]:
                kbrows.append([btn(f"↩️ Вернуть #{p['id']} ({p['stars']} ⭐)", f"a:ai:pay:ref:{p['id']}")])
        if not rows:
            lines.append("Пока пусто.")
        nav = ([btn("◀️", f"a:ai:pay:{page - 1}")] if page else []) + ([btn("▶️", f"a:ai:pay:{page + 1}")] if len(rows) == 8 else [])
        return await render(update, "\n".join(lines), kb(*(kbrows + ([nav] if nav else []) + [[btn("⬅️ Назад", "a:ai")]])))
    text, markup = await screen_admin_ai()
    return await render(update, text, markup)


async def admin_ai_text(update, ctx, state):
    """Typed answers for the AI settings. Returns True if consumed."""
    msg = update.message
    raw = (msg.text or "").strip()
    uid = update.effective_user.id
    back = kb([btn("⬅️ К настройкам ИИ", "a:ai")])
    field = state[3:]
    if field not in ("test", "logwho"):
        ctx.user_data.pop("admin_state", None)
    if field == "extra":
        await save_ai_cfg(extra="" if raw == "-" else raw[:3000])
        return await msg.reply_text("✅ Инструкции сохранены.", reply_markup=back)
    if field == "disc":
        await save_ai_cfg(disc="" if raw == "-" else raw[:300])
        return await msg.reply_text("✅ Пометка сохранена.", reply_markup=back)
    if field == "test":
        u = dict(await get_user(uid))
        await update.effective_chat.send_action("typing")
        answer, model, err = await ai_answer(u, raw, keep=False)
        text = (ai_markup_html(answer) + f"\n\n<i>🧪 {esc(model)}</i>") if answer else t("ru", err)
        return await msg.reply_text(text[:4000], parse_mode=ParseMode.HTML, reply_markup=back)
    if field == "logwho":
        ctx.user_data.pop("admin_state", None)
        who = await find_user_id(raw)
        return await admin_ai(update, ctx, ["a", "ai", "log", "0", str(who or 0)])
    if field == "key":
        try:
            r = await HTTP.get("https://generativelanguage.googleapis.com/v1beta/models", params={"pageSize": 5},
                               headers={"x-goog-api-key": raw}, timeout=15)
            r.raise_for_status()
        except Exception:  # noqa: BLE001
            return await msg.reply_text("❌ Ключ не подошёл. Проверьте и отправьте ещё раз.", reply_markup=back)
        await kv_set("gemini_key", raw)
        AI["key"], AI["models"], AI["cool"] = raw, [], {}
        try:
            await msg.delete()  # don't leave the key in the chat
        except Exception:  # noqa: BLE001
            pass
        await ai_models()
        return await update.effective_chat.send_message("✅ Новый ключ сохранён и работает.", reply_markup=back)
    if field.startswith("pkey:"):
        p = field[5:]
        pback = kb([btn("⬅️ К запасным ИИ", "a:ai:prov")])
        if raw != "-":
            try:
                model = await provider_models(p, key=raw)
            except Exception:  # noqa: BLE001
                return await msg.reply_text("❌ Ключ не подошёл. Проверьте и отправьте ещё раз.", reply_markup=pback)
        AI["pkeys"][p] = "" if raw == "-" else raw
        AI["pmodel"].pop(p, None)
        AI["cool"].pop("p:" + p, None)
        saved = json.loads(await kv_get("ai_pkeys", "{}") or "{}")
        saved[p] = AI["pkeys"][p]
        await kv_set("ai_pkeys", json.dumps(saved))
        try:
            await msg.delete()  # don't leave the key in the chat
        except Exception:  # noqa: BLE001
            pass
        note = "🗑 Ключ удалён." if raw == "-" else f"✅ Ключ {PROVIDERS[p]['name']} сохранён. Модель: <code>{esc(model)}</code>"
        return await update.effective_chat.send_message(note, parse_mode=ParseMode.HTML, reply_markup=pback)
    if field in ("selected", "banned"):
        who = await find_user_id(raw)
        if not who or not await get_user(who):
            return await msg.reply_text("🤷 Такого человека нет в базе.", reply_markup=back)
        await save_ai_cfg(**{field: sorted(set(AI["cfg"][field]) | {who})})
        return await msg.reply_text(f"✅ Добавлен: {esc(await admin_name(who))}", parse_mode=ParseMode.HTML, reply_markup=back)
    if field == "packs":
        packs = []
        for i, line in enumerate(raw.splitlines()):
            m = re.match(r"\s*(\d+)\s*(д|d|дн|days?)?\s+(\d+)\s*$", line.lower())
            if not m:
                continue
            n, is_days, stars = int(m.group(1)), bool(m.group(2)), int(m.group(3))
            if n and 1 <= stars <= 100000:
                packs.append({"id": f"{'u' if is_days else 'q'}{n}_{stars}", **({"days": n} if is_days else {"q": n}), "stars": stars})
        if not packs:
            return await msg.reply_text("❗ Не понял список. Пример: <code>50 50</code>, <code>30д 300</code>.",
                                        parse_mode=ParseMode.HTML, reply_markup=back)
        AI["packs"] = packs[:6]
        await kv_set("ai_packs", json.dumps(AI["packs"]))
        return await msg.reply_text("✅ Пакеты сохранены:\n" + "\n".join("• " + pack_label("ru", p) for p in AI["packs"]),
                                    reply_markup=back)
    if field == "cards":
        cards, owner = [], AI["cards"].get("owner", "")
        for line in raw.splitlines():
            line = line.strip()
            if line.lower().startswith(("владелец:", "owner:")):
                owner = line.split(":", 1)[1].strip()
                continue
            m = re.match(r"([A-Za-zА-Яа-я]+)\s+([\d ]{12,23})$", line)
            if m:
                cards.append({"label": m.group(1).upper(), "number": " ".join(re.findall(r"\d{4}", m.group(2).replace(" ", "")))})
        if not cards:
            return await msg.reply_text("❗ Не понял. Пример: <code>VISA 4466 1369 0003 3243</code>", parse_mode=ParseMode.HTML,
                                        reply_markup=back)
        AI["cards"] = {"owner": owner, "cards": cards[:6]}
        await kv_set("ai_cards", json.dumps(AI["cards"], ensure_ascii=False))
        text, _ = screen_cards("ru")
        return await msg.reply_text("✅ Сохранено.\n\n" + text, parse_mode=ParseMode.HTML, reply_markup=back)
    if field.startswith("grant:"):
        target = int(field.split(":")[1])
        m = re.match(r"\s*(\d+)\s*(д|d|дн|days?)?\s*$", raw.lower())
        if not m:
            return await msg.reply_text("❗ Отправьте число, например 20 или 30д.", reply_markup=back)
        n, is_days = int(m.group(1)), bool(m.group(2))
        await grant(target, questions=0 if is_days else n, days=n if is_days else 0)
        tu = await get_user(target)
        tl = (tu or {}).get("lang") or "en"
        try:
            await ctx.bot.send_message(target, t(tl, "ai_granted", n=(f"♾ {n} д." if is_days else n)))
        except Exception:  # noqa: BLE001
            pass
        return await msg.reply_text(f"✅ Начислено {'безлимит на ' + str(n) + ' дн.' if is_days else str(n) + ' вопросов'}.",
                                    reply_markup=back)
    return True


# mini app admin: AI settings

async def api_admin_ai(request):
    uid = await admin_auth(request, "ai")
    if request.method == "POST":
        body = await read_json(request)
        if body.get("test"):
            u = dict(await get_user(uid))
            answer, model, err = await ai_answer(u, str(body["test"])[:2000], keep=False)
            return web.json_response({"ok": bool(answer), "html": ai_markup_html(answer) if answer else "", "model": model,
                                      "error": err})
        patch = {}
        for k in ("enabled", "disc_on"):
            if isinstance(body.get(k), bool):
                patch[k] = body[k]
        if body.get("access") in AI_ACCESS_RU:
            patch["access"] = body["access"]
        for k in ("daily_free", "global_free", "memory"):
            if body.get(k) in AI_OPTIONS[k]:
                patch[k] = body[k]
        if body.get("length") in AI_OPTIONS["length"]:
            patch["length"] = body["length"]
        if isinstance(body.get("model"), str) and (body["model"] == "auto" or body["model"] in await ai_models()):
            patch["model"] = body["model"]
        for k, lim in (("extra", 3000), ("disc", 300)):
            if isinstance(body.get(k), str):
                patch[k] = body[k].strip()[:lim]
        if patch:
            await save_ai_cfg(**patch)
    main = is_main(uid)
    logs = await POOL.fetch("SELECT l.*, u.full_name, u.username FROM ai_log l JOIN users u ON u.user_id = l.user_id "
                            "WHERE (NOT u.hidden OR $1) ORDER BY l.id DESC LIMIT 30", main)
    stats = {}
    for days in (1, 7, 30):
        s = await ai_stats(days)
        stats[str(days)] = {"q": s.get("ai_questions", 0), "free": s.get("ai_free", 0),
                            "paid": s.get("ai_credit", 0) + s.get("ai_unl", 0), "quota": s.get("ai_quota", 0),
                            "err": s.get("ai_errors", 0), "stars_pack": s.get("stars_pack", 0), "stars_don": s.get("stars_don", 0)}
    return web.json_response({
        "ok": True, "cfg": AI["cfg"], "models": await ai_models(), "has_key": bool(AI["key"]), "stats": stats,
        "options": AI_OPTIONS,
        "log": [{"name": r["full_name"] or str(r["user_id"]), "username": r["username"], "id": r["user_id"],
                 "at": r["at"].isoformat(), "q": r["question"][:500], "a": r["answer"][:1500], "model": r["model"]} for r in logs]})


# ───────────────────────── bot settings (main admin), defaults for newcomers, one person's settings ─────────────────────────

FEATURES = [("remind", "🔔 Напоминания о намазе"), ("ayah", "📖 Аят дня"), ("ai", "🤖 ИИ-помощник"), ("app", "📱 Мини-приложение"),
            ("share", "🤝 Поделиться с друзьями"), ("groups", "➕ Добавление в группы"), ("donate", "💝 Пожертвования"),
            ("weekly", "📊 Недельные отчёты"), ("auto", "🔄 Автообновление карточки"), ("tour", "🎬 Приветственный тур"),
            ("support", "💬 Поддержка")]
MENU_ITEMS = {"times": "🕌 Время намаза", "app": "📱 Приложение", "ayah": "📖 Аят дня", "qibla": "🧭 Кибла",
              "remind": "🔔 Напоминания", "settings": "⚙️ Настройки", "ai": "🤖 Вопрос об исламе", "groups": "➕ В группу",
              "share": "🤝 Поделиться"}
MENU_DEFAULT = [["times"], ["app"], ["ayah", "qibla"], ["remind", "settings"], ["ai"], ["groups"], ["share"]]
BOT_CFG_DEFAULT = {"maint": False, "maint_text": "", "closed": False, "closed_text": "", "feat": {},
                   "menu": MENU_DEFAULT, "hide": [], "sub": {"on": False, "channel": "", "text": ""},
                   "defaults": {}, "welcome": "", "sup_auto": "", "profile": {}}
BOT_CFG = json.loads(json.dumps(BOT_CFG_DEFAULT))
SUB_OK = {}      # user_id -> time until which the subscription check is trusted
GATE_NOTE = {}   # user_id -> last time we told them the bot is off/closed


async def load_bot_cfg():
    try:
        cfg = json.loads(await kv_get("bot_cfg", "{}") or "{}")
    except ValueError:
        cfg = {}
    BOT_CFG.clear()
    BOT_CFG.update(json.loads(json.dumps(BOT_CFG_DEFAULT)))
    BOT_CFG.update(cfg)
    known = {k for row in BOT_CFG["menu"] for k in row}
    BOT_CFG["menu"] += [[k] for row in MENU_DEFAULT for k in row if k not in known]  # buttons added later


async def save_bot_cfg():
    await kv_set("bot_cfg", json.dumps(BOT_CFG, ensure_ascii=False))


def feat(name):
    return BOT_CFG["feat"].get(name, True)


def bot_off():
    return BOT_CFG.get("maint", False)


# ── what people see ──

def menu_button(u, key):
    lang = u["lang"]
    if key == "times":
        return InlineKeyboardButton(t(lang, "btn_times"), callback_data="m:times", style="success")
    if key == "app":
        return webapp_btn(t(lang, "btn_app"), "today") if WEBAPP_URL and feat("app") else None
    if key == "ayah":
        return btn(t(lang, "ayah_btn"), "ay:show") if feat("ayah") else None
    if key == "qibla":
        return qibla_btn(u)
    if key == "remind":
        return btn(t(lang, "btn_rem_s_on" if u["remind"] else "btn_rem_s_off"), "m:toggle")
    if key == "settings":
        return btn(t(lang, "btn_settings"), "m:settings")
    if key == "ai":
        return InlineKeyboardButton(t(lang, "ai_btn"), callback_data="ai:start", style="primary") \
            if ai_allowed_now(u["user_id"]) else None
    if key == "groups":
        return add_group_btn(lang) if BOT_USERNAME and feat("groups") else None
    if key == "share":
        if not feat("share"):
            return None
        return btn(t(lang, "fr_btn"), "fr:share")  # the bot sends the card right here (the mini app has its own screen)
    return None


def private_menu_rows(u):
    hide = set(BOT_CFG.get("hide", []))
    rows = []
    for row in BOT_CFG["menu"]:
        bs = [b for b in (menu_button(u, k) for k in row if k not in hide or k == "settings") if b]
        if bs:
            rows.append(bs)
    return rows


GATE_T = {
    "en": {"g_maint": "🛠 The bot is under maintenance. We'll be back soon 🤍", "g_closed": "🚪 New sign-ups are closed for now. Please try again later 🤍",
           "g_sub": "📢 To use the bot, please subscribe to our channel first, then tap «✅ I've subscribed».",
           "g_sub_btn": "📢 Subscribe", "g_sub_chk": "✅ I've subscribed", "g_sub_no": "You haven't subscribed yet 🙏", "g_sub_ok": "✅ Thank you! Press /start"},
    "ru": {"g_maint": "🛠 Бот на техническом обслуживании. Скоро вернёмся 🤍", "g_closed": "🚪 Регистрация новых пользователей пока закрыта. Загляните позже 🤍",
           "g_sub": "📢 Чтобы пользоваться ботом, подпишитесь на наш канал и нажмите «✅ Я подписался».",
           "g_sub_btn": "📢 Подписаться", "g_sub_chk": "✅ Я подписался", "g_sub_no": "Вы ещё не подписались 🙏", "g_sub_ok": "✅ Спасибо! Нажмите /start"},
    "uz": {"g_maint": "🛠 Botda texnik ishlar olib borilmoqda. Tez orada qaytamiz 🤍", "g_closed": "🚪 Yangi foydalanuvchilar uchun ro'yxatdan o'tish hozircha yopiq. Keyinroq urinib ko'ring 🤍",
           "g_sub": "📢 Botdan foydalanish uchun kanalimizga obuna bo'ling va «✅ Obuna bo'ldim» tugmasini bosing.",
           "g_sub_btn": "📢 Obuna bo'lish", "g_sub_chk": "✅ Obuna bo'ldim", "g_sub_no": "Hali obuna bo'lmadingiz 🙏", "g_sub_ok": "✅ Rahmat! /start ni bosing"},
    "tg": {"g_maint": "🛠 Бот дар таъмир аст. Ба зудӣ бармегардем 🤍", "g_closed": "🚪 Сабти номи корбарони нав ҳоло баста аст. Баъдтар биёед 🤍",
           "g_sub": "📢 Барои истифодаи бот ба канали мо обуна шавед ва «✅ Обуна шудам»-ро пахш кунед.",
           "g_sub_btn": "📢 Обуна шудан", "g_sub_chk": "✅ Обуна шудам", "g_sub_no": "Шумо ҳанӯз обуна нашудаед 🙏", "g_sub_ok": "✅ Ташаккур! /start-ро пахш кунед"},
    "ar": {"g_maint": "🛠 البوت قيد الصيانة. سنعود قريبًا 🤍", "g_closed": "🚪 التسجيل للمستخدمين الجدد مغلق حاليًا. حاول لاحقًا 🤍",
           "g_sub": "📢 لاستخدام البوت اشترك في قناتنا أولاً ثم اضغط «✅ اشتركت».",
           "g_sub_btn": "📢 اشترك", "g_sub_chk": "✅ اشتركت", "g_sub_no": "لم تشترك بعد 🙏", "g_sub_ok": "✅ شكرًا! اضغط /start"},
}
for _l, _d in GATE_T.items():
    T[_l].update(_d)
T["uzc"].update(to_cyr(GATE_T["uz"]))


async def gate_note(update, text, markup=None):
    """Tells the person why the bot doesn't answer (at most once a minute for messages)."""
    uid = update.effective_user.id
    if update.callback_query:
        try:
            await update.callback_query.answer(text[:190], show_alert=True)
        except Exception:  # noqa: BLE001
            pass
        return
    if GATE_NOTE.get(uid, 0) > _time.time() - 60 and markup is None:
        return
    GATE_NOTE[uid] = _time.time()
    try:
        await update.effective_chat.send_message(text, reply_markup=markup, disable_web_page_preview=True)
    except Exception:  # noqa: BLE001
        pass


async def sub_ok(bot, uid, fresh=False):
    ch = BOT_CFG["sub"].get("channel")
    if not ch:
        return True
    if not fresh and SUB_OK.get(uid, 0) > _time.time():
        return True
    try:
        m = await bot.get_chat_member(ch, uid)
        ok = m.status in ("member", "administrator", "creator", "restricted")
    except Exception:  # noqa: BLE001
        log.warning("subscription check failed for %s", ch)
        ok = True  # the bot isn't an admin of the channel: don't lock people out
    if ok:
        SUB_OK[uid] = _time.time() + 600
    return ok


async def gate_rules(update, ctx, user, lang, inserted):
    """Maintenance, closed sign-ups, required channel. Raises ApplicationHandlerStop when the person must wait."""
    if is_admin(user.id):
        return
    chat = update.effective_chat
    private = chat is not None and chat.type == "private"
    if bot_off():
        if private or update.callback_query:
            await gate_note(update, BOT_CFG.get("maint_text") or t(lang, "g_maint"))
        raise ApplicationHandlerStop
    if not private:
        return
    if inserted and BOT_CFG.get("closed"):
        await POOL.execute("DELETE FROM users WHERE user_id = $1 AND NOT onboarded", user.id)
        await gate_note(update, BOT_CFG.get("closed_text") or t(lang, "g_closed"))
        raise ApplicationHandlerStop
    sub = BOT_CFG.get("sub") or {}
    if sub.get("on") and sub.get("channel"):
        q = update.callback_query
        if q and q.data == "subchk":
            if await sub_ok(ctx.bot, user.id, fresh=True):
                await q.answer(t(lang, "g_sub_ok"), show_alert=True)
                try:
                    await q.message.delete()
                except Exception:  # noqa: BLE001
                    pass
            else:
                await q.answer(t(lang, "g_sub_no"), show_alert=True)
            raise ApplicationHandlerStop
        if not await sub_ok(ctx.bot, user.id):
            ch = sub["channel"].lstrip("@")
            markup = kb([InlineKeyboardButton(t(lang, "g_sub_btn"), url=f"https://t.me/{ch}")], [btn(t(lang, "g_sub_chk"), "subchk")])
            if update.callback_query:
                await gate_note(update, t(lang, "g_sub_no"))
            await gate_note(update, sub.get("text") or t(lang, "g_sub"), markup)
            raise ApplicationHandlerStop


async def apply_defaults(uid):
    d = BOT_CFG.get("defaults") or {}
    fields = {}
    for k, v in d.items():
        if k == "quiet":
            fields.update(quiet_start=None, quiet_end=None) if v == "off" else \
                fields.update(quiet_start=int(v.split("-")[0]), quiet_end=int(v.split("-")[1]))
        elif k == "pm":
            fields["prayer_modes"] = v
        elif k in USER_FIELDS:
            fields[k] = v
    if fields:
        await save(uid, **fields)


async def send_welcome(bot, uid):
    await asyncio.sleep(2)
    try:
        await bot.send_message(uid, BOT_CFG["welcome"], disable_web_page_preview=True)
    except Exception:  # noqa: BLE001
        pass


# ── the settings a person has (used for one person and for the defaults) ──

def _yn(v):
    return "да ✅" if v else "нет ❌"


def _quiet_label(v):
    return "выкл" if v in (None, "off") else f"{int(v.split('-')[0]):02d}:00–{int(v.split('-')[1]):02d}:00"


USER_FIELDS = {
    "lang": ("🌐 Язык", list(LANGS), lambda v: LANG_BUTTONS.get(v, v or "—")),
    "madhab": ("🕌 Мазхаб", ["hanafi", "std"], lambda v: MADHAB_RU.get(v, "—")),
    "remind": ("🔔 Напоминания", [True, False], _yn),
    "lead_min": ("⏰ Напоминать за", LEAD_OPTIONS, lambda v: f"{v} мин" if v else "без заранее"),
    "at_time": ("🕌 В момент азана", [True, False], _yn),
    "quiet": ("🔕 Тихие часы", ["off"] + [f"{a}-{b}" for a, b in QUIET_PRESETS], _quiet_label),
    "auto_mode": ("🔄 Автообновление", AUTO_OPTIONS, lambda v: auto_label("ru", v)),
    "ramadan": ("🌙 Рамадан в карточке", [True, False], _yn),
    "suhoor_rem": ("🥣 Сухур", SUH_OPTS, lambda v: "выкл" if v < 0 else f"за {v} мин"),
    "iftar_rem": ("🍽 Ифтар", IFT_OPTS, lambda v: "выкл" if v < 0 else ("в момент Магриба" if v == 0 else f"за {v} мин")),
    "ayah_rem": ("📖 Аят дня в 9:00", [True, False], _yn),
    "weekly": ("📊 Недельный отчёт", [True, False], _yn),
    "daily": ("📅 Расписание в чат", ["off", "fajr", "sunrise"], lambda v: {"off": "выкл", "fajr": "в Фаджр", "sunrise": "на восходе"}.get(v, v)),
}
PRIVATE_FIELDS = ["lang", "madhab", "remind", "lead_min", "at_time", "quiet", "auto_mode", "ramadan", "suhoor_rem", "iftar_rem",
                  "ayah_rem", "weekly"]
CHAT_FIELDS = ["lang", "madhab", "remind", "lead_min", "at_time", "quiet", "auto_mode", "ramadan", "daily"]
DEFAULT_FIELDS = ["lead_min", "at_time", "quiet", "auto_mode", "ramadan", "suhoor_rem", "iftar_rem", "ayah_rem", "weekly"]
MODE_RU = {"s": "🔔", "q": "🔕", "o": "❌"}


def field_value(u, f):
    if f == "quiet":
        return "off" if u["quiet_start"] is None else f"{u['quiet_start']}-{u['quiet_end']}"
    return u[f]


def enc(v):
    return "1" if v is True else "0" if v is False else str(v)


def dec(f, raw):
    opts = USER_FIELDS[f][1]
    for o in opts:
        if enc(o) == raw:
            return o, True
    return None, False


async def screen_user_settings(uid, back):
    u = await get_user(uid)
    if not u:
        return "🤷 Нет такого пользователя.", kb(ADMIN_BACK)
    private = u["chat_type"] == "private"
    fields = PRIVATE_FIELDS if private else CHAT_FIELDS
    who = esc(await admin_name(uid))
    lines = [f"⚙️ <b>Настройки: {who}</b>", "", f"📍 Город: {esc(u['city'] or '—')}"]
    rows, cur = [[btn("📍 Изменить город", f"a:usc:{uid}:{back}")]], []
    for f in fields:
        label, _, show = USER_FIELDS[f]
        val = field_value(u, f)
        lines.append(f"{label}: <b>{esc(show(val))}</b>")
        cur.append(btn(label, f"a:uso:{uid}:{f}:{back}"))
        if len(cur) == 2:
            rows.append(cur)
            cur = []
    if cur:
        rows.append(cur)
    modes = (u["prayer_modes"] or "sssss").ljust(5, "s")
    lines.append("🔊 Звук намазов: " + " ".join(f"{PN['ru'][k.lower()]} {MODE_RU[modes[i]]}" for i, k in enumerate(EVENTS)))
    rows.append([btn(f"{MODE_RU[modes[i]]} {PN['ru'][k.lower()]}", f"a:uspm:{uid}:{i}:{back}") for i, k in enumerate(EVENTS)])
    lines += ["", "Нажмите на настройку, чтобы изменить. Человеку ничего не придёт."]
    rows.append([btn("⬅️ К карточке", f"a:card:{uid}:{back}")])
    return "\n".join(lines), kb(*rows)


async def set_user_field(bot, uid, f, val):
    u = await get_user(uid)
    if f == "quiet":
        if val == "off":
            await save(uid, quiet_start=None, quiet_end=None)
        else:
            a, b = (int(x) for x in val.split("-"))
            await save(uid, quiet_start=a, quiet_end=b)
        return
    await save(uid, **{f: val})
    if f == "lang" and u and u["lang"] != val:
        await relocalize_city(uid, val)
        if u["chat_type"] == "private" and u["onboarded"]:
            try:
                await sync_menu_button(bot, await get_user(uid))
            except Exception:  # noqa: BLE001
                pass


# ── admin screens ──

def screen_bset_home():
    c = BOT_CFG
    off = [n for k, n in FEATURES if not feat(k)]
    sub = c.get("sub") or {}
    text = ("⚙️ <b>Настройки бота</b>\n\n"
            f"Бот: {'🔴 выключен (техработы)' if c['maint'] else '🟢 работает'}\n"
            f"Регистрация: {'🚪 закрыта' if c['closed'] else '✅ открыта'}\n"
            f"Подписка на канал: {('✅ ' + esc(sub.get('channel', ''))) if sub.get('on') else 'выкл'}\n"
            f"Выключенные функции: {', '.join(off) if off else 'нет'}")
    return text, kb(
        [btn("🟢 Включить бота" if c["maint"] else "🔴 Выключить бота", "a:bset:maint")],
        [btn("✅ Открыть регистрацию" if c["closed"] else "🚪 Закрыть регистрацию", "a:bset:closed")],
        [btn("🧩 Функции", "a:bset:feat"), btn("🧭 Меню", "a:bset:menu")],
        [btn("✍️ Тексты", "a:bset:texts"), btn("📢 Подписка на канал", "a:bset:sub")],
        [btn("👥 По умолчанию для новичков", "a:bset:def")],
        [btn("🤝 Карточка приглашения", "a:bset:inv")],
        [btn("🖥 Система", "a:bset:sys")],
        ADMIN_BACK)


TEXT_KEYS = {"maint_text": ("🛠 Текст техработ", "Что увидят люди, когда бот выключен."),
             "closed_text": ("🚪 Текст закрытой регистрации", "Что увидят новые люди, когда регистрация закрыта."),
             "welcome": ("👋 Приветствие новичкам", "Отдельное сообщение каждому новому человеку после первого /start."),
             "sup_auto": ("💬 Автоответ поддержки", "Приходит человеку после его сообщения в поддержку."),
             "sub_text": ("📢 Текст про подписку", "Что увидит человек, пока не подписан на канал.")}
PROFILE_LANGS = ["en", "ru", "uz", "tg", "ar"]


async def admin_bset(update, ctx, parts):
    """a:bset:… — the main admin's bot settings."""
    what = parts[2] if len(parts) > 2 else "home"
    arg = parts[3] if len(parts) > 3 else ""
    c = BOT_CFG
    if what in ("maint", "closed"):
        c[what] = not c[what]
        await save_bot_cfg()
    elif what == "feat":
        if arg:
            c["feat"][arg] = not feat(arg)
            if arg == "ai":
                await save_ai_cfg(enabled=c["feat"][arg])
            await save_bot_cfg()
        rows = [[btn(("✅ " if feat(k) else "⛔ ") + n, f"a:bset:feat:{k}")] for k, n in FEATURES]
        return await render(update, "🧩 <b>Функции бота</b>\n\nНажмите, чтобы включить или выключить для всех.\n"
                                    "Выключенная функция пропадает из меню и перестаёт работать.", kb(*rows, [btn("⬅️ Назад", "a:bset")]))
    elif what == "menu":
        menu, hide = c["menu"], set(c.get("hide", []))
        if arg == "up" and len(parts) > 4 and parts[4].isdigit():
            i = int(parts[4])
            if 0 < i < len(menu):
                menu[i - 1], menu[i] = menu[i], menu[i - 1]
        elif arg == "down" and len(parts) > 4 and parts[4].isdigit():
            i = int(parts[4])
            if 0 <= i < len(menu) - 1:
                menu[i + 1], menu[i] = menu[i], menu[i + 1]
        elif arg == "hide" and len(parts) > 4 and parts[4] in MENU_ITEMS and parts[4] != "settings":
            hide ^= {parts[4]}
            c["hide"] = sorted(hide)
        elif arg == "join" and len(parts) > 4 and parts[4].isdigit():  # put this row next to the one above
            i = int(parts[4])
            if 0 < i < len(menu) and len(menu[i - 1]) + len(menu[i]) <= 3:
                menu[i - 1] = menu[i - 1] + menu.pop(i)
        elif arg == "split" and len(parts) > 4 and parts[4].isdigit():
            i = int(parts[4])
            if i < len(menu) and len(menu[i]) > 1:
                menu[i:i + 1] = [[k] for k in menu[i]]
        elif arg == "reset":
            c["menu"], c["hide"] = json.loads(json.dumps(MENU_DEFAULT)), []
        if arg:
            await save_bot_cfg()
        menu, hide = c["menu"], set(c.get("hide", []))
        lines = ["🧭 <b>Меню бота</b>", "", "Порядок строк сверху вниз. 🙈 — скрыто. «Админка» всегда внизу у админов.", ""]
        rows = []
        for i, row in enumerate(menu):
            lines.append(f"{i + 1}. " + " | ".join(("🙈 " if k in hide else "") + MENU_ITEMS[k] for k in row))
            rows.append([btn("🔼", f"a:bset:menu:up:{i}"), btn("🔽", f"a:bset:menu:down:{i}")] +
                        ([btn("⤴️ Склеить", f"a:bset:menu:join:{i}")] if i and len(menu[i - 1]) + len(row) <= 3 else []) +
                        ([btn("↔️ Разделить", f"a:bset:menu:split:{i}")] if len(row) > 1 else []))
            rows.append([btn(("👁 " if k in hide else "🙈 ") + MENU_ITEMS[k], f"a:bset:menu:hide:{k}") for k in row if k != "settings"]
                        or [btn("⚙️ Настройки — всегда видны", "a:bset:menu")])
        rows += [[btn("♻️ Как было", "a:bset:menu:reset")], [btn("⬅️ Назад", "a:bset")]]
        return await render(update, "\n".join(lines), kb(*rows))
    elif what == "texts":
        if arg in TEXT_KEYS or arg.startswith("pd_") or arg.startswith("pa_"):
            ctx.user_data["admin_state"] = "bs_text:" + arg
            if arg in TEXT_KEYS:
                title, hint = TEXT_KEYS[arg]
                cur = (c.get("sub") or {}).get("text", "") if arg == "sub_text" else c.get(arg, "")
            else:
                pl = arg[3:]
                title = ("📝 Описание бота" if arg.startswith("pd_") else "🏷 Короткое описание") + f" ({pl.upper()})"
                hint = ("Текст на пустом экране бота до /start (до 512 символов)." if arg.startswith("pd_")
                        else "Текст в профиле бота (до 120 символов).")
                cur = (c.get("profile", {}).get(pl) or {}).get("desc" if arg.startswith("pd_") else "about", "")
            return await render(update, f"{title}\n\n{hint}\n\nСейчас: <i>{esc(cur) if cur else 'стандартный'}</i>\n\n"
                                        "Отправьте новый текст или «-», чтобы вернуть стандартный.", kb([btn("⬅️ Назад", "a:bset:texts")]))
        rows = [[btn(v[0], f"a:bset:texts:{k}")] for k, v in TEXT_KEYS.items()]
        rows.append([btn(f"📝 {pl.upper()}", f"a:bset:texts:pd_{pl}") for pl in PROFILE_LANGS])
        rows.append([btn(f"🏷 {pl.upper()}", f"a:bset:texts:pa_{pl}") for pl in PROFILE_LANGS])
        rows.append([btn("⬅️ Назад", "a:bset")])
        return await render(update, "✍️ <b>Тексты</b>\n\nСвои тексты показываются всем на одном языке — так, как вы их напишете.\n"
                                    "📝 — описание бота на пустом экране, 🏷 — короткое описание в профиле (по языкам).", kb(*rows))
    elif what == "sub":
        sub = c.setdefault("sub", {"on": False, "channel": "", "text": ""})
        if arg == "on":
            if not sub.get("channel"):
                return await update.callback_query.answer("Сначала укажите канал", show_alert=True)
            try:
                me = await ctx.bot.get_chat_member(sub["channel"], ctx.bot.id)
                if me.status not in ("administrator", "creator"):
                    return await update.callback_query.answer("Сделайте бота админом канала, иначе он не видит подписчиков.",
                                                              show_alert=True)
            except Exception:  # noqa: BLE001
                return await update.callback_query.answer("Бот не видит канал. Добавьте бота в канал админом.", show_alert=True)
            sub["on"] = True
            await save_bot_cfg()
        elif arg == "off":
            sub["on"] = False
            await save_bot_cfg()
        elif arg == "ch":
            ctx.user_data["admin_state"] = "bs_text:sub_ch"
            return await render(update, "📢 Отправьте @username канала (например, <code>@MawaqitNews</code>).\n\n"
                                        "Бота нужно добавить в этот канал администратором.", kb([btn("⬅️ Назад", "a:bset:sub")]))
        return await render(update, "📢 <b>Обязательная подписка на канал</b>\n\n"
                                    f"Статус: {'✅ включена' if sub.get('on') else '⛔ выключена'}\n"
                                    f"Канал: {esc(sub.get('channel') or '— не указан')}\n\n"
                                    "Пока человек не подписан, бот показывает ему кнопку «Подписаться». Админов это не касается.",
                            kb([btn("✏️ Указать канал", "a:bset:sub:ch")],
                               [btn("⛔ Выключить", "a:bset:sub:off") if sub.get("on") else btn("✅ Включить", "a:bset:sub:on")],
                               [btn("✍️ Свой текст", "a:bset:texts:sub_text")], [btn("⬅️ Назад", "a:bset")]))
    elif what == "def":
        d = c.setdefault("defaults", {})
        if arg == "set" and len(parts) > 5:
            f, raw = parts[4], parts[5]
            if f == "pm" and re.match(r"^[sqo]{5}$", raw):
                d["pm"] = raw
            elif f in DEFAULT_FIELDS:
                v, ok = dec(f, raw)
                if ok:
                    d[f] = v
            await save_bot_cfg()
        elif arg == "opt" and len(parts) > 4 and parts[4] in DEFAULT_FIELDS:
            f = parts[4]
            label, opts, show = USER_FIELDS[f]
            rows = [[btn(("✅ " if enc(d.get(f)) == enc(o) else "") + show(o), f"a:bset:def:set:{f}:{enc(o)}")] for o in opts]
            rows.append([btn("📣 Применить текущее ко всем", f"a:bset:def:all:{f}")] if f in d else [])
            rows.append([btn("⬅️ Назад", "a:bset:def")])
            return await render(update, f"{label} — <b>по умолчанию для новичков</b>", kb(*rows))
        elif arg == "all" and len(parts) > 4 and (parts[4] in d):
            f = parts[4]
            return await render(update, f"📣 Поставить «{esc(USER_FIELDS[f][0] if f != 'pm' else '🔊 Звук намазов')}» = "
                                        f"<b>{esc(USER_FIELDS[f][2](d[f]) if f != 'pm' else d[f])}</b> всем пользователям?\n\n"
                                        "Это изменит настройку у всех, кто уже пользуется ботом.",
                                kb([btn("✅ Да, всем", f"a:bset:def:allok:{f}"), btn("⬅️ Нет", "a:bset:def")]))
        elif arg == "allok" and len(parts) > 4 and parts[4] in d:
            f, v = parts[4], d[parts[4]]
            if f == "quiet":
                a, b = (None, None) if v == "off" else (int(x) for x in v.split("-"))
                n = await POOL.execute("UPDATE users SET quiet_start = $1, quiet_end = $2 WHERE chat_type = 'private'", a, b)
            else:
                col = "prayer_modes" if f == "pm" else f
                n = await POOL.execute(f"UPDATE users SET {col} = $1 WHERE chat_type = 'private'", v)
            await update.effective_chat.send_message(f"✅ Готово: {n.split()[-1]} пользователей.")
        elif arg == "pm" and len(parts) > 4 and parts[4].isdigit():
            pm = list((d.get("pm") or "sssss").ljust(5, "s"))
            i = int(parts[4]) % 5
            pm[i] = {"s": "q", "q": "o", "o": "s"}[pm[i]]
            d["pm"] = "".join(pm)
            await save_bot_cfg()
        lines = ["👥 <b>По умолчанию для новичков</b>", "", "Так будет у каждого нового человека. Не задано — стандартное значение.", ""]
        rows, cur = [], []
        for f in DEFAULT_FIELDS:
            label, _, show = USER_FIELDS[f]
            lines.append(f"{label}: <b>{esc(show(d[f])) if f in d else 'стандарт'}</b>")
            cur.append(btn(label, f"a:bset:def:opt:{f}"))
            if len(cur) == 2:
                rows.append(cur)
                cur = []
        if cur:
            rows.append(cur)
        pm = (d.get("pm") or "sssss").ljust(5, "s")
        lines.append("🔊 Звук намазов: " + " ".join(f"{PN['ru'][k.lower()]} {MODE_RU[pm[i]]}" for i, k in enumerate(EVENTS)))
        rows.append([btn(f"{MODE_RU[pm[i]]} {PN['ru'][k.lower()]}", f"a:bset:def:pm:{i}") for i, k in enumerate(EVENTS)])
        if "pm" in d:
            rows.append([btn("📣 Звук намазов — применить ко всем", "a:bset:def:all:pm")])
        rows.append([btn("⬅️ Назад", "a:bset")])
        return await render(update, "\n".join(lines), kb(*rows))
    elif what == "inv":
        inv = invite_cfg()
        if arg in ("video", "photo"):
            inv["mode"] = arg
            await save_bot_cfg()
        elif arg == "clr":
            inv["custom"] = {}
            await save_bot_cfg()
        elif arg == "up":
            ctx.user_data["admin_state"] = "inv_up"
            return await render(update, "📤 Отправьте своё фото, видео или GIF — оно заменит наши карточки для всех языков.\n\n"
                                        "Подпись с хадисом и @MawaqitTimeBot добавится сама.", kb([btn("⬅️ Назад", "a:bset:inv")]))
        custom = inv["custom"].get("all")
        return await render(update, "🤝 <b>Карточка приглашения</b>\n\n"
                                    f"По умолчанию: <b>{'🎬 видео' if inv['mode'] == 'video' else '🖼 фото'}</b>\n"
                                    f"Своя карточка: {('✅ загружено ' + custom['type']) if custom else 'нет — наши карточки на языке человека'}\n\n"
                                    "В мини-приложении человек может сам переключить видео/фото.",
                            kb([btn(("✅ " if inv["mode"] == "video" else "") + "🎬 Видео", "a:bset:inv:video"),
                                btn(("✅ " if inv["mode"] == "photo" else "") + "🖼 Фото", "a:bset:inv:photo")],
                               [btn("📤 Загрузить свою", "a:bset:inv:up")] + ([btn("🗑 Убрать свою", "a:bset:inv:clr")] if custom else []),
                               [btn("⬅️ Назад", "a:bset")]))
    elif what == "sys":
        if arg == "restart":
            return await render(update, "♻️ Перезапустить бота? Он будет недоступен около минуты.",
                                kb([btn("♻️ Да, перезапустить", "a:bset:sys:restartok"), btn("⬅️ Нет", "a:bset:sys")]))
        if arg == "restartok":
            await render(update, "♻️ Перезапускаю… Через минуту нажмите /start.", kb(ADMIN_BACK))
            log.warning("restart requested by the main admin")
            asyncio.get_running_loop().call_later(1.5, os._exit, 1)
            return
        if arg == "backup":
            await update.callback_query.answer("Собираю копию…")
            return await send_backup(update)
        errs = "\n".join(f"• <code>{e[0]:%d.%m %H:%M}</code> {esc(e[1])}" for e in list(ERRBUF)) or "— ошибок нет 🎉"
        up = int(_time.time() - START_TS)
        size = await POOL.fetchval("SELECT pg_size_pretty(pg_database_size(current_database()))")
        return await render(update, f"🖥 <b>Система</b>\n\n⏱ Работает: {up // 86400} д {up % 86400 // 3600} ч {up % 3600 // 60} мин\n"
                                    f"🗄 Размер базы: {size}\n\n<b>Последние ошибки</b>\n{errs}",
                            kb([btn("💾 Резервная копия базы", "a:bset:sys:backup")],
                               [btn("♻️ Перезапустить бота", "a:bset:sys:restart")], [btn("🔄 Обновить", "a:bset:sys")],
                               [btn("⬅️ Назад", "a:bset")]))
    text, markup = screen_bset_home()
    return await render(update, text, markup)


async def send_backup(update):
    data, n = await build_backup()
    await update.effective_chat.send_document(document=data, filename=f"mawaqit_backup_{datetime.utcnow():%Y%m%d_%H%M}.zip",
                                              caption=f"💾 Резервная копия: {n} таблиц")


async def build_backup():
    """All tables as CSV files in one zip."""
    import zipfile
    buf = io.BytesIO()
    tables = [r["table_name"] for r in await POOL.fetch(
        "SELECT table_name FROM information_schema.tables WHERE table_schema = current_schema() AND table_type = 'BASE TABLE' "
        "ORDER BY table_name")]
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        async with POOL.acquire() as conn:
            for tname in tables:
                out = io.BytesIO()
                await conn.copy_from_query(f'SELECT * FROM "{tname}"', output=out, format="csv", header=True)
                z.writestr(f"{tname}.csv", out.getvalue())
    buf.seek(0)
    return buf, len(tables)


async def admin_bset_text(update, ctx, state):
    """Typed answers for the bot settings. Returns True if consumed."""
    msg = update.message
    plain = (msg.text or "").strip()
    key = state.split(":", 1)[1]
    ctx.user_data.pop("admin_state", None)
    c = BOT_CFG
    back = kb([btn("⬅️ К настройкам", "a:bset")])
    if key == "sub_ch":
        ch = plain.split("/")[-1].lstrip("@")
        if not re.match(r"^[A-Za-z0-9_]{4,}$", ch):
            await msg.reply_text("❗ Нужен @username канала, например @MawaqitNews", reply_markup=back)
            return True
        c.setdefault("sub", {})["channel"] = "@" + ch
        c["sub"]["on"] = False
        await save_bot_cfg()
        await msg.reply_text(f"✅ Канал: @{esc(ch)}. Подписка пока выключена — включите её в «📢 Подписка на канал», "
                             "когда добавите бота в канал админом.", parse_mode=ParseMode.HTML,
                             reply_markup=kb([btn("📢 Подписка на канал", "a:bset:sub")]))
        return True
    if key in TEXT_KEYS:
        if key == "sub_text":
            c.setdefault("sub", {})["text"] = "" if plain == "-" else plain[:1000]
        else:
            c[key] = "" if plain == "-" else plain[:3000]
        await save_bot_cfg()
        await msg.reply_text("✅ Сохранено.", reply_markup=kb([btn("⬅️ К текстам", "a:bset:texts")]))
        return True
    if key[:3] in ("pd_", "pa_") and key[3:] in PROFILE_LANGS:
        pl, field = key[3:], ("desc" if key.startswith("pd_") else "about")
        limit = 512 if field == "desc" else 120
        text = plain if plain != "-" else ""
        if len(text) > limit:
            await msg.reply_text(f"❗ Слишком длинно: {len(text)} символов, можно до {limit}.")
            return True
        c.setdefault("profile", {}).setdefault(pl, {})[field] = text
        await save_bot_cfg()
        ok = await apply_profile_texts(ctx.bot, only=pl)
        await msg.reply_text("✅ Сохранено" + (" и обновлено в профиле бота." if ok else ", но Telegram пока не принял — попробую при перезапуске."),
                             reply_markup=kb([btn("⬅️ К текстам", "a:bset:texts")]))
        return True
    return False


async def apply_profile_texts(bot, only=None):
    ok = True
    for pl in PROFILE_LANGS:
        if only and pl != only:
            continue
        custom = BOT_CFG.get("profile", {}).get(pl) or {}
        about = custom.get("about") or (BOT_ABOUT["en"] if pl == "en" else "")
        desc = custom.get("desc") or (BOT_DESCRIPTION["en"] if pl == "en" else "")
        for code in ([None, pl] if pl == "en" else [pl]):
            try:
                await bot.set_my_short_description(about, language_code=code)
                await bot.set_my_description(desc, language_code=code)
            except Exception:  # noqa: BLE001
                log.exception("could not set profile texts for %s", code or "default")
                ok = False
    return ok


async def admin_user_settings(update, ctx, parts):
    """a:us / a:uso / a:usset / a:uspm / a:usc — one person's (or chat's) settings."""
    sub = parts[1]
    uid = int(parts[2]) if len(parts) > 2 and parts[2].lstrip("-").isdigit() else 0
    u = await get_user(uid) if uid else None
    if not u:
        return await render(update, "🤷 Нет такого пользователя.", kb(ADMIN_BACK))
    if sub == "uso" and len(parts) > 3 and parts[3] in USER_FIELDS:
        f, back = parts[3], (parts[4] if len(parts) > 4 else "")
        label, opts, show = USER_FIELDS[f]
        cur = field_value(u, f)
        rows = [[btn(("✅ " if enc(cur) == enc(o) else "") + show(o), f"a:usset:{uid}:{f}:{enc(o)}:{back}")] for o in opts]
        rows.append([btn("⬅️ Назад", f"a:us:{uid}:{back}")])
        return await render(update, f"{label} — {esc(await admin_name(uid))}", kb(*rows))
    if sub == "usset" and len(parts) > 4 and parts[3] in USER_FIELDS:
        v, ok = dec(parts[3], parts[4])
        if ok:
            await set_user_field(ctx.bot, uid, parts[3], v)
            await update.callback_query.answer("✅ Изменено")
        back = parts[5] if len(parts) > 5 else ""
    elif sub == "uspm" and len(parts) > 3 and parts[3].isdigit():
        pm = list((u["prayer_modes"] or "sssss").ljust(5, "s"))
        i = int(parts[3]) % 5
        pm[i] = {"s": "q", "q": "o", "o": "s"}[pm[i]]
        await save(uid, prayer_modes="".join(pm))
        back = parts[4] if len(parts) > 4 else ""
    elif sub == "usc":
        back = parts[3] if len(parts) > 3 else ""
        ctx.user_data["admin_state"] = f"us_city:{uid}:{back}"
        return await render(update, f"📍 Отправьте город для {esc(await admin_name(uid))}, например <code>Самарканд</code>.",
                            kb([btn("⬅️ Назад", f"a:us:{uid}:{back}")]))
    else:
        back = parts[3] if len(parts) > 3 else ""
    text, markup = await screen_user_settings(uid, back)
    return await render(update, text, markup)


async def admin_user_city(update, ctx, state):
    msg = update.message
    _, uid, back = (state.split(":") + [""])[:3]
    uid = int(uid)
    ctx.user_data.pop("admin_state", None)
    u = await get_user(uid)
    if not u:
        return True
    place = await geocode((msg.text or "").strip()[:80], u["lang"] or "ru")
    if not place:
        await msg.reply_text("🤷 Город не найден. Попробуйте написать иначе.", reply_markup=kb([btn("📍 Ещё раз", f"a:usc:{uid}:{back}")]))
        return True
    name, lat, lon, cc = place
    pu = dict(u, lat=lat, lon=lon, country=cc, tz=None)
    try:
        data = await get_timings(pu, datetime.utcnow().date())
    except Exception:  # noqa: BLE001
        await msg.reply_text("⚠️ Не получилось получить время для этого места. Попробуйте позже.")
        return True
    await save(uid, city=name, lat=lat, lon=lon, country=cc, tz=data["tz"], awaiting_city=False)
    text, markup = await screen_user_settings(uid, back)
    await msg.reply_text(f"✅ Город: {esc(name)}\n\n" + text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return True


# ── invite card: video or photo (the main admin picks the default, may upload their own) ──

def invite_cfg():
    inv = BOT_CFG.setdefault("invite", {})
    inv.setdefault("mode", "video")
    inv.setdefault("custom", {})  # "all" or a language -> {"type": "photo"|"video"|"animation", "file_id": ...}
    return inv


def invite_custom(lang):
    c = invite_cfg()["custom"]
    return c.get(lang) or c.get("all")


def card_lang(lang):
    return lang if lang in SHARE_CARD_LANGS else "en"


def card_url(lang, kind):
    return f"{WEBAPP_URL}/card/{card_lang(lang)}.{'mp4' if kind == 'video' else 'jpg'}"


async def page_card(request):
    name = request.match_info["name"]
    m = re.match(r"^(en|ru|uz|uzc|tg|ar)\.(mp4|jpg)$", name)
    if not m:
        raise web.HTTPNotFound()
    path = SHARE_CARD_DIR / f"mawaqit_card_{name}"
    if not path.exists():
        raise web.HTTPNotFound()
    return web.FileResponse(path, headers={"Cache-Control": "public, max-age=86400"})


async def api_invite(request):
    tg_user, u, lang = await api_auth(request)
    lang = (u or {}).get("lang") or lang
    inv = invite_cfg()
    custom = invite_custom(lang)
    return web.json_response({"ok": feat("share"), "mode": inv["mode"], "custom": bool(custom),
                              "custom_type": custom["type"] if custom else None,
                              "video": card_url(lang, "video"), "photo": card_url(lang, "photo"),
                              "caption": t(card_lang(lang), "fr_cap", bot=f"@{BOT_USERNAME}")})


async def api_invite_prepare(request):
    """A ready message for Telegram's share window: the card (video or photo) with the hadith caption."""
    tg_user, u, lang = await api_auth(request)
    if not feat("share"):
        raise web.HTTPForbidden(text="off")
    lang = card_lang((u or {}).get("lang") or lang)
    body = await read_json(request)
    kind = "photo" if body.get("kind") == "photo" else "video"
    cap = t(lang, "fr_cap", bot=f"@{BOT_USERNAME}")
    custom = invite_custom(lang)
    rid = f"inv_{lang}_{kind}_{int(_time.time())}"
    if custom:
        typ, fid = custom["type"], custom["file_id"]
        res = (InlineQueryResultCachedPhoto(id=rid, photo_file_id=fid, caption=cap) if typ == "photo" else
               InlineQueryResultCachedVideo(id=rid, video_file_id=fid, title="Mawaqit", caption=cap) if typ == "video" else
               InlineQueryResultCachedMpeg4Gif(id=rid, mpeg4_file_id=fid, caption=cap))
    elif kind == "photo":
        res = InlineQueryResultPhoto(id=rid, photo_url=card_url(lang, "photo"), thumbnail_url=card_url(lang, "photo"), caption=cap,
                                     photo_width=1020, photo_height=1770)
    else:
        fid = await kv_get("share_card_" + lang)
        res = InlineQueryResultCachedMpeg4Gif(id=rid, mpeg4_file_id=fid, caption=cap) if fid else \
            InlineQueryResultMpeg4Gif(id=rid, mpeg4_url=card_url(lang, "video"), thumbnail_url=card_url(lang, "photo"),
                                      caption=cap, mpeg4_width=1020, mpeg4_height=1770, mpeg4_duration=7, thumbnail_mime_type="image/jpeg")
    try:
        pm = await request.app["bot"].save_prepared_inline_message(u["user_id"], res, allow_user_chats=True, allow_bot_chats=True,
                                                                   allow_group_chats=True, allow_channel_chats=True)
    except Exception:  # noqa: BLE001
        log.exception("invite prepare failed")
        return web.json_response({"ok": False}, status=502)
    await bump("share_card")
    return web.json_response({"ok": True, "id": pm.id})


async def api_invite_send(request):
    """Old Telegram (no share window): the bot sends the card to the person's chat."""
    tg_user, u, lang = await api_auth(request)
    body = await read_json(request)
    await send_share_card(request.app["bot"], u, "photo" if body.get("kind") == "photo" else "video")
    return web.json_response({"ok": True})


async def send_share_card(bot, u, kind=None):
    lang = (u or {}).get("lang") or "en"
    cl = card_lang(lang)
    kind = kind or invite_cfg()["mode"]
    cap = t(cl, "fr_cap", bot=f"@{BOT_USERNAME}")
    chat = u["user_id"]
    custom = invite_custom(cl)
    other = "photo" if kind == "video" else "video"
    markup = kb([btn(t(lang, "fr_how"), "fr:how")],
                *([[btn(t(lang, "fr_as_" + other), "fr:as:" + other)]] if not custom else []))
    if custom:
        send = {"photo": bot.send_photo, "video": bot.send_video}.get(custom["type"], bot.send_animation)
        return await send(chat, custom["file_id"], caption=cap, reply_markup=markup)
    key = ("share_card_" if kind == "video" else "share_photo_") + cl
    fid = await kv_get(key)
    send = bot.send_animation if kind == "video" else bot.send_photo
    if fid:
        try:
            return await send(chat, fid, caption=cap, reply_markup=markup)
        except BadRequest:
            log.warning("share card file id expired for %s", key)
    path = SHARE_CARD_DIR / f"mawaqit_card_{cl}.{'mp4' if kind == 'video' else 'jpg'}"
    with open(path, "rb") as f:
        if kind == "video":
            msg = await bot.send_animation(chat, f, caption=cap, reply_markup=markup, width=1020, height=1770, duration=7,
                                           filename=f"mawaqit_{cl}.mp4")
            new = msg.animation.file_id if msg.animation else None
        else:
            msg = await bot.send_photo(chat, f, caption=cap, reply_markup=markup)
            new = msg.photo[-1].file_id if msg.photo else None
    if new:
        await kv_set(key, new)
    await bump("share_card")
    return msg


# ── the "⚙️ Bot" tab of the mini app admin (main admin only) ──

def _opts_for(f):
    label, opts, show = USER_FIELDS[f]
    return {"label": label, "options": [[enc(o), show(o)] for o in opts]}


async def api_admin_botcfg(request):
    uid = await admin_auth(request)
    if not is_main(uid):
        raise web.HTTPForbidden(text="main admin only")
    c = BOT_CFG
    note = ""
    if request.method == "POST":
        b = await read_json(request)
        for k in ("maint", "closed"):
            if isinstance(b.get(k), bool):
                c[k] = b[k]
        if isinstance(b.get("feat"), dict):
            for k, v in b["feat"].items():
                if k in dict(FEATURES) and isinstance(v, bool):
                    c["feat"][k] = v
                    if k == "ai":
                        await save_ai_cfg(enabled=v)
        if isinstance(b.get("menu"), list):
            rows = [[k for k in row if k in MENU_ITEMS] for row in b["menu"] if isinstance(row, list)]
            rows = [r[:3] for r in rows if r]
            if sorted(k for r in rows for k in r) == sorted(MENU_ITEMS):
                c["menu"] = rows
        if isinstance(b.get("hide"), list):
            c["hide"] = sorted({k for k in b["hide"] if k in MENU_ITEMS and k != "settings"})
        if b.get("menu_reset"):
            c["menu"], c["hide"] = json.loads(json.dumps(MENU_DEFAULT)), []
        if isinstance(b.get("texts"), dict):
            for k, v in b["texts"].items():
                if k in TEXT_KEYS and isinstance(v, str):
                    if k == "sub_text":
                        c.setdefault("sub", {})["text"] = v.strip()[:1000]
                    else:
                        c[k] = v.strip()[:3000]
        if isinstance(b.get("profile"), dict):
            for pl, d in b["profile"].items():
                if pl in PROFILE_LANGS and isinstance(d, dict):
                    p = c.setdefault("profile", {}).setdefault(pl, {})
                    if isinstance(d.get("desc"), str):
                        p["desc"] = d["desc"].strip()[:512]
                    if isinstance(d.get("about"), str):
                        p["about"] = d["about"].strip()[:120]
                    await apply_profile_texts(request.app["bot"], only=pl)
        if isinstance(b.get("sub"), dict):
            sub = c.setdefault("sub", {"on": False, "channel": "", "text": ""})
            if isinstance(b["sub"].get("channel"), str):
                ch = b["sub"]["channel"].strip().split("/")[-1].lstrip("@")
                sub["channel"] = ("@" + ch) if re.match(r"^[A-Za-z0-9_]{4,}$", ch) else ""
                sub["on"] = False
            if b["sub"].get("on") is True:
                try:
                    me = await request.app["bot"].get_chat_member(sub["channel"], request.app["bot"].id)
                    if me.status in ("administrator", "creator"):
                        sub["on"] = True
                    else:
                        note = "Сделайте бота админом канала — иначе он не видит подписчиков."
                except Exception:  # noqa: BLE001
                    note = "Бот не видит канал. Укажите канал и добавьте бота туда админом."
            elif b["sub"].get("on") is False:
                sub["on"] = False
        if isinstance(b.get("defaults"), dict):
            d = c.setdefault("defaults", {})
            for f, raw in b["defaults"].items():
                if f == "pm" and isinstance(raw, str) and re.match(r"^[sqo]{5}$", raw):
                    d["pm"] = raw
                elif f in DEFAULT_FIELDS:
                    if raw is None:
                        d.pop(f, None)
                    else:
                        v, ok = dec(f, str(raw))
                        if ok:
                            d[f] = v
        if b.get("apply_all") in list(DEFAULT_FIELDS) + ["pm"] and b["apply_all"] in c.get("defaults", {}):
            f, v = b["apply_all"], c["defaults"][b["apply_all"]]
            if f == "quiet":
                qa, qb = (None, None) if v == "off" else (int(x) for x in v.split("-"))
                res = await POOL.execute("UPDATE users SET quiet_start = $1, quiet_end = $2 WHERE chat_type = 'private'", qa, qb)
            else:
                res = await POOL.execute(f"UPDATE users SET {'prayer_modes' if f == 'pm' else f} = $1 WHERE chat_type = 'private'", v)
            note = f"Применено к {res.split()[-1]} пользователям."
        if isinstance(b.get("invite"), dict):
            inv = invite_cfg()
            if b["invite"].get("mode") in ("video", "photo"):
                inv["mode"] = b["invite"]["mode"]
            if b["invite"].get("clear_custom"):
                inv["custom"] = {}
        if b.get("backup"):
            async def _send_backup():
                data, n = await build_backup()
                await request.app["bot"].send_document(uid, document=data, filename=f"mawaqit_backup_{datetime.utcnow():%Y%m%d_%H%M}.zip",
                                                       caption=f"💾 Резервная копия: {n} таблиц")
            asyncio.get_running_loop().create_task(_send_backup())
            note = "Резервная копия придёт в чат с ботом."
        if b.get("restart"):
            log.warning("restart requested from the mini app")
            asyncio.get_running_loop().call_later(1.5, os._exit, 1)
            note = "Перезапуск… Через минуту откройте приложение заново."
        await save_bot_cfg()
    up = int(_time.time() - START_TS)
    return web.json_response({
        "ok": True, "note": note, "cfg": c, "features": [[k, n] for k, n in FEATURES], "menu_items": MENU_ITEMS,
        "texts": {k: v[0] for k, v in TEXT_KEYS.items()}, "profile_langs": PROFILE_LANGS,
        "defaults": {f: _opts_for(f) for f in DEFAULT_FIELDS}, "pm_names": [PN["ru"][k.lower()] for k in EVENTS],
        "invite": invite_cfg(),
        "sys": {"uptime": up, "db": await POOL.fetchval("SELECT pg_size_pretty(pg_database_size(current_database()))"),
                "errors": [[e[0].strftime("%d.%m %H:%M"), e[1]] for e in list(ERRBUF)]}})


# ── mini app: broadcast v2 (the draft is sent to the admin's own chat first, then copied to everyone) ──

BC_DRAFTS = {}  # admin_id -> {"src": [chat, msg], "opts": {...}}


async def bc_from_body2(body, admin):
    kind = body.get("kind")
    value = body.get("value")
    if kind == "lang":
        value = value if value in LANGS else "ru"
    elif kind == "country":
        value = str(value or "").strip().lower()[:2]
        if len(value) != 2 or not value.isalpha():
            raise web.HTTPBadRequest(text="bad country")
    elif kind == "city":
        value = str(value or "").strip()[:60]
        if not value:
            raise web.HTTPBadRequest(text="bad city")
    elif kind in BC_DAYS:
        try:
            value = max(1, min(365, int(value)))
        except (TypeError, ValueError):
            value = 30
    elif kind == "picked":
        value = await bc_picks(admin)
    elif kind not in ("all", "everything", "chats", "remind"):
        kind, value = "all", None
    return {"kind": kind, "value": value}


def b64_file(raw, limit):
    import base64
    try:
        data = base64.b64decode(str(raw).split(",", 1)[-1], validate=True)
    except Exception:  # noqa: BLE001
        raise web.HTTPBadRequest(text="bad file")
    if len(data) > limit:
        raise web.HTTPBadRequest(text="file too big")
    return data


async def bc2_status(admin):
    hist = await POOL.fetch("SELECT * FROM broadcasts ORDER BY id DESC LIMIT 12")
    fresh = datetime.now(ZoneInfo("UTC")) - timedelta(hours=48)
    me = await get_user(admin)
    tz = (me or {}).get("tz") or "Asia/Tashkent"
    picks = await bc_picks(admin)
    return {"tz": tz, "picks": [{"id": x, "name": await admin_name(x)} for x in picks[:50]],
            "items": [{"id": r["id"], "status": r["status"], "label": r["label"], "total": r["total"], "sent": r["sent"] or 0,
                       "failed": r["failed"] or 0, "blocked": r["blocked"] or 0,
                       "when": (r["finished_at"] or r["run_at"] or r["created_at"]).isoformat(),
                       "run_at": r["run_at"].isoformat() if r["run_at"] else None,
                       "can_delete": r["status"] in ("done", "stopped") and bool(r["sent"]) and bool(r["finished_at"])
                       and r["finished_at"] > fresh} for r in hist]}


async def api_admin_bc2(request):
    admin = await admin_auth(request, "bc")
    bot = request.app["bot"]
    ptb = request.app["ptb"]
    if request.method == "GET":
        if request.query.get("count"):
            bc = await bc_from_body2(dict(request.query), admin)
            return web.json_response({"ok": True, "count": await bc_count(bc), "label": bc_label(bc)})
        return web.json_response({"ok": True, **await bc2_status(admin)})
    b = await read_json(request)
    act = b.get("action")
    if act == "draft":  # make the message in the admin's chat: that's the preview and the source
        text = admin_markup_text(str(b.get("text") or "").strip()[:4000])
        opts = {"buttons": [], "app": bool(b.get("app")), "times": bool(b.get("times")), "silent": bool(b.get("silent")),
                "pin": bool(b.get("pin"))}
        for row in (b.get("buttons") or [])[:6]:
            if isinstance(row, list) and len(row) == 2 and str(row[0]).strip() and re.match(r"^(https?://|tg://)\S+$", str(row[1]).strip()):
                opts["buttons"].append([str(row[0]).strip()[:60], str(row[1]).strip()[:500]])
        media = None
        if b.get("photo"):
            media = ("photo", b64_file(b["photo"], 9 * 1024 * 1024))
        elif b.get("video"):
            media = ("video", b64_file(b["video"], 19 * 1024 * 1024))
        if not text and not media:
            raise web.HTTPBadRequest(text="empty")
        if media and len(text) > 1024:
            raise web.HTTPBadRequest(text="caption too long")
        markup = bc_markup(opts, "ru")
        try:
            await bot.send_message(admin, "👁 <b>Превью рассылки</b> — так увидят люди 👇", parse_mode=ParseMode.HTML)
            if media and media[0] == "photo":
                m = await bot.send_photo(admin, media[1], caption=text or None, parse_mode=ParseMode.HTML, reply_markup=markup)
            elif media:
                m = await bot.send_video(admin, media[1], caption=text or None, parse_mode=ParseMode.HTML, reply_markup=markup,
                                         supports_streaming=True)
            else:
                m = await bot.send_message(admin, text, parse_mode=ParseMode.HTML, reply_markup=markup, disable_web_page_preview=False)
        except BadRequest as e:
            return web.json_response({"ok": False, "error": str(e)}, status=400)
        BC_DRAFTS[admin] = {"src": [admin, m.message_id], "opts": opts}
        return web.json_response({"ok": True})
    if act in ("go", "schedule"):
        d = BC_DRAFTS.get(admin)
        if not d:
            return web.json_response({"ok": False, "error": "no_draft"}, status=400)
        bc = await bc_from_body2(b, admin)
        bc.update(src=d["src"], opts=d["opts"])
        if act == "go":
            if ptb.bot_data.get("bc_running"):
                return web.json_response({"ok": False, "error": "running"}, status=409)
            bc_id = await bc_save(admin, bc, "queued")
            bc_start(ptb, bc_id)
        else:
            me = await get_user(admin)
            tz = (me or {}).get("tz") or "Asia/Tashkent"
            try:
                when = datetime.fromisoformat(str(b.get("when"))).replace(tzinfo=ZoneInfo(tz))
            except ValueError:
                raise web.HTTPBadRequest(text="bad time")
            if when <= datetime.now(ZoneInfo(tz)):
                return web.json_response({"ok": False, "error": "past"}, status=400)
            bc_id = await bc_save(admin, bc, "scheduled", when)
        BC_DRAFTS.pop(admin, None)
        return web.json_response({"ok": True, "id": bc_id, **await bc2_status(admin)})
    bc_id = int(b.get("id") or 0)
    if act == "stop":
        ptb.bot_data["bc_stop"] = bc_id
    elif act == "cancel":
        await POOL.execute("UPDATE broadcasts SET status = 'cancelled' WHERE id = $1 AND status = 'scheduled'", bc_id)
    elif act == "delete":
        task = asyncio.create_task(run_bc_delete(ptb, bc_id, admin))
        ptb.bot_data.setdefault("tasks", set()).add(task)
    elif act == "picks_add":
        picks = await bc_picks(admin)
        for tok in re.split(r"[\s,;]+", str(b.get("text") or "")):
            who = await find_user_id(tok) if tok else None
            if who and who not in picks and await get_user(who):
                picks.append(who)
        await kv_set(f"bcpick:{admin}", json.dumps(picks))
    elif act == "picks_clear":
        await kv_set(f"bcpick:{admin}", "[]")
    elif act == "pick_toggle":
        uid = int(b.get("uid") or 0)
        picks = await bc_picks(admin)
        picks = [x for x in picks if x != uid] if uid in picks else picks + [uid]
        await kv_set(f"bcpick:{admin}", json.dumps(picks))
    return web.json_response({"ok": True, **await bc2_status(admin)})


# ── mini app: one person's settings, their messages from the bot, deleting them ──

async def person_tools_json(uid, viewer):
    u = await get_user(uid)
    private = u["chat_type"] == "private"
    fields = PRIVATE_FIELDS if private else CHAT_FIELDS
    msgs = await POOL.fetch("SELECT * FROM sent_msgs WHERE user_id = $1 AND NOT deleted AND at > now() - interval '7 days' "
                            "ORDER BY id DESC LIMIT 10", uid)
    fresh = datetime.now(ZoneInfo("UTC")) - timedelta(hours=48)
    return {"fields": [{"key": f, "label": USER_FIELDS[f][0], "value": enc(field_value(u, f)),
                        "options": [[enc(o), USER_FIELDS[f][2](o)] for o in USER_FIELDS[f][1]]} for f in fields],
            "pm": (u["prayer_modes"] or "sssss").ljust(5, "s"), "pm_names": [PN["ru"][k.lower()] for k in EVENTS],
            "city": u["city"], "picked": uid in await bc_picks(viewer),
            "msgs": [{"id": r["id"], "at": r["at"].isoformat(), "preview": r["preview"] or r["kind"], "fresh": r["at"] > fresh} for r in msgs],
            "can": {"users": has_perm(viewer, "users"), "bc": has_perm(viewer, "bc"), "bans": has_perm(viewer, "bans") and not is_admin(uid)}}


async def api_admin_person_tools(request):
    viewer = await admin_auth(request)
    bot = request.app["bot"]
    if request.method == "GET":
        uid = int(request.query.get("id") or 0)
    else:
        b = await read_json(request)
        uid = int(b.get("id") or 0)
    u = await get_user(uid) if uid else None
    if not u or (u["hidden"] and not is_main(viewer)):
        raise web.HTTPNotFound()
    note = ""
    if request.method == "POST":
        act = b.get("action")
        need = {"set": "users", "pm": "users", "city": "users", "delmsg": "users", "delmsg_all": "users", "pick": "bc",
                "delete": "bans"}.get(act)
        if not need or not has_perm(viewer, need):
            raise web.HTTPForbidden(text="no right")
        if act == "set" and b.get("field") in USER_FIELDS:
            v, ok = dec(b["field"], str(b.get("value")))
            if ok:
                await set_user_field(bot, uid, b["field"], v)
        elif act == "pm":
            pm = list((u["prayer_modes"] or "sssss").ljust(5, "s"))
            i = int(b.get("i") or 0) % 5
            pm[i] = {"s": "q", "q": "o", "o": "s"}[pm[i]]
            await save(uid, prayer_modes="".join(pm))
        elif act == "city":
            place = await geocode(str(b.get("city") or "").strip()[:80], u["lang"] or "ru")
            if not place:
                return web.json_response({"ok": False, "error": "not_found"})
            name, lat, lon, cc = place
            data = await get_timings(dict(u, lat=lat, lon=lon, country=cc, tz=None), datetime.utcnow().date())
            await save(uid, city=name, lat=lat, lon=lon, country=cc, tz=data["tz"], awaiting_city=False)
            note = f"Город: {name}"
        elif act in ("delmsg", "delmsg_all"):
            if act == "delmsg":
                rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE id = $1 AND user_id = $2", int(b.get("msg") or 0), uid)
            else:
                rows = await POOL.fetch("SELECT id, user_id, message_id FROM sent_msgs WHERE user_id = $1 AND NOT deleted "
                                        "AND at > now() - interval '48 hours'", uid)
            ok, gone = await delete_sent(bot, rows)
            note = f"Удалено: {ok}" + (f", не удалось: {gone}" if gone else "")
        elif act == "pick":
            picks = await bc_picks(viewer)
            picks = [x for x in picks if x != uid] if uid in picks else picks + [uid]
            await kv_set(f"bcpick:{viewer}", json.dumps(picks))
        elif act == "delete":
            if is_admin(uid):
                raise web.HTTPBadRequest(text="admin")
            await wipe_user(bot, uid, bool(b.get("ban")))
            return web.json_response({"ok": True, "deleted": True})
    return web.json_response({"ok": True, "note": note, **await person_tools_json(uid, viewer)})


# ───────────────────────── app ─────────────────────────


# Bot profile texts per language (set automatically on startup). Telegram shows each user
# the version for their app language; "en" is also used as the default for everyone else.
BOT_ABOUT = {
    "en": "🕌 Prayer times, reminders, Qibla and a prayer tracker — for any city in the world 🤍",
    "ru": "🕌 Время намаза, напоминания, кибла и трекер — для любого города мира 🤍",
    "uz": "🕌 Namoz vaqtlari, eslatmalar, qibla va namoz kundaligi — dunyoning istalgan shahri uchun 🤍",
    "tg": "🕌 Вақти намоз, ёдовариҳо, қибла ва рӯйхати намозҳо — барои ҳар шаҳри ҷаҳон 🤍",
    "ar": "🕌 مواقيت الصلاة والتذكيرات والقبلة ومتابعة الصلوات — لأي مدينة في العالم 🤍",
}
_LANG_LINE = "🌐 English · Русский · Oʻzbekcha · Тоҷикӣ · العربية"
BOT_DESCRIPTION = {
    "en": ("🕌 Mawaqit — prayer times by your side\n\n"
           "Accurate prayer times for any city in the world and gentle reminders so you never miss a prayer 🤍\n\n"
           "🔔 Reminders ahead of time and at the adhan\n🧭 Qibla with a live compass\n📿 Tasbih, adhkar and the 99 Names of Allah\n"
           "✅ Prayer tracker and challenges with friends\n🌙 Suhoor & Iftar in Ramadan\n👥 Works in groups and channels\n\n"
           + _LANG_LINE + "\n\nTap «Start» — and may every prayer be on time 🤲"),
    "ru": ("🕌 Mawaqit — время намаза рядом с тобой\n\n"
           "Точное время намаза для любого города мира и бережные напоминания, чтобы не пропустить ни одной молитвы 🤍\n\n"
           "🔔 Напоминание заранее и в момент азана\n🧭 Кибла с живым компасом\n📿 Тасбих, азкары и 99 имён Аллаха\n"
           "✅ Трекер намазов и вызовы с друзьями\n🌙 Сухур и ифтар в Рамадан\n👥 Работает в группах и каналах\n\n"
           + _LANG_LINE + "\n\nНажми «Старт» — и пусть каждая молитва будет вовремя 🤲"),
    "uz": ("🕌 Mawaqit — namoz vaqti doim yoningizda\n\n"
           "Dunyoning istalgan shahri uchun aniq namoz vaqtlari va birorta namozni qoldirmaslik uchun e'tiborli eslatmalar 🤍\n\n"
           "🔔 Oldindan va azon vaqtida eslatma\n🧭 Jonli kompasli qibla\n📿 Tasbeh, zikrlar va Allohning 99 ismi\n"
           "✅ Namoz kundaligi va do'stlar bilan musobaqalar\n🌙 Ramazonda saharlik va iftor\n👥 Guruh va kanallarda ishlaydi\n\n"
           + _LANG_LINE + "\n\n«Start»ni bosing — har bir namoz o'z vaqtida bo'lsin 🤲"),
    "tg": ("🕌 Mawaqit — вақти намоз ҳамеша бо шумо\n\n"
           "Вақти дақиқи намоз барои ҳар шаҳри ҷаҳон ва ёдовариҳои ғамхорона, то ягон намозро аз даст надиҳед 🤍\n\n"
           "🔔 Ёдоварӣ пешакӣ ва дар вақти азон\n🧭 Қибла бо компаси зинда\n📿 Тасбеҳ, зикрҳо ва 99 номи Аллоҳ\n"
           "✅ Рӯйхати намозҳо ва мусобиқа бо дӯстон\n🌙 Саҳарӣ ва ифтор дар Рамазон\n👥 Дар гурӯҳҳо ва каналҳо кор мекунад\n\n"
           + _LANG_LINE + "\n\n«Start»-ро пахш кунед — бигзор ҳар намоз сари вақт бошад 🤲"),
    "ar": ("🕌 مواقيت — وقت الصلاة معك دائماً\n\n"
           "مواقيت صلاة دقيقة لأي مدينة في العالم وتذكيرات لطيفة حتى لا تفوتك أي صلاة 🤍\n\n"
           "🔔 تذكير مسبق وعند الأذان\n🧭 القبلة مع بوصلة حيّة\n📿 التسبيح والأذكار وأسماء الله الحسنى\n"
           "✅ متابعة الصلوات وتحديات مع الأصدقاء\n🌙 السحور والإفطار في رمضان\n👥 يعمل في المجموعات والقنوات\n\n"
           + _LANG_LINE + "\n\nاضغط «ابدأ» — ولتكن كل صلاة في وقتها 🤲"),
}
BOT_COMMAND = {"en": "🕌 Menu", "ru": "🕌 Меню", "uz": "🕌 Menyu", "tg": "🕌 Меню", "ar": "🕌 القائمة"}


async def setup_profile(bot):
    """Name-independent profile texts in every language. Safe to run on every start."""
    try:  # first: the button next to the message field opens the app
        if WEBAPP_URL:
            await bot.set_chat_menu_button(menu_button=MenuButtonWebApp("🕌 App", WebAppInfo(url=WEBAPP_URL)))
        else:
            await bot.set_chat_menu_button(menu_button=MenuButtonCommands())
    except Exception:  # noqa: BLE001
        log.exception("could not set menu button")
    log.info("menu button: %s", "mini app" if WEBAPP_URL else "commands")
    for lang in LANGS:
        if lang not in BOT_ABOUT:  # Telegram has one "uz": the profile stays in Latin
            continue
        for code in ([None, lang] if lang == "en" else [lang]):
            try:
                # The bot's profile description is English for everyone: other languages get an empty one,
                # so Telegram shows the default (English) text.
                custom = BOT_CFG.get("profile", {}).get(lang) or {}
                await bot.set_my_short_description(custom.get("about") or (BOT_ABOUT["en"] if lang == "en" else ""),
                                                   language_code=code)
                await bot.set_my_description(custom.get("desc") or (BOT_DESCRIPTION["en"] if lang == "en" else ""),
                                             language_code=code)
                await bot.set_my_commands([BotCommand("start", BOT_COMMAND[lang])], language_code=code)
            except RetryAfter as e:
                log.warning("profile texts rate-limited, retry in %ss", e.retry_after)
                return
            except Exception:  # noqa: BLE001
                log.exception("could not set profile texts for %s", code or "default")


async def post_init(app: Application):
    global POOL, HTTP
    POOL = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5)
    async with POOL.acquire() as conn:
        await conn.execute(SCHEMA)
    HTTP = httpx.AsyncClient(timeout=15)
    await load_azans()
    await load_admins()
    await load_ai()
    await load_bot_cfg()
    await load_ayah_pool()
    await POOL.execute("UPDATE broadcasts SET status = 'failed', finished_at = now() WHERE status IN ('running', 'queued')")
    if AI["key"]:  # check the key and pick the models in the background
        asyncio.get_running_loop().create_task(ai_models())
    global BOT_USERNAME
    BOT_USERNAME = app.bot.username
    asyncio.get_running_loop().create_task(setup_profile(app.bot))  # in background, never blocks startup
    try:
        await start_web(app)
    except Exception:  # noqa: BLE001
        log.exception("mini app server failed to start (the bot keeps working)")
    log.info("Bot is ready (arabic shaping: %s)", "raqm" if art.RAQM else "reshaper")


async def post_shutdown(app: Application):
    if WEB_RUNNER:
        await WEB_RUNNER.cleanup()
    if HTTP:
        await HTTP.aclose()
    if POOL:
        await POOL.close()


async def on_error(update, ctx: ContextTypes.DEFAULT_TYPE):
    log.error("Unhandled error", exc_info=ctx.error)


def main():
    app = (Application.builder().token(BOT_TOKEN).post_init(post_init).post_shutdown(post_shutdown)
           .concurrent_updates(16).build())
    app.add_handler(TypeHandler(Update, gate), group=-1)  # activity tracking + ban check
    # group 0: support conversation (any message type, private chats only)
    app.add_handler(MessageHandler(
        filters.ChatType.PRIVATE & ~filters.COMMAND & ~filters.UpdateType.EDITED_MESSAGE & ~filters.StatusUpdate.ALL,
        support_msg), group=0)
    # group 1: everything else
    app.add_handler(ChatMemberHandler(on_my_member, ChatMemberHandler.MY_CHAT_MEMBER), group=1)
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, on_migrate), group=1)
    app.add_handler(CommandHandler(["start", "menu"], cmd_start), group=1)
    app.add_handler(CommandHandler("admin", cmd_admin, filters=filters.ChatType.PRIVATE), group=1)
    app.add_handler(CallbackQueryHandler(on_button), group=1)
    app.add_handler(MessageHandler(filters.LOCATION & filters.ChatType.PRIVATE & ~filters.UpdateType.EDITED_MESSAGE,
                                   on_location), group=1)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.UpdateType.EDITED_MESSAGE,
                                   on_text), group=1)
    app.add_error_handler(on_error)
    app.job_queue.run_repeating(tick, interval=30, first=10)
    app.job_queue.run_repeating(refresh_cards, interval=60, first=40)
    app.job_queue.run_repeating(periodic, interval=600, first=90)
    app.job_queue.run_repeating(cleanup_job, interval=60, first=30)
    app.job_queue.run_repeating(menu_buttons_job, interval=120, first=120)
    app.job_queue.run_once(prefetch_ayahs, 60)
    app.job_queue.run_once(check_backup_ai, 30)
    app.job_queue.run_repeating(bc_scheduler, interval=30, first=45)
    app.add_handler(InlineQueryHandler(on_inline), group=1)
    app.add_handler(PreCheckoutQueryHandler(on_precheckout), group=1)
    app.add_handler(MessageHandler(filters.SUCCESSFUL_PAYMENT, on_paid), group=1)
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
