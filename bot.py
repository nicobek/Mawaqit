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
import time as _time
from collections import deque
from datetime import datetime, time as dtime, timedelta
from pathlib import Path
from urllib.parse import parse_qsl
from zoneinfo import ZoneInfo

import asyncpg
import httpx
from aiohttp import web
from telegram import (
    BotCommand,
    ForceReply,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InlineQueryResultArticle,
    InlineQueryResultsButton,
    InputTextMessageContent,
    KeyboardButton,
    MenuButtonCommands,
    MenuButtonWebApp,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
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

LANGS = ["en", "ru", "uz", "tg", "ar"]
LANG_BUTTONS = {
    "en": "🇬🇧 English",
    "ru": "🇷🇺 Русский",
    "uz": "🇺🇿 Oʻzbekcha",
    "tg": "🇹🇯 Тоҷикӣ",
    "ar": "🇸🇦 العربية",
}
LANG_PICK_TEXT = (
    "🌐 <b>Choose your language</b>\n"
    "Выберите язык · Tilni tanlang\n"
    "Забонро интихоб кунед · اختر لغتك"
)

EVENTS = ["Fajr", "Dhuhr", "Asr", "Maghrib", "Isha"]  # prayers that get reminders
ROWS = [("Fajr", "🌌"), ("Sunrise", "🌅"), ("Dhuhr", "☀️"), ("Asr", "🌤"), ("Maghrib", "🌇"), ("Isha", "🌙")]
LEAD_OPTIONS = [5, 10, 15, 30, 0]  # 0 = no early reminder
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
}
DEFAULT_METHOD = 3


def method_for(country):
    return METHOD_BY_COUNTRY.get((country or "").lower(), DEFAULT_METHOD)


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
    params = {"latitude": lat, "longitude": lon, "method": method, "school": school}
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
        return CACHE[key]
    async with SEM:
        if key in CACHE:
            return CACHE[key]
        data = await fetch_timings(u["lat"], u["lon"], d, method, school)
    CACHE[key] = data
    return data


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


async def geocode(query, lang):
    data = await nominatim("search", {"q": query, "limit": 1, "accept-language": lang})
    if not data:
        return None
    d = data[0]
    addr = d.get("address", {})
    name = place_name(addr) or d.get("display_name", query).split(",")[0]
    return name, float(d["lat"]), float(d["lon"]), addr.get("country_code", "")


async def reverse_geocode(lat, lon, lang):
    try:
        d = await nominatim("reverse", {"lat": lat, "lon": lon, "zoom": 10, "accept-language": lang})
        addr = d.get("address", {})
        return place_name(addr) or f"{lat:.2f}, {lon:.2f}", addr.get("country_code", "")
    except Exception:  # noqa: BLE001
        log.exception("reverse geocode failed")
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


async def render(update: Update, text, markup=None):
    """Edit the message in place for button presses, send a new one otherwise."""
    q = update.callback_query
    if q:
        try:
            await q.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
            return q.message
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return q.message
            log.warning("edit failed (%s), sending new message", e)
        return await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    return await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)


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
            [btn(LANG_BUTTONS["uz"], "lang:uz"), btn(LANG_BUTTONS["tg"], "lang:tg")],
            [btn(LANG_BUTTONS["ar"], "lang:ar")]]
    if back:
        rows.append([btn("⬅️", "s:settings")])
    return LANG_PICK_TEXT, kb(*rows)


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
    text, markup = screen_city(u)
    await remember_prompt(update, ctx, await render(update, text, markup))
    old_helper = ctx.user_data.pop("loc_msg", None)
    if old_helper:
        await drop_message(update, old_helper)
    helper = await update.effective_chat.send_message(
        t(lang, "loc_hint"),
        reply_markup=ReplyKeyboardMarkup(
            [[KeyboardButton(t(lang, "loc_btn"), request_location=True)]],
            resize_keyboard=True, one_time_keyboard=True),
    )
    ctx.user_data["loc_msg"] = helper.message_id


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
        [btn(t(lang, "btn_times"), "m:times")],
        [qibla_btn(u)],
        [btn(t(lang, "btn_rem_on" if u["remind"] else "btn_rem_off"), "m:toggle")],
        [btn(t(lang, "btn_settings"), "m:settings")],
    ]
    if kind(u) == "channel":
        rows.append([btn(t(lang, "btn_my_channels"), "ch:list"), btn(t(lang, "btn_my_menu"), "ch:exit")])
        return t(lang, "channel_menu_title", title=esc(u["title"] or "—"), city=esc(u["city"] or "—")), kb(*rows)
    if is_private(u):
        if WEBAPP_URL:
            rows.insert(0, [webapp_btn(t(lang, "btn_app"), "today")])
        rows.append([add_group_btn(lang), add_channel_btn(lang)])
        rows.append([btn(t(lang, "btn_my_channels"), "ch:list")])
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
             f"🔕 {quiet_label(lang, u['quiet_start'], u['quiet_end'])}"]
    rows = [
        [btn(t(lang, "btn_city"), "s:city")],
        [btn(t(lang, "btn_lang"), "s:lang"), btn(t(lang, "btn_madhab"), "s:madhab")],
        [btn(t(lang, "btn_lead"), "s:lead")],
        [btn(t(lang, "btn_at_on" if u["at_time"] else "btn_at_off"), "s:attime")],
        [btn(t(lang, "btn_auto", v=auto_label(lang, u["auto_mode"])), "s:auto")],
        [btn(t(lang, "btn_quiet"), "s:quiet")],
        [btn(t(lang, "btn_ram_on" if u["ramadan"] else "btn_ram_off"), "s:ramadan")],
    ]
    if not is_private(u):
        lines.append(f"📅 {daily_label(lang, u['daily'])}")
        rows.append([btn(t(lang, "btn_daily"), "s:daily")])
    else:
        rows.append([btn(t(lang, "btn_azr_on" if u["azkar_rem"] else "btn_azr_off"), "s:azr")])
        rows.append([btn(t(lang, "btn_wk_on" if u["weekly"] else "btn_wk_off"), "s:wk")])
        if ADMINS:
            rows.append([btn(t(lang, "btn_support"), "s:support")])
    rows.append([btn(t(lang, "btn_back"), "m:home")])
    return "\n".join(lines), kb(*rows)


def screen_lead(u):
    lang = u["lang"]
    opts = [btn(("✅ " if u["lead_min"] == n else "") + lead_label(lang, n), f"set:lead:{n}") for n in LEAD_OPTIONS]
    rows = [opts[i:i + 2] for i in range(0, len(opts), 2)]
    rows.append([btn(t(lang, "btn_back"), "s:settings")])
    return t(lang, "lead_title"), kb(*rows)


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
    if ram:
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


def card_markup(u):
    lang = u["lang"]
    return kb([qibla_btn(u), btn("🔄", "tc:refresh")], [btn(t(lang, "btn_menu"), "m:new")])


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
    m = await chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=card_markup(u))
    await remember_card(chat.id, m.message_id, u["user_id"], ctx.bot)


async def refresh_cards(context: ContextTypes.DEFAULT_TYPE):
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
                                                parse_mode=ParseMode.HTML, reply_markup=card_markup(u))
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
    await save(tid, city=name, lat=lat, lon=lon, country=cc, tz=data["tz"], awaiting_city=False)
    u = await get_user(tid)
    await cleanup_loc_kb(update, ctx)
    await cleanup_city_prompt(update, ctx)
    for mid in drop_ids:  # the user's own message with the city / location
        await drop_message(update, mid)
    onboarding = not u["onboarded"]
    if onboarding:
        shown = await render(update, await card_text(u), None)
        if shown is not None:
            await remember_card(update.effective_chat.id, shown.message_id, tid, ctx.bot)
        return await ask_remind(update, u)
    shown = await render(update, await card_text(u), card_markup(u))
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
    if chat.type == "private" and ctx.args and ctx.args[0].startswith("ch_"):
        await join_challenge(update, ctx, ctx.args[0][3:])
    u = await target_for(update, ctx)
    await resume(update, ctx, u)


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.message
    if chat.type == "private":
        if is_admin(update.effective_user.id) and ctx.user_data.get("admin_state"):
            if await admin_text(update, ctx):
                return
        u = await target_for(update, ctx)
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
    if chat.type == "private":
        ctx.user_data.pop("support_mode", None)
        ctx.user_data.pop("reply_to", None)
    if act == "ch":
        await q.answer()
        if chat.type == "private":
            return await channel_button(update, ctx, parts)
        return

    u = await target_for(update, ctx)
    public = act == "tc" or (act == "m" and len(parts) > 1 and parts[1] in ("home", "times", "qibla", "new"))
    if chat.type != "private" and not public and not await can_manage(update, ctx):
        return await q.answer(t(u["lang"] or "en", "only_admins"), show_alert=True)
    await q.answer()
    tid = u["user_id"]

    # language can always be picked
    if act == "lang" and len(parts) > 1 and parts[1] in LANGS:
        await save(tid, lang=parts[1])
        u = await get_user(tid)
        if u["onboarded"]:
            text, markup = screen_settings(u)
            return await render(update, text, markup)
        return await resume(update, ctx, u)

    if not u["lang"]:
        return await resume(update, ctx, u)
    lang = u["lang"]

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
        return await render(update, text, markup)

    # everything below needs a finished setup
    if not (u["madhab"] and u["city"] and u["tz"]):
        return await resume(update, ctx, u)

    if act == "tc":  # refresh this card now
        try:
            text = await card_text(u)
            await render(update, text, card_markup(u))
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
            return await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
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
        elif sub in ("azr", "wk") and is_private(u):
            col = "azkar_rem" if sub == "azr" else "weekly"
            await save(tid, **{col: not u[col]})
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
                                                    reply_markup=card_markup(await get_user(tid)))
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
        target = int(parts[2])
        ctx.user_data["reply_to"] = target
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
    if is_admin(uid) and ctx.user_data.get("reply_to"):
        await admin_reply(update, ctx)
        raise ApplicationHandlerStop
    if ctx.user_data.get("support_mode") and ADMINS:
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
        for admin in sorted(ADMINS):  # every admin gets it; any of them can reply
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


async def admin_reply(update: Update, ctx):
    msg = update.message
    target = ctx.user_data["reply_to"]
    tu = await get_user(target)
    tlang = (tu or {}).get("lang") or "en"
    mg = msg.media_group_id
    first = not mg or ctx.user_data.get("rep_last_mg") != mg
    ctx.user_data["rep_last_mg"] = mg
    try:
        if first:
            await ctx.bot.send_message(target, t(tlang, "support_reply_header"), parse_mode=ParseMode.HTML)
        await msg.copy(target)
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
        await msg.reply_text(f"✅ Доставлено пользователю <code>{target}</code>.\nМожно отправить ещё или завершить 👇",
                             parse_mode=ParseMode.HTML, reply_markup=kb([btn("✅ Готово", "sup:rdone")]))


# ───────────────────────── reminders ─────────────────────────

SENT = {}  # (chat_id, date, event) -> unix time


def in_quiet(hour, qs, qe):
    if qs is None or qe is None:
        return False
    return (qs <= hour < qe) if qs <= qe else (hour >= qs or hour < qe)


async def send_reminder(bot, u, text, markup=None):
    lang = u["lang"]
    if markup is None:
        markup = kb([btn(t(lang, "btn_menu"), "m:home")]) if is_private(u) else None
    for attempt in range(2):
        try:
            await bot.send_message(u["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=markup)
            await bump("reminders_sent")
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

    # morning adhkar after Fajr (before sunrise), evening adhkar after Asr
    if is_private(u) and u["azkar_rem"]:
        fh, fm = map(int, data["Fajr"].split(":"))
        sh, sm = map(int, data["Sunrise"].split(":"))
        ah, am = map(int, data["Asr"].split(":"))
        fajr = datetime.combine(d, dtime(fh, fm), tzinfo=tz)
        sunrise = datetime.combine(d, dtime(sh, sm), tzinfo=tz)
        plan = (("m", min(fajr + timedelta(minutes=15), sunrise - timedelta(minutes=10))),
                ("e", datetime.combine(d, dtime(ah, am), tzinfo=tz) + timedelta(minutes=15)))
        for mode, when in plan:
            sk = (u["user_id"], d.isoformat(), "az_" + mode)
            if due(now, when) and sk not in SENT:
                SENT[sk] = _time.time()
                if in_quiet(when.hour, u["quiet_start"], u["quiet_end"]):
                    continue
                rows = [[webapp_btn(t(lang, "btn_open_azkar"), f"more&sub=azkar&az={mode}")]] if WEBAPP_URL else []
                await send_reminder(bot, u, t(lang, "az_rem_" + mode), kb(*rows, [btn(t(lang, "btn_menu"), "m:home")]))

    if not u["remind"]:
        return
    ramadan = u["ramadan"] and data["hmonth"] == 9
    for key in EVENTS:
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
            await send_reminder(bot, u, text)


async def tick(context: ContextTypes.DEFAULT_TYPE):
    try:
        rows = await POOL.fetch(
            "SELECT * FROM users WHERE (remind OR daily <> 'off' OR (azkar_rem AND chat_type = 'private')) "
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
                "full_name = EXCLUDED.full_name, username = EXCLUDED.username RETURNING banned",
                user.id, user.full_name, user.username)
            await POOL.execute("INSERT INTO daily_active (day, user_id) VALUES (CURRENT_DATE, $1) ON CONFLICT DO NOTHING",
                               user.id)
        else:
            row = await POOL.fetchrow(
                "UPDATE users SET last_seen = now(), full_name = $2, username = $3 WHERE user_id = $1 RETURNING banned",
                user.id, user.full_name, user.username)
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


# ── screens ──

async def screen_admin_home():
    r = await POOL.fetchrow(
        "SELECT count(*) AS total, count(*) FILTER (WHERE remind AND NOT blocked AND NOT banned) AS rem "
        "FROM users WHERE chat_type = 'private'")
    text = (f"🛠 <b>Админка</b>\n\n"
            f"👥 Пользователей: <b>{r['total']}</b>\n"
            f"🔔 С напоминаниями: <b>{r['rem']}</b>\n\n"
            f"Выберите раздел 👇")
    markup = kb(
        [btn("📈 Статистика", "a:stats"), btn("🌍 География", "a:geo")],
        [btn("👥 Пользователи", "a:users:0"), btn("📢 Группы и каналы", "a:chats:0")],
        [btn("📣 Рассылка", "a:bc"), btn("🔎 Поиск", "a:user")],
        [btn("✉️ Тест напоминания", "a:test"), btn("🚫 Баны", "a:bans")],
        [btn("📤 Экспорт CSV", "a:export"), btn("🩺 Здоровье", "a:health")],
        [btn("🏠 В меню бота", "m:home")],
    )
    return text, markup


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


async def user_card(uid, back=None):
    r = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    if not r:
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
            rows.append([btn("✉️ Написать", f"sup:reply:{uid}"),
                         btn("✅ Разбанить", f"a:unban:{uid}:{back or ''}") if u["banned"]
                         else btn("🚫 Забанить", f"a:ban:{uid}:{back or ''}")])
        if u["username"]:
            rows.append([InlineKeyboardButton("💬 Открыть в Telegram", url=f"https://t.me/{u['username']}")])
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
    rows.append([btn("⬅️ Назад", back_cb(back))])
    return text, kb(*rows)


def search_where(query):
    q = query.strip()
    if q.lstrip("-").isdigit():
        return "user_id = $1", [int(q)]
    if q.startswith("@"):
        return "username ILIKE $1", [q[1:] + "%"]
    return "(full_name ILIKE $1 OR username ILIKE $1 OR city ILIKE $1 OR title ILIKE $1)", [f"%{q}%"]


async def screen_people(page, kind="users", query=None):
    """kind: users | search | chats"""
    if kind == "chats":
        where, args, title = "chat_type <> 'private'", [], "📢 <b>Группы и каналы</b>"
    elif kind == "search":
        w, args = search_where(query or "")
        where, title = w, f"🔎 <b>Поиск:</b> «{esc(query)}»"
    else:
        where, args, title = "chat_type = 'private'", [], "👥 <b>Пользователи</b>"
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


async def screen_admin_bans():
    rows = await POOL.fetch("SELECT user_id, city FROM users WHERE banned ORDER BY user_id LIMIT 20")
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

def bc_where(bc):
    base = "lang IS NOT NULL AND NOT banned AND NOT blocked"
    if bc["kind"] == "everything":
        return base, []
    base += " AND chat_type = 'private'"
    if bc["kind"] == "lang":
        return base + " AND lang = $1", [bc["value"]]
    if bc["kind"] == "country":
        return base + " AND lower(country) = $1", [bc["value"]]
    return base, []


def bc_label(bc):
    if bc["kind"] == "lang":
        return f"язык {LANG_BUTTONS.get(bc['value'], bc['value'])}"
    if bc["kind"] == "country":
        return f"страна {flag(bc['value'])} {bc['value'].upper()}"
    if bc["kind"] == "everything":
        return "пользователи + группы и каналы"
    return "все пользователи"


async def ask_bc_text(update, ctx):
    bc = ctx.user_data["bc"]
    where, args = bc_where(bc)
    n = await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)
    ctx.user_data["admin_state"] = "bc_text"
    text = (f"✍️ <b>Текст рассылки</b>\n\n"
            f"Кому: <b>{bc_label(bc)}</b> (получателей: <b>{n}</b>)\n\n"
            f"Отправьте сообщение. Можно использовать форматирование Telegram: жирный, курсив, ссылки.")
    await render(update, text, kb([btn("❌ Отмена", "a:home")]))


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


# ── router ──

async def admin_router(update: Update, ctx: ContextTypes.DEFAULT_TYPE, parts):
    ctx.user_data.pop("admin_state", None)
    sub = parts[1] if len(parts) > 1 else "home"
    uid = update.effective_user.id

    if sub == "home":
        ctx.user_data.pop("bc", None)
        text, markup = await screen_admin_home()
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
        text, markup = await screen_admin_bans()
        return await render(update, text, markup)

    if sub == "card" and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        back = parts[3] if len(parts) > 3 else None
        card = await user_card(int(parts[2]), back)
        if not card:
            return await update.effective_chat.send_message("🤷 Такого пользователя нет в базе.")
        if back:  # opened from a list: show in place
            return await render(update, card[0], card[1])
        return await update.effective_chat.send_message(card[0], parse_mode=ParseMode.HTML, reply_markup=card[1])

    if sub in ("users", "usearch", "chats"):
        page = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
        kind = {"users": "users", "usearch": "search", "chats": "chats"}[sub]
        text, markup = await screen_people(page, kind, ctx.user_data.get("user_q"))
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
        card = await user_card(target, parts[3] if len(parts) > 3 else None)
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
        rows = await POOL.fetch(f"SELECT {', '.join(CSV_COLUMNS)} FROM users ORDER BY created_at")
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

    if sub == "bc":
        what = parts[2] if len(parts) > 2 else "menu"
        if what == "menu":
            return await render(update, "📣 <b>Рассылка</b>\n\nКому отправить?", kb(
                [btn("👥 Всем пользователям", "a:bc:all")],
                [btn("👥📢 Пользователям + группам и каналам", "a:bc:everything")],
                [btn("🌐 По языку", "a:bc:lang")],
                [btn("🌍 По стране", "a:bc:country")],
                ADMIN_BACK))
        if what in ("all", "everything"):
            ctx.user_data["bc"] = {"kind": what, "value": None, "text": None}
            return await ask_bc_text(update, ctx)
        if what == "lang":
            rows = [[btn(LANG_BUTTONS["en"], "a:bcl:en"), btn(LANG_BUTTONS["ru"], "a:bcl:ru")],
                    [btn(LANG_BUTTONS["uz"], "a:bcl:uz"), btn(LANG_BUTTONS["tg"], "a:bcl:tg")],
                    [btn(LANG_BUTTONS["ar"], "a:bcl:ar")], [btn("⬅️ Назад", "a:bc")]]
            return await render(update, "🌐 <b>Выберите язык получателей</b>", kb(*rows))
        if what == "country":
            ctx.user_data["admin_state"] = "bc_country"
            return await render(update, "🌍 <b>Страна получателей</b>\n\nОтправьте двухбуквенный код страны, "
                                        "например: <code>uz</code>, <code>ru</code>, <code>tj</code>, <code>sa</code>.",
                                kb([btn("⬅️ Назад", "a:bc")]))
        if what == "go":
            bc = ctx.user_data.get("bc")
            if not bc or not bc.get("text"):
                return await render(update, "⚠️ Текст рассылки не найден. Начните заново.", kb(ADMIN_BACK))
            if ctx.application.bot_data.get("bc_running"):
                return await render(update, "⏳ Другая рассылка ещё идёт. Дождитесь её завершения.", kb(ADMIN_BACK))
            ctx.user_data.pop("bc", None)
            await render(update, "🚀 Рассылка запущена. Отчёт придёт, когда она завершится.", kb(ADMIN_BACK))
            task = asyncio.create_task(run_broadcast(ctx.application, update.effective_chat.id, bc["text"], bc))
            tasks = ctx.application.bot_data.setdefault("tasks", set())
            tasks.add(task)
            task.add_done_callback(tasks.discard)
            return

    if sub == "bcl" and len(parts) > 2 and parts[2] in LANGS:
        ctx.user_data["bc"] = {"kind": "lang", "value": parts[2], "text": None}
        return await ask_bc_text(update, ctx)

    text, markup = await screen_admin_home()
    await render(update, text, markup)


async def admin_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handles the admin's typed answers. Returns True if the message was consumed."""
    state = ctx.user_data.get("admin_state")
    msg = update.message

    if state == "search":
        raw = msg.text.strip()[:64]
        ctx.user_data.pop("admin_state", None)
        ctx.user_data["user_q"] = raw
        text, markup = await screen_people(0, "search", raw)
        await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        return True

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
    text, markup = await screen_admin_home()
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


async def fetch_month(u, y, m):
    method, school = method_for(u["country"]), (1 if u["madhab"] == "hanafi" else 0)
    key = (round(u["lat"], 2), round(u["lon"], 2), method, school, y, m)
    if key in MONTH_CACHE:
        return MONTH_CACHE[key]
    async with SEM:
        r = await HTTP.get(f"https://api.aladhan.com/v1/calendar/{y}/{m}",
                           params={"latitude": u["lat"], "longitude": u["lon"], "method": method, "school": school})
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


async def fetch_hijri_month(u, hy, hm):
    method, school = method_for(u["country"]), (1 if u["madhab"] == "hanafi" else 0)
    key = ("h", round(u["lat"], 2), round(u["lon"], 2), method, school, hy, hm)
    if key in MONTH_CACHE:
        return MONTH_CACHE[key]
    async with SEM:
        r = await HTTP.get(f"https://api.aladhan.com/v1/hijriCalendar/{hy}/{hm}",
                           params={"latitude": u["lat"], "longitude": u["lon"], "method": method, "school": school})
    r.raise_for_status()
    days = []
    for item in r.json()["data"]:
        g, h, tm = item["date"]["gregorian"], item["date"]["hijri"], item["timings"]
        days.append({"date": g["date"], "hday": int(h["day"]),
                     "t": {k: tm[k].split()[0] for k in TIMING_KEYS}})
    MONTH_CACHE[key] = days
    return days


def profile_json(u, lang):
    quiet = "off" if u["quiet_start"] is None else f"{u['quiet_start']}-{u['quiet_end']}"
    return {"lang": lang, "city": u["city"], "lat": u["lat"], "lon": u["lon"], "tz": u["tz"],
            "madhab": u["madhab"], "country": u["country"], "lead": u["lead_min"], "at_time": u["at_time"],
            "remind": u["remind"], "auto": u["auto_mode"], "ramadan": u["ramadan"], "quiet": quiet,
            "azkar_rem": u["azkar_rem"], "weekly": u["weekly"],
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
                     ("azkar_rem", "azkar_rem"), ("weekly", "weekly")):
        if isinstance(body.get(key), bool):
            fields[col] = body[key]
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
    app = web.Application(client_max_size=12 * 1024 * 1024)  # broadcast photos
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
                    web.get("/api/tracker", api_tracker), web.post("/api/tracker", api_tracker_set),
                    web.post("/api/tracker_bulk", api_tracker_bulk), web.get("/api/community", api_community),
                    web.get("/api/challenges", api_challenges), web.post("/api/challenges", api_challenge_new),
                    web.post("/api/challenges/leave", api_challenge_leave)])
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


def render_share(u, data, day_iso):
    """A 1080×1920 story picture with the day's prayer times."""
    from PIL import Image, ImageDraw
    lang = u["lang"] or "en"
    rtl = lang == "ar"
    W, H = 1080, 1920
    img = Image.new("RGB", (W, H), (12, 21, 38))
    d = ImageDraw.Draw(img)
    for y in range(H):  # soft vertical gradient
        k = y / H
        d.line([(0, y), (W, y)], fill=(int(12 + 14 * k), int(21 + 16 * k), int(38 + 26 * k)))
    gold, white, hint, card = (212, 175, 55), (238, 242, 248), (150, 164, 186), (24, 38, 64)

    def text(xy, s, font, fill, anchor="la"):
        if rtl and anchor[0] == "l":
            xy, anchor = (W - xy[0], xy[1]), "r" + anchor[1]
        kw = {"direction": "rtl"} if rtl and any("؀" <= ch <= "ۿ" for ch in s) else {}
        try:
            d.text(xy, s, font=font, fill=fill, anchor=anchor, **kw)
        except Exception:  # noqa: BLE001  (no RAQM: draw without direction)
            d.text(xy, s, font=font, fill=fill, anchor=anchor)

    # crescent
    d.ellipse([W // 2 - 70, 150, W // 2 + 70, 290], fill=gold)
    d.ellipse([W // 2 - 38, 132, W // 2 + 92, 262], fill=(13, 22, 40))
    text((W // 2, 360), t(lang, "times_title").replace("🕌 ", "").replace("<b>", "").replace("</b>", ""),
         _font(72, True), white, "mm")
    text((W // 2, 450), u["city"] or "", _font(44), gold, "mm")
    y0, m0, dd = (int(x) for x in day_iso.split("-"))
    hij = f"{data['hday']} {HM[lang][data['hmonth'] - 1]} {data['hyear']}"
    text((W // 2, 520), f"{dd:02d}.{m0:02d}.{y0} · {hij}", _font(36), hint, "mm")

    names = PN[lang]
    top = 620
    for i, key in enumerate(("Fajr", "Sunrise", "Dhuhr", "Asr", "Maghrib", "Isha")):
        y = top + i * 170
        d.rounded_rectangle([90, y, W - 90, y + 140], radius=36, fill=card)
        if key != "Sunrise":
            d.rounded_rectangle([90, y, 104, y + 140], radius=7, fill=gold)
        text((150, y + 70), names[key.lower()], _font(52, True), white, "lm")
        if rtl:
            d.text((150, y + 70), data[key], font=_font(60, True), fill=gold, anchor="lm")
        else:
            d.text((W - 150, y + 70), data[key], font=_font(60, True), fill=gold, anchor="rm")
    if BOT_USERNAME:
        d.text((W // 2, H - 120), f"@{BOT_USERNAME}", font=_font(40, True), fill=hint, anchor="mm")
    buf = io.BytesIO()
    img.save(buf, "PNG", optimize=True)
    return buf.getvalue()


async def share_png_for(u, day_iso):
    key = (u["user_id"], day_iso, u["lang"], u["city"], u["madhab"])
    if key in SHARE_CACHE:
        return SHARE_CACHE[key]
    y, m, dd = (int(x) for x in day_iso.split("-"))
    data = await get_timings(u, datetime(y, m, dd).date())
    png = await asyncio.get_running_loop().run_in_executor(None, render_share, u, data, day_iso)
    if len(SHARE_CACHE) > 200:
        SHARE_CACHE.clear()
    SHARE_CACHE[key] = png
    return png


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
    return web.Response(body=png, content_type="image/png", headers={"Cache-Control": "public, max-age=3600"})


async def api_share_send(request):
    """Send the picture to the user's chat with the bot, so they can keep or forward it."""
    tg_user, u, lang = await api_auth(request)
    if not u or not u["city"] or not u["tz"]:
        raise web.HTTPBadRequest(text="no city")
    day_iso = datetime.now(ZoneInfo(u["tz"])).date().isoformat()
    try:
        png = await share_png_for(u, day_iso)
        await request.app["bot"].send_photo(u["user_id"], png, caption=f"🕌 {esc(u['city'])} · @{BOT_USERNAME}",
                                            parse_mode=ParseMode.HTML)
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

OVERPASS = ("https://overpass-api.de/api/interpreter",
            "https://overpass.kumi.systems/api/interpreter",
            "https://overpass.private.coffee/api/interpreter")
MOSQUE_CACHE = {}


async def overpass(query):
    last = None
    for url in OVERPASS:  # the free servers are often busy, so try the mirrors in turn
        try:
            r = await HTTP.post(url, data={"data": query}, timeout=30,
                                headers={"User-Agent": f"PrayerTimesTelegramBot/1.0 ({CONTACT})"})
            r.raise_for_status()
            return r.json().get("elements", [])
        except Exception as e:  # noqa: BLE001
            last = e
            log.warning("overpass %s failed: %r", url, e)
    raise last or RuntimeError("overpass unavailable")


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
    items, radius = [], 5000
    try:
        for radius in (5000, 15000):  # widen the search if nothing is close
            q = (f'[out:json][timeout:25];nwr["amenity"="place_of_worship"]["religion"="muslim"]'
                 f'(around:{radius},{lat},{lon});out center 120;')
            items = []
            for e in await overpass(q):
                la, lo = e.get("lat") or (e.get("center") or {}).get("lat"), e.get("lon") or (e.get("center") or {}).get("lon")
                if la is None or lo is None:
                    continue
                tags = e.get("tags") or {}
                names = {k[5:]: v for k, v in tags.items() if k.startswith("name:") and len(k) == 7}
                items.append({"lat": la, "lon": lo, "name": tags.get("name") or "", "names": names})
            if items:
                break
    except Exception:  # noqa: BLE001
        log.exception("mosques lookup failed")
        return web.json_response({"ok": False}, status=502)
    out = {"ok": True, "radius": radius, "items": items}
    if len(MOSQUE_CACHE) > 300:
        MOSQUE_CACHE.clear()
    MOSQUE_CACHE[key] = (_time.time(), out)
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

async def admin_auth(request):
    tg_user = check_init_data(request.headers.get("X-Init-Data", ""))
    if not tg_user or not is_admin(int(tg_user["id"])):
        raise web.HTTPForbidden(text="admins only")
    return int(tg_user["id"])


def series(rows, days=30):
    have = {r["d"].isoformat(): r["c"] for r in rows}
    today = datetime.utcnow().date()
    return [{"d": (today - timedelta(days=i)).isoformat(), "c": have.get((today - timedelta(days=i)).isoformat(), 0)}
            for i in range(days - 1, -1, -1)]


async def api_admin_summary(request):
    await admin_auth(request)
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
    await admin_auth(request)
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
    total = await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args)
    rows = await POOL.fetch(f"SELECT * FROM users WHERE {where} ORDER BY last_seen DESC NULLS LAST, created_at DESC "
                            f"LIMIT 20 OFFSET {page * 20}", *args)
    return web.json_response({"ok": True, "total": total, "page": page, "items": [person_json(r) for r in rows]})


async def api_admin_person(request):
    await admin_auth(request)
    try:
        uid = int(request.query["id"])
    except (KeyError, ValueError):
        raise web.HTTPBadRequest(text="bad id")
    r = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    if not r:
        raise web.HTTPNotFound()
    u = dict(r)
    out = person_json(r)
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
    await admin_auth(request)
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


async def api_admin_message(request):
    await admin_auth(request)
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
        await request.app["bot"].send_message(uid, t(lang, "support_reply_header") + "\n\n" + admin_markup_text(text),
                                              parse_mode=ParseMode.HTML)
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
    await admin_auth(request)
    bc = bc_from_body(dict(request.query))
    where, args = bc_where(bc)
    return web.json_response({"ok": True, "count": await POOL.fetchval(f"SELECT count(*) FROM users WHERE {where}", *args),
                              "label": bc_label(bc)})


async def api_admin_broadcast(request):
    admin = await admin_auth(request)
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
    await admin_auth(request)
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
    admin = await admin_auth(request)
    rows = await POOL.fetch(f"SELECT {', '.join(CSV_COLUMNS)} FROM users ORDER BY created_at")
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
        name, lat, lon, cc = place
        pu = {"user_id": 0, "chat_type": "private", "lat": lat, "lon": lon, "country": cc, "lang": lang, "city": name,
              "madhab": (u or {}).get("madhab") or "std", "ramadan": True, "tz": None}
        first = await get_timings(pu, datetime.utcnow().date())
        pu["tz"] = first["tz"]
        day = await get_timings(pu, datetime.now(ZoneInfo(pu["tz"])).date())
        text, _ = await screen_times(pu, onboarding=True)
        desc = " · ".join(f"{PN[lang][k.lower()]} {day[k]}" for k in EVENTS)
        open_btn = InlineKeyboardMarkup([[InlineKeyboardButton(t(lang, "in_open"), url=f"https://t.me/{BOT_USERNAME}?start=inline")]])
        result = InlineQueryResultArticle(
            id=hashlib.md5(f"{lat:.3f},{lon:.3f},{lang},{pu['madhab']}".encode()).hexdigest(),
            title=f"🕌 {name}", description=desc,
            input_message_content=InputTextMessageContent(text, parse_mode=ParseMode.HTML),
            reply_markup=open_btn)
        await iq.answer([result], cache_time=120, is_personal=not q, button=hint)
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
        await bot.send_message(u["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=markup)
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
    try:
        rows = await POOL.fetch(
            "SELECT u.* FROM users u WHERE chat_type = 'private' AND weekly AND NOT banned AND NOT blocked "
            "AND tz IS NOT NULL AND lang IS NOT NULL "
            "AND EXISTS (SELECT 1 FROM tracker t WHERE t.user_id = u.user_id AND t.day > CURRENT_DATE - 14)")
        for r in rows:
            u = dict(r)
            now = datetime.now(ZoneInfo(u["tz"]))
            if now.weekday() == 0 and now.hour == 9 and u["last_weekly"] != now.date():
                await POOL.execute("UPDATE users SET last_weekly = $2 WHERE user_id = $1", u["user_id"], now.date())
                await send_weekly(bot, u, now.date())
                await asyncio.sleep(0.05)
    except Exception:  # noqa: BLE001
        log.exception("weekly reports failed")
    try:
        for admin in sorted(ADMINS):
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


# ───────────────────────── app ─────────────────────────


# Bot profile texts per language (set automatically on startup). Telegram shows each user
# the version for their app language; "en" is also used as the default for everyone else.
BOT_ABOUT = {
    "en": "🕌 Prayer times & reminders for your city. Qibla, Ramadan, Jumu'ah. For private chats, groups & channels 🤍",
    "ru": "🕌 Время намаза и напоминания для вашего города. Кибла, Рамадан, Джума. Для лички, групп и каналов 🤍",
    "uz": "🕌 Shahringiz uchun namoz vaqtlari va eslatmalar. Qibla, Ramazon, Juma. Shaxsiy chat, guruh va kanallar uchun 🤍",
    "tg": "🕌 Вақти намоз ва ёдовариҳо барои шаҳри шумо. Қибла, Рамазон, Ҷумъа. Барои чат, гурӯҳ ва каналҳо 🤍",
    "ar": "🕌 مواقيت الصلاة والتذكيرات لمدينتك. القبلة، رمضان، الجمعة. للمحادثات الخاصة والمجموعات والقنوات 🤍",
}
_LANG_LINE = "🌐 English · Русский · Oʻzbekcha · Тоҷикӣ · العربية"
BOT_DESCRIPTION = {
    "en": ("🕌 Assalamu alaikum!\n\nI'll show accurate prayer times for your city and remind you before every prayer.\n\n"
           "🔔 Reminders 5–30 minutes ahead\n🕋 Qibla direction\n🌙 Suhoor & Iftar in Ramadan\n"
           "🕌 Jumu'ah reminder\n👥 Works in groups and channels\n\n" + _LANG_LINE + "\n\nTap «Start» 👇"),
    "ru": ("🕌 Ассаламу алейкум!\n\nЯ покажу точное время намаза для вашего города и напомню о каждой молитве заранее.\n\n"
           "🔔 Напоминания за 5–30 минут\n🕋 Направление Киблы\n🌙 Сухур и ифтар в Рамадан\n"
           "🕌 Напоминание о Джума-намазе\n👥 Работаю в группах и каналах\n\n" + _LANG_LINE + "\n\nНажмите «Старт» 👇"),
    "uz": ("🕌 Assalomu alaykum!\n\nShahringiz uchun aniq namoz vaqtlarini ko'rsataman va har bir namozdan oldin eslataman.\n\n"
           "🔔 5–30 daqiqa oldin eslatma\n🕋 Qibla yo'nalishi\n🌙 Ramazonda saharlik va iftor\n"
           "🕌 Juma namozi eslatmasi\n👥 Guruh va kanallarda ishlayman\n\n" + _LANG_LINE + "\n\n«Start» tugmasini bosing 👇"),
    "tg": ("🕌 Ассалому алайкум!\n\nМан вақти дақиқи намозро барои шаҳри шумо нишон медиҳам ва пеш аз ҳар намоз ёдрас мекунам.\n\n"
           "🔔 Ёдоварӣ 5–30 дақиқа пеш\n🕋 Самти қибла\n🌙 Саҳарӣ ва ифтор дар Рамазон\n"
           "🕌 Ёдоварии намози ҷумъа\n👥 Дар гурӯҳҳо ва каналҳо кор мекунам\n\n" + _LANG_LINE + "\n\nТугмаи «Start»-ро пахш кунед 👇"),
    "ar": ("🕌 السلام عليكم!\n\nسأعرض لك مواقيت الصلاة الدقيقة لمدينتك وأذكّرك قبل كل صلاة.\n\n"
           "🔔 تذكير قبل 5–30 دقيقة\n🕋 اتجاه القبلة\n🌙 السحور والإفطار في رمضان\n"
           "🕌 تذكير بصلاة الجمعة\n👥 أعمل في المجموعات والقنوات\n\n" + _LANG_LINE + "\n\nاضغط «ابدأ» 👇"),
}
BOT_COMMAND = {"en": "🕌 Menu", "ru": "🕌 Меню", "uz": "🕌 Menyu", "tg": "🕌 Меню", "ar": "🕌 القائمة"}


async def setup_profile(bot):
    """Name-independent profile texts in every language. Safe to run on every start."""
    for lang in LANGS:
        for code in ([None, lang] if lang == "en" else [lang]):
            try:
                await bot.set_my_short_description(BOT_ABOUT[lang], language_code=code)
                await bot.set_my_description(BOT_DESCRIPTION[lang], language_code=code)
                await bot.set_my_commands([BotCommand("start", BOT_COMMAND[lang])], language_code=code)
            except RetryAfter as e:
                log.warning("profile texts rate-limited, retry in %ss", e.retry_after)
                return
            except Exception:  # noqa: BLE001
                log.exception("could not set profile texts for %s", code or "default")
    try:  # the button next to the message field opens the app
        if WEBAPP_URL:
            await bot.set_chat_menu_button(menu_button=MenuButtonWebApp("🕌 App", WebAppInfo(url=WEBAPP_URL)))
        else:
            await bot.set_chat_menu_button(menu_button=MenuButtonCommands())
    except Exception:  # noqa: BLE001
        log.exception("could not set menu button")


async def post_init(app: Application):
    global POOL, HTTP
    POOL = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5)
    async with POOL.acquire() as conn:
        await conn.execute(SCHEMA)
    HTTP = httpx.AsyncClient(timeout=15)
    global BOT_USERNAME
    BOT_USERNAME = app.bot.username
    asyncio.get_running_loop().create_task(setup_profile(app.bot))  # in background, never blocks startup
    try:
        await start_web(app)
    except Exception:  # noqa: BLE001
        log.exception("mini app server failed to start (the bot keeps working)")
    log.info("Bot is ready")


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
    app.add_handler(InlineQueryHandler(on_inline), group=1)
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
