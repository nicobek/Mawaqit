# -*- coding: utf-8 -*-
"""
🕌 Prayer Times Bot
Languages: English, Русский, Oʻzbekcha, Тоҷикӣ, العربية
Everything is controlled with inline buttons.

Env vars:
  BOT_TOKEN     - token from @BotFather
  DATABASE_URL  - PostgreSQL URL (Railway sets it for you)
  ADMIN_ID      - your Telegram user ID (enables the admin panel)
  CONTACT       - (optional) your email/@username, sent to the geocoder as required by its usage policy
"""
import asyncio
import csv
import html
import io
import logging
import math
import os
import time as _time
from collections import deque
from datetime import datetime, time as dtime, timedelta
from zoneinfo import ZoneInfo

import asyncpg
import httpx
from telegram import (
    BotCommand,
    ForceReply,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    Update,
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
    MessageHandler,
    TypeHandler,
    filters,
)

BOT_TOKEN = os.environ["BOT_TOKEN"]
DATABASE_URL = os.environ["DATABASE_URL"]
CONTACT = os.getenv("CONTACT", "prayer-times-bot")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0") or 0)  # your Telegram ID; 0 = admin panel disabled
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
LEAD_OPTIONS = [0, 5, 10, 15, 30]
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

GROUP_WELCOME = ("🕌 <b>Assalamu alaikum!</b>\n\n"
                 "I'll post prayer times and reminders here. Group admins, please set me up 👇\n\n" + LANG_PICK_TEXT)


def t(lang, key, **kw):
    s = T.get(lang, EN).get(key) or EN[key]
    return s.format(**kw) if kw else s


def esc(s):
    return html.escape(str(s))


def lead_label(lang, n):
    return t(lang, "lead_0") if n == 0 else t(lang, "lead_n", n=n)


def lead_phrase(lang, n):
    return t(lang, "phrase_0") if n == 0 else t(lang, "phrase_n", n=n)


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
            return
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return
            log.warning("edit failed (%s), sending new message", e)
        await update.effective_chat.send_message(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)


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
        await update.effective_chat.send_message(
            t(lang, "group_ask_city"), parse_mode=ParseMode.HTML,
            reply_markup=ForceReply(input_field_placeholder=t(lang, "city_ph")))
        return
    text, markup = screen_city(u)
    await render(update, text, markup)
    helper = await update.effective_chat.send_message(
        t(lang, "loc_hint"),
        reply_markup=ReplyKeyboardMarkup(
            [[KeyboardButton(t(lang, "loc_btn"), request_location=True)]],
            resize_keyboard=True, one_time_keyboard=True),
    )
    ctx.user_data["loc_msg"] = helper.message_id


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


def screen_menu(u):
    lang = u["lang"]
    rows = [
        [btn(t(lang, "btn_times"), "m:times")],
        [btn(t(lang, "btn_qibla"), "m:qibla")],
        [btn(t(lang, "btn_rem_on" if u["remind"] else "btn_rem_off"), "m:toggle")],
        [btn(t(lang, "btn_settings"), "m:settings")],
    ]
    if kind(u) == "channel":
        rows.append([btn(t(lang, "btn_my_channels"), "ch:list"), btn(t(lang, "btn_my_menu"), "ch:exit")])
        return t(lang, "channel_menu_title", title=esc(u["title"] or "—"), city=esc(u["city"] or "—")), kb(*rows)
    if is_private(u):
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
        [btn(t(lang, "btn_quiet"), "s:quiet")],
        [btn(t(lang, "btn_ram_on" if u["ramadan"] else "btn_ram_off"), "s:ramadan")],
    ]
    if not is_private(u):
        lines.append(f"📅 {daily_label(lang, u['daily'])}")
        rows.append([btn(t(lang, "btn_daily"), "s:daily")])
    elif ADMIN_ID:
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


def screen_qibla(u):
    lang = u["lang"]
    deg = qibla_bearing(u["lat"], u["lon"])
    arrow = ARROWS[int((deg + 22.5) // 45) % 8]
    text = t(lang, "qibla", city=esc(u["city"]), arrow=arrow, deg=round(deg))
    markup = kb(
        [InlineKeyboardButton(t(lang, "btn_kaaba"), url=f"https://maps.google.com/?q={KAABA[0]},{KAABA[1]}")],
        [btn(t(lang, "btn_menu"), "m:home")],
    )
    return text, markup


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
        [btn(t(lang, "btn_qibla"), "m:qibla")],
        [btn(t(lang, "btn_menu"), "m:home")],
    )
    return "\n".join(lines), markup


async def ask_remind(update, u):
    lang = u["lang"]
    await update.effective_chat.send_message(
        t(lang, "ask_remind", phrase=lead_phrase(lang, u["lead_min"])),
        parse_mode=ParseMode.HTML,
        reply_markup=kb([btn(t(lang, "btn_yes"), "rem:yes")], [btn(t(lang, "btn_no"), "rem:no")]),
    )


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


async def apply_location(update, ctx, u, name, lat, lon, cc):
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
    onboarding = not u["onboarded"]
    text, markup = await screen_times(u, onboarding)
    await render(update, text, markup)
    if onboarding:
        await ask_remind(update, u)


async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "channel":
        return
    if chat.type == "private":
        for k in ("admin_state", "support_mode", "reply_to", "target"):
            ctx.user_data.pop(k, None)
    elif _time.time() - ctx.chat_data.get("welcomed", 0) < 20:
        return  # the bot was just added and already greeted the group
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
    ctx.chat_data["pending_city"] = (u["user_id"], name, lat, lon, cc)
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
    await apply_location(update, ctx, u, name, loc.latitude, loc.longitude, cc)


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
    public = act == "m" and len(parts) > 1 and parts[1] in ("home", "times", "qibla")
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
        if parts[1] == "yes" and pending and pending[0] == tid:
            _, name, lat, lon, cc = pending
            return await apply_location(update, ctx, u, name, lat, lon, cc)
        return await show_city_prompt(update, ctx, u)  # "type again" (or an old, expired button)

    if act == "rem" and parts[1] in ("yes", "no"):
        on = parts[1] == "yes"
        await save(tid, remind=on, onboarded=True)
        u = await get_user(tid)
        _, markup = screen_menu(u)
        text = t(lang, "remind_on", phrase=lead_phrase(lang, u["lead_min"])) if on else t(lang, "remind_off")
        return await render(update, text, markup)

    # everything below needs a finished setup
    if not (u["madhab"] and u["city"] and u["tz"]):
        return await resume(update, ctx, u)

    if act == "m":
        sub = parts[1]
        if sub == "times":
            try:
                text, markup = await screen_times(u)
            except Exception:  # noqa: BLE001
                log.exception("times failed")
                text, markup = t(lang, "error"), screen_menu(u)[1]
        elif sub == "qibla":
            text, markup = screen_qibla(u)
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
        if sub == "support" and is_private(u) and ADMIN_ID:
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
    if ctx.user_data.get("support_mode") and ADMIN_ID:
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
            await ctx.bot.send_message(ADMIN_ID, header, parse_mode=ParseMode.HTML)
        try:
            await msg.copy(ADMIN_ID, reply_markup=markup)
        except BadRequest:  # some messages (e.g. polls) can't be copied with buttons
            await msg.forward(ADMIN_ID)
            await ctx.bot.send_message(ADMIN_ID, "👆", reply_markup=markup)
    except Exception:  # noqa: BLE001
        log.exception("support forward failed (has the admin started the bot?)")
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


async def send_reminder(bot, u, text):
    lang = u["lang"]
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

    if not u["remind"]:
        return
    ramadan = u["ramadan"] and data["hmonth"] == 9
    for key in EVENTS:
        hh, mm = map(int, data[key].split(":"))
        event_time = datetime.combine(d, dtime(hh, mm), tzinfo=tz)
        remind_at = event_time - timedelta(minutes=u["lead_min"])
        if not due(now, remind_at):
            continue
        sk = (u["user_id"], d.isoformat(), key)
        if sk in SENT:
            continue
        SENT[sk] = _time.time()
        if in_quiet(remind_at.hour, u["quiet_start"], u["quiet_end"]):
            continue
        if key == "Dhuhr" and d.weekday() == 4:
            kind_ = "jumah"
        elif ramadan and key == "Fajr":
            kind_ = "fajr_ram"
        elif ramadan and key == "Maghrib":
            kind_ = "iftar"
        else:
            kind_ = "std"
        tmpl = f"rem_{kind_}_{'n' if u['lead_min'] == 0 else 'b'}"
        text = t(lang, tmpl, name=PN[lang][key.lower()], n=u["lead_min"], time=data[key])
        await send_reminder(bot, u, text)


async def tick(context: ContextTypes.DEFAULT_TYPE):
    try:
        rows = await POOL.fetch(
            "SELECT * FROM users WHERE (remind OR daily <> 'off') AND NOT banned AND NOT blocked "
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
# One admin (ADMIN_ID). The admin UI is in Russian and fully button-driven.

ADMIN_BACK = [btn("⬅️ Назад", "a:home")]
CSV_COLUMNS = ("user_id", "chat_type", "title", "owner_id", "members", "lang", "madhab", "city", "country", "tz", "remind", "lead_min", "quiet_start",
               "quiet_end", "ramadan", "onboarded", "banned", "blocked", "created_at", "last_seen")
MADHAB_RU = {"std": "Шафиитский / Маликитский / Ханбалитский", "hanafi": "Ханафитский"}


def is_admin(uid):
    return bool(ADMIN_ID) and uid == ADMIN_ID


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
    try:
        row = await POOL.fetchrow(
            "UPDATE users SET last_seen = now(), blocked = FALSE WHERE user_id = $1 RETURNING banned", user.id)
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
        [btn("📣 Рассылка", "a:bc"), btn("🔎 Пользователь", "a:user")],
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


async def screen_admin_geo():
    cities = await POOL.fetch(
        "SELECT min(city) AS name, count(*) AS c FROM users WHERE lat IS NOT NULL "
        "GROUP BY round(lat::numeric, 1), round(lon::numeric, 1) ORDER BY c DESC LIMIT 10")
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


async def user_card(uid):
    r = await POOL.fetchrow("SELECT * FROM users WHERE user_id = $1", uid)
    if not r:
        return None
    u = dict(r)
    lead = "в момент азана" if u["lead_min"] == 0 else f"за {u['lead_min']} мин"
    quiet = "выкл" if u["quiet_start"] is None else f"{u['quiet_start']:02d}:00–{u['quiet_end']:02d}:00"
    kind_ru = {"private": "👤 Пользователь", "group": "👥 Группа", "channel": "📢 Канал"}.get(u["chat_type"], "👤")
    extra = "" if u["chat_type"] == "private" else (
        f"🏷 {esc(u['title'] or '—')} · 👤 участников: {u['members'] or '—'}\n"
        f"🙋 Добавил: <code>{u['owner_id'] or '—'}</code> · 📅 Ежедневно: {u['daily']}\n")
    text = (f"<b>{kind_ru}</b> <code>{u['user_id']}</code>\n\n{extra}"
            f"🌐 Язык: {LANG_BUTTONS.get(u['lang'], '—')}\n"
            f"🕌 Мазхаб: {MADHAB_RU.get(u['madhab'], '—')}\n"
            f"📍 Город: {esc(u['city'] or '—')} {flag(u['country']) if u['country'] else ''}\n"
            f"🕒 Часовой пояс: {esc(u['tz'] or '—')}\n"
            f"🔔 Напоминания: {'вкл, ' + lead if u['remind'] else 'выкл'}\n"
            f"🔕 Тихие часы: {quiet}\n"
            f"🌙 Режим Рамадана: {yn(u['ramadan'])}\n"
            f"✅ Настройка завершена: {yn(u['onboarded'])}\n"
            f"🚫 Бан: {yn(u['banned'])} · 🧱 Заблокировал бота: {yn(u['blocked'])}\n"
            f"📅 Регистрация: {fdt(u['created_at'])} UTC\n"
            f"👁 Последний визит: {fdt(u['last_seen'])} UTC")
    rows = []
    if not is_admin(uid):
        rows.append([btn("✅ Разбанить", f"a:unban:{uid}") if u["banned"] else btn("🚫 Забанить", f"a:ban:{uid}")])
    rows.append(ADMIN_BACK)
    return text, kb(*rows)


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


async def send_one(bot, uid, text):
    for _ in range(2):
        try:
            await bot.send_message(uid, text, parse_mode=ParseMode.HTML)
            return "ok"
        except Forbidden:
            await POOL.execute("UPDATE users SET blocked = TRUE WHERE user_id = $1", uid)
            return "blocked"
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception:  # noqa: BLE001
            log.exception("broadcast send failed for %s", uid)
            return "fail"
    return "fail"


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
        for i, uid in enumerate(ids, 1):
            res = await send_one(app.bot, uid, text)
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
        card = await user_card(int(parts[2]))
        if card:
            return await update.effective_chat.send_message(card[0], parse_mode=ParseMode.HTML, reply_markup=card[1])
        return await update.effective_chat.send_message("🤷 Такого пользователя нет в базе.")

    if sub == "user":
        ctx.user_data["admin_state"] = "search"
        return await render(update, "🔎 <b>Поиск пользователя</b>\n\nОтправьте Telegram ID пользователя (число).",
                            kb(ADMIN_BACK))

    if sub in ("ban", "unban") and len(parts) > 2 and parts[2].lstrip("-").isdigit():
        target = int(parts[2])
        if is_admin(target):
            return await render(update, "😅 Себя забанить нельзя.", kb(ADMIN_BACK))
        await POOL.execute("UPDATE users SET banned = $2 WHERE user_id = $1", target, sub == "ban")
        card = await user_card(target)
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
        raw = msg.text.strip()
        if not raw.lstrip("-").isdigit():
            await msg.reply_text("❗ Нужен числовой Telegram ID. Попробуйте ещё раз.", reply_markup=kb(ADMIN_BACK))
            return True
        ctx.user_data.pop("admin_state", None)
        card = await user_card(int(raw))
        if not card:
            await msg.reply_text("🤷 Такого пользователя нет в базе.", reply_markup=kb(ADMIN_BACK))
        else:
            await msg.reply_text(card[0], parse_mode=ParseMode.HTML, reply_markup=card[1])
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


async def post_init(app: Application):
    global POOL, HTTP
    POOL = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5)
    async with POOL.acquire() as conn:
        await conn.execute(SCHEMA)
    HTTP = httpx.AsyncClient(timeout=15)
    global BOT_USERNAME
    BOT_USERNAME = app.bot.username
    asyncio.get_running_loop().create_task(setup_profile(app.bot))  # in background, never blocks startup
    log.info("Bot is ready")


async def post_shutdown(app: Application):
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
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
