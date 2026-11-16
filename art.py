"""Share pictures: the ayah of the day and the day's prayer times.

10 backgrounds and 7 font pairs (Arabic + text). Pure drawing: the bot passes in ready strings.
Arabic is shaped with Pillow's raqm layout when available, otherwise with arabic_reshaper + python-bidi.
"""
import io
import math
import random
from functools import lru_cache
from pathlib import Path

from PIL import Image, ImageDraw, ImageFilter, ImageFont, features

FONT_DIR = Path(__file__).with_name("fonts")
RAQM = features.check("raqm")
N_BG = 10

# id: (arabic regular, arabic bold, text regular, text bold, strip Qur'an pause marks)
FONT_SETS = [
    ("Amiri_400Regular", "Amiri_700Bold", "NotoSerif_400Regular", "NotoSerif_700Bold", False),
    ("Amiri_400Regular", "Amiri_700Bold", "CormorantGaramond_500Medium", "CormorantGaramond_700Bold", False),
    ("NotoNaskhArabic_400Regular", "NotoNaskhArabic_700Bold", "Montserrat_500Medium", "Montserrat_700Bold", False),
    ("ScheherazadeNew_400Regular", "ScheherazadeNew_700Bold", "Lora_400Regular", "Lora_700Bold", False),
    ("NotoNaskhArabic_400Regular", "NotoNaskhArabic_700Bold", "PTSerif_400Regular", "PTSerif_700Bold", False),
    ("ReemKufi_500Medium", "ReemKufi_700Bold", "Montserrat_500Medium", "Montserrat_700Bold", True),
    ("ArefRuqaa_400Regular", "ArefRuqaa_700Bold", "Caveat_500Medium", "Caveat_700Bold", True),
]
N_FONT = len(FONT_SETS)
FONT_NAMES = {
    "en": ["Classic", "Elegant", "Modern", "Book", "Strict", "Kufi", "Handwritten"],
    "ru": ["Классика", "Элегант", "Современный", "Книжный", "Строгий", "Куфи", "Рукописный"],
    "uz": ["Klassik", "Nafis", "Zamonaviy", "Kitobiy", "Qat'iy", "Kufiy", "Qo'lyozma"],
    "uzc": ["Классик", "Нафис", "Замонавий", "Китобий", "Қатъий", "Куфий", "Қўлёзма"],
    "tg": ["Классикӣ", "Нафис", "Замонавӣ", "Китобӣ", "Қатъӣ", "Куфӣ", "Дастнавис"],
    "ar": ["كلاسيكي", "أنيق", "عصري", "كتابي", "رسمي", "كوفي", "رقعة"],
}
FALLBACK = FONT_DIR / "DejaVuSans.ttf"


@lru_cache(maxsize=64)
def font(name, size):
    try:
        return ImageFont.truetype(str(FONT_DIR / f"{name}.ttf"), size,
                                  layout_engine=ImageFont.Layout.RAQM if RAQM else ImageFont.Layout.BASIC)
    except Exception:  # noqa: BLE001
        return ImageFont.truetype(str(FALLBACK), size)


def is_ar(s):
    return any("؀" <= ch <= "ۿ" or "ﭐ" <= ch <= "﻿" for ch in s)


def fix_text(s):
    """Letters some fonts lack: the Uzbek ʻ ʼ → ‘ ’."""
    return s.replace("ʻ", "‘").replace("ʼ", "’").replace("`", "‘")


def strip_marks(s):
    return "".join(ch for ch in s if not ("ۖ" <= ch <= "ۭ")).replace("﴿", "(").replace("﴾", ")")


def shape(s):
    """Without raqm: join the Arabic letters and put them right to left ourselves."""
    if RAQM or not is_ar(s):
        return s
    try:
        import arabic_reshaper
        from bidi.algorithm import get_display
        return get_display(arabic_reshaper.reshape(s))
    except Exception:  # noqa: BLE001
        return s


def _kw(s):
    return {"direction": "rtl", "language": "ar"} if RAQM and is_ar(s) else {}


def tlen(d, s, f):
    try:
        return d.textlength(shape(s), font=f, **_kw(s))
    except Exception:  # noqa: BLE001
        return d.textlength(shape(s), font=f)


def draw_text(d, xy, s, f, fill, anchor="mm"):
    try:
        d.text(xy, shape(s), font=f, fill=fill, anchor=anchor, **_kw(s))
    except Exception:  # noqa: BLE001
        d.text(xy, shape(s), font=f, fill=fill, anchor=anchor)


def wrap(d, s, f, maxw):
    lines = []
    for para in s.split("\n"):
        cur = ""
        for w in para.split():
            test = (cur + " " + w).strip()
            if tlen(d, test, f) <= maxw or not cur:
                cur = test
            else:
                lines.append(cur)
                cur = w
        if cur:
            lines.append(cur)
    return lines


# ───────────────────────── backgrounds ─────────────────────────

def _grad(W, H, stops):
    """Vertical gradient through (position 0..1, colour) stops."""
    img = Image.new("RGB", (W, H))
    d = ImageDraw.Draw(img)
    for y in range(H):
        k = y / (H - 1)
        for (p0, c0), (p1, c1) in zip(stops, stops[1:]):
            if p0 <= k <= p1:
                kk = (k - p0) / ((p1 - p0) or 1)
                d.line([(0, y), (W, y)], fill=tuple(int(c0[i] + (c1[i] - c0[i]) * kk) for i in range(3)))
                break
    return img


def _glow(img, shapes, blur):
    layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
    g = ImageDraw.Draw(layer)
    for box, col in shapes:
        g.ellipse(box, fill=col)
    layer = layer.filter(ImageFilter.GaussianBlur(blur))
    img.paste(layer, (0, 0), layer)


def _stars(img, n, ymax, seed, avoid=None):
    d = ImageDraw.Draw(img)
    rnd = random.Random(seed)
    for _ in range(n):
        x, y, r = rnd.randint(0, img.width), rnd.randint(0, ymax), rnd.choice((1, 1, 1, 2, 2, 3))
        c = rnd.randint(150, 255)
        d.ellipse([x - r, y - r, x + r, y + r], fill=(c, c, min(255, c + 10)))


def _crescent(img, cx, cy, r, col, sky):
    halo = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(halo).ellipse([cx - r * 1.7, cy - r * 1.7, cx + r * 1.7, cy + r * 1.7], fill=col + (70,))
    halo = halo.filter(ImageFilter.GaussianBlur(r * 0.5))
    img.paste(halo, (0, 0), halo)
    moon = Image.new("RGBA", img.size, (0, 0, 0, 0))
    md = ImageDraw.Draw(moon)
    md.ellipse([cx - r, cy - r, cx + r, cy + r], fill=col + (255,))
    md.ellipse([cx - r + r * 0.55, cy - r - r * 0.27, cx + r + r * 0.55, cy + r - r * 0.27], fill=(0, 0, 0, 0))
    img.paste(moon, (0, 0), moon)


def _skyline(img, base, col, scale=1.0):
    layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
    sd = ImageDraw.Draw(layer)
    W = img.width
    s = scale
    sd.rectangle([0, base - 30 * s, W, img.height], fill=col)

    def dome(cx, w, h):
        w, h = w * s, h * s
        sd.rectangle([cx - w / 2, base - h * 0.45, cx + w / 2, base], fill=col)
        sd.ellipse([cx - w * 0.42, base - h, cx + w * 0.42, base - h * 0.3], fill=col)
        sd.polygon([(cx - w * 0.12, base - h * 0.93), (cx + w * 0.12, base - h * 0.93), (cx, base - h - 34 * s)], fill=col)
        sd.rectangle([cx - 3, base - h - 52 * s, cx + 3, base - h - 26 * s], fill=col)

    def minaret(mx, mh):
        mh = mh * s
        sd.rectangle([mx - 14 * s, base - mh, mx + 14 * s, base], fill=col)
        sd.rectangle([mx - 22 * s, base - mh * 0.62, mx + 22 * s, base - mh * 0.62 + 14 * s], fill=col)
        sd.polygon([(mx - 18 * s, base - mh), (mx + 18 * s, base - mh), (mx, base - mh - 56 * s)], fill=col)

    dome(W * 0.14, 170, 120)
    dome(W * 0.37, 210, 165)
    dome(W * 0.54, 300, 215)
    dome(W * 0.87, 190, 135)
    for mx, mh in ((W * 0.04, 150), (W * 0.25, 205), (W * 0.67, 225), (W * 0.97, 170)):
        minaret(mx, mh)
    img.paste(layer, (0, 0), layer)


def _star8(d, cx, cy, r, col, width=2):
    pts = []
    for k in range(16):
        a = math.pi * k / 8
        rr = r if k % 2 == 0 else r * 0.62
        pts.append((cx + rr * math.cos(a), cy + rr * math.sin(a)))
    d.polygon(pts, outline=col, width=width)


def _arch(d, x0, x1, ytop, ybottom, col, width=4, fill=None):
    """A pointed (mihrab) arch: two circle arcs meeting at the top, straight sides down."""
    w = x1 - x0
    r = w * 0.85
    spring = ytop + w * 0.62
    pts = []
    for k in range(41):  # left arc: centre on the right side
        t = k / 40
        x = x0 + (w / 2) * t
        cx = x0 + r
        y = spring - 0.42 * math.sqrt(max(0, r * r - (x - cx) ** 2))
        pts.append((x, y))
    for k in range(41):
        t = k / 40
        x = x0 + w / 2 + (w / 2) * t
        cx = x1 - r
        y = spring - 0.42 * math.sqrt(max(0, r * r - (x - cx) ** 2))
        pts.append((x, y))
    top_y = min(p[1] for p in pts)
    shift = ytop - top_y
    pts = [(x, y + shift) for x, y in pts]
    poly = [(x0, ybottom)] + pts + [(x1, ybottom)]
    if fill:
        d.polygon(poly, fill=fill)
    d.line(poly, fill=col, width=width, joint="curve")


@lru_cache(maxsize=12)
def background(i, W, H):
    """Returns (image, palette). Each one is a different scene."""
    i %= N_BG
    gold = (226, 190, 92)
    if i == 0:  # night sky, crescent, mosque skyline
        img = _grad(W, H, [(0, (10, 16, 40)), (0.45, (33, 24, 66)), (1, (14, 22, 44))])
        _glow(img, [([W / 2 - 420, 40, W / 2 + 420, 760], (226, 190, 92, 40)), ([-300, H * 0.6, 520, H], (110, 70, 160, 60))], 110)
        _stars(img, 160, int(H * 0.55), 7)
        _crescent(img, W - 150, 270, 54, gold, (26, 21, 58))
        _skyline(img, H - 40, (226, 190, 92, 34), 0.9)
        pal = {"text": (244, 246, 250), "accent": gold, "soft": (175, 182, 210), "card": (255, 255, 255, 26), "dark": True}
    elif i == 1:  # dawn over the mosque
        img = _grad(W, H, [(0, (22, 30, 70)), (0.45, (96, 72, 138)), (0.75, (226, 138, 128)), (1, (250, 196, 140))])
        _glow(img, [([W / 2 - 330, H - 380, W / 2 + 330, H + 280], (255, 220, 160, 150))], 90)
        _stars(img, 70, int(H * 0.3), 11)
        _skyline(img, H - 30, (32, 22, 50, 235), 1.0)
        pal = {"text": (255, 255, 255), "accent": (255, 214, 150), "soft": (240, 222, 236), "card": (20, 12, 40, 70), "dark": True}
    elif i == 2:  # desert sunset with dunes
        img = _grad(W, H, [(0, (252, 178, 96)), (0.38, (214, 96, 92)), (0.7, (96, 40, 84)), (1, (40, 18, 46))])
        _glow(img, [([W / 2 - 170, H * 0.55, W / 2 + 170, H * 0.55 + 340], (255, 236, 180, 230))], 30)
        d = ImageDraw.Draw(img)
        for k, (yb, col, amp, ph) in enumerate(((0.62, (150, 60, 70), 50, 0.3), (0.72, (110, 40, 70), 60, 1.7), (0.84, (62, 22, 50), 45, 3.1))):
            pts = [(x, H * yb + amp * math.sin(x / W * 2.4 * math.pi + ph)) for x in range(0, W + 20, 20)]
            d.polygon(pts + [(W, H), (0, H)], fill=col)
        pal = {"text": (255, 255, 255), "accent": (255, 230, 170), "soft": (255, 220, 210), "card": (40, 10, 30, 70), "dark": True}
    elif i == 3:  # emerald with a gold star lattice
        img = _grad(W, H, [(0, (8, 72, 58)), (1, (2, 28, 24))])
        layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ld = ImageDraw.Draw(layer)
        step = 180
        for yy in range(-step, H + step, step):
            for xx in range(-step, W + step, step):
                off = step / 2 if (yy // step) % 2 else 0
                _star8(ld, xx + off, yy, 70, (226, 190, 92, 40))
        img.paste(layer, (0, 0), layer)
        _glow(img, [([W / 2 - 500, H / 2 - 500, W / 2 + 500, H / 2 + 500], (0, 20, 16, 200))], 120)
        pal = {"text": (240, 248, 240), "accent": (228, 196, 112), "soft": (176, 210, 194), "card": (0, 0, 0, 60), "dark": True}
    elif i == 4:  # royal blue, circles pattern
        img = _grad(W, H, [(0, (18, 38, 96)), (1, (6, 12, 42))])
        layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ld = ImageDraw.Draw(layer)
        r = 90
        for row, yy in enumerate(range(-r, H + r, int(r * 0.866))):
            for xx in range(-r, W + r, r):
                cx = xx + (r / 2 if row % 2 else 0)
                ld.ellipse([cx - r, yy - r, cx + r, yy + r], outline=(150, 190, 255, 26), width=2)
        img.paste(layer, (0, 0), layer)
        _glow(img, [([W / 2 - 520, H / 2 - 520, W / 2 + 520, H / 2 + 520], (6, 12, 42, 210))], 130)
        pal = {"text": (255, 255, 255), "accent": (236, 204, 128), "soft": (180, 196, 236), "card": (255, 255, 255, 22), "dark": True}
    elif i == 5:  # white marble
        img = _grad(W, H, [(0, (248, 245, 238)), (1, (232, 226, 214))])
        layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ld = ImageDraw.Draw(layer)
        rnd = random.Random(5)
        for _ in range(14):
            x, y = rnd.uniform(-100, W), rnd.uniform(0, H)
            ang = rnd.uniform(-0.6, 0.6) + math.pi / 4
            pts = []
            for _ in range(60):
                x += 22 * math.cos(ang)
                y += 22 * math.sin(ang)
                ang += rnd.uniform(-0.25, 0.25)
                pts.append((x, y))
            ld.line(pts, fill=(140, 130, 120, rnd.randint(30, 70)), width=rnd.choice((1, 2, 3)))
        layer = layer.filter(ImageFilter.GaussianBlur(1.6))
        img.paste(layer, (0, 0), layer)
        d = ImageDraw.Draw(img)
        d.rectangle([36, 36, W - 36, H - 36], outline=(176, 140, 70), width=3)
        pal = {"text": (44, 38, 32), "accent": (156, 116, 44), "soft": (108, 96, 84), "card": (120, 100, 70, 26), "dark": False}
    elif i == 6:  # black and gold, ornamental frame
        img = _grad(W, H, [(0, (16, 15, 14)), (1, (30, 26, 20))])
        d = ImageDraw.Draw(img)
        g = (212, 176, 96)
        d.rectangle([40, 40, W - 40, H - 40], outline=g, width=3)
        d.rectangle([58, 58, W - 58, H - 58], outline=g, width=1)
        for cx, cy in ((58, 58), (W - 58, 58), (58, H - 58), (W - 58, H - 58)):
            _star8(d, cx, cy, 34, g, 2)
        for cx in (W / 2,):
            _star8(d, cx, 58, 22, g, 2)
            _star8(d, cx, H - 58, 22, g, 2)
        pal = {"text": (246, 240, 226), "accent": g, "soft": (190, 180, 160), "card": (212, 176, 96, 24), "dark": True}
    elif i == 7:  # purple night with hanging lanterns
        img = _grad(W, H, [(0, (44, 18, 66)), (1, (14, 8, 30))])
        _stars(img, 120, H, 17)
        d = ImageDraw.Draw(img)
        for x, length, sz in ((W * 0.07, 150, 0.9), (W * 0.17, 70, 0.65), (W * 0.83, 90, 0.7), (W * 0.93, 190, 1.0)):
            ytop = length
            _glow(img, [([x - 90 * sz, ytop + 10, x + 90 * sz, ytop + 190 * sz], (255, 190, 90, 120))], 40)
            d = ImageDraw.Draw(img)
            d.line([(x, 0), (x, ytop)], fill=(210, 170, 90), width=2)
            w, h = 46 * sz, 110 * sz
            d.polygon([(x - w * 0.5, ytop + 18 * sz), (x + w * 0.5, ytop + 18 * sz), (x + w, ytop + h * 0.45),
                       (x + w * 0.6, ytop + h), (x - w * 0.6, ytop + h), (x - w, ytop + h * 0.45)], fill=(255, 196, 96),
                      outline=(160, 110, 40))
            d.polygon([(x - w * 0.5, ytop + 18 * sz), (x, ytop - 6 * sz), (x + w * 0.5, ytop + 18 * sz)], fill=(200, 150, 60))
            d.line([(x, ytop + 24 * sz), (x, ytop + h - 4)], fill=(190, 120, 40), width=2)
        pal = {"text": (255, 255, 255), "accent": (255, 204, 120), "soft": (210, 196, 230), "card": (255, 255, 255, 22), "dark": True}
    elif i == 8:  # aurora
        img = _grad(W, H, [(0, (4, 18, 30)), (1, (6, 28, 36))])
        _glow(img, [([-200, H * 0.05, W * 0.8, H * 0.35], (60, 220, 170, 110)), ([W * 0.3, H * 0.15, W + 260, H * 0.5], (90, 120, 255, 90)),
                    ([-100, H * 0.55, W * 0.7, H * 0.95], (150, 80, 220, 70))], 120)
        layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ld = ImageDraw.Draw(layer)
        rnd = random.Random(8)
        for _ in range(26):
            x, y, r = rnd.uniform(0, W), rnd.uniform(0, H), rnd.uniform(8, 40)
            ld.ellipse([x - r, y - r, x + r, y + r], fill=(200, 255, 240, rnd.randint(18, 50)))
        layer = layer.filter(ImageFilter.GaussianBlur(4))
        img.paste(layer, (0, 0), layer)
        pal = {"text": (240, 255, 250), "accent": (140, 240, 210), "soft": (170, 210, 220), "card": (255, 255, 255, 20), "dark": True}
    else:  # sand, mihrab arch
        img = _grad(W, H, [(0, (240, 230, 208)), (1, (216, 198, 160))])
        d = ImageDraw.Draw(img)
        _arch(d, 90, W - 90, 40, H - 70, (160, 116, 56), 5, fill=(246, 238, 220))
        _arch(d, 116, W - 116, 70, H - 70, (190, 150, 90), 2)
        pal = {"text": (62, 42, 22), "accent": (150, 98, 36), "soft": (120, 96, 70), "card": (150, 110, 50, 26), "dark": False}
    return img, pal


# ───────────────────────── pictures ─────────────────────────

def _pill(img, d, W, y, label, pal, f):
    tw = tlen(d, label, f) + 90
    fill = pal["accent"]
    ink = (30, 22, 6) if sum(fill) > 420 else (255, 255, 255)
    d.rounded_rectangle([W / 2 - tw / 2, y - 40, W / 2 + tw / 2, y + 40], radius=40, fill=fill)
    draw_text(d, (W / 2, y), label, f, ink)


def _save(img):
    buf = io.BytesIO()
    img.save(buf, "JPEG", quality=92, optimize=True)
    return buf.getvalue()


def render_ayah(arabic, translation, ref, header, bot_label, bg=0, fs=0):
    """1080×1350: header, Arabic ayah, translation, sura reference, @bot pill."""
    W, H = 1080, 1350
    base, pal = background(bg, W, H)
    img = base.copy()
    d = ImageDraw.Draw(img)
    ar_r, ar_b, tx_r, tx_b, strip = FONT_SETS[fs % N_FONT]
    arabic = strip_marks(arabic) if strip else arabic
    translation = fix_text(translation or "")
    ref = fix_text(ref)
    maxw = W - 220
    top, bottom = 220, H - 190
    # fit: shrink until it all fits
    for k in range(14):
        asz, tsz = int(70 - k * 3.2), int(44 - k * 1.6)
        fa, ft = font(ar_r, asz), font(tx_r, tsz)
        al = wrap(d, arabic, fa, maxw) if arabic else []
        tl = wrap(d, translation, ft, maxw) if translation else []
        alh, tlh = int(asz * 1.9), int(tsz * 1.45)
        gap = 56 if al and tl else 0
        total = len(al) * alh + gap + len(tl) * tlh + 90
        if total <= bottom - top:
            break
    # header
    fh = font(ar_b if is_ar(header) else tx_b, 34)
    draw_text(d, (W / 2, 140), header, fh, pal["accent"])
    hw = tlen(d, header, fh) / 2 + 30
    d.line([(W / 2 - hw - 120, 140), (W / 2 - hw, 140)], fill=pal["accent"], width=2)
    d.line([(W / 2 + hw, 140), (W / 2 + hw + 120, 140)], fill=pal["accent"], width=2)
    y = top + (bottom - top - total) / 2
    # soft card behind the text on busy backgrounds
    card = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(card).rounded_rectangle([70, y - 40, W - 70, y + total + 10], radius=44, fill=pal["card"])
    img.paste(card, (0, 0), card)
    d = ImageDraw.Draw(img)
    for line in al:
        draw_text(d, (W / 2, y + alh / 2), line, fa, pal["text"])
        y += alh
    if al and tl:
        y += gap / 2
        d.line([(W / 2 - 60, y), (W / 2 + 60, y)], fill=pal["accent"], width=2)
        y += gap / 2
    for line in tl:
        draw_text(d, (W / 2, y + tlh / 2), line, ft, pal["text"] if not al else pal["soft"] if pal["dark"] else pal["text"])
        y += tlh
    draw_text(d, (W / 2, y + 50), ref, font(ar_b if is_ar(ref) else tx_b, max(26, tsz - 6)), pal["accent"])
    _pill(img, d, W, H - 100, bot_label, pal, font(tx_b, 38))
    return _save(img)


def render_times(title, city, date_line, rows, bot_label, bg=0, fs=0, rtl=False):
    """1080×1920: the day's prayer times. rows = [(kind, name, time, dim)], kind: moon / half / sun."""
    W, H = 1080, 1920
    base, pal = background(bg, W, H)
    img = base.copy()
    d = ImageDraw.Draw(img)
    ar_r, ar_b, tx_r, tx_b, _ = FONT_SETS[fs % N_FONT]

    def tf(s, size, bold=True):  # text font, Arabic font for Arabic words
        if is_ar(s):
            return font(ar_b if bold else ar_r, size)
        return font(tx_b if bold else tx_r, size)

    title, city, date_line = fix_text(title), fix_text(city), fix_text(date_line)
    draw_text(d, (W / 2, 300), title, tf(title, 76), pal["text"])
    draw_text(d, (W / 2, 390), city, tf(city, 46), pal["accent"])
    f = tf(date_line, 34, False)
    pw = tlen(d, date_line, f) + 70
    d.rounded_rectangle([W / 2 - pw / 2, 440, W / 2 + pw / 2, 506], radius=33, outline=pal["accent"], width=2)
    draw_text(d, (W / 2, 473), date_line, f, pal["soft"])
    top_y, step, ch = 600, 168, 136
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    cd = ImageDraw.Draw(layer)
    for i, row in enumerate(rows):
        y = top_y + i * step
        cd.rounded_rectangle([80, y, W - 80, y + ch], radius=42, fill=pal["card"],
                             outline=(255, 255, 255, 50) if pal["dark"] else (0, 0, 0, 30), width=2)
    img.paste(layer, (0, 0), layer)
    d = ImageDraw.Draw(img)
    acc = pal["accent"]
    for i, (kind, name, tm, dim) in enumerate(rows):
        y = top_y + i * step + ch // 2
        ix = W - 170 if rtl else 170
        d.ellipse([ix - 46, y - 46, ix + 46, y + 46], outline=acc, width=3)
        if kind == "sun":
            d.ellipse([ix - 18, y - 18, ix + 18, y + 18], fill=acc)
            for k in range(8):
                a = math.pi * k / 4
                d.line([(ix + 26 * math.cos(a), y + 26 * math.sin(a)), (ix + 34 * math.cos(a), y + 34 * math.sin(a))], fill=acc, width=4)
        elif kind == "half":
            hy = y + 10
            d.pieslice([ix - 20, hy - 20, ix + 20, hy + 20], 180, 360, fill=acc)
            for k in range(5):
                a = math.pi + math.pi * (k + 0.5) / 5
                d.line([(ix + 27 * math.cos(a), hy + 27 * math.sin(a)), (ix + 35 * math.cos(a), hy + 35 * math.sin(a))], fill=acc, width=4)
            d.line([(ix - 32, hy + 2), (ix + 32, hy + 2)], fill=acc, width=3)
        else:
            moon = Image.new("RGBA", (120, 120), (0, 0, 0, 0))
            md = ImageDraw.Draw(moon)
            md.ellipse([36, 36, 84, 84], fill=acc + (255,))
            md.ellipse([48, 28, 94, 74], fill=(0, 0, 0, 0))
            img.paste(moon, (int(ix - 60), int(y - 60)), moon)
            d = ImageDraw.Draw(img)
        col = pal["soft"] if dim else pal["text"]
        name = fix_text(name)
        if rtl:
            draw_text(d, (W - 250, y), name, tf(name, 54), col, "rm")
            d.text((150, y), tm, font=font(tx_b, 66), fill=pal["soft"] if dim else acc, anchor="lm")
        else:
            draw_text(d, (250, y), name, tf(name, 54), col, "lm")
            d.text((W - 150, y), tm, font=font(tx_b, 66), fill=pal["soft"] if dim else acc, anchor="rm")
    _pill(img, d, W, H - 120, bot_label, pal, font(tx_b, 40))
    return _save(img)
