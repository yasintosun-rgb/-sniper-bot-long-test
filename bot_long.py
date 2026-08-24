"""
LONG BOT — "EMA200 DÖNÜŞÜ" STRATEJİSİ
======================================
Bu bot, SHORT bot'tan (bot.py) TAMAMEN AYRI ve BAĞIMSIZ çalışır — ayrı bir
process, ayrı state/journal dosyaları. AYNI Binance hesabını (Hedge Mode
açık) ve isteğe bağlı aynı/farklı Telegram botunu kullanabilir.

STRATEJİ (backtest_ema_htf.py'de doğrulandı, 2026-08-22):
  Giriş : fiyat en az EMA200_ALTI_MIN_MUM (72 = 3 gün) ardışık 1 SAATLİK
          mum boyunca EMA200'ün ALTINDA kalmış, SONRA 2 ardışık 1 saatlik
          mum EMA200'ün ÜZERİNDE kapanmış → LONG gir.
  Çıkış : SL = giriş - %PERCENT_TRAILING_MESAFE (varsayılan %7). Fiyat
          yükseldikçe SL, GÖRÜLEN EN YÜKSEK FİYATIN %7 altında kalacak
          şekilde SÜREKLİ yukarı çekilir (asla gevşetilmez). TP YOK.
  Zaman dilimi: 1 SAAT (SHORT bot'un 15dk'sından farklı).
  Rejim kapısı: YOK (backtest'te eklemek zararlı çıktı — MaxDD kötüleşti).

DOĞRULAMA (backtest_ema_htf.py, 1h, 20 coin, 2024-01→2026-08, kapısız):
  Tam dönem: Getiri=%20.54 PF=1.29 MaxDD=%10.83 (386 işlem)
  Walk-forward (%50/50): doğrulama penceresi Getiri=%12.11 PF=1.37 (185 işlem)
  5-bölünmeli sağlamlık: 5/5 bölünmede referanstan iyi (%100, SAĞLAM)

HEDGE MODE UYARISI (ÖNEMLİ — bkz. bot.py'deki aynı başlık):
  Bu bot POZISYON_YONU='LONG' ile SADECE LONG tarafını takip eder. AYNI
  Binance hesabında SHORT bot (bot.py) ile birlikte çalıştırılacaksa:
    1) Binance hesabında Hedge Mode (dualSidePosition=true) AÇIK olmalı
       (açık pozisyon/emir yokken, Binance uygulaması → Futures → Ayarlar
       → Pozisyon Modu).
    2) LEVERAGE değeri SHORT bot'takiyle AYNI olmalı (kaldıraç sembol
       bazında paylaşılır, positionSide'a göre ayrı değildir).
    3) Bu bot da (bot.py gibi) TÜM emirlere positionSide gönderir, asla
       reduceOnly kullanmaz, TÜM pozisyon sorgularını POZISYON_YONU'na
       göre filtreler, ve emir iptallerini blanket "cancel_all" yerine
       SADECE kendi tarafına ait emirleri tek tek iptal ederek yapar —
       böylece SHORT bot'un emirlerine/pozisyonlarına ASLA dokunmaz.

CANLIYA ALMADAN ÖNCE MUTLAKA:
  - Binance TESTNET'te (TESTNET=True) en az birkaç gün çalıştırıp gözlemleyin.
  - _guvenli_algo_emir_iptal() içindeki futures_cancel_algo_order metod adı
    python-binance sürümünüze göre değişebilir — testnet'te bunu özellikle
    doğrulayın (log'da "algo emir iptal hatasi" görürseniz kütüphane
    sürümünüzün desteklediği doğru metodu bulup güncelleyin).
"""
import json, math, time, threading, logging, os, csv, hmac, hashlib, secrets, shutil
from datetime import datetime, timezone, timedelta
from pathlib import Path
from flask import Flask, request, jsonify, render_template_string, send_file
from binance.client import Client
from binance.exceptions import BinanceAPIException
import requests

logging.basicConfig(
    level=getattr(logging, os.environ.get('LOG_LEVEL', 'INFO').upper(), logging.INFO),
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[logging.StreamHandler()]
)
log = logging.getLogger(__name__)

app = Flask(__name__)

API_KEY          = os.environ.get('API_KEY', '')
API_SECRET       = os.environ.get('API_SECRET', '')
TELEGRAM_TOKEN   = os.environ.get('TELEGRAM_TOKEN', '')
TELEGRAM_CHAT_ID = os.environ.get('TELEGRAM_CHAT_ID', '')
TESTNET          = os.environ.get('TESTNET', 'False') == 'True'
WEBHOOK_SECRET   = os.environ.get('WEBHOOK_SECRET', '')
DASHBOARD_TOKEN  = os.environ.get('DASHBOARD_TOKEN', '')
TG_SECRET_TOKEN  = os.environ.get('TG_SECRET_TOKEN', '')

# ── Ayarlar ──────────────────────────────────────────────────────────────────
AYAR_SINIRLAR = {
    'LEVERAGE':                (1,   125),
    'RISK_PERCENT':            (0.1, 5.0),
    'MAX_OPEN_TRADES':         (1,   20),
    'MAX_GUNLUK_ISLEM':        (1,   50),
    'MAX_GUNLUK_ZARAR':        (0.1, 20.0),
    'DRAWDOWN_LIMIT':          (1.0, 30.0),
    'KOMISYON_ORAN':           (0.0001, 0.001),
    'EMA200_ALTI_MIN_MUM':     (24,  336),   # 1-14 gün (1sa mum) arası
    'PERCENT_TRAILING_MESAFE': (2.0, 20.0),
    'COOLDOWN_SURE':           (300, 86400),
    'SEMBOL_GUNLUK_MAX_KAYIP': (1,   10),
    'MAX_TOPLAM_RISK':         (1.0, 20.0),
}

AYARLAR = {
    'LEVERAGE':                int(os.environ.get('LEVERAGE', 3)),         # bot.py ile AYNI OLMALI (Hedge Mode, sembol bazlı paylaşılıyor)
    'RISK_PERCENT':            float(os.environ.get('RISK_PERCENT', 0.5)),
    'MAX_OPEN_TRADES':         int(os.environ.get('MAX_OPEN_TRADES', 5)),
    'MAX_GUNLUK_ISLEM':        int(os.environ.get('MAX_GUNLUK_ISLEM', 10)),
    'MAX_GUNLUK_ZARAR':        float(os.environ.get('MAX_GUNLUK_ZARAR', 5.0)),
    'DRAWDOWN_LIMIT':          float(os.environ.get('DRAWDOWN_LIMIT', 10.0)),
    'KOMISYON_ORAN':           float(os.environ.get('KOMISYON_ORAN', 0.0005)),
    # ⚠️ GEÇİCİ TEST DEĞERİ (2026-08-23): mekanizma testini (giriş+SL+
    # trailing) hızlandırmak için 72 yerine 2 — bu, DOĞRULANMIŞ strateji
    # değeri DEĞİL, backtest'te 72 (3 gün) kullanıldı ve doğrulandı.
    # CANLIYA ALMADAN ÖNCE MUTLAKA 72'YE GERİ DÖNDÜRÜN (ya da bu satırı
    # 'int(os.environ.get(...(...), 72))' haline getirin).
    'EMA200_ALTI_MIN_MUM':     int(os.environ.get('EMA200_ALTI_MIN_MUM', 2)),     # ⚠️ TEST DEĞERİ — GERÇEK: 72
    'PERCENT_TRAILING_MESAFE': float(os.environ.get('PERCENT_TRAILING_MESAFE', 7.0)),  # backtest'te doğrulanmış
    'COOLDOWN_SURE':           int(os.environ.get('COOLDOWN_SURE', 3600)),
    'SEMBOL_GUNLUK_MAX_KAYIP': int(os.environ.get('SEMBOL_GUNLUK_MAX_KAYIP', 2)),
    'MAX_TOPLAM_RISK':         float(os.environ.get('MAX_TOPLAM_RISK', 5.0)),
}

INTERVAL = '1h'   # backtest'te doğrulanmış zaman dilimi — SHORT bot'un 15dk'sından FARKLI
WARMUP_MUM = 250  # EMA200 ısınması için ekstra geçmiş mum

# 20 coin evreni — backtest_ema_htf.py ile AYNI (doğrulama bu evrende yapıldı)
# DENEY (2026-08-23, kullanıcı isteği): TESTNET'te mekanizma doğrulamasını
# HIZLANDIRMAK için sabit 20-coin listesi yerine DİNAMİK, hacme göre
# genişletilmiş bir evren kullanılıyor — bot.py'deki (SHORT)
# en_yuksek_hacimli_coinler() ile AYNI mantık/aynı EXCLUDE listesi.
# ÖNEMLİ: Bu SADECE testnet/mekanizma testi içindir — backtest_ema_htf.py'de
# doğrulanan strateji SADECE 20-coin evreninde test edildi. GERÇEK PARAYA
# geçerken SYMBOLS'u tekrar doğrulanmış 20-coin sabit listesine (aşağıda
# ORIJINAL_20_SYMBOLS olarak saklandı) döndürün — daha geniş evren
# stratejinin edge'inin geçerli olduğu kanıtlanmamış coinleri de içerir.
ORIJINAL_20_SYMBOLS = [
    "BTCUSDT", "ETHUSDT", "SOLUSDT", "BNBUSDT", "XRPUSDT",
    "ADAUSDT", "DOGEUSDT", "LINKUSDT", "AVAXUSDT", "LTCUSDT",
    "DOTUSDT", "MATICUSDT", "TRXUSDT", "ATOMUSDT", "NEARUSDT",
    "APTUSDT", "ARBUSDT", "OPUSDT", "SUIUSDT", "INJUSDT",
]

DINAMIK_COIN_EVRENI = True   # False yaparsanız ORIJINAL_20_SYMBOLS sabit listesi kullanılır
DUSUK_HACIM_USD_LONG = 30_000_000   # bot.py ile aynı eşik

# bot.py'deki EXCLUDE listesiyle AYNI — TradFi tokenize hisse/stabilcoin/
# bilinen sorunlu semboller (canlı SHORT tecrübesinden).
EXCLUDE_LONG = {
    'USDTUSDT','BUSDUSDT','USDCUSDT','TUSDUSDT','FDUSDUSDT',
    'BTCDOMUSDT','DEFIUSDT','BNBUSDT','SPCXUSDT','XAUUSDT','XAGUSDT',
    'MSTRUSDT','SKHYNIXUSDT','SNDKUSDT','SOXLUSDT','MUUSDT','KORUUSDT',
    'LABUSDT','CLUSDT','SKLUSDT','EVAAUSDT','CRCLUSDT','DRAMUSDT',
    'VELVETUSDT','DEXEUSDT','BZUSDT','TACUSDT','EWYUSDT','TAGUSDT',
    'USUSDT','SAMSUNGUSDT','SKHYUSDT','XPINUSDT','BUSDT',
    'MMTUSDT','ARBUSDT','VANRYUSDT',
    'QQQUSDT','NVDAUSDT','INTCUSDT','BILLUSDT','MRVLUSDT','ALLOUSDT',
    'GOOGLUSDT','TSLAUSDT','AMDUSDT','SOXSUSDT','AAPLUSDT','SPYUSDT','MSFTUSDT','METAUSDT','AMZNUSDT','ARMUSDT',
    'COINUSDT','HOODUSDT','GSUSDT','PYPLUSDT','DELLUSDT','AMATUSDT','IBMUSDT','NOKUSDT','SMHUSDT','BEUSDT',
    'AAOIUSDT','COHRUSDT',
}
ZAYIF_PERFORMANS_SEMBOLLER_LONG = {'IDOLUSDT', 'KAITOUSDT', 'HYPEUSDT'}

SYMBOLS = list(ORIJINAL_20_SYMBOLS)  # dinamik mod açıksa tarama_dongusu her döngüde bunu günceller

TARAMA_ARALIK = 300   # ana döngü aralığı (saniye) — 1sa stratejisi için 15dk'lık bot kadar sık taramaya gerek yok

# ── Bot durumu ────────────────────────────────────────────────────────────────
client = Client(API_KEY, API_SECRET, testnet=TESTNET)

# ══ HEDGE MODE DESTEĞİ (bkz. bot.py'deki aynı başlık, birebir aynı mantık) ═══
POZISYON_YONU = 'LONG'   # bu bot instance'ı SADECE bu tarafla ilgilenir

def _kendi_pozisyonum(p):
    return p.get('positionSide') == POZISYON_YONU

lock             = threading.Lock()
acik             = {}
gunluk_islem     = 0
gunluk_zarar     = 0.0
gunluk_net_kz    = 0.0
son_gun          = None
son_islem_zamani = {}
son_islem_cooldown = {}
sembol_gunluk_kayip = {}
baslangic_bakiye = 0.0
bot_durduruldu   = False

perf_ozet = {
    'toplam': 0, 'kazanan': 0, 'kaybeden': 0,
    'toplam_kz': 0.0, 'ort_kazanc': 0.0, 'ort_kayip': 0.0,
    'profit_factor': 0.0, 'win_rate': 0.0,
    'kazanc_toplam': 0.0, 'kayip_toplam': 0.0,
}

PERSIST_DIR = Path(os.environ.get('PERSIST_DIR', '.'))
try:
    PERSIST_DIR.mkdir(parents=True, exist_ok=True)
except Exception:
    pass

DURUM_DOSYA   = PERSIST_DIR / 'bot_long_durum.json'
JOURNAL_DOSYA = PERSIST_DIR / 'trade_long_journal.csv'
AYAR_DOSYA    = PERSIST_DIR / 'bot_long_ayarlar.json'

exchange_cache = {}; exchange_cache_zaman = 0; EXCHANGE_CACHE_SURE = 12*3600
pozisyonlar_cache = {}; pozisyonlar_cache_zaman = 0


# ════════════════════════════════════════════════════════════════════════════════
# GÜVENLİK (bot.py ile birebir aynı — değiştirilmedi)
# ════════════════════════════════════════════════════════════════════════════════

def webhook_dogrula(req):
    if not WEBHOOK_SECRET:
        return True
    try:
        imza      = req.headers.get('X-Signature', '')
        timestamp = req.headers.get('X-Timestamp', '')
        if not imza or not timestamp:
            return False
        if abs(time.time() - int(timestamp)) > 60:
            return False
        mesaj    = f"{timestamp}.{req.get_data(as_text=True)}"
        beklenen = hmac.new(WEBHOOK_SECRET.encode(), mesaj.encode(), hashlib.sha256).hexdigest()
        return hmac.compare_digest(imza, beklenen)
    except Exception as e:
        log.error(f"HMAC hatasi: {e}"); return False

def telegram_dogrula(req):
    if not TG_SECRET_TOKEN:
        return True
    return req.headers.get('X-Telegram-Bot-Api-Secret-Token', '') == TG_SECRET_TOKEN

def dashboard_dogrula(req):
    if not DASHBOARD_TOKEN:
        return True
    token = req.args.get('token') or req.headers.get('X-Dashboard-Token', '')
    return token == DASHBOARD_TOKEN

def ayar_dogrula(anahtar, deger_str):
    if anahtar not in AYARLAR:
        return None, f"Bilinmeyen ayar: {anahtar}"
    eski  = AYARLAR[anahtar]
    sinir = AYAR_SINIRLAR.get(anahtar)
    try:
        yeni = type(eski)(deger_str)
    except (ValueError, TypeError):
        return None, f"Geçersiz tip: {deger_str} ({type(eski).__name__} bekleniyor)"
    if sinir:
        mn, mx = sinir
        if not (mn <= yeni <= mx):
            return None, f"Sınır dışı: {yeni} ({mn}–{mx} arası olmalı)"
    return yeni, None


# ════════════════════════════════════════════════════════════════════════════════
# ÇÖKÜŞ KORUMA (bot.py ile aynı desen, dosya adları farklı)
# ════════════════════════════════════════════════════════════════════════════════

def durum_kaydet():
    with lock:
        acik_kopya = {k: dict(v) for k, v in acik.items()}
        islem_kopya = gunluk_islem
        zarar_kopya = gunluk_zarar
        net_kz_kopya = gunluk_net_kz
        son_islem_zamani_kopya = dict(son_islem_zamani)
        son_islem_cooldown_kopya = dict(son_islem_cooldown)
        sembol_gunluk_kayip_kopya = dict(sembol_gunluk_kayip)
    try:
        veri = {
            'acik': acik_kopya, 'gunluk_islem': islem_kopya, 'gunluk_zarar': zarar_kopya,
            'gunluk_net_kz': net_kz_kopya, 'son_gun': str(son_gun),
            'baslangic_bakiye': baslangic_bakiye,
            'son_islem_zamani': son_islem_zamani_kopya,
            'son_islem_cooldown': son_islem_cooldown_kopya,
            'sembol_gunluk_kayip': sembol_gunluk_kayip_kopya,
        }
        DURUM_DOSYA.write_text(json.dumps(veri, default=str), encoding='utf-8')
    except Exception as e:
        log.error(f"Durum kaydetme hatasi: {e}")

def durum_yukle():
    global acik, gunluk_islem, gunluk_zarar, gunluk_net_kz, son_gun, baslangic_bakiye
    global son_islem_zamani, son_islem_cooldown, sembol_gunluk_kayip
    if not DURUM_DOSYA.exists(): return
    try:
        veri = json.loads(DURUM_DOSYA.read_text(encoding='utf-8'))
        acik = veri.get('acik', {})
        gunluk_islem = veri.get('gunluk_islem', 0)
        gunluk_zarar = veri.get('gunluk_zarar', 0.0)
        gunluk_net_kz = veri.get('gunluk_net_kz', 0.0)
        baslangic_bakiye = veri.get('baslangic_bakiye', 0.0)
        son_islem_zamani = {k: float(v) for k, v in veri.get('son_islem_zamani', {}).items()}
        son_islem_cooldown = {k: float(v) for k, v in veri.get('son_islem_cooldown', {}).items()}
        sembol_gunluk_kayip = {k: int(v) for k, v in veri.get('sembol_gunluk_kayip', {}).items()}
        gun_str = veri.get('son_gun', '')
        if gun_str and gun_str != 'None':
            son_gun = datetime.strptime(gun_str, '%Y-%m-%d').date()
        log.info(f"Durum yuklendi: {len(acik)} acik pozisyon")
        tg(f"♻️ LONG BOT YENİDEN BAŞLADI\n{len(acik)} pozisyon geri yüklendi\n" +
           '\n'.join([f"  {s} giriş:{i['entry']} en_yuksek:{i.get('en_yuksek_fiyat', i['entry'])}"
                      for s, i in acik.items()]))
    except Exception as e:
        log.error(f"Durum yukleme hatasi: {e}")

def ayarlar_kaydet():
    try:
        AYAR_DOSYA.write_text(json.dumps(AYARLAR), encoding='utf-8')
    except Exception as e:
        log.error(f"Ayarlar kaydetme hatasi: {e}")

def ayarlar_yukle():
    if not AYAR_DOSYA.exists():
        return
    try:
        kayitli = json.loads(AYAR_DOSYA.read_text(encoding='utf-8'))
        degisen = []
        for anahtar, deger in kayitli.items():
            if anahtar not in AYARLAR:
                continue
            try:
                AYARLAR[anahtar] = type(AYARLAR[anahtar])(deger)
                degisen.append(anahtar)
            except (ValueError, TypeError):
                log.warning(f"Ayar yukleme: {anahtar} icin gecersiz deger atlandi: {deger}")
        if degisen:
            log.info(f"Kayitli ayarlar geri yuklendi: {', '.join(degisen)}")
    except Exception as e:
        log.error(f"Ayarlar yukleme hatasi: {e}")


# ════════════════════════════════════════════════════════════════════════════════
# TRADE JOURNAL (bot.py ile aynı desen; TP1/TP2/rejim/adx alanları yok — bu
# stratejide yok, sadece trailing SL var)
# ════════════════════════════════════════════════════════════════════════════════

def _perf_guncelle(kz):
    perf_ozet['toplam'] += 1
    perf_ozet['toplam_kz'] = round(perf_ozet['toplam_kz'] + kz, 4)
    if kz >= 0:
        perf_ozet['kazanan'] += 1; perf_ozet['kazanc_toplam'] += kz
    else:
        perf_ozet['kaybeden'] += 1; perf_ozet['kayip_toplam'] += abs(kz)
    t = perf_ozet['toplam']
    perf_ozet['win_rate']   = round(perf_ozet['kazanan'] / t * 100, 1) if t else 0
    perf_ozet['ort_kazanc'] = round(perf_ozet['kazanc_toplam'] / max(perf_ozet['kazanan'], 1), 2)
    perf_ozet['ort_kayip']  = round(perf_ozet['kayip_toplam']  / max(perf_ozet['kaybeden'], 1), 2)
    pf_pay = perf_ozet['kazanc_toplam']; pf_pay2 = perf_ozet['kayip_toplam']
    perf_ozet['profit_factor'] = round(pf_pay / pf_pay2, 2) if pf_pay2 > 0 else 999.0

def perf_baslangic_yukle():
    if not JOURNAL_DOSYA.exists(): return
    try:
        with open(JOURNAL_DOSYA, 'r', encoding='utf-8') as f:
            for row in csv.DictReader(f):
                try:
                    _perf_guncelle(float(row['kar_zarar_usdt']))
                except: pass
        log.info(f"Journal yuklendi: {perf_ozet['toplam']} islem")
    except Exception as e:
        log.error(f"Journal yukleme hatasi: {e}")

def journal_baslik_yaz():
    if not JOURNAL_DOSYA.exists():
        with open(JOURNAL_DOSYA, 'w', newline='', encoding='utf-8') as f:
            csv.writer(f).writerow([
                'tarih', 'symbol', 'giris', 'kapanis', 'en_yuksek_fiyat', 'sl_son',
                'miktar', 'kar_zarar_usdt', 'kar_zarar_yuzde', 'sebep',
            ])

def journal_sifirla():
    global perf_ozet
    yedek_adi = None
    if JOURNAL_DOSYA.exists():
        yedek_adi = f"trade_long_journal_yedek_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        yedek_yolu = PERSIST_DIR / yedek_adi
        try:
            shutil.move(str(JOURNAL_DOSYA), str(yedek_yolu))
        except Exception as e:
            log.error(f"Journal yedekleme hatasi: {e}")
            raise
    perf_ozet.update({
        'toplam': 0, 'kazanan': 0, 'kaybeden': 0, 'toplam_kz': 0.0,
        'ort_kazanc': 0.0, 'ort_kayip': 0.0, 'profit_factor': 0.0, 'win_rate': 0.0,
        'kazanc_toplam': 0.0, 'kayip_toplam': 0.0,
    })
    journal_baslik_yaz()
    return yedek_adi

def journal_yaz(symbol, islem, kapanis_fiyat, sebep):
    global sembol_gunluk_kayip
    try:
        giris = islem.get('entry', 0)
        m = islem.get('q', 0)
        kz = (kapanis_fiyat - giris) * m
        kz_y = (kz / (giris * m) * 100) if giris * m > 0 else 0
        with open(JOURNAL_DOSYA, 'a', newline='', encoding='utf-8') as f:
            csv.writer(f).writerow([
                datetime.now().strftime('%Y-%m-%d %H:%M:%S'), symbol,
                round(giris, 6), round(kapanis_fiyat, 6),
                round(islem.get('en_yuksek_fiyat', giris), 6), round(islem.get('sl', 0), 6),
                m, round(kz, 4), round(kz_y, 2), sebep,
            ])
        if kz < 0:
            with lock:
                sembol_gunluk_kayip[symbol] = sembol_gunluk_kayip.get(symbol, 0) + 1
                sayac = sembol_gunluk_kayip[symbol]
            if sayac == AYARLAR['SEMBOL_GUNLUK_MAX_KAYIP']:
                log.warning(f"{symbol}: gunluk kayip esigine ulasildi ({sayac})")
                tg(f"🚫 {symbol} DEVRE DIŞI (LONG)\nBugün {sayac}. kayıp — gün sonuna kadar yeni işlem yok")
        _perf_guncelle(kz)
    except Exception as e:
        log.error(f"Journal yazma hatasi: {e}")


# ════════════════════════════════════════════════════════════════════════════════
# EXCHANGE (bot.py ile aynı)
# ════════════════════════════════════════════════════════════════════════════════

def exchange_info_al():
    global exchange_cache, exchange_cache_zaman
    simdi = time.time()
    if simdi - exchange_cache_zaman < EXCHANGE_CACHE_SURE and exchange_cache:
        return exchange_cache
    try:
        bilgi = client.futures_exchange_info()
        yeni = {}
        for s in bilgi['symbols']:
            sym = s['symbol']
            fp = lp = 2; step = 0.01; min_notional = 5.0
            for f in s['filters']:
                if f['filterType'] == 'PRICE_FILTER':
                    t = f"{float(f['tickSize']):.8f}".rstrip('0')
                    fp = len(t.split('.')[-1]) if '.' in t else 0
                elif f['filterType'] == 'LOT_SIZE':
                    step = float(f['stepSize'])
                    t = f"{step:.8f}".rstrip('0')
                    lp = len(t.split('.')[-1]) if '.' in t else 0
                elif f['filterType'] == 'MIN_NOTIONAL':
                    min_notional = float(f.get('notional', 5))
            yeni[sym] = {'fp': fp, 'lp': lp, 'step': step, 'min_notional': min_notional}
        exchange_cache = yeni; exchange_cache_zaman = simdi
        return exchange_cache
    except Exception as e:
        log.error(f"Exchange info hatasi: {e}"); return exchange_cache

def precision_al(symbol):
    c = exchange_info_al()
    return (c[symbol]['fp'], c[symbol]['lp']) if symbol in c else (2, 2)

def tg(m):
    try:
        requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                      data={"chat_id": TELEGRAM_CHAT_ID, "text": m}, timeout=10)
    except Exception as e:
        log.error(f"Telegram hatasi: {e}")

def bakiye():
    try:
        return float(client.futures_account()['availableBalance'])
    except Exception as e:
        log.error(f"Bakiye hatasi: {e}"); return 0.0

def efektif_risk_percent():
    b = bakiye()
    if baslangic_bakiye <= 0: return AYARLAR['RISK_PERCENT']
    dd = (baslangic_bakiye - b) / baslangic_bakiye * 100
    return AYARLAR['RISK_PERCENT'] * 0.5 if dd >= AYARLAR['DRAWDOWN_LIMIT'] else AYARLAR['RISK_PERCENT']

def toplam_acik_risk():
    b = bakiye()
    if b <= 0: return 0
    with lock:
        toplam = sum(abs(i['entry'] - i['sl']) * i['q']
                     for i in acik.values() if i.get('sl', 0) > 0 and i.get('entry', 0) > 0)
    return (toplam / b) * 100

def miktar_hesapla(symbol, fiyat, sl_fiyat, kaldirac=None):
    try:
        cache = exchange_info_al()
        b = bakiye()
        risk_usdt = b * efektif_risk_percent() / 100
        sl_m = abs(fiyat - sl_fiyat) - fiyat * AYARLAR['KOMISYON_ORAN'] * 2
        if sl_m <= 0: return 0
        m = risk_usdt / sl_m
        lev = kaldirac or AYARLAR['LEVERAGE']
        max_m = (b * 0.20 * lev) / fiyat
        if m > max_m: m = max_m
        if symbol in cache:
            step = cache[symbol]['step']; mn = cache[symbol]['min_notional']
            m = math.floor(m / step) * step
            if m * fiyat < mn: m = math.ceil(mn / fiyat / step) * step
            if step >= 1: return max(1, int(m))
            return round(m, cache[symbol]['lp'])
        return round(m, 2)
    except Exception as e:
        log.error(f"Miktar hatasi: {e}"); return 0

def _order_id(prefix, symbol):
    return f"{prefix}_{symbol}_{int(time.time()*1000)}"

def binance_emir_gonder(fn, idempotency_prefix=None, sym_key=None, **kwargs):
    """bot.py ile aynı idempotency mantığı."""
    order_id = None
    if idempotency_prefix and sym_key:
        order_id = _order_id(idempotency_prefix, sym_key)
        id_param = 'newClientAlgoId' if fn == client.futures_create_algo_order else 'newClientOrderId'
        if id_param not in kwargs:
            kwargs[id_param] = order_id
    for deneme in range(3):
        try:
            return fn(**kwargs)
        except BinanceAPIException as e:
            if e.code == -2010 and order_id:
                log.info(f"Idempotent emir zaten mevcut: {order_id}")
                return None
            if e.code in [-1001, -1007] and deneme < 2:
                time.sleep(1)
            else:
                raise
        except Exception as e:
            if deneme < 2:
                log.warning(f"Emir retry ({deneme+1}/3): {e}")
                time.sleep(1)
            else:
                raise

def dinamik_kaldirac(symbol):
    """
    HEDGE MODE GÜVENLİK: SABİT, bot.py ile AYNI kaldıraç kullanılıyor —
    kaldıraç sembol bazında paylaşılır, bu bot farklı bir değer set ederse
    SHORT bot'un açık pozisyonunun kaldıracını da değiştirebilir.
    """
    lev = AYARLAR['LEVERAGE']
    try:
        client.futures_change_leverage(symbol=symbol, leverage=lev)
    except Exception as e:
        log.error(f"Kaldirac hatasi {symbol}: {e}")
    return lev


# ════════════════════════════════════════════════════════════════════════════════
# EMİR YÖNETİMİ (bot.py'deki Hedge Mode güvenli mekanizmanın birebir aynısı)
# ════════════════════════════════════════════════════════════════════════════════

def _guvenli_emir_iptal(symbol):
    try:
        emirler = client.futures_get_open_orders(symbol=symbol)
    except Exception as e:
        log.debug(f"{symbol}: acik emir listesi alma hatasi (normal): {e}")
        return
    for o in emirler:
        if o.get('positionSide') == POZISYON_YONU:
            try:
                client.futures_cancel_order(symbol=symbol, orderId=o['orderId'])
            except Exception as e:
                log.debug(f"{symbol}: emir iptal hatasi (orderId={o.get('orderId')}): {e}")

def _guvenli_conditional_emir_iptal(symbol):
    try:
        emirler = client.futures_get_open_orders(symbol=symbol, conditional=True)
    except Exception as e:
        log.debug(f"{symbol}: acik emir listesi alma hatasi (conditional): {e}")
        return
    for o in emirler:
        if o.get('positionSide') == POZISYON_YONU:
            try:
                client.futures_cancel_order(symbol=symbol, orderId=o['orderId'], conditional=True)
            except Exception as e:
                log.debug(f"{symbol}: conditional emir iptal hatasi (orderId={o.get('orderId')}): {e}")

def _guvenli_algo_emir_iptal(symbol):
    """DİKKAT: bkz. dosya başındaki 'CANLIYA ALMADAN ÖNCE' notu — metod adı
    python-binance sürümüne göre değişebilir, testnet'te doğrulayın."""
    try:
        emirler = client.futures_get_open_orders(symbol=symbol, conditional=True)
    except Exception as e:
        log.debug(f"{symbol}: acik algo emir listesi alma hatasi: {e}")
        return
    for o in emirler:
        if o.get('positionSide') == POZISYON_YONU:
            algo_id = o.get('algoId') or o.get('orderId')
            try:
                client.futures_cancel_algo_order(symbol=symbol, algoId=algo_id)
            except Exception as e:
                log.debug(f"{symbol}: algo emir iptal hatasi (algoId={algo_id}): {e}")

def _stale_emirleri_temizle(symbol):
    _guvenli_emir_iptal(symbol)
    _guvenli_conditional_emir_iptal(symbol)
    _guvenli_algo_emir_iptal(symbol)

def _conditional_emri_gonder(symbol, side, tip, tetik_fiyat, quantity=None, close_position=False,
                              idempotency_prefix=None, position_side=None):
    """bot.py ile birebir aynı — yeni Algo Order API'sini dener, olmazsa
    eski API'ye düşer. Hedge Mode: reduceOnly YOK, positionSide ZORUNLU."""
    params = {'symbol': symbol, 'side': side, 'type': tip, 'triggerPrice': tetik_fiyat}
    if position_side:
        params['positionSide'] = position_side
    if close_position:
        params['closePosition'] = True
    elif quantity is not None:
        params['quantity'] = quantity
    try:
        return binance_emir_gonder(client.futures_create_algo_order,
                                   idempotency_prefix=idempotency_prefix, sym_key=symbol, **params)
    except Exception as e:
        log.warning(f"{symbol}: futures_create_algo_order basarisiz ({e}), eski API'ye dusuluyor...")
        eski_params = {'symbol': symbol, 'side': side, 'type': tip, 'stopPrice': tetik_fiyat}
        if position_side:
            eski_params['positionSide'] = position_side
        if close_position:
            eski_params['closePosition'] = True
        elif quantity is not None:
            eski_params['quantity'] = quantity
        return binance_emir_gonder(client.futures_create_order,
                                   idempotency_prefix=idempotency_prefix, sym_key=symbol, **eski_params)

def _fill_fiyati_al(order, symbol):
    try:
        avg = float((order or {}).get('avgPrice', 0) or 0)
        if avg > 0:
            return avg
        trades = client.futures_account_trades(symbol=symbol, limit=1)
        if trades:
            return float(trades[-1]['price'])
    except Exception as e:
        log.error(f"Fill fiyati alma hatasi {symbol}: {e}")
    return float(client.futures_symbol_ticker(symbol=symbol)['price'])


# ════════════════════════════════════════════════════════════════════════════════
# TEKNİK İNDİKATÖRLER
# ════════════════════════════════════════════════════════════════════════════════

def ema_hesapla(fiyatlar, periyot):
    if len(fiyatlar) < periyot: return None
    k = 2 / (periyot + 1)
    ema = sum(fiyatlar[:periyot]) / periyot
    for f in fiyatlar[periyot:]:
        ema = f * k + ema * (1 - k)
    return ema

def ema_serisi(fiyatlar, periyot):
    """Her nokta için EMA değerini döndürür (tek bir sayı değil, dizi) —
    'fiyat kaç mumdur EMA200 altında' kontrolü için gerekli."""
    n = len(fiyatlar)
    if n < periyot:
        return [None] * n
    k = 2 / (periyot + 1)
    sonuc = [None] * (periyot - 1)
    ema = sum(fiyatlar[:periyot]) / periyot
    sonuc.append(ema)
    for i in range(periyot, n):
        ema = fiyatlar[i] * k + ema * (1 - k)
        sonuc.append(ema)
    return sonuc


# ════════════════════════════════════════════════════════════════════════════════
# POZİSYON YÖNETİMİ
# ════════════════════════════════════════════════════════════════════════════════

def buy(symbol, fiyat):
    global gunluk_islem
    if POZISYON_YONU != 'LONG':
        return  # güvenlik — bu bot her zaman LONG olmalı, savunma amaçlı
    if bot_durduruldu:
        log.info(f"{symbol} sinyali atlandi: bot durduruldu")
        return

    with lock:
        if symbol in acik:
            return
        if len(acik) >= AYARLAR['MAX_OPEN_TRADES']:
            log.info(f"{symbol} sinyali atlandi: MAX_OPEN_TRADES doldu")
            return
        if gunluk_islem >= AYARLAR['MAX_GUNLUK_ISLEM']:
            log.info(f"{symbol} sinyali atlandi: MAX_GUNLUK_ISLEM doldu")
            return
        if time.time() - son_islem_zamani.get(symbol, 0) < son_islem_cooldown.get(symbol, AYARLAR['COOLDOWN_SURE']):
            log.info(f"{symbol} cooldown"); return
        if sembol_gunluk_kayip.get(symbol, 0) >= AYARLAR['SEMBOL_GUNLUK_MAX_KAYIP']:
            log.info(f"{symbol} gunluk kayip esigi asildi"); return
        acik[symbol] = {'_rezerve': True}
        gunluk_net_kz_kopya = gunluk_net_kz

    try:
        if gunluk_net_kz_kopya <= -bakiye() * AYARLAR['MAX_GUNLUK_ZARAR'] / 100:
            log.info(f"{symbol} sinyali atlandi: MAX_GUNLUK_ZARAR limiti doldu")
            with lock: acik.pop(symbol, None)
            return
        if toplam_acik_risk() >= AYARLAR['MAX_TOPLAM_RISK']:
            log.info(f"{symbol} sinyali atlandi: MAX_TOPLAM_RISK doldu")
            with lock: acik.pop(symbol, None)
            return

        fp, lp = precision_al(symbol)
        mesafe_yuzde = AYARLAR['PERCENT_TRAILING_MESAFE'] / 100
        sl = fiyat * (1 - mesafe_yuzde)

        lev = dinamik_kaldirac(symbol)
        m = miktar_hesapla(symbol, fiyat, sl, lev)
        if m <= 0:
            log.info(f"{symbol} sinyali atlandi: hesaplanan miktar gecersiz (m={m})")
            with lock: acik.pop(symbol, None); return

        order = binance_emir_gonder(client.futures_create_order,
                                    idempotency_prefix='BUY_L', sym_key=symbol,
                                    symbol=symbol, side='BUY', type='MARKET', quantity=m,
                                    positionSide='LONG')
        gercek = _fill_fiyati_al(order, symbol)

        _stale_emirleri_temizle(symbol)

        sl_gercek = gercek * (1 - mesafe_yuzde)
        try:
            _conditional_emri_gonder(symbol, 'SELL', 'STOP_MARKET', round(sl_gercek, fp),
                                     close_position=True, idempotency_prefix='SL_L',
                                     position_side='LONG')
            log.info(f"SL emri gonderildi {symbol}: {round(sl_gercek, fp)}")
        except Exception as e:
            log.error(f"SL hatasi {symbol}: {e}")
            _guvenli_emir_iptal(symbol)
            client.futures_create_order(symbol=symbol, side='SELL', type='MARKET', quantity=m,
                                        positionSide='LONG')
            with lock: acik.pop(symbol, None)
            tg(f"⚠ {symbol} (LONG) SL gonderilemedi, kapatildi!"); return

        with lock:
            acik[symbol] = {
                'entry': gercek, 'sl': sl_gercek, 'en_yuksek_fiyat': gercek,
                'q': m, 'lev': lev, 'acilis_zaman': int(time.time() * 1000),
            }
            gunluk_islem += 1
            son_islem_zamani[symbol] = time.time()
        durum_kaydet()
        tg(f"✅ LONG {symbol}\nGiriş:{gercek} SL(%{AYARLAR['PERCENT_TRAILING_MESAFE']}):{round(sl_gercek,fp)}\n"
           f"Kaldıraç:{lev}x Miktar:{m}")
    except BinanceAPIException as e:
        log.error(f"BUY hata {symbol}: {e}")
        with lock: acik.pop(symbol, None)
    except Exception as e:
        log.error(f"BUY beklenmedik hata {symbol}: {e}")
        with lock: acik.pop(symbol, None)


def kapat(symbol, sebep="EXIT"):
    global gunluk_zarar, gunluk_net_kz
    with lock:
        if symbol not in acik or acik[symbol].get('_rezerve'): return
        i = acik[symbol]
    try:
        _guvenli_emir_iptal(symbol)
        _guvenli_conditional_emir_iptal(symbol)
        _guvenli_algo_emir_iptal(symbol)
        client.futures_create_order(symbol=symbol, side='SELL', type='MARKET', quantity=i['q'],
                                    positionSide='LONG')
        try:
            kp = float(client.futures_symbol_ticker(symbol=symbol)['price'])
            kz = (kp - i['entry']) * i['q']
            if kz < 0:
                with lock: gunluk_zarar += abs(kz)
            with lock: gunluk_net_kz += kz
            journal_yaz(symbol, i, kp, sebep)
        except Exception as e:
            log.error(f"Kapanis KZ hatasi {symbol}: {e}")

        with lock:
            acik.pop(symbol, None)
            son_islem_zamani[symbol] = time.time()
            son_islem_cooldown[symbol] = AYARLAR['COOLDOWN_SURE']
        durum_kaydet()
        tg(f"🔴 KAPANDI (LONG) {symbol}\n{sebep}\nGiriş:{i['entry']}")
    except BinanceAPIException as e:
        log.error(f"Kapatma hata {symbol}: {e}")


def trailing_guncelle(pozisyonlar=None):
    """
    Bu stratejinin KALBİ — sabit TP/breakeven yerine SÜREKLİ trailing.
    Her açık pozisyon için: güncel fiyatı kontrol et, en_yuksek_fiyat'ı
    güncelle, yeni SL (en_yuksek_fiyat * (1-%mesafe)) mevcut SL'den daha
    sıkıysa, ESKİ SL emrini iptal edip YENİ SL emrini gönder.
    """
    if pozisyonlar is None:
        pozisyonlar = pozisyonlar_cache
    with lock:
        islemler = list(acik.items())
    mesafe_yuzde = AYARLAR['PERCENT_TRAILING_MESAFE'] / 100
    for symbol, islem in islemler:
        if islem.get('_rezerve'): continue
        p = pozisyonlar.get(symbol)
        if not p:
            continue
        try:
            mark = float(p['markPrice'])
            en_yuksek_eski = islem.get('en_yuksek_fiyat', islem['entry'])
            en_yuksek_yeni = max(en_yuksek_eski, mark)
            if en_yuksek_yeni <= en_yuksek_eski:
                continue  # yeni zirve yok, SL'i tekrar gondermeye gerek yok
            yeni_sl = en_yuksek_yeni * (1 - mesafe_yuzde)
            if yeni_sl <= islem.get('sl', 0):
                with lock:
                    if symbol in acik:
                        acik[symbol]['en_yuksek_fiyat'] = en_yuksek_yeni
                continue  # yeni zirve var ama SL'i anlamli miktarda sikilastirmiyor

            fp, _ = precision_al(symbol)
            _guvenli_emir_iptal(symbol)
            _guvenli_conditional_emir_iptal(symbol)
            _guvenli_algo_emir_iptal(symbol)
            time.sleep(0.5)
            try:
                _conditional_emri_gonder(symbol, 'SELL', 'STOP_MARKET', round(yeni_sl, fp),
                                         close_position=True, idempotency_prefix='TRAIL_L',
                                         position_side='LONG')
                with lock:
                    if symbol in acik:
                        acik[symbol]['sl'] = yeni_sl
                        acik[symbol]['en_yuksek_fiyat'] = en_yuksek_yeni
                durum_kaydet()
                log.info(f"{symbol}: trailing SL guncellendi -> {round(yeni_sl,fp)} (en yuksek: {round(en_yuksek_yeni,fp)})")
            except Exception as e:
                log.error(f"{symbol}: trailing SL gonderme hatasi: {e} — pozisyon GEÇİCİ olarak SL'siz kalmış olabilir!")
                tg(f"⚠️ {symbol} (LONG) trailing SL güncellenemedi — LÜTFEN KONTROL EDİN")
        except Exception as e:
            log.error(f"Trailing guncelleme hatasi {symbol}: {e}")


def binance_senkronize():
    """bot.py'deki ile aynı desen — Binance'te kapanmış (SL'e takılmış)
    pozisyonları tespit edip journal'a yazar, HEDGE MODE filtreli."""
    global gunluk_zarar, gunluk_net_kz
    try:
        binance_poz = {p['symbol'] for p in client.futures_position_information()
                       if _kendi_pozisyonum(p) and float(p['positionAmt']) != 0}
        open_orders = [o for o in client.futures_get_open_orders() if o.get('positionSide') == POZISYON_YONU]
        conditional_open_orders = [o for o in client.futures_get_open_orders(conditional=True)
                                   if o.get('positionSide') == POZISYON_YONU]
        open_symbols = {e['symbol'] for e in open_orders + conditional_open_orders}

        with lock:
            kapananlar = [s for s, i in acik.items() if s not in binance_poz and not i.get('_rezerve')]
        for sym in kapananlar:
            _guvenli_emir_iptal(sym)
            _guvenli_conditional_emir_iptal(sym)
            _guvenli_algo_emir_iptal(sym)
            try:
                islem = acik.get(sym, {})
                isle = client.futures_account_trades(symbol=sym, limit=5)
                if isle:
                    kp = float(isle[-1]['price'])
                    kz = (kp - islem.get('entry', kp)) * islem.get('q', 0)
                    if kz < 0:
                        with lock: gunluk_zarar += abs(kz)
                    with lock: gunluk_net_kz += kz
                    journal_yaz(sym, islem, kp, 'TRAILING_SL')
                    emoji = "💰" if kz >= 0 else "🔴"
                    tg(f"{emoji} SL'e takıldı (LONG): {sym}\nGiriş:{islem.get('entry','?')}\nKapanış:{kp}\nK/Z:{round(kz,2)} USDT")
                else:
                    tg(f"💰 SL'e takıldı (LONG): {sym}")
            except Exception as e:
                log.error(f"KZ hesap hatasi {sym}: {e}")
            with lock:
                acik.pop(sym, None)
        durum_kaydet()

        for sym in open_symbols:
            if sym not in binance_poz:
                _guvenli_emir_iptal(sym)
                _guvenli_conditional_emir_iptal(sym)
                _guvenli_algo_emir_iptal(sym)
    except Exception as e:
        log.error(f"Senkron hatasi: {e}")


def pozisyonlar_al():
    global pozisyonlar_cache, pozisyonlar_cache_zaman
    try:
        pozisyonlar_cache = {p['symbol']: p for p in client.futures_position_information()
                             if _kendi_pozisyonum(p) and float(p['positionAmt']) != 0}
        pozisyonlar_cache_zaman = time.time()
        return pozisyonlar_cache
    except Exception as e:
        log.error(f"Pozisyon yükleme hatasi: {e}")
        return {}


# ════════════════════════════════════════════════════════════════════════════════
# STRATEJİ — "EMA200 DÖNÜŞÜ"
# ════════════════════════════════════════════════════════════════════════════════

def en_yuksek_hacimli_coinler_long():
    """bot.py'deki en_yuksek_hacimli_coinler() ile AYNI mantık — TESTNET
    mekanizma testini hızlandırmak için MAX_COIN yerine sabit, oldukça
    geniş bir üst sınır (80) kullanıyor. DUSUK_HACIM_USD_LONG altındaki
    ve EXCLUDE_LONG/ZAYIF_PERFORMANS_SEMBOLLER_LONG'daki semboller elenir."""
    try:
        coins = []
        for t in client.futures_ticker():
            sym = t['symbol']
            if not sym.endswith('USDT') or sym in EXCLUDE_LONG or sym in ZAYIF_PERFORMANS_SEMBOLLER_LONG:
                continue
            h = float(t['quoteVolume'])
            if h < DUSUK_HACIM_USD_LONG:
                continue
            coins.append({'symbol': sym, 'hacim': h})
        coins.sort(key=lambda x: x['hacim'], reverse=True)
        sonuc = [c['symbol'] for c in coins[:80]]
        log.info(f"Dinamik coin evreni güncellendi: {len(sonuc)} sembol")
        return sonuc
    except Exception as e:
        log.error(f"Dinamik coin evreni hatasi: {e}")
        return list(ORIJINAL_20_SYMBOLS)  # hata olursa güvenli/bilinen listeye düş


def strateji_kontrol(symbol):
    """
    Giriş: fiyat en az EMA200_ALTI_MIN_MUM ardışık 1sa mum boyunca EMA200
    altında kalmış, SONRA 2 ardışık mum EMA200 üzerinde kapanmış → LONG.
    """
    try:
        with lock:
            sym_acik = symbol in acik and not acik[symbol].get('_rezerve')
        if sym_acik:
            return  # zaten pozisyon var, yeni giris aranmiyor

        mumlar = client.futures_klines(symbol=symbol, interval=INTERVAL,
                                       limit=AYARLAR['EMA200_ALTI_MIN_MUM'] + 210)
        if len(mumlar) < 210:
            return
        kapanis = [float(m[4]) for m in mumlar[:-1]]  # son (kapanmamis) mumu haric tut
        ema200_serisi = ema_serisi(kapanis, 200)
        if ema200_serisi[-1] is None or ema200_serisi[-2] is None:
            return

        n = len(kapanis)
        iki_mum_ustunde = (kapanis[-1] > ema200_serisi[-1]) and (kapanis[-2] > ema200_serisi[-2])
        if not iki_mum_ustunde:
            return

        ardisik_altinda = 0
        j = n - 3
        while j >= 0 and ema200_serisi[j] is not None and kapanis[j] < ema200_serisi[j]:
            ardisik_altinda += 1
            j -= 1

        if ardisik_altinda < AYARLAR['EMA200_ALTI_MIN_MUM']:
            log.debug(f"{symbol}: donus var ama sadece {ardisik_altinda} mum EMA200 altindaydi "
                      f"(gerekli: {AYARLAR['EMA200_ALTI_MIN_MUM']})")
            return

        fiyat = kapanis[-1]
        log.info(f"LONG sinyali: {symbol}@{fiyat} ({ardisik_altinda} mum EMA200 altindan donus)")
        buy(symbol, fiyat)
    except Exception as e:
        log.error(f"Strateji hatasi {symbol}: {e}")


# ════════════════════════════════════════════════════════════════════════════════
# ANA DÖNGÜ
# ════════════════════════════════════════════════════════════════════════════════

def tarama_dongusu():
    global gunluk_islem, gunluk_zarar, gunluk_net_kz, son_gun, baslangic_bakiye, SYMBOLS
    son_gun = datetime.now().date(); baslangic_bakiye = bakiye()
    journal_baslik_yaz(); perf_baslangic_yukle()
    log.info("LONG bot tarama dongusu basladi, 60 saniye bekleniyor...")
    time.sleep(60)
    _test_uyarisi = ""
    if AYARLAR['EMA200_ALTI_MIN_MUM'] != 72:
        _test_uyarisi = (f"\n\n⚠️⚠️⚠️ TEST MODU AKTİF ⚠️⚠️⚠️\n"
                         f"EMA200_ALTI_MIN_MUM={AYARLAR['EMA200_ALTI_MIN_MUM']} — DOĞRULANMIŞ DEĞER DEĞİL (gerçek: 72)!\n"
                         f"Bu SADECE mekanizma testi içindir — sonuçlar strateji kalitesini YANSITMAZ.\n"
                         f"CANLIYA ALMADAN ÖNCE bu değeri 72'ye geri döndürün!")
        log.warning(f"TEST MODU: EMA200_ALTI_MIN_MUM={AYARLAR['EMA200_ALTI_MIN_MUM']} (doğrulanmış değer: 72) — CANLIYA ALMADAN ÖNCE DÜZELTİN!")
    tg(f"🤖 LONG BOT BAŞLADI\nBakiye:{bakiye()} USDT Kaldıraç:{AYARLAR['LEVERAGE']}x\n"
       f"Risk:%{AYARLAR['RISK_PERCENT']} Trailing:%{AYARLAR['PERCENT_TRAILING_MESAFE']}\n"
       f"Strateji: EMA200 dönüşü ({AYARLAR['EMA200_ALTI_MIN_MUM']} saat) — 1sa zaman dilimi"
       f"{_test_uyarisi}")
    while True:
        try:
            bugun = datetime.now().date()
            if bugun != son_gun:
                with lock: is_say = gunluk_islem; acik_say = len(acik)
                b = bakiye(); kz = round(b - baslangic_bakiye, 2)
                p = perf_ozet
                tg(f"📊 LONG GÜNLÜK RAPOR {son_gun}\nİşlem:{is_say} Açık:{acik_say}\n"
                   f"Bakiye:{round(b,2)} K/Z:{kz} USDT\n\n"
                   f"📈 TOPLAM\nWin Rate:%{p['win_rate']} ({p['kazanan']}/{p['toplam']})\n"
                   f"Toplam K/Z:{p['toplam_kz']} USDT PF:{p['profit_factor']}")
                with lock:
                    gunluk_islem = 0; gunluk_zarar = 0.0; gunluk_net_kz = 0.0; son_gun = bugun
                    sembol_gunluk_kayip.clear()
                baslangic_bakiye = bakiye()

            binance_senkronize()
            pozisyonlar = pozisyonlar_al()
            trailing_guncelle(pozisyonlar)

            if DINAMIK_COIN_EVRENI:
                SYMBOLS = en_yuksek_hacimli_coinler_long()

            log.info("═══ TARAMA DÖNGÜSÜ BAŞLIYOR (LONG) ═══")
            for i, sym in enumerate(SYMBOLS):
                log.info(f"  [{i+1}/{len(SYMBOLS)}] {sym} kontrol ediliyor...")
                strateji_kontrol(sym)
                time.sleep(0.3)
            log.info(f"Tüm coinler için strateji kontrolü tamamlandı, {TARAMA_ARALIK}sn uyuyacak...")

            time.sleep(TARAMA_ARALIK)
        except Exception as e:
            log.error(f"Dongu hatasi: {e}", exc_info=True)
            time.sleep(60)


# ════════════════════════════════════════════════════════════════════════════════
# TELEGRAM KOMUTLARI
# ════════════════════════════════════════════════════════════════════════════════

@app.route('/telegram', methods=['POST'])
def telegram_komut():
    global bot_durduruldu
    if not telegram_dogrula(request):
        return jsonify({'ok': True})
    try:
        data = request.get_json()
        mesaj = data.get('message', {})
        chat_id = str(mesaj.get('chat', {}).get('id', ''))
        metin = mesaj.get('text', '').strip()
        if chat_id != TELEGRAM_CHAT_ID: return jsonify({'ok': True})
        cmd = metin.lower()

        if cmd == '/durum':
            with lock:
                acik_say = len(acik); gunluk = gunluk_islem
            tg(f"📊 LONG DURUM {'🔴 DURDURULDU' if bot_durduruldu else '🟢 AKTİF'}\n"
               f"Bakiye:{round(bakiye(),2)} USDT\nAçık:{acik_say} Günlük:{gunluk}/{AYARLAR['MAX_GUNLUK_ISLEM']}\n"
               f"Günlük NET K/Z:{round(gunluk_net_kz,2)} USDT")
        elif cmd == '/bakiye':
            tg(f"💰 Bakiye: {round(bakiye(),2)} USDT")
        elif cmd == '/acik':
            with lock:
                if not acik or all(i.get('_rezerve') for i in acik.values()):
                    tg("📭 Açık pozisyon yok (LONG)")
                else:
                    msg = "📈 AÇIK LONG POZİSYONLAR:\n"
                    for sym, i in acik.items():
                        if i.get('_rezerve'): continue
                        msg += f"\n{sym} Giriş:{i['entry']} SL:{round(i['sl'],4)} En yüksek:{round(i.get('en_yuksek_fiyat',i['entry']),4)}\n"
                    tg(msg)
        elif cmd.startswith('/kapat'):
            parcalar = metin.strip().split()
            if len(parcalar) == 2:
                sembol_hedef = parcalar[1].upper()
                with lock:
                    var_mi = sembol_hedef in acik and not acik[sembol_hedef].get('_rezerve')
                if not var_mi:
                    tg(f"❌ {sembol_hedef} icin acik pozisyon bulunamadi")
                else:
                    kapat(sembol_hedef, "Manuel kapatma")
                    tg(f"✅ {sembol_hedef} kapatıldı")
            else:
                with lock: semboller = [s for s, i in acik.items() if not i.get('_rezerve')]
                for sym in semboller: kapat(sym, "Manuel kapatma")
                tg("✅ Tüm LONG pozisyonlar kapatıldı")
        elif cmd == '/durdur':
            bot_durduruldu = True
            tg("🔴 LONG BOT DURDURULDU\nYeni işlem alınmayacak. /devam ile başlat.")
        elif cmd == '/devam':
            bot_durduruldu = False
            tg("🟢 LONG BOT AKTİF")
        elif cmd == '/rapor':
            p = perf_ozet
            if p['toplam'] == 0: tg("📊 Henüz işlem yok.")
            else:
                tg(f"📊 LONG PERFORMANS RAPORU\nToplam:{p['toplam']} Kazanan:{p['kazanan']} Kaybeden:{p['kaybeden']}\n"
                   f"Win Rate:%{p['win_rate']}\nToplam K/Z:{p['toplam_kz']} USDT\nProfit Factor:{p['profit_factor']}")
        elif cmd.startswith('/ayar '):
            parcalar = metin.strip().split()
            if len(parcalar) == 3:
                anahtar = parcalar[1].upper()
                yeni, hata = ayar_dogrula(anahtar, parcalar[2])
                if hata: tg(f"❌ {hata}")
                else:
                    eski = AYARLAR[anahtar]; AYARLAR[anahtar] = yeni
                    ayarlar_kaydet()
                    tg(f"✅ {anahtar}: {eski} → {yeni}\n💾 Kalıcı kaydedildi")
            else:
                tg("Kullanım: /ayar ANAHTAR DEGER")
        elif cmd == '/ayarlar':
            tg("⚙️ LONG AYARLAR:\n" + '\n'.join([f"{k}:{v}" for k, v in AYARLAR.items()]))
        elif cmd == '/journal_sifirla':
            yedek = journal_sifirla()
            tg(f"♻️ LONG journal sıfırlandı." + (f"\nEski veri: {yedek}" if yedek else ""))
        return jsonify({'ok': True})
    except Exception as e:
        log.error(f"Telegram komut hatasi: {e}"); return jsonify({'ok': True})


# ════════════════════════════════════════════════════════════════════════════════
# WEB DASHBOARD
# ════════════════════════════════════════════════════════════════════════════════

DASHBOARD_HTML = """<!DOCTYPE html><html lang="tr"><head><meta charset="UTF-8">
<meta http-equiv="refresh" content="30"><title>LONG Trading Bot</title>
<style>body{font-family:monospace;background:#0d1117;color:#c9d1d9;padding:20px;margin:0}
h1{color:#3fb950}h2{color:#8b949e;font-size:14px;margin:20px 0 8px}
.card{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:16px;margin-bottom:16px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px}
.stat{background:#0d1117;border-radius:6px;padding:12px;text-align:center}
.stat .val{font-size:22px;font-weight:bold;color:#3fb950}.stat .lbl{font-size:11px;color:#8b949e;margin-top:4px}
.pos{border-left:3px solid #3fb950;padding:8px 12px;margin:6px 0;background:#0d1117;border-radius:4px}
.green{color:#3fb950}.red{color:#f85149}
</style></head><body><h1>🤖 LONG Trading Bot Dashboard</h1>
<div class="card"><div class="grid">
<div class="stat"><div class="val" id="bakiye">-</div><div class="lbl">Bakiye (USDT)</div></div>
<div class="stat"><div class="val" id="acik">-</div><div class="lbl">Açık Pozisyon</div></div>
<div class="stat"><div class="val" id="gunluk">-</div><div class="lbl">Günlük İşlem</div></div>
<div class="stat"><div class="val" id="durum">-</div><div class="lbl">Bot Durumu</div></div>
</div></div>
<div class="card"><h2>AÇIK POZİSYONLAR</h2><div id="pozlar">Yükleniyor...</div></div>
<div class="card"><h2>PERFORMANS</h2><div id="perf">Yükleniyor...</div></div>
<div class="card"><h2>JOURNAL</h2>
<a id="journalLink" href="#" style="color:#3fb950;text-decoration:none;font-size:13px">📥 trade_long_journal.csv indir</a>
</div>
<div style="color:#8b949e;font-size:11px">Son güncelleme: <span id="zaman"></span></div>
<script>
const token = new URLSearchParams(window.location.search).get('token') || '';
async function yukle(){
  const r=await fetch('/api/durum?token='+token); const d=await r.json();
  if(d.hata){document.body.innerHTML='<h2 style="color:#f85149">'+d.hata+'</h2>';return;}
  document.getElementById('bakiye').textContent=d.bakiye.toFixed(2);
  document.getElementById('acik').textContent=d.acik;
  document.getElementById('gunluk').textContent=d.gunluk+'/'+d.max_gunluk;
  const ds=document.getElementById('durum');
  ds.textContent=d.durduruldu?'🔴 DURDURULDU':'🟢 AKTİF';
  ds.className='val '+(d.durduruldu?'red':'green');
  const poz=document.getElementById('pozlar');
  if(!d.pozisyonlar||!d.pozisyonlar.length){poz.innerHTML='<span style="color:#8b949e">Açık pozisyon yok</span>';}
  else{poz.innerHTML=d.pozisyonlar.map(p=>`<div class="pos">
    <b>${p.symbol}</b> <span style="color:#8b949e;font-size:12px">LONG</span><br>
    <span style="font-size:12px">Giriş:<b>${p.entry}</b> SL:${p.sl} En yüksek:${p.en_yuksek_fiyat}</span>
  </div>`).join('');}
  const perf=document.getElementById('perf');
  if(d.perf&&d.perf.toplam>0){perf.innerHTML=`<div class="grid">
    <div class="stat"><div class="val green">${d.perf.win_rate}%</div><div class="lbl">Win Rate</div></div>
    <div class="stat"><div class="val ${d.perf.toplam_kz>=0?'green':'red'}">${d.perf.toplam_kz}</div><div class="lbl">Toplam K/Z</div></div>
    <div class="stat"><div class="val">${d.perf.toplam}</div><div class="lbl">Toplam İşlem</div></div>
    <div class="stat"><div class="val">${d.perf.profit_factor}</div><div class="lbl">Profit Factor</div></div>
  </div>`;}else{perf.innerHTML='<span style="color:#8b949e">Henüz veri yok</span>';}
  document.getElementById('journalLink').href='/journal?token='+token;
  document.getElementById('zaman').textContent=new Date().toLocaleTimeString('tr-TR');
}
yukle();
</script></body></html>"""

@app.route('/')
def dashboard():
    if not dashboard_dogrula(request):
        return "<h2>Yetkisiz erişim</h2>", 401
    return render_template_string(DASHBOARD_HTML)

@app.route('/api/durum')
def api_durum():
    if not dashboard_dogrula(request):
        return jsonify({'hata': 'Yetkisiz erisim'}), 401
    with lock:
        pozlar = [{'symbol': s, 'entry': round(i['entry'], 4), 'sl': round(i['sl'], 4),
                   'en_yuksek_fiyat': round(i.get('en_yuksek_fiyat', i['entry']), 4)}
                  for s, i in acik.items() if not i.get('_rezerve')]
    return jsonify({
        'bakiye': bakiye(), 'acik': len(pozlar),
        'gunluk': gunluk_islem, 'max_gunluk': AYARLAR['MAX_GUNLUK_ISLEM'],
        'durduruldu': bot_durduruldu, 'pozisyonlar': pozlar, 'perf': perf_ozet,
    })

@app.route('/journal')
def journal_indir():
    if not dashboard_dogrula(request):
        return jsonify({'hata': 'Yetkisiz erisim'}), 401
    if not JOURNAL_DOSYA.exists():
        return jsonify({'hata': 'Henuz journal dosyasi yok'}), 404
    return send_file(JOURNAL_DOSYA, as_attachment=True, download_name='trade_long_journal.csv', mimetype='text/csv')


# ════════════════════════════════════════════════════════════════════════════════
# BAŞLANGIÇ
# ════════════════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    try:
        ayarlar_yukle()
        exchange_info_al()
        time.sleep(1.0)
        durum_yukle()
        time.sleep(1.0)
        log.info("Baslangic: Binance LONG pozisyon yukleniyor")
        # HEDGE MODE: SADECE bu bota ait (POZISYON_YONU) taraf filtreleniyor —
        # bkz. bot.py'deki aynı başlıklı blok, birebir aynı mantık.
        positions = [p for p in client.futures_position_information() if _kendi_pozisyonum(p)]
        aktif_pozisyonlar = {p['symbol'] for p in positions if float(p['positionAmt']) != 0}
        for p in positions:
            if float(p['positionAmt']) != 0:
                sym = p['symbol']
                if sym in acik: continue
                try:
                    normal_orders = [o for o in client.futures_get_open_orders(symbol=sym)
                                     if o.get('positionSide') == POZISYON_YONU]
                except Exception as e:
                    log.error(f"Pozisyon yukleme open order hatasi {sym}: {e}")
                    normal_orders = []
                try:
                    conditional_orders = [o for o in client.futures_get_open_orders(symbol=sym, conditional=True)
                                          if o.get('positionSide') == POZISYON_YONU]
                except Exception as e:
                    conditional_orders = []
                sl_f = 0
                for e in normal_orders + conditional_orders:
                    order_type = (str(e.get('type') or e.get('origType') or e.get('contingencyType') or '')).upper()
                    order_price = None
                    if e in conditional_orders:
                        trigger = e.get('triggerPrice')
                        if trigger not in (None, ''):
                            try: order_price = float(trigger)
                            except (ValueError, TypeError): order_price = None
                    if order_price is None:
                        for price_key in ('stopPrice', 'triggerPrice', 'price'):
                            if e.get(price_key) not in (None, ''):
                                try:
                                    order_price = float(e.get(price_key)); break
                                except (ValueError, TypeError):
                                    continue
                    if order_price is None:
                        order_price = 0.0
                    if 'STOP' in order_type:
                        sl_f = order_price
                giris = float(p['entryPrice'])
                acik[sym] = {
                    'entry': giris, 'sl': sl_f or giris * (1 - AYARLAR['PERCENT_TRAILING_MESAFE']/100),
                    'en_yuksek_fiyat': giris,  # restart sonrasi bilinmiyor, guvenli varsayim: girisle basla
                    'q': abs(float(p['positionAmt'])), 'lev': AYARLAR['LEVERAGE'],
                    'acilis_zaman': int(time.time() * 1000),
                }
                log.info(f"LONG pozisyon yuklendi: {sym} giris:{giris} SL:{sl_f}")

        try:
            normal_orphan_orders = [o for o in client.futures_get_open_orders()
                                    if o.get('positionSide') == POZISYON_YONU]
            time.sleep(1.0)
            try:
                conditional_orphan_orders = [o for o in client.futures_get_open_orders(conditional=True)
                                             if o.get('positionSide') == POZISYON_YONU]
            except Exception as e:
                conditional_orphan_orders = []
            all_orphan_orders = normal_orphan_orders + conditional_orphan_orders
            seen = set()
            for order in all_orphan_orders:
                oid = (order.get('symbol'), order.get('orderId'), order.get('clientOrderId'))
                if oid in seen: continue
                seen.add(oid)
                sym = order.get('symbol')
                if not sym or sym in aktif_pozisyonlar: continue
                log.info(f"Orphan emir temizleniyor (LONG): {sym}")
                _guvenli_emir_iptal(sym)
        except Exception as e:
            log.error(f"Orphan emir kontrol hatasi: {e}")
    except Exception as e:
        log.error(f"Baslangic hatasi: {e}")
    threading.Thread(target=tarama_dongusu, daemon=True).start()
    app.run(host='0.0.0.0', port=int(os.environ.get('PORT', 5001)), debug=False)
