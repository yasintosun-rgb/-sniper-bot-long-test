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
    'LONG_HACIM_ONAY_CARPAN':  (0.5, 5.0),
    'PERCENT_TRAILING_MESAFE': (2.0, 20.0),
    'COOLDOWN_SURE':           (300, 86400),
    'SEMBOL_GUNLUK_MAX_KAYIP': (1,   10),
    'MAX_TOPLAM_RISK':         (1.0, 20.0),
}

# ── Volatilite bazlı pozisyon boyutlandırma (2026-09-18, backtest'te 5/5 ──
# sağlamlıkla doğrulandı: LONG'un 48-aylık MaxDD'sini ~%11.6 -> ~%10.8'e
# düşürdü, getiri çoğu bölünmede makul ölçüde etkilendi, 2/5 bölünmede
# getiri DE arttı). BTC'nin GÜNLÜK GERÇEKLEŞEN volatilitesine (o günün
# 15dk log-getirilerinin std'si) göre RISK_PERCENT'i ölçekler: yüksek
# volatilite rejiminde küçült, düşük volatilite rejiminde büyüt. Mevcut
# DRAWDOWN_LIMIT bazlı risk küçültmesiyle (efektif_risk_percent) ÇARPIMSAL
# olarak birleşir — backtest'teki mekanizmayla birebir aynı.
VOLATILITE_BOYUTLANDIRMA_AKTIF = os.environ.get('VOLATILITE_BOYUTLANDIRMA_AKTIF', 'true').lower() == 'true'
VOL_TRAILING_PENCERE_GUN = int(os.environ.get('VOL_TRAILING_PENCERE_GUN', 30))
VOL_YUKSEK_CARPAN = float(os.environ.get('VOL_YUKSEK_CARPAN', 0.5))
VOL_DUSUK_CARPAN = float(os.environ.get('VOL_DUSUK_CARPAN', 1.3))

# FIX (2026-09-19): EMA200 hesabı için yeterli ISINMA süresi (bkz.
# strateji_kontrol içindeki ilgili FIX notu). Binance futures_klines tek
# çağrıda en fazla 1500 mum döndürür; EMA200_ALTI_MIN_MUM üst sınırı 336
# olduğu için 336+1000=1336 hâlâ tek çağrıya sığar.
EMA_ISINMA_MUM = int(os.environ.get('EMA_ISINMA_MUM', 1000))

# FIX (2026-09-19, backtest'te dogrulandi — 5/5 saglamlik, en iyi getiri/
# MaxDD dengesi %99/98/97/96/95 arasinda %98'de bulundu): "kesintisiz N mum
# EMA200 altinda kalma" sarti cok kirilgan — fiyat ortalamayi test ederken
# dogal olarak birkac kez ustune/altina sicrayabilir, bu da GERCEK bir
# donusu (canli ornek: BTC, 2026-08-04—08-18) kacirtiyordu. Artik sabit bir
# PENCEREYE (son EMA200_ALTI_MIN_MUM mum) bakip, o pencerenin en az bu
# orandaki kismi dogru tarafta olsun yeterli — ara sira kisa sicramalara
# tolerans taniniyor. Bedel: backtest'te MaxDD ~%11.6 -> ~%14 (getiri
# karsiliginda kabul edilebilir bulundu).
EMA200_DONUS_TOLERANS_ORAN = float(os.environ.get('EMA200_DONUS_TOLERANS_ORAN', 0.98))

AYARLAR = {
    'LEVERAGE':                int(os.environ.get('LEVERAGE', 3)),         # bot.py ile AYNI OLMALI (Hedge Mode, sembol bazlı paylaşılıyor)
    'RISK_PERCENT':            float(os.environ.get('RISK_PERCENT', 1.0)),  # backtest'te doğrulandı
    'MAX_OPEN_TRADES':         int(os.environ.get('MAX_OPEN_TRADES', 10)),  # backtest'te doğrulandı (5/5 sağlamlık, hacim eşiğiyle birlikte)
    'MAX_GUNLUK_ISLEM':        int(os.environ.get('MAX_GUNLUK_ISLEM', 10)),
    'MAX_GUNLUK_ZARAR':        float(os.environ.get('MAX_GUNLUK_ZARAR', 5.0)),
    'DRAWDOWN_LIMIT':          float(os.environ.get('DRAWDOWN_LIMIT', 10.0)),
    'KOMISYON_ORAN':           float(os.environ.get('KOMISYON_ORAN', 0.0005)),
    'EMA200_ALTI_MIN_MUM':     int(os.environ.get('EMA200_ALTI_MIN_MUM', 72)),     # ✅ CANLI DEĞER (backtest'te doğrulanmış, 3 gün)
    # DENEY (2026-09-06, backtest'te doğrulandı, 4/5 sağlamlık): dönüş
    # mumunda hacim onayı — mevcut hacim, önceki 20 mumun ortalamasının
    # en az bu kadar katı olmalı. Getiri %18.78->%31.42, MaxDD %10.77->%5.94.
    'LONG_HACIM_ONAY_CARPAN': float(os.environ.get('LONG_HACIM_ONAY_CARPAN', 2.0)),
    'PERCENT_TRAILING_MESAFE': float(os.environ.get('PERCENT_TRAILING_MESAFE', 7.0)),  # backtest'te doğrulanmış
    'COOLDOWN_SURE':           int(os.environ.get('COOLDOWN_SURE', 3600)),
    'SEMBOL_GUNLUK_MAX_KAYIP': int(os.environ.get('SEMBOL_GUNLUK_MAX_KAYIP', 2)),
    'MAX_TOPLAM_RISK':         float(os.environ.get('MAX_TOPLAM_RISK', 5.0)),
}

# ── PİRAMİTLEME (2026-09-26, backtest_rolling_v2_KESIN.py LONG_PIRAMIT_TEST ile doğrulandı) ──
# Gerçekçi motor 2022-08→2026-08: piramitsiz Getiri +%91 / MaxDD %24.3 (Getiri/DD 3.74) →
# +%7'de 1 ekleme 1x: +%182 / %26.3 (Getiri/DD 6.91), 5/5 dilim; 9 varyantın 9'u da daha iyi.
# Fiyat İLK GİRİŞİN +%PIRAMIT_ADIM_YUZDE üstüne çıkınca, ilk miktarın PIRAMIT_BOYUT katı
# eklenir (en fazla PIRAMIT_MAX kez). Stop emri closePosition=True olduğu için eklenen
# miktarı da otomatik kapsar. İlk giriş fiyatı ('e0') ayrıca saklanır — Binance'in
# ortalama giriş fiyatı trailing hesabında KULLANILMAZ.
PIRAMIT_AKTIF = os.environ.get('PIRAMIT_AKTIF', 'true').lower() in ('1', 'true', 'evet', 'yes')
PIRAMIT_ADIM_YUZDE = float(os.environ.get('PIRAMIT_ADIM_YUZDE', 7.0))
PIRAMIT_MAX = int(os.environ.get('PIRAMIT_MAX', 1))
PIRAMIT_BOYUT = float(os.environ.get('PIRAMIT_BOYUT', 1.0))
# TRAILING HESABI (2026-09-26): backtest (ve tüm LONG doğrulamaları) stop mesafesini
# İLK GİRİŞ fiyatının %'si olarak SABİT tutar: SL = en_yüksek − e0 × %mesafe.
# Canlı eskiden SL = en_yüksek × (1 − %mesafe) kullanıyordu (fiyat yükseldikçe mesafe
# büyür, backtest'ten gevşek). 'GIRIS' = backtest ile birebir (varsayılan); 'ZIRVE' = eski.
TRAILING_MOD = os.environ.get('TRAILING_MOD', 'GIRIS').strip().upper()

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

DINAMIK_COIN_EVRENI = False   # ✅ CANLI: sadece doğrulanmış 20-coin listesi (test için True yapılıp 80 coine genişletilmişti)
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
# FIX (2026-08-26): Client'a ZORUNLU bir istek zaman aşımı (timeout)
# eklendi. Bu olmadan, Render <-> Binance arasında geçici bir ağ sorunu
# olursa, altta yatan istek SONSUZA KADAR bekleyebilir — hiçbir hata
# vermeden, hiçbir log basmadan thread'i tamamen dondurur (canlıda tam
# olarak bu yaşandı: bot "60 saniye bekleniyor" sonrası hiç ilerlemedi).
client = Client(API_KEY, API_SECRET, testnet=TESTNET, requests_params={'timeout': 20})

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

_VOL_CACHE = {'tarih': None, 'carpan': 1.0}
_VOL_CACHE_LOCK = threading.Lock()

def _btc_volatilite_carpani():
    """Backtest'teki _compute_btc_volatilite_risk_map ile AYNI mantık:
    BTC'nin GÜNLÜK gerçekleşen volatilitesi (o günün 15dk log-getirilerinin
    std'si), DÜNKÜ TAMAMLANMIŞ güne göre, trailing VOL_TRAILING_PENCERE_GUN
    günün percentile'ına yerleştirilir (lookahead yok — bugünün henüz
    tamamlanmamış mumu asla kullanılmaz, en son gün de güvenlik payı için
    atlanır). Günde bir kez hesaplanıp cache'lenir — her pozisyon açılışında
    ağır bir API çağrısı tekrarlanmasın diye."""
    global _VOL_CACHE
    bugun = datetime.now(timezone.utc).date()
    with _VOL_CACHE_LOCK:
        if _VOL_CACHE['tarih'] == bugun:
            return _VOL_CACHE['carpan']

    try:
        gerekli_mum = (VOL_TRAILING_PENCERE_GUN + 3) * 96  # 96x15dk = 1 gün
        tum_klines = []
        end_time = None
        while len(tum_klines) < gerekli_mum:
            params = dict(symbol='BTCUSDT', interval='15m', limit=1500)
            if end_time:
                params['endTime'] = end_time
            batch = client.futures_klines(**params)
            if not batch:
                break
            tum_klines = batch + tum_klines
            end_time = batch[0][0] - 1
            if len(batch) < 1500:
                break

        if len(tum_klines) < 96 * 5:
            log.error("[Volatilite] Yeterli BTC verisi alınamadı, nötr (1.0x) kullanılacak.")
            return 1.0

        gunluk_getiriler = {}
        onceki_close = None
        for k in tum_klines:
            gun = k[0] // 86_400_000
            close = float(k[4])
            if onceki_close is not None and onceki_close > 0:
                gunluk_getiriler.setdefault(gun, []).append(math.log(close / onceki_close))
            onceki_close = close

        gunluk_vol = {}
        for gun, rets in gunluk_getiriler.items():
            if len(rets) < 2:
                continue
            ortalama = sum(rets) / len(rets)
            varyans = sum((r - ortalama) ** 2 for r in rets) / len(rets)
            gunluk_vol[gun] = math.sqrt(varyans)

        gunler_sirali = sorted(gunluk_vol.keys())
        if len(gunler_sirali) < VOL_TRAILING_PENCERE_GUN + 2:
            log.error("[Volatilite] Yeterli gün geçmişi yok, nötr (1.0x) kullanılacak.")
            return 1.0

        # En son (muhtemelen henüz tamamlanmamış) günü ATLA — ondan önceki
        # tamamlanmış gün "dünkü gün" kabul edilir.
        dunku_gun = gunler_sirali[-2]
        dunku_vol = gunluk_vol[dunku_gun]
        pencere_gunleri = [g for g in gunler_sirali if g < dunku_gun][-VOL_TRAILING_PENCERE_GUN:]
        if len(pencere_gunleri) < VOL_TRAILING_PENCERE_GUN // 2:
            return 1.0
        pencere_vols = [gunluk_vol[g] for g in pencere_gunleri]
        pct = sum(1 for v in pencere_vols if v <= dunku_vol) / len(pencere_vols)

        if pct >= (2.0 / 3.0):
            carpan = VOL_YUKSEK_CARPAN
        elif pct <= (1.0 / 3.0):
            carpan = VOL_DUSUK_CARPAN
        else:
            carpan = 1.0

        with _VOL_CACHE_LOCK:
            _VOL_CACHE = {'tarih': bugun, 'carpan': carpan}
        log.info(f"[Volatilite] BTC günlük vol percentile={pct:.2f} -> risk çarpanı={carpan}x "
                 f"(dünkü_vol={dunku_vol:.6f}, pencere={len(pencere_vols)} gün)")
        return carpan
    except Exception as e:
        log.error(f"[Volatilite] Çarpan hesaplama hatası, nötr (1.0x) kullanılacak: {e}")
        return 1.0


# ════════════════════════════════════════════════════════════════════════════════
# HESAP GENELİ DEVRE KESİCİ (2026-09-25)
# ════════════════════════════════════════════════════════════════════════════════
# Aynı Binance hesabını birden fazla strateji paylaşıyor (bu süreçte LONG; ana
# SHORT + YeniListe ayrı bir serviste, bot.py — AYNI modül orada da var). Mevcut korumalar (günlük NET zarar limiti,
# DRAWDOWN_LIMIT risk yarılama) sadece ANA SHORT'un kendi işlemlerine bakıyor —
# hesabın TOPLAM özkaynağındaki düşüşü hiçbir şey izlemiyordu (bkz. 2026-09-18:
# Lead hesabı 7 günde -%16, 35 eşzamanlı pozisyon).
#
# NE YAPAR: hesabın özkaynağını (cüzdan + gerçekleşmemiş K/Z) son
# DEVRE_KESICI_PENCERE_GUN günün TEPESİYLE karşılaştırır. Düşüş
# DEVRE_KESICI_DD_YUZDE'yi aşarsa bu süreçteki TÜM stratejilerde YENİ GİRİŞ durur.
# Açık pozisyonlara DOKUNMAZ — borsadaki stop emirleri onları korumaya devam eder
# (panik anında toplu market kapatma genelde en kötü fiyattan olur).
#
# TEPE, DURUM DOSYASI GEREKTİRMEDEN hesaplanır: Binance gelir geçmişinden
# (REALIZED_PNL/COMMISSION/FUNDING_FEE...) son N günün cüzdan eğrisi yeniden
# kurulur. Böylece diski olmayan servislerde (sniper-bot-lead) restart sonrası
# da doğru çalışır ve aynı hesaptaki iki servis (bot.py + bot_long.py) birbirinden
# habersiz AYNI sonuca varır. Para yatırma/çekme (TRANSFER vb.) performans
# sayılmaz — çekim yapmak devre kesiciyi tetiklemez.
#
# YENİDEN AÇILMA: düşüş eşiğin altına inerse (tepe pencereden çıkınca ya da
# özkaynak toparlanınca) ve en az DEVRE_KESICI_MIN_DURUS_SAAT geçtiyse otomatik.
# Elle: Telegram /devre_sifirla (tepe referansını ŞİMDİYE çeker). Restart'a
# dayanıklı elle sıfırlama için: DEVRE_KESICI_SIFIRLAMA=2026-09-25T12:00 env var.
DEVRE_KESICI_AKTIF = os.environ.get('DEVRE_KESICI_AKTIF', 'true').lower() in ('1', 'true', 'evet', 'yes')
DEVRE_KESICI_DD_YUZDE = float(os.environ.get('DEVRE_KESICI_DD_YUZDE', 15.0))      # 5-50 makul
DEVRE_KESICI_PENCERE_GUN = int(os.environ.get('DEVRE_KESICI_PENCERE_GUN', 30))    # 7-90
DEVRE_KESICI_KONTROL_SN = int(os.environ.get('DEVRE_KESICI_KONTROL_SN', 300))     # 60-3600
DEVRE_KESICI_MIN_DURUS_SAAT = float(os.environ.get('DEVRE_KESICI_MIN_DURUS_SAAT', 24))
_DK_PERFORMANS_TIPLERI = {'REALIZED_PNL', 'COMMISSION', 'FUNDING_FEE', 'INSURANCE_CLEAR',
                          'COMMISSION_REBATE', 'API_REBATE', 'REFERRAL_KICKBACK',
                          'DELIVERED_SETTELMENT', 'AUTO_EXCHANGE'}


def _dk_env_sifirlama_ms():
    ham = os.environ.get('DEVRE_KESICI_SIFIRLAMA', '').strip()
    if not ham:
        return 0
    try:
        dt = datetime.fromisoformat(ham)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.timestamp() * 1000)
    except Exception:
        log.error(f"[DevreKesici] DEVRE_KESICI_SIFIRLAMA okunamadı: {ham!r} (örnek: 2026-09-25T12:00)")
        return 0


DEVRE_KESICI_TETIK = False
_dk_durum = {'gelirler': {}, 'son_ms': 0, 'sifirlama_ms': _dk_env_sifirlama_ms(),
             'tetik_ms': 0, 'son': None, 'hata_sayisi': 0}
_dk_lock = threading.Lock()


def _dk_gelirleri_guncelle(simdi_ms):
    """Gelir geçmişini artımlı çeker (ilk seferde pencere kadar geriye)."""
    pencere_bas = simdi_ms - DEVRE_KESICI_PENCERE_GUN * 86_400_000
    # 10 dk örtüşme: Binance bazı gelir kayıtlarını gecikmeli yayınlar; kayıtlar
    # anahtarla tekilleştirildiği için çift sayılmaz.
    bas = max(_dk_durum['son_ms'] - 600_000, pencere_bas)
    for _ in range(50):  # sayfalama güvenlik sınırı
        parca = client.futures_income_history(startTime=bas, endTime=simdi_ms, limit=1000)
        for g in parca:
            anahtar = (g.get('tranId'), g.get('incomeType'), g.get('symbol'), g.get('time'))
            _dk_durum['gelirler'][anahtar] = (int(g['time']), g.get('incomeType'), float(g['income']))
        if len(parca) < 1000:
            break
        bas = int(parca[-1]['time']) + 1
    _dk_durum['son_ms'] = simdi_ms
    # pencere dışına düşenleri at (bellek)
    for k in [k for k, v in _dk_durum['gelirler'].items() if v[0] < pencere_bas]:
        del _dk_durum['gelirler'][k]


def devre_kesici_hesapla():
    """Döner: {'ozkaynak','tepe','dd'} ya da None (hata)."""
    simdi_ms = int(time.time() * 1000)
    hesap = client.futures_account()
    cuzdan = float(hesap['totalWalletBalance'])
    ozkaynak = cuzdan + float(hesap['totalUnrealizedProfit'])
    _dk_gelirleri_guncelle(simdi_ms)
    pencere_bas = max(simdi_ms - DEVRE_KESICI_PENCERE_GUN * 86_400_000, _dk_durum['sifirlama_ms'])
    olaylar = sorted((t, tutar) for t, tip, tutar in _dk_durum['gelirler'].values()
                     if tip in _DK_PERFORMANS_TIPLERI and t >= pencere_bas)
    # Geriye doğru: her olaydan hemen sonraki "performans cüzdanı"
    toplam_sonra = sum(t for _, t in olaylar)
    seviye = cuzdan - toplam_sonra          # pencere başındaki seviye
    tepe = max(seviye, ozkaynak)
    for _, tutar in olaylar:
        seviye += tutar
        tepe = max(tepe, seviye)
    dd = (tepe - ozkaynak) / tepe * 100 if tepe > 0 else 0.0
    return {'ozkaynak': ozkaynak, 'tepe': tepe, 'dd': max(dd, 0.0)}


def devre_kesici_kontrol():
    global DEVRE_KESICI_TETIK
    if not DEVRE_KESICI_AKTIF:
        return
    with _dk_lock:
        try:
            s = devre_kesici_hesapla()
            _dk_durum['hata_sayisi'] = 0
        except Exception as e:
            _dk_durum['hata_sayisi'] += 1
            log.error(f"[DevreKesici] hesaplama hatası ({_dk_durum['hata_sayisi']}): {e}")
            if _dk_durum['hata_sayisi'] == 6:
                tg(f"⚠️ [DevreKesici] 6 kez üst üste hesaplanamadı — son durum korunuyor "
                   f"({'TETİKLİ' if DEVRE_KESICI_TETIK else 'normal'}). Hata: {e}")
            return
        _dk_durum['son'] = s
        simdi_ms = int(time.time() * 1000)
        if not DEVRE_KESICI_TETIK and s['dd'] >= DEVRE_KESICI_DD_YUZDE:
            DEVRE_KESICI_TETIK = True
            _dk_durum['tetik_ms'] = simdi_ms
            log.error(f"[DevreKesici] TETİKLENDİ: düşüş %{s['dd']:.2f} >= %{DEVRE_KESICI_DD_YUZDE}")
            tg(f"🛑 HESAP DEVRE KESİCİSİ TETİKLENDİ\n"
               f"Özkaynak {s['ozkaynak']:.2f} USDT, son {DEVRE_KESICI_PENCERE_GUN} günün tepesi "
               f"{s['tepe']:.2f} USDT → düşüş %{s['dd']:.2f} (eşik %{DEVRE_KESICI_DD_YUZDE:.0f})\n"
               f"Bu serviste TÜM stratejilerde yeni giriş DURDU. Açık pozisyonlar borsadaki "
               f"stoplarıyla korunmaya devam ediyor.\n"
               f"En erken otomatik açılma: {DEVRE_KESICI_MIN_DURUS_SAAT:.0f} saat sonra (düşüş eşiğin "
               f"altına inerse). Elle: /devre_sifirla")
        elif DEVRE_KESICI_TETIK and s['dd'] < DEVRE_KESICI_DD_YUZDE:
            gecen_saat = (simdi_ms - _dk_durum['tetik_ms']) / 3_600_000
            if gecen_saat >= DEVRE_KESICI_MIN_DURUS_SAAT:
                DEVRE_KESICI_TETIK = False
                tg(f"🟢 Hesap devre kesicisi kendiliğinden AÇILDI (düşüş %{s['dd']:.2f} < "
                   f"%{DEVRE_KESICI_DD_YUZDE:.0f}, {gecen_saat:.0f} saattir kapalıydı). Yeni girişler serbest.")


def devre_kesici_sifirla():
    """Elle sıfırlama: tepe referansı şimdiye çekilir, kesici açılır."""
    global DEVRE_KESICI_TETIK
    with _dk_lock:
        _dk_durum['sifirlama_ms'] = int(time.time() * 1000)
        DEVRE_KESICI_TETIK = False
    devre_kesici_kontrol()


def devre_kesici_ozet():
    if not DEVRE_KESICI_AKTIF:
        return "🛡️ Hesap devre kesicisi: kapalı (DEVRE_KESICI_AKTIF=false)"
    s = _dk_durum['son']
    durum = '🔴 TETİKLİ (yeni giriş yok)' if DEVRE_KESICI_TETIK else '🟢 normal'
    if s is None:
        return f"🛡️ Hesap devre kesicisi: {durum} — henüz hesaplanmadı"
    return (f"🛡️ Hesap devre kesicisi: {durum}\n"
            f"   Özkaynak {s['ozkaynak']:.2f} / tepe {s['tepe']:.2f} USDT → düşüş %{s['dd']:.2f} "
            f"(eşik %{DEVRE_KESICI_DD_YUZDE:.0f}, pencere {DEVRE_KESICI_PENCERE_GUN} gün)")


def devre_kesici_dongusu():
    while True:
        devre_kesici_kontrol()
        time.sleep(max(60, DEVRE_KESICI_KONTROL_SN))


def efektif_risk_percent():
    b = bakiye()
    if baslangic_bakiye <= 0:
        base = AYARLAR['RISK_PERCENT']
    else:
        dd = (baslangic_bakiye - b) / baslangic_bakiye * 100
        base = AYARLAR['RISK_PERCENT'] * 0.5 if dd >= AYARLAR['DRAWDOWN_LIMIT'] else AYARLAR['RISK_PERCENT']
    if VOLATILITE_BOYUTLANDIRMA_AKTIF:
        base = base * _btc_volatilite_carpani()
    return base

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
    # FIX (2026-09-19, kullanıcı sorusu — SHORT/bot.py'de zaten uygulandı):
    # marjin tipi hesap ekranında Cross görünüyordu — likidasyon durumunda
    # TÜM hesap bakiyesi risk altında kalabilir. Her pozisyon açılışında
    # GARANTİLİ olarak Isolated'a geçiyoruz. -4046 (zaten Isolated) zararsız,
    # sessizce geçilir. NOT: kaldıraç gibi bu da sembol bazında PAYLAŞILIR —
    # SHORT botu da aynı sembolde Isolated istiyor, çakışma yok.
    try:
        client.futures_change_margin_type(symbol=symbol, marginType='ISOLATED')
    except Exception as e:
        if '-4046' not in str(e):
            log.error(f"Marjin tipi ayarlama hatası {symbol}: {e}")
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
    if DEVRE_KESICI_TETIK:
        log.info(f"{symbol} sinyali atlandi: hesap devre kesicisi tetikli")
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
                'e0': gercek, 'q0': m, 'piramit_ek': 0,
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


def _piramit_kontrol(symbol, mark):
    """Fiyat ilk girişin +%PIRAMIT_ADIM_YUZDE × (ek+1) seviyesine ulaştıysa pozisyona ekler."""
    with lock:
        islem = acik.get(symbol)
        if not islem or islem.get('_rezerve') or islem.get('_piramit_suruyor'):
            return
        e0 = islem.get('e0', islem['entry'])
        ek = islem.get('piramit_ek', 0)
        q0 = islem.get('q0', islem['q'])
        if ek >= PIRAMIT_MAX or mark < e0 * (1 + PIRAMIT_ADIM_YUZDE * (ek + 1) / 100):
            return
        islem['_piramit_suruyor'] = True
    try:
        if bot_durduruldu or DEVRE_KESICI_TETIK:
            log.info(f"{symbol}: piramit seviyesi geldi ama ekleme atlandı "
                     f"({'/durdur' if bot_durduruldu else 'devre kesici'})")
            return
        cache = exchange_info_al()
        b = bakiye()
        qa = q0 * PIRAMIT_BOYUT
        tavan_q = (b * 0.20 * AYARLAR['LEVERAGE']) / mark - islem['q']   # miktar_hesapla ile aynı tavan
        if qa > tavan_q:
            qa = max(tavan_q, 0.0)
        if symbol in cache:
            step = cache[symbol]['step']
            qa = math.floor(qa / step + 1e-9) * step
            qa = max(1, int(qa)) if step >= 1 and qa >= 1 else round(qa, cache[symbol]['lp'])
            if qa * mark < cache[symbol]['min_notional']:
                qa = 0
        if qa <= 0:
            log.info(f"{symbol}: piramit ekleme miktarı sıfır (tavan/min notional) — atlandı")
            with lock:
                if symbol in acik:
                    acik[symbol]['piramit_ek'] = ek + 1   # tekrar tekrar denemesin
            durum_kaydet()
            return
        order = binance_emir_gonder(client.futures_create_order,
                                    idempotency_prefix='PIR_L', sym_key=symbol,
                                    symbol=symbol, side='BUY', type='MARKET', quantity=qa,
                                    positionSide='LONG')
        fill = _fill_fiyati_al(order, symbol)
        yeni_q = islem['q'] + qa
        with lock:
            if symbol in acik:
                i = acik[symbol]
                yeni_q = i['q'] + qa
                i['entry'] = (i['entry'] * i['q'] + fill * qa) / yeni_q   # ortalama (K/Z raporu için)
                i['q'] = yeni_q
                i['e0'] = e0
                i['q0'] = q0
                i['piramit_ek'] = ek + 1
        durum_kaydet()
        tg(f"➕ LONG PİRAMİT {symbol}\nİlk giriş {e0} → +%{(fill/e0-1)*100:.1f} seviyesinde {qa} eklendi @ {fill}\n"
           f"Toplam miktar {yeni_q} | ekleme {ek+1}/{PIRAMIT_MAX} | stop (closePosition) tüm pozisyonu kapsıyor")
        log.info(f"{symbol}: piramit eklemesi {qa} @ {fill} (ilk giriş {e0}, ekleme {ek+1}/{PIRAMIT_MAX})")
    except Exception as e:
        log.error(f"{symbol}: piramit ekleme hatası: {e}")
        tg(f"⚠️ {symbol} (LONG) piramit eklemesi başarısız: {e}")
        with lock:
            if symbol in acik:
                acik[symbol]['piramit_ek'] = ek + 1   # hata döngüsüne girmesin
        durum_kaydet()
    finally:
        with lock:
            if symbol in acik:
                acik[symbol].pop('_piramit_suruyor', None)


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
            if PIRAMIT_AKTIF:
                _piramit_kontrol(symbol, mark)
                with lock:
                    islem = dict(acik.get(symbol, islem))
            e0 = islem.get('e0', islem['entry'])
            en_yuksek_eski = islem.get('en_yuksek_fiyat', islem['entry'])
            en_yuksek_yeni = max(en_yuksek_eski, mark)
            if en_yuksek_yeni <= en_yuksek_eski:
                continue  # yeni zirve yok, SL'i tekrar gondermeye gerek yok
            if TRAILING_MOD == 'ZIRVE':
                yeni_sl = en_yuksek_yeni * (1 - mesafe_yuzde)
            else:
                yeni_sl = en_yuksek_yeni - e0 * mesafe_yuzde
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

        # FIX (2026-09-19): EMA200'un SMA-tohumlu hesap yontemi (bkz.
        # ema_serisi), tohumun etkisinin silinmesi icin YETERLI ISINMA
        # SURESI gerektirir. Eskiden sadece EMA200_ALTI_MIN_MUM+210 (=282)
        # mum cekiliyordu — 200'u SMA tohumuna gidince geriye sadece 81
        # mumluk bir "isinma" kaliyordu, bu da EMA200 agirlik formulune
        # gore tohumun HALA ~%45'inin etkisini tasidigi, gercek/yakinsamis
        # bir EMA200 OLMAYAN bir deger uretiyordu (TradingView gibi yillarca
        # geriye giden veriyle hesaplanan EMA200'den GORULEBILIR olcude
        # farkli olabiliyordu). Canli ornek: 20 Agustos 2026'daki BTC
        # kirilimi TradingView'da net bir EMA200-donusu gibi gorunuyordu
        # ama bot hic sinyal uretmedi — kok neden buydu. EMA_ISINMA_MUM
        # ile artik cok daha genis bir pencere cekiliyor (varsayilan 1000
        # mum ek isinma -> tohumun etkisi ~%1'in altina iner).
        mumlar = client.futures_klines(symbol=symbol, interval=INTERVAL,
                                       limit=AYARLAR['EMA200_ALTI_MIN_MUM'] + EMA_ISINMA_MUM)
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

        # FIX (2026-09-19): eskiden burada kesintisiz bir 'while' sayacı
        # (ardisik_altinda) vardı — tek bir mumun bile üstüne sıçraması
        # sayacı sıfırlıyordu. Artık sabit bir pencereye (son
        # EMA200_ALTI_MIN_MUM mum) bakıp, pencerenin en az
        # EMA200_DONUS_TOLERANS_ORAN kadarının EMA200 altında olmasını
        # arıyoruz — backtest'te doğrulanmış, %98'de en iyi denge.
        N = AYARLAR['EMA200_ALTI_MIN_MUM']
        pencere_baslangic = n - 2 - N
        if pencere_baslangic < 0:
            return
        pencere_kapanis = kapanis[pencere_baslangic:n-2]
        pencere_ema = ema200_serisi[pencere_baslangic:n-2]
        gecerli = [(c, e) for c, e in zip(pencere_kapanis, pencere_ema) if e is not None]
        if not gecerli:
            return
        altinda_sayisi = sum(1 for c, e in gecerli if c < e)
        oran = altinda_sayisi / len(gecerli)
        if oran < EMA200_DONUS_TOLERANS_ORAN:
            log.debug(f"{symbol}: donus var ama pencerenin sadece %{oran*100:.0f}'i EMA200 "
                      f"altindaydi (gerekli: %{EMA200_DONUS_TOLERANS_ORAN*100:.0f})")
            return

        # DENEY (2026-09-06, backtest'te doğrulandı — 4/5 sağlamlık):
        # dönüş mumunda hacim onayı — mevcut hacim, önceki 20 mumun
        # ortalamasının en az LONG_HACIM_ONAY_CARPAN katı değilse sinyal
        # atlanır. Getiri %18.78->%31.42, MaxDD %10.77->%5.94 (backtest).
        # 'mumlar[:-1]' ile kapanis dizisi olusturuldugu icin, donus mumu
        # kapanis[-1] = mumlar[-2]'ye karsilik geliyor. Fail-safe: hacim
        # hesabi basarisiz olursa (veri sorunu), filtre UYGULANMAZ -- bir
        # veri aksakligi yuzunden gecerli bir sinyali kaybetmeyelim.
        try:
            donus_mum_hacim = float(mumlar[-2][5])
            onceki_20_hacim = [float(m[5]) for m in mumlar[-22:-2]]
            hacim_ort = sum(onceki_20_hacim) / len(onceki_20_hacim) if onceki_20_hacim else 0
            if hacim_ort > 0 and donus_mum_hacim <= hacim_ort * AYARLAR['LONG_HACIM_ONAY_CARPAN']:
                log.debug(f"{symbol}: donus var ama hacim yetersiz "
                          f"({round(donus_mum_hacim/hacim_ort,2)}x, "
                          f"gerekli:{AYARLAR['LONG_HACIM_ONAY_CARPAN']}x)")
                return
        except Exception as e:
            log.warning(f"{symbol}: hacim onayi hesaplanamadi, filtre uygulanmadan devam ediliyor: {e}")

        fiyat = kapanis[-1]
        # FIX (2026-09-26, KRİTİK): burada eskiden silinmiş 'ardisik_altinda' değişkeni
        # kullanılıyordu → her gerçek sinyalde NameError, buy() HİÇ çağrılmıyordu
        # (19 Eylül tolerans düzeltmesinden beri sessiz arıza).
        log.info(f"LONG sinyali: {symbol}@{fiyat} (pencerenin %{oran*100:.0f}'i EMA200 altındaydı, dönüş)")
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
       f"Risk:%{AYARLAR['RISK_PERCENT']} Trailing:%{AYARLAR['PERCENT_TRAILING_MESAFE']} ({TRAILING_MOD})\n"
       f"Piramit: {'AÇIK' if PIRAMIT_AKTIF else 'kapalı'} (+%{PIRAMIT_ADIM_YUZDE:g}, {PIRAMIT_MAX} ek, {PIRAMIT_BOYUT:g}x)\n"
       f"Strateji: EMA200 dönüşü ({AYARLAR['EMA200_ALTI_MIN_MUM']} saat) — 1sa zaman dilimi"
       f"{_test_uyarisi}")
    while True:
        log.info("Yeni dongu iterasyonu basliyor...")
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

            log.info("Senkronizasyon basliyor (binance_senkronize)...")
            binance_senkronize()
            log.info("Senkronizasyon bitti. Pozisyonlar aliniyor (pozisyonlar_al)...")
            pozisyonlar = pozisyonlar_al()
            log.info(f"Pozisyonlar alindi ({len(pozisyonlar)}). Trailing guncelleniyor...")
            trailing_guncelle(pozisyonlar)
            log.info("Trailing guncelleme bitti.")

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
               f"Risk:%{AYARLAR['RISK_PERCENT']} Trailing:%{AYARLAR['PERCENT_TRAILING_MESAFE']} MaxOpen:{AYARLAR['MAX_OPEN_TRADES']}\n"
               f"Günlük NET K/Z:{round(gunluk_net_kz,2)} USDT\n"+devre_kesici_ozet())
        elif cmd == '/devre':
            tg(devre_kesici_ozet())
        elif cmd == '/devre_sifirla':
            devre_kesici_sifirla()
            tg("🟢 Hesap devre kesicisi elle SIFIRLANDI (LONG) — tepe referansı şimdiye çekildi.\n"+devre_kesici_ozet()+
               "\n(Not: SHORT servisinde de ayrıca /devre_sifirla gönderin; restart sonrası kalıcılık için DEVRE_KESICI_SIFIRLAMA env var.)")
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
                        msg += (f"\n{sym} Giriş:{i['entry']} SL:{round(i['sl'],4)} En yüksek:{round(i.get('en_yuksek_fiyat',i['entry']),4)}"
                                f" | ilk giriş:{i.get('e0', i['entry'])} ekleme:{i.get('piramit_ek', 0)}/{PIRAMIT_MAX}\n")
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

@app.route('/health')
def health():
    """FIX (2026-09-21, kullanıcı gözlemi — UptimeRobot bu servise 3+ gündür
    401 aldığı için ping ATAMIYORDU, bu da Render'ın 15dk hareketsizlik
    sonrası container'ı TAMAMEN DURDURMASINA yol açtı (11.5 saatlik donma
    gözlemlendi). Bu endpoint DASHBOARD_TOKEN GEREKTIRMEZ — UptimeRobot'u
    '/' yerine buraya yönlendirin, böylece her zaman gerçek 200 OK alınır."""
    return "OK", 200

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
                    # hafıza kaybolmuş: ilk giriş/ekleme durumu bilinmiyor → güvenli taraf:
                    # bu pozisyona piramit EKLENMEZ (çift ekleme riski olmasın)
                    'e0': giris, 'q0': abs(float(p['positionAmt'])), 'piramit_ek': PIRAMIT_MAX,
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
    # FIX (2026-09-25): hesap devre kesicisi — tarama başlamadan önce bir kez senkron.
    if DEVRE_KESICI_AKTIF:
        devre_kesici_kontrol()
        log.info(devre_kesici_ozet())
        threading.Thread(target=devre_kesici_dongusu, daemon=True).start()
    threading.Thread(target=tarama_dongusu, daemon=True).start()
    app.run(host='0.0.0.0', port=int(os.environ.get('PORT', 5001)), debug=False)
