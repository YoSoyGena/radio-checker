import re
import time
import json
import requests
import sys
import cv2
import numpy as np
from urllib.parse import urlparse, quote_plus
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock, Thread
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.common.exceptions import TimeoutException, NoSuchWindowException, WebDriverException, InvalidSessionIdException
from PIL import Image
import io
import os
import shutil
import ctypes
from ctypes import wintypes
GIST_RAW_URL = (
    "https://gist.githubusercontent.com/YoSoyGena/"
    "7f3a225f39e98d5ac988e1af1526fdc4/raw"
)
TIMEOUT = 5
MAX_THREADS = 30
MAX_BROWSER_THREADS = 2
ARCHIVO_LOG = "resultado_streams.txt"
ARCHIVO_MD_ACTUALIZADO = "radios_actualizadas.md"
ARCHIVO_SETTINGS = "settings.json"
VIDEO_DIR = "videos"
TEMP_DIR = os.path.join(VIDEO_DIR, "temp")
EXPORTED_DIR = os.path.join(VIDEO_DIR, "exported")
for d in [VIDEO_DIR, TEMP_DIR, EXPORTED_DIR]:
    if not os.path.exists(d):
        os.makedirs(d)
PATRON_URL = re.compile(r"(https?://[^\s)]+)", re.IGNORECASE)
HEADERS_STREAM = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/120.0.0.0",
    "Accept": "*/*",
    "Icy-MetaData": "1",
    "Connection": "close"
}
cache_hosts = {}
cache_lock = Lock()

def obtener_gist():
    """Descarga el contenido del gist"""
    url_nocache = f"{GIST_RAW_URL}?nocache={int(time.time())}"
    r = requests.get(
        url_nocache,
        timeout=TIMEOUT,
        headers={"Cache-Control": "no-cache", "Pragma": "no-cache"}
    )
    r.raise_for_status()
    return r.text

def extraer_radios(markdown):
    """Extrae todas las radios del markdown manteniendo estructura"""
    radios = []
    lineas_originales = markdown.splitlines()
    for idx, linea in enumerate(lineas_originales):
        linea_stripped = linea.strip()
        if not linea_stripped.startswith("|"):
            continue
        if "---" in linea_stripped or "Frecuencia" in linea_stripped or "**" in linea_stripped:
            continue
        columnas = [c.strip() for c in linea_stripped.strip("|").split("|")]
        if len(columnas) < 3:
            continue
        frecuencia = columnas[0]
        nombre = columnas[1]
        url_column = None
        for i, col in enumerate(columnas):
            if PATRON_URL.search(col):
                url_column = i
                break
        if url_column is None:
            continue
        urls = PATRON_URL.findall(columnas[url_column])
        for url in urls:
            radios.append({
                "nombre": nombre,
                "frecuencia": frecuencia,
                "url": url,
                "linea_original": linea,
                "linea_num": idx,
                "columnas": columnas
            })
    return radios, lineas_originales

def ajustar_nombre_por_url(nombre, url):
    """
    Agrega un asterisco al nombre si la URL es de streamtheworld,
    o lo quita si no lo es.
    """
    if not url:
        return nombre
    es_stw = 'streamtheworld.com' in url.lower()
    nombre_base = nombre.replace('*', '').strip()
    while '  ' in nombre_base:
        nombre_base = nombre_base.replace('  ', ' ')
    if es_stw:
        if '(' in nombre_base:
            partes = nombre_base.split('(', 1)
            return f"{partes[0].strip()}* ({partes[1]}"
        else:
            return f"{nombre_base}*"
    else:
        return nombre_base

def verificar_stream(radio):
    """Verifica si un stream está funcionando"""
    url = radio["url"]
    host = urlparse(url).netloc
    with cache_lock:
        if host in cache_hosts:
            estado, info = cache_hosts[host]
            return radio, estado, f"(cache) {info}"
    try:
        r = requests.get(
            url,
            headers=HEADERS_STREAM,
            timeout=TIMEOUT,
            stream=True,
            allow_redirects=True
        )
        for _ in r.iter_content(chunk_size=1024):
            break
        if r.status_code < 400:
            ct = r.headers.get('Content-Type', '').lower()
            tipos_audio = ['audio/', 'mpegurl', 'video/mp2t', 'application/ogg', 'application/x-mpegurl', 'application/vnd.apple.mpegurl', 'application/octet-stream', 'video/mp4']
            is_icy = any(k.lower().startswith('icy-') for k in r.headers.keys())
            if not is_icy and not any(t in ct for t in tipos_audio):
                if 'text/html' in ct or 'image/' in ct:
                    estado, info = "CAIDO", f"No es audio ({ct})"
                else:
                    estado, info = "ACTIVO", f"{r.status_code} ({ct})"
            else:
                estado, info = "ACTIVO", r.status_code
        else:
            estado, info = "CAIDO", r.status_code
    except requests.exceptions.ReadTimeout:
        estado, info = "TIMEOUT", "Timeout de lectura"
    except requests.exceptions.SSLError:
        estado, info = "ACTIVO", "SSL incompatible"
    except requests.exceptions.ConnectionError:
        estado, info = "CAIDO", "Error de conexión"
    except Exception as e:
        estado, info = "CAIDO", str(e)
    with cache_lock:
        cache_hosts[host] = (estado, info)
    radio['nombre'] = ajustar_nombre_por_url(radio['nombre'], url)
    return radio, estado, info

class RadioStreamFinder:
    def __init__(self, headless=True, grabar_video=False):
        self.headless = headless
        self.grabar_video = grabar_video
        self.grabacion_activa = False
        self.driver = None
        self.thread_grabacion = None
        self.video_writer = None
        self.video_path = None
        self.driver_lock = Lock()
        self.last_exported_video = None
        self.monitoring_network = False
        self.thread_network = None
        self._streams_detectados_pasivamente = set()
        self._streams_confirmados_pasivamente = set()
        self.verbose_network = True
    def iniciar_grabacion(self, nombre_archivo):
        """Inicia la grabación de video"""
        if not self.grabar_video or self.grabacion_activa:
            return
        self.grabacion_activa = True
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        nombre_limpio = re.sub(r'[^\w\s-]', '', nombre_archivo).strip().replace(' ', '_')
        self.video_filename = f"debug_{nombre_limpio}_{timestamp}.mp4"
        self.video_path = os.path.join(TEMP_DIR, self.video_filename)
        fps = 5
        self.video_writer = None
        def grabar():
            """Función que corre en un thread separado"""
            while self.grabacion_activa:
                try:
                    with self.driver_lock:
                        if self.driver:
                            try:
                                all_handles = self.driver.window_handles
                                if len(all_handles) > 1:
                                    try:
                                        original_h = self.driver.current_window_handle
                                        last_h = all_handles[-1]
                                        if original_h != last_h:
                                            self.driver.switch_to.window(last_h)
                                            screenshot = self.driver.get_screenshot_as_png()
                                            self.driver.switch_to.window(original_h)
                                        else:
                                            screenshot = self.driver.get_screenshot_as_png()
                                    except:
                                        screenshot = self.driver.get_screenshot_as_png()
                                else:
                                    screenshot = self.driver.get_screenshot_as_png()
                            except (InvalidSessionIdException, WebDriverException):
                                break
                        else:
                            break
                    img = Image.open(io.BytesIO(screenshot))
                    frame = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)
                    if self.video_writer is None:
                        height, width, _ = frame.shape
                        fourcc = cv2.VideoWriter_fourcc(*'mp4v')
                        self.video_writer = cv2.VideoWriter(
                            self.video_path, fourcc, fps, (width, height)
                        )
                    self.video_writer.write(frame)
                    time.sleep(1/fps)
                except Exception as e:
                    error_msg = str(e).lower()
                    if "no such window" in error_msg or "web view not found" in error_msg:
                        time.sleep(0.5)
                        continue
                    print(f"     ⚠️ Error en grabación: {e}")
                    break
        self.thread_grabacion = Thread(target=grabar, daemon=True)
        self.thread_grabacion.start()
        print(f"      🎥 Grabación iniciada: {self.video_path}")
    def detener_grabacion(self):
        """Detiene la grabación de video"""
        if not self.grabacion_activa:
            return
        self.grabacion_activa = False
        if self.thread_grabacion:
            self.thread_grabacion.join(timeout=2)
        if self.video_writer:
            self.video_writer.release()
            dest_path = os.path.join(EXPORTED_DIR, self.video_filename)
            try:
                if os.path.exists(self.video_path):
                    shutil.move(self.video_path, dest_path)
                    print(f"      ✅ Video exportado: {dest_path}")
                    self.last_exported_video = dest_path
                else:
                    print(f"      ⚠️ No se encontró el video temporal: {self.video_path}")
            except Exception as e:
                print(f"      ❌ Error al exportar video: {e}")
        self.video_writer = None
    def iniciar_monitoreo_red(self):
        """Inicia el hilo de monitoreo de red"""
        if self.monitoring_network:
            return
        self.monitoring_network = True
        self.thread_network = Thread(target=self._monitor_network_logic, daemon=True)
        self.thread_network.start()
        print("      🌐 Monitoreo de red activo (Capturando requests...)")
    def detener_monitoreo_red(self):
        """Detiene el monitoreo de red"""
        self.monitoring_network = False
        if self.thread_network:
            self.thread_network.join(timeout=1)
        self.thread_network = None
    def _monitor_network_logic(self):
        """Lógica del hilo de monitoreo: extrae logs de performance continuamente"""
        while self.monitoring_network:
            try:
                with self.driver_lock:
                    if self.driver:
                        try:
                            logs = self.driver.get_log('performance')
                        except:
                            logs = []
                    else:
                        logs = []
                for entry in logs:
                    try:
                        msg = json.loads(entry['message'])['message']
                        method = msg.get('method')
                        params = msg.get('params', {})
                        if method == 'Network.requestWillBeSent':
                            url = params.get('request', {}).get('url')
                            if url:
                                self._analizar_url_request(url, params)
                        elif method == 'Network.responseReceived':
                            url = params.get('response', {}).get('url')
                            if url:
                                self._analizar_url_response(url, params)
                    except:
                        continue
                time.sleep(0.5)
            except Exception as e:
                time.sleep(1)
    def _analizar_url_request(self, url, params):
        """
        PROCESAMIENTO DE REQUESTS (Desde el principio)
        Aquí es donde se analizan las URLs apenas se intentan solicitar.
        """
        if self._es_stream_audio(url):
            if url not in self._streams_detectados_pasivamente:
                print(f"      🎵 Stream detectado al INICIAR solicitud: {url[:80]}...")
                self._streams_detectados_pasivamente.add(url)
    def _analizar_url_response(self, url, params):
        """PROCESAMIENTO DE RESPUESTAS"""
        response = params.get('response', {})
        headers = response.get('headers', {})
        content_type = (headers.get('content-type', '').lower() or
                       headers.get('Content-Type', '').lower() or
                       response.get('mimeType', '').lower())
        tipos_audio = [
            'audio/', 'mpegurl', 'video/mp2t', 'application/ogg',
            'application/x-mpegurl', 'application/vnd.apple.mpegurl'
        ]
        if any(t in content_type for t in tipos_audio):
            if url not in self._streams_confirmados_pasivamente:
                print(f"      🎵 Stream CONFIRMADO por respuesta ({content_type}): {url[:80]}...")
                self._streams_confirmados_pasivamente.add(url)
                self._streams_detectados_pasivamente.add(url)
    def setup_driver(self):
        """Configura Chrome con captura de network"""
        if self.driver is not None:
            try:
                _ = self.driver.current_url
                return
            except Exception:
                print("      ⚠️ Sesión expirada o driver cerrado, reiniciando...")
                try:
                    self.driver.quit()
                except:
                    pass
                self.driver = None
        chrome_options = Options()
        if self.headless:
            chrome_options.add_argument('--headless=new')
        chrome_options.page_load_strategy = 'eager'
        chrome_options.add_argument('--disable-gpu')
        chrome_options.add_argument('--disable-software-rasterizer')
        chrome_options.add_argument('--disable-extensions')
        chrome_options.add_argument('--disable-dev-shm-usage')
        chrome_options.add_argument('--no-sandbox')
        chrome_options.add_argument('--window-size=1024,768')
        chrome_options.add_argument('--disable-site-isolation-trials')
        chrome_options.add_argument('--renderer-process-limit=1')
        chrome_options.add_argument('--disable-background-timer-throttling')
        chrome_options.add_argument('--disable-backgrounding-occluded-windows')
        chrome_options.add_argument('--disable-breakpad')
        chrome_options.add_argument('--disable-component-update')
        chrome_options.add_argument('--disable-domain-reliability')
        chrome_options.add_argument('--disable-sync')
        chrome_options.add_argument('--js-flags="--max-device-memory=512 --max-heap-size=512"')
        chrome_options.add_argument('--mute-audio')
        chrome_options.add_argument('--disable-notifications')
        chrome_options.add_argument('--disable-popup-blocking')
        prefs = {
            "profile.default_content_setting_values.notifications": 2,
            "profile.default_content_setting_values.geolocation": 2,
            "profile.default_content_setting_values.popups": 2,
            "profile.content_settings.exceptions.mixed_script": {
                "*": {"setting": 1}
            },
            "safebrowsing.enabled": False
        }
        chrome_options.add_argument('--allow-running-insecure-content')
        chrome_options.add_argument('--disable-web-security')
        chrome_options.add_argument('--ignore-certificate-errors')
        if not self.grabar_video:
            prefs["profile.default_content_setting_values.images"] = 2
        chrome_options.add_experimental_option("prefs", prefs)
        chrome_options.add_argument('--disable-blink-features=AutomationControlled')
        chrome_options.add_experimental_option("excludeSwitches", ["enable-automation"])
        chrome_options.add_experimental_option('useAutomationExtension', False)
        chrome_options.add_argument('--autoplay-policy=no-user-gesture-required')
        chrome_options.add_argument('user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')
        chrome_options.set_capability('goog:loggingPrefs', {
            'performance': 'ALL',
            'browser': 'ALL'
        })
        self.driver = webdriver.Chrome(options=chrome_options)
        self.driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
        self.iniciar_monitoreo_red()
        print("      ⏳ Navegador iniciando con 5s de paciencia...")
        time.sleep(5)
    def limpiar_nombre_radio(self, nombre):
        """Limpia el nombre de la radio (quita asteriscos, etc)"""
        nombre = nombre.strip()
        nombre = nombre.replace('*', '')
        nombre = ' '.join(nombre.split())
        return nombre
    def preparar_query_busqueda(self, nombre_radio):
        """Prepara la query de búsqueda optimizada"""
        nombre = self.limpiar_nombre_radio(nombre_radio)
        nombre_lower = nombre.lower()
        if 'radio' not in nombre_lower:
            query = f"radio {nombre}"
        else:
            query = nombre
        query += " en vivo online"
        return query
    def buscar_sitios_duckduckgo(self, nombre_radio, max_resultados=5):
        """Busca sitios de la radio usando DuckDuckGo (HTML) y retorna una lista de candidatos"""
        query = self.preparar_query_busqueda(nombre_radio)
        search_url = f"https://html.duckduckgo.com/html/?q={quote_plus(query)}&kl=ar-es"
        print(f"    🔎 Buscando en DuckDuckGo: '{query}'")
        try:
            with self.driver_lock:
                self.driver.get(search_url)
            time.sleep(10)
        except Exception as e:
            print(f"    ✗ Error cargando búsqueda: {e}")
            return []
        elementos_resultado = []
        try:
            results = self.driver.find_elements(By.CSS_SELECTOR, '.result')
            for res in results:
                try:
                    link_el = res.find_element(By.CSS_SELECTOR, '.result__a')
                    href = link_el.get_attribute('href')
                    if href and 'uddg=' in href:
                        try:
                            import urllib.parse
                            parsed = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
                            if 'uddg' in parsed:
                                href = parsed['uddg'][0]
                        except: pass
                    try:
                        snippet = res.find_element(By.CSS_SELECTOR, '.result__snippet').text.lower()
                    except:
                        snippet = ""
                    if href and href.startswith('http'):
                        elementos_resultado.append({'url': href, 'snippet': snippet})
                except:
                    continue
        except Exception as e:
            print(f"    Error extrayendo resultados detallados: {e}")
        if not elementos_resultado:
            try:
                todos_links = self.driver.find_elements(By.TAG_NAME, 'a')
                for link in todos_links:
                    href = link.get_attribute('href')
                    if href and 'duckduckgo.com' not in href and href.startswith('http'):
                        elementos_resultado.append({'url': href, 'snippet': ""})
            except: pass
        nombre_limpio = self.limpiar_nombre_radio(nombre_radio).lower()
        primera_palabra = nombre_limpio.split()[0] if nombre_limpio.split() else ""
        keywords_radio = ["radio", "emisora", "escuchar", "online", "vivo", "dial", "fm", "am", "estación", "streaming", "broadcasting"]
        dominios_ignorar = [
            'duckduckgo.com', 'google.com', 'youtube.com', 'facebook.com',
            'instagram.com', 'twitter.com', 'x.com', 'wikipedia.org',
            'wikimedia', 'linkedin.com', 'tiktok.com', 'reddit.com'
        ]
        agregadores = [
            'tunein.com', 'radio.net', 'onlineradiobox.com', 'radiostationusa.fm',
            'raddio.net', 'radioarg.net', 'streema.com', 'mytuner-radio.com',
            'radio.garden', 'radios.com.ar', 'vtuner.com', 'live-radio.net',
            'radiomap.eu', 'fmstream.org', 'streamitter.com', 'estacionesderadio.com.ar'
        ]
        candidatos_top = []
        candidatos_oficiales = []
        candidatos_otros = []
        candidatos_agregadores = []
        vistos = set()
        for res in elementos_resultado:
            url = res['url']
            url_lower = url.lower()
            snippet = res['snippet']
            domain = urlparse(url_lower).netloc
            if domain in vistos: continue
            vistos.add(domain)
            if any(d in url_lower for d in dominios_ignorar):
                continue
            if any(agg in url_lower for agg in agregadores):
                candidatos_agregadores.append(url)
                continue
            es_com_ar = url_lower.endswith('.ar') or '.com.ar' in url_lower or '.com' in url_lower
            tiene_nombre = primera_palabra in url_lower
            tiene_radio_snippet = any(kw in snippet for kw in keywords_radio)
            domain_exacto = domain.replace('www.', '')
            domain_pure = domain_exacto
            for tld in ['.com.ar', '.com', '.ar', '.net', '.fm', '.org', '.live', '.tv']:
                if domain_exacto.endswith(tld):
                    domain_pure = domain_exacto[:-len(tld)]
                    if domain_pure.endswith('.'): domain_pure = domain_pure[:-1]
                    break
            else:
                if '.' in domain_exacto:
                    domain_pure = domain_exacto.split('.')[0]
            nombre_puro_busq = nombre_limpio.replace('radio', '').strip().replace(' ', '').replace('-', '')
            nombre_total_busq = nombre_limpio.replace(' ', '').replace('-', '')
            if domain_pure == nombre_puro_busq or domain_pure == nombre_total_busq:
                print(f"      💎 MUY PROBABLE: {url} (usando inmediatamente)")
                return [url]
            if es_com_ar and tiene_nombre:
                if tiene_radio_snippet:
                    candidatos_top.append(url)
                else:
                    candidatos_oficiales.append(url)
            elif tiene_nombre or tiene_radio_snippet:
                candidatos_otros.append(url)
        resultados = candidatos_top + candidatos_oficiales + candidatos_otros + candidatos_agregadores
        print(f"    ✓ Priorización finalizada: {len(candidatos_top)} top, {len(candidatos_oficiales)} oficiales, {len(candidatos_agregadores)} agregadores")
        return resultados[:max_resultados]
    def _generar_urls_posibles(self, nombre_limpio):
        """Genera URLs posibles basadas en el nombre"""
        urls = []
        nombre_sin_radio = nombre_limpio.replace('radio ', '').replace(' radio', '').strip()
        versiones = [
            nombre_sin_radio.replace(' ', ''),
            nombre_sin_radio.replace(' ', '-'),
            'radio' + nombre_sin_radio.replace(' ', ''),
        ]
        tlds = ['.com.ar', '.ar', '.fm']
        for version in versiones:
            for tld in tlds:
                urls.append(f"https://www.{version}{tld}")
                urls.append(f"https://{version}{tld}")
        return urls
    def _escanear_contexto_actual(self):
        """Escanea el DOM y retorna los streams detectados por el monitor de red en tiempo real"""
        encontrados = list(self._streams_detectados_pasivamente)
        for tag in ['audio', 'video', 'source', 'object', 'embed']:
            try:
                with self.driver_lock:
                    if not self.driver: continue
                    elements = self.driver.find_elements(By.TAG_NAME, tag)
                for el in elements:
                    for attr in ['src', 'data', 'value']:
                        try:
                            val = el.get_attribute(attr)
                            if val and self._es_stream_audio(val):
                                encontrados.append(val)
                        except: continue
            except:
                continue
        return list(set(encontrados))
    def _buscar_en_iframes(self):
        """Busca streams dentro de iframes en el contexto actual"""
        streams_found = []
        try:
            iframes = self.driver.find_elements(By.TAG_NAME, 'iframe')
            if not iframes:
                return []
            print(f"      🖼️ Analizando {len(iframes)} iframes...")
            for iframe in iframes:
                try:
                    iframe_src = iframe.get_attribute('src')
                    if iframe_src and any(kw in iframe_src.lower() for kw in ['player', 'stream', 'listen', 'radio', 'vivo', 'embed', 'cast', 'media']):
                        print(f"      📺 Analizando iframe: {iframe_src[:60]}...")
                        self.driver.switch_to.frame(iframe)
                        time.sleep(10)
                        streams_iframe = self._clickear_botones_play()
                        if isinstance(streams_iframe, list):
                            urls_validadas = [s for s in streams_iframe if isinstance(s, str) and s.startswith('http')]
                            streams_found.extend(urls_validadas)
                        time.sleep(10)
                        streams_found.extend(self._escanear_contexto_actual())
                        self.driver.switch_to.default_content()
                except Exception:
                    try:
                        self.driver.switch_to.default_content()
                    except:
                        pass
                    continue
        except Exception as e:
            print(f"      ⚠️ Error buscando en iframes: {e}")
        return streams_found
    def _esperar_stream(self, timeout):
        """Espera hasta que se detecte un stream confirmado o se agote el tiempo"""
        start = time.time()
        confirmado_una_vez = False
        while time.time() - start < timeout:
            if self._streams_confirmados_pasivamente:
                if not confirmado_una_vez:
                    print(f"      🎵 Stream confirmado detectado, esperando 3s para estabilizar solicitud...")
                    confirmado_una_vez = True
                    time.sleep(3)
                return True
            time.sleep(0.5)
        return False
    def extraer_streams(self, url, nombre_radio=None):
        """Extrae streams de una URL"""
        streams = []
        es_repo = "radios-argentinas.org" in url
        try:
            if self.grabar_video:
                if nombre_radio:
                    id_video = nombre_radio
                else:
                    id_video = urlparse(url).netloc.replace('.', '_')
                self.iniciar_grabacion(id_video)
            print(f"      📡 Cargando página...")
            with self.driver_lock:
                self.driver.get(url)
            if es_repo:
                print(f"      ⏳ Esperando actividad en el repositorio (máx 12s)...")
                if self._esperar_stream(12):
                    print(f"      ✅ Actividad detectada rápidamente!")
                else:
                    if "/embed/" not in url:
                        print(f"      ⏳ Sin actividad, buscando posible redirección rápida...")
                    else:
                        print(f"      ⏱️ Sin actividad inmediata en embed, seguiremos analizando...")
            else:
                time.sleep(10)
            if "radios-argentinas.org" in url and "/embed/" not in url:
                print(f"      🇦🇷 Analizando estructura de radios-argentinas.org...")
                try:
                    with self.driver_lock:
                        elementos_popup = self.driver.find_elements(By.XPATH, "//*[contains(@onclick, 'openPopUp')]")
                    for el in elementos_popup:
                        onclick_text = el.get_attribute('onclick')
                        match_id = re.search(r"openPopUp\(['\"]([^'\"]+)['\"]\)", onclick_text)
                        if match_id:
                            popup_id = match_id.group(1)
                            embed_url = f"http://e.radios-argentinas.org/embed/{popup_id}"
                            print(f"      🚀 Popup ID detectado: {popup_id}")
                            print(f"      🔗 Redirigiendo página principal a: {embed_url}")
                            with self.driver_lock:
                                self.driver.get(embed_url)
                            print(f"      ⏳ Esperando actividad en embed (máx 12s)...")
                            if self._esperar_stream(12):
                                print(f"      ✅ Actividad detectada en embed!")
                            else:
                                print(f"      ⚠️ No se detectó actividad automática en embed. Intentaremos clickear.")
                            break
                except Exception as e:
                    print(f"      ⚠️ No se pudo procesar el popup de radios-argentinas: {e}")
            print(f"      🔍 Escaneo pasivo inicial...")
            streams.extend(self._escanear_contexto_actual())
            if not streams:
                print(f"      ⚠️ No se detectó audio inicial. Intentando interactuar con botones de play...")
                streams_encontrados = self._clickear_botones_play()
                if streams_encontrados:
                    print(f"      🎮 Streams encontrados tras interacción, esperando estabilización...")
                    if isinstance(streams_encontrados, list):
                        urls_validadas = [s for s in streams_encontrados if isinstance(s, str) and s.startswith('http')]
                        streams.extend(urls_validadas)
                    time.sleep(10)
                    streams.extend(self._escanear_contexto_actual())
            else:
                print(f"      ✅ Stream detectado pasivamente")
            if not streams:
                streams_iframes = self._buscar_en_iframes()
                streams.extend(streams_iframes)
                if streams_iframes:
                    streams.extend(self._escanear_contexto_actual())
            self._imprimir_logs_consola()
            if self.grabar_video:
                self.detener_grabacion()
        except Exception as e:
            print(f"      ✗ Error extrayendo streams: {e}")
            if self.grabar_video:
                self.detener_grabacion()
        print(f"      🔬 Normalizando y validando {len(streams)} candidatos...")
        streams = list(set(streams))
        streams_procesados = []
        for s in streams:
            url_norm = self._normalizar_url_stream(s)
            streams_procesados.append(url_norm)
        streams = list(set(streams_procesados))
        candidatos_validos = []
        candidatos_ya_validados = set()
        def validar_candidato(url_candidata):
            """Valida si la URL es un stream real usando el verificador central"""
            if url_candidata in candidatos_ya_validados:
                return None
            candidatos_ya_validados.add(url_candidata)
            if self._verificar_stream_real(url_candidata):
                return url_candidata
            return None
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=5) as executor:
            futures = [executor.submit(validar_candidato, s) for s in streams]
            for f in as_completed(futures):
                res = f.result()
                if res:
                    candidatos_validos.append(res)
        if not candidatos_validos and streams:
            print(f"      ⚠️ Ningún candidato pasó la validación estricta de headers. No se devolverán sospechosos.")
            return []
        return list(set(candidatos_validos))
    def _imprimir_logs_consola(self):
        """Captura y muestra los logs de la consola de JavaScript del navegador"""
        try:
            with self.driver_lock:
                logs = self.driver.get_log('browser')
            if logs:
                print(f"      🌐 [CONSOLA JS] {len(logs)} mensajes encontrados:")
                for entry in logs:
                    timestamp = datetime.fromtimestamp(entry['timestamp']/1000).strftime('%H:%M:%S')
                    level = entry['level']
                    msg = entry['message']
                    if len(msg) > 150: msg = msg[:147] + "..."
                    print(f"         [{timestamp}] {level}: {msg}")
        except:
            pass
    def _clickear_botones_play(self):
        """Busca y clickea el PRIMER botón de play que encuentre en el contexto actual.
           Retorna una lista de streams encontrados durante la interacción."""
        streams_interaccion = []
        ventanas_originales = len(self.driver.window_handles)
        selectores = [
            'button#play_pause_button', '#play_pause_button',
            '[class*="play"]', '[class*="Play"]', '[class*="PLAY"]',
            '[class*="player"]', '[class*="Player"]',
            '[class*="btn-play"]', '[class*="playButton"]', '[class*="play-button"]',
            '[class*="btnPlay"]', '[class*="PlayBtn"]',
            '[id*="play"]', '[id*="Play"]', '[id*="player"]',
            '[id*="btnPlay"]', '[id*="playBtn"]',
            '[aria-label*="play" i]', '[aria-label*="reproducir" i]',
            '[aria-label*="Play" i]', '[aria-label*="Reproducir" i]',
            '[title*="play" i]', '[title*="reproducir" i]',
            'button[class*="icon-play"]', 'button[class*="fa-play"]',
            'div[class*="icon-play"]', 'div[class*="fa-play"]',
            'svg[class*="play"]', 'svg[aria-label*="play" i]',
            '.player-button', '.audio-player button', '.radio-player button',
            '.stream-button', '.live-button', '.online-button',
            'div[onclick*="play"]', 'div[onclick*="stream"]',
            'a[href*="play"]', 'a[href*="stream"]'
        ]
        for selector in selectores:
            try:
                with self.driver_lock:
                    elementos = self.driver.find_elements(By.CSS_SELECTOR, selector)
                if elementos:
                    print(f"      🔎 Selector '{selector}' encontró {len(elementos)} candidato(s)")
                for i, elemento in enumerate(elementos):
                    try:
                        with self.driver_lock:
                            is_displayed = elemento.is_displayed()
                            size = elemento.size
                        if not is_displayed:
                            if any(kw in selector for kw in ['play', 'player', '#']):
                                print(f"         ⚠️ Elemento {i} ({selector}) existe pero está ocultO (size: {size})")
                            continue
                        print(f"         🎯 Intentando interactuar con elemento {i} visible...")
                        try:
                            with self.driver_lock:
                                onclick_attr = elemento.get_attribute('onclick')
                            if onclick_attr and ('openPopUp' in onclick_attr or 'window.open' in onclick_attr):
                                print(f"      🚀 Ejecutando JS directamente (onclick): {onclick_attr[:60]}...")
                                js_to_run = onclick_attr.replace('return ', '').strip()
                                with self.driver_lock:
                                    self.driver.execute_script(js_to_run)
                                time.sleep(10)
                                print(f"      🖱️ Script ejecutado exitosamente sin click físico")
                            else:
                                try:
                                    with self.driver_lock:
                                        elemento.click()
                                except:
                                    with self.driver_lock:
                                        self.driver.execute_script("arguments[0].click();", elemento)
                                print(f"      🖱️ Primer botón de play clickeado ({selector})")
                        except Exception:
                            try:
                                with self.driver_lock:
                                    elemento.click()
                            except:
                                pass
                        time.sleep(10)
                        streams_interaccion.extend(self._escanear_contexto_actual())
                        with self.driver_lock:
                            ventanas_actuales = len(self.driver.window_handles)
                        if ventanas_actuales > ventanas_originales:
                            print(f"      🪟 Popup detectado por el click, analizando...")
                            with self.driver_lock:
                                self.driver.switch_to.window(self.driver.window_handles[-1])
                            time.sleep(10)
                            streams_interaccion.extend(self._escanear_contexto_actual())
                            streams_pop = self._clickear_botones_play()
                            streams_interaccion.extend(streams_pop)
                            streams_interaccion.extend(self._buscar_en_iframes())
                            time.sleep(10)
                            streams_interaccion.extend(self._escanear_contexto_actual())
                            with self.driver_lock:
                                self.driver.close()
                                if len(self.driver.window_handles) > 0:
                                    self.driver.switch_to.window(self.driver.window_handles[0])
                        streams_validos = [s for s in streams_interaccion if isinstance(s, str) and s.startswith('http')]
                        if streams_validos:
                            return streams_interaccion
                    except Exception:
                        continue
            except Exception:
                continue
        return streams_interaccion
    def _es_stream_audio(self, url):
        """Detecta si una URL es de audio streaming"""
        if not url or not isinstance(url, str):
            return False
        url_lower = url.lower()
        extensiones_ignorar = [
            '.js', '.css', '.png', '.jpg', '.jpeg', '.gif', '.svg', '.ico',
            '.woff', '.woff2', '.ttf', '.eot', '.json', '.xml', '.html',
            '.webp', '.map', '.txt'
        ]
        if any(url_lower.endswith(ext) for ext in extensiones_ignorar):
            return False
        palabras_ignorar = [
            'duckduckgo.com', 'google.com', 'facebook.com',
            '/js/', '/css/', '/images/', '/img/', '/fonts/',
            '/assets/', '/_astro/', '/static/',
            'analytics', 'tracking', 'pixel', 'advertisement'
        ]
        if any(palabra in url_lower for palabra in palabras_ignorar):
            return False
        extensiones_audio = ['.mp3', '.aac', '.aacp', '.m3u8', '.pls', '.m3u', '.ogg', '.oga']
        if any(ext in url_lower for ext in extensiones_audio):
            return True
        keywords_validos = [
            'icecast', 'shoutcast', 'streamtheworld',
            '/stream', '/live', '/radio', '/audio',
            'listen', 'player', 'broadcast', 'api/listening',
        ]
        parsed = urlparse(url)
        path = parsed.path.lower()
        if any(kw in path or kw in parsed.netloc.lower() for kw in keywords_validos):
            if not any(ignore in path for ignore in ['/js/', '/css/', '/fonts/', '/images/']):
                return True
        if 'emisoraenvivo.com/api/listening/' in url_lower:
            return True
        if any(f':{port}' in url for port in ['8000', '8080', '8443', '9000', '7189']):
            if not any(ext in url_lower for ext in extensiones_ignorar):
                return True
        return False
    def _normalizar_url_stream(self, url):
        """Transforma URLs de StreamTheWorld o APIs de terceros al formato de stream directo"""
        if not url or not isinstance(url, str):
            return url
        url_lower = url.lower()
        if 'live.streamtheworld.com' in url_lower:
            match = re.search(r'https?://\d+\.live\.streamtheworld\.com/([^?#]+)', url, re.IGNORECASE)
            if match:
                mountpoint = match.group(1)
                query_params = ""
                if '?' in url:
                    query_params = "?" + url.split('?', 1)[1]
                nueva_url = f"https://playerservices.streamtheworld.com/api/livestream-redirect/{mountpoint}{query_params}"
                print(f"      🔄 StreamTheWorld detectado: {url[:40]}... -> {nueva_url}")
                return nueva_url
        if 'emisoraenvivo.com/api/listening/' in url_lower:
            try:
                print(f"      📡 Consultando API de EmisoraEnvivo: {url[:60]}...")
                response = requests.get(url, headers=HEADERS_STREAM, timeout=5)
                if response.status_code == 200:
                    data = response.json()
                    nueva_url = data.get('stream', {}).get('data', {}).get('url')
                    if nueva_url:
                        print(f"      🔄 EmisoraEnvivo API resuelta: -> {nueva_url[:60]}...")
                        return self._normalizar_url_stream(nueva_url)
                else:
                    print(f"      ⚠️ API de EmisoraEnvivo respondió con status {response.status_code}")
            except Exception as e:
                print(f"      ⚠️ Error procesando API de EmisoraEnvivo: {e}")
        return url
    def buscar_en_repositorio_radios(self, nombre_radio):
        """Busca en el repositorio de radios-argentinas.org como fallback"""
        nombre_limpio = self.limpiar_nombre_radio(nombre_radio)
        query = quote_plus(nombre_limpio)
        url_busqueda = f"https://www.radios-argentinas.org/busca?q={query}"
        print(f"    � Buscando en repositorio: {url_busqueda}")
        try:
            with self.driver_lock:
                self.driver.get(url_busqueda)
            start_search = time.time()
            found_results = False
            while time.time() - start_search < 8:
                try:
                    elementos = self.driver.find_elements(By.CSS_SELECTOR, 'li.mdc-grid-tile a')
                    if elementos:
                        found_results = True
                        break
                except:
                    pass
                time.sleep(0.5)
            if not found_results:
                print(f"    ✗ No se encontraron resultados en el repositorio (timeout 8s)")
                return None
            mejor_href = None
            for el in elementos:
                try:
                    titulo = el.find_element(By.CSS_SELECTOR, '.mdc-grid-tile__title').text.strip().lower()
                    href = el.get_attribute('href')
                    if nombre_limpio.lower() in titulo or titulo in nombre_limpio.lower():
                        mejor_href = href
                        print(f"      ✓ Match en repositorio: '{titulo}' -> {href}")
                        break
                except:
                    continue
            if not mejor_href and elementos:
                mejor_href = elementos[0].get_attribute('href')
                print(f"      ⚠️ Usando primer resultado del repositorio: {mejor_href}")
            return mejor_href
        except Exception as e:
            print(f"    ✗ Error en repositorio: {e}")
        return None
    def _verificar_stream_real(self, url):
        """Verifica si un stream de audio está realmente activo y es del tipo correcto"""
        try:
            r = requests.get(url, headers=HEADERS_STREAM, timeout=7, stream=True, allow_redirects=True)
            ct = r.headers.get('Content-Type', '').lower()
            tipos_audio = [
                'audio/', 'mpegurl', 'video/mp2t', 'application/ogg',
                'application/x-mpegurl', 'application/vnd.apple.mpegurl',
                'application/octet-stream', 'video/mp4'
            ]
            is_icy = any(k.lower().startswith('icy-') for k in r.headers.keys())
            if 'text/html' in ct or 'image/' in ct or 'text/javascript' in ct:
                print(f"    ✗ Candidato rechazado por Content-Type no-audio: {ct}")
                return False
            if not is_icy and not any(t in ct for t in tipos_audio):
                if ct and ct != 'binary/octet-stream':
                     print(f"    ⚠️ Content-Type inusual: {ct}. Verificando contenido...")
            for _ in r.iter_content(chunk_size=1024):
                break
            if r.status_code < 400:
                print(f"    ✅ Stream verificado! (Type: {ct if ct else 'unknown/icy'})")
                return True
        except Exception as e:
            pass
        return False
    def buscar_en_radio_browser(self, nombre_radio):
        """Busca la radio usando la API de Radio Browser (working=true)"""
        print(f"    🔍 Buscando en Radio Browser API: {nombre_radio}")
        try:
            nombre_busqueda = self.limpiar_nombre_radio(nombre_radio)
            nombre_limpio = re.sub(r'\(.*?\)', '', nombre_busqueda).strip()
            url_api = "https://de1.api.radio-browser.info/json/stations/search"
            params = {
                "name": nombre_limpio,
                "hidebroken": "true",
                "limit": 10,
                "order": "votes",
                "reverse": "true",
                "countrycode": "AR"
            }
            response = requests.get(url_api, params=params, timeout=10)
            if response.status_code == 200:
                resultados = response.json()
                if not resultados:
                    print(f"    ❌ No se encontraron resultados en Radio Browser para: {nombre_limpio}")
                    return None
                print(f"    ✨ Radio Browser encontró {len(resultados)} candidatos. Verificando...")
                for station in resultados:
                    url_stream = station.get("url_resolved") or station.get("url")
                    if url_stream:
                        if not self._es_stream_audio(url_stream):
                             continue
                        nombre_encontrado = station.get("name", "Desconocida")
                        print(f"    ⏳ Probando candidato: {nombre_encontrado} ({url_stream[:50]}...)")
                        if self._verificar_stream_real(url_stream):
                             print(f"    ✅ Stream verificado desde Radio Browser!")
                             return url_stream
                print(f"    ❌ Ninguno de los candidatos de Radio Browser funcionó.")
            else:
                print(f"    ❌ Error en Radio Browser API (Status: {response.status_code})")
        except Exception as e:
            print(f"    ❌ Error durante búsqueda en Radio Browser: {e}")
        return None
    def buscar_stream(self, nombre_radio):
        """Proceso completo de búsqueda: 1. API Radio Browser, 2. Repositorio, 3. DuckDuckGo"""
        print(f"    🔍 Buscando nuevo stream para: {nombre_radio}")
        print(f"    📡 Probando Radio Browser API primero...")
        stream_rb = self.buscar_en_radio_browser(nombre_radio)
        if stream_rb:
            return stream_rb, "Radio Browser"
        print(f"    🌐 No se encontró por API, iniciando navegador para búsqueda profunda...")
        self.setup_driver()
        print(f"    📦 Probando repositorio especializado...")
        sitio_repo = self.buscar_en_repositorio_radios(nombre_radio)
        if sitio_repo:
            print(f"    🌐 Analizando página del repositorio: {sitio_repo}")
            streams_repo = self.extraer_streams(sitio_repo, nombre_radio)
            for stream in streams_repo:
                if self._verificar_stream_real(stream):
                    return stream, "Navegador"
        print(f"    ⚠️ No se encontró en el repositorio, buscando en DuckDuckGo...")
        candidatos_ddg = self.buscar_sitios_duckduckgo(nombre_radio)
        for i, sitio in enumerate(candidatos_ddg, 1):
            print(f"    🌐 ({i}/{len(candidatos_ddg)}) Analizando candidato DDG: {sitio}")
            streams_ddg = self.extraer_streams(sitio, nombre_radio)
            for stream in streams_ddg:
                if self._verificar_stream_real(stream):
                    print(f"    ✅ Stream encontrado en DDG ({sitio})")
                    return stream, "Navegador"
        print(f"    ⚠️ Probando construcción manual de URLs...")
        nombre_limpio = self.limpiar_nombre_radio(nombre_radio).lower()
        urls_posibles = self._generar_urls_posibles(nombre_limpio)
        for url in urls_posibles:
            try:
                r = requests.head(url, timeout=3, allow_redirects=True)
                if r.status_code < 400:
                    print(f"    ✓ Sitio manual encontrado: {url}")
                    streams_manual = self.extraer_streams(url, nombre_radio)
                    for s in streams_manual:
                        if self._verificar_stream_real(s): return s, "Navegador"
            except: continue
        if 'streams_repo' in locals() and streams_repo:
            print(f"    ⚠️ Usando stream del repo sin verificación completa como último recurso")
            return streams_repo[0], "Navegador"
        return None, None
    def cerrar(self):
        self.detener_monitoreo_red()
        if self.driver:
            with self.driver_lock:
                try:
                    self.driver.quit()
                except:
                    pass
            self.driver = None

def buscar_stream_worker(radio, grabar_video):
    """Worker para buscar streams en paralelo"""
    finder = RadioStreamFinder(headless=True, grabar_video=grabar_video)
    error = None
    meta_info = {"origen": None}
    try:
        nuevo_stream, origen = finder.buscar_stream(radio['nombre'])
        meta_info["origen"] = origen
    except Exception as e:
        error = str(e)
        nuevo_stream = None
    finally:
        try:
            finder.cerrar()
        except:
            pass
    return radio, nuevo_stream, error, finder.last_exported_video, meta_info

def obtener_tag_por_url(url):
    """Determina el tag de formato basado en la URL"""
    u = url.lower()
    if '.m3u8' in u: return "M3U8"
    if '.m3u' in u: return "M3U"
    if '.pls' in u: return "PLS"
    if '.aac' in u or '.aacp' in u or 'streamtheworld' in u: return "AAC"
    if '.mp3' in u: return "MP3"
    return "STREAM"

def actualizar_markdown(lineas_originales, radios_actualizadas):
    """Actualiza las URLs, nombres y tags en el markdown original"""
    lineas_nuevas = lineas_originales.copy()
    for ra in radios_actualizadas:
        linea_num = ra['linea_num']
        url_vieja = ra['url_vieja']
        url_nueva = ra['url_nueva']
        nombre_nuevo = ra['nombre']
        linea_original = lineas_nuevas[linea_num]
        nuevo_tag = obtener_tag_por_url(url_nueva)
        url_vieja_esc = re.escape(url_vieja)
        patron = rf"\[([^\]]+)\]\({url_vieja_esc}\)"
        match = re.search(patron, linea_original)
        if match:
            linea_actualizada = linea_original.replace(match.group(0), f"[{nuevo_tag}]({url_nueva})")
        else:
            linea_actualizada = linea_original.replace(url_vieja, url_nueva)
        partes = linea_actualizada.split('|')
        if len(partes) >= 3:
            partes[2] = f" {nombre_nuevo} "
            linea_actualizada = "|".join(partes)
        lineas_nuevas[linea_num] = linea_actualizada
    return "\n".join(lineas_nuevas)

def es_primera_vez():
    """Verifica si es la primera vez que se abre la aplicación"""
    if not os.path.exists(ARCHIVO_SETTINGS):
        return True
    try:
        with open(ARCHIVO_SETTINGS, "r") as f:
            settings = json.load(f)
            return settings.get("primera_vez", True)
    except:
        return True

def marcar_primera_vez_completada():
    """Marca que ya se mostró la advertencia de primera vez"""
    settings = {}
    if os.path.exists(ARCHIVO_SETTINGS):
        try:
            with open(ARCHIVO_SETTINGS, "r") as f:
                settings = json.load(f)
        except:
            pass
    settings["primera_vez"] = False
    try:
        with open(ARCHIVO_SETTINGS, "w") as f:
            json.dump(settings, f)
    except:
        pass
try:
    from PyQt6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout,
                                QHBoxLayout, QPushButton, QCheckBox, QTableWidget,
                                QTableWidgetItem, QHeaderView, QTextEdit, QLabel,
                                QProgressBar, QSplitter, QMessageBox, QStyle,
                                QListWidget, QListWidgetItem, QStackedWidget, QSlider,
                                QDialog, QAbstractItemView)
    from PyQt6.QtCore import Qt, QThread, pyqtSignal, QObject, pyqtSlot, QUrl
    from PyQt6.QtGui import QColor, QFont, QTextCursor, QIcon, QPalette
    from PyQt6.QtMultimedia import QMediaPlayer, QAudioOutput
    from PyQt6.QtMultimediaWidgets import QVideoWidget
except ImportError:
    print("Error: PyQt6 no está instalado. Instálalo con: pip install PyQt6")
    sys.exit(1)

class StreamRedirector(QObject):
    text_written = pyqtSignal(str)
    def write(self, text):
        self.text_written.emit(str(text))
    def flush(self):
        pass

class RadioCheckWorker(QThread):
    log_signal = pyqtSignal(str)
    progress_signal = pyqtSignal(int, int)
    status_signal = pyqtSignal(str)
    table_init_signal = pyqtSignal(list)
    row_update_signal = pyqtSignal(int, str, str, str, str)
    video_found_signal = pyqtSignal(str, str)
    finished_signal = pyqtSignal(str)
    def __init__(self, auto_search, record_video):
        super().__init__()
        self.auto_search = auto_search
        self.record_video = record_video
        self.is_running = True
        self.radios = []
        self.lineas_originales = []
    def run(self):
        inicio = datetime.now()
        self.log_signal.emit("="*80)
        self.log_signal.emit("RADIO CHECKER")
        self.log_signal.emit("="*80)
        try:
            self.log_signal.emit("\n📥 Descargando gist...")
            try:
                markdown = obtener_gist()
                self.radios, self.lineas_originales = extraer_radios(markdown)
                total = len(self.radios)
                self.table_init_signal.emit(self.radios)
                self.log_signal.emit(f"✓ Se encontraron {total} streams para verificar\n")
            except Exception as e:
                self.log_signal.emit(f"❌ Error descargando/procesando gist: {e}")
                self.finished_signal.emit("Error inicial")
                return
            self.log_signal.emit("🔍 VERIFICANDO STREAMS...")
            self.status_signal.emit(f"Verificando {total} streams...")
            completados = 0
            conteo = {"ACTIVO": 0, "TIMEOUT": 0, "CAIDO": 0}
            radios_caidas = []
            radios_actualizadas = []
            with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
                future_to_index = {executor.submit(verificar_stream, radio.copy()): i for i, radio in enumerate(self.radios)}
                for future in as_completed(future_to_index):
                    if not self.is_running:
                        executor.shutdown(wait=False)
                        break
                    idx = future_to_index[future]
                    try:
                        radio_verificada, estado, info = future.result()
                        radio_original = self.radios[idx]
                        completados += 1
                        conteo[estado] += 1
                        if radio_verificada['nombre'] != radio_original['nombre']:
                            radios_actualizadas.append({
                                'nombre': radio_verificada['nombre'],
                                'url_vieja': radio_original['url'],
                                'url_nueva': radio_original['url'],
                                'linea_num': radio_original['linea_num']
                            })
                        self.radios[idx] = radio_verificada
                        self.progress_signal.emit(completados, total)
                        self.row_update_signal.emit(idx, estado, radio_verificada['url'], str(info), radio_verificada['nombre'])
                        if estado in ["CAIDO", "TIMEOUT"]:
                            radios_caidas.append((idx, radio_verificada))
                    except Exception as e:
                        self.log_signal.emit(f"Error verificando: {e}")
            if not self.is_running:
                self.finished_signal.emit("Cancelado por usuario")
                return
            self.log_signal.emit("\n" + "="*80)
            self.log_signal.emit("RESUMEN DE VERIFICACIÓN:")
            for estado_key, cantidad in conteo.items():
                porcentaje = (cantidad * 100 / total) if total else 0
                self.log_signal.emit(f"  {estado_key:<7}: {cantidad:3} ({porcentaje:.2f}%)")
            if radios_caidas and self.auto_search:
                self.log_signal.emit(f"\n⚠️  {len(radios_caidas)} streams caídos. Iniciando búsqueda automática...")
                self.status_signal.emit(f"Buscando {len(radios_caidas)} nuevos streams...")
                if self.record_video:
                    self.log_signal.emit("🎥 Modo grabación activado")
                with ThreadPoolExecutor(max_workers=MAX_BROWSER_THREADS) as executor:
                    future_to_item = {
                        executor.submit(buscar_stream_worker, item[1], self.record_video): item
                        for item in radios_caidas
                    }
                    completados_busqueda = 0
                    total_busqueda = len(radios_caidas)
                    for future in as_completed(future_to_item):
                        if not self.is_running:
                            break
                        idx_original, radio_orig = future_to_item[future]
                        completados_busqueda += 1
                        self.progress_signal.emit(completados_busqueda, total_busqueda)
                        try:
                            radio, nuevo_stream, error, video_path, meta_info = future.result()
                            progreso_msg = f"[{completados_busqueda}/{total_busqueda}] {radio['nombre']}"
                            if video_path:
                                self.video_found_signal.emit(radio['nombre'], video_path)
                            if error:
                                self.log_signal.emit(f"\n{progreso_msg}\n      ✗ Error: {error}")
                                self.row_update_signal.emit(idx_original, "ERROR_BUSQ", radio['url'], f"Err: {error}", radio['nombre'])
                            elif nuevo_stream:
                                radio['nombre'] = ajustar_nombre_por_url(radio['nombre'], nuevo_stream)
                                radios_actualizadas.append({
                                    'nombre': radio['nombre'],
                                    'url_vieja': radio_orig['url'],
                                    'url_nueva': nuevo_stream,
                                    'linea_num': radio['linea_num']
                                })
                                status_txt = f"ACTUALIZADO ({meta_info.get('origen', '')})"
                                self.row_update_signal.emit(idx_original, status_txt, nuevo_stream, "Nuevo stream encontrado", radio['nombre'])
                            else:
                                self.log_signal.emit(f"\n{progreso_msg}\n      ✗ No encontrado")
                                self.row_update_signal.emit(idx_original, "NO_ENCONTRADO", radio['url'], "Búsqueda fallida", radio['nombre'])
                        except Exception as e:
                            self.log_signal.emit(f"Error procesando resultado búsqueda: {e}")
            if radios_actualizadas:
                self.log_signal.emit(f"\n✅ Se encontraron {len(radios_actualizadas)} nuevos streams")
                markdown_nuevo = actualizar_markdown(self.lineas_originales, radios_actualizadas)
                try:
                    with open(ARCHIVO_MD_ACTUALIZADO, "w", encoding="utf-8") as f:
                        f.write(markdown_nuevo)
                    self.log_signal.emit(f"✓ Markdown guardado: {ARCHIVO_MD_ACTUALIZADO}")
                except Exception as e:
                    self.log_signal.emit(f"Error guardando markdown: {e}")
            else:
                 self.log_signal.emit("\nNo hubo actualizaciones para guardar.")
            fin = datetime.now()
            tiempo_total = fin - inicio
            self.log_signal.emit(f"\n⏱️  Tiempo total: {tiempo_total}")
            self.finished_signal.emit(f"Proceso finalizado. {len(radios_actualizadas)} actualizados.")
        except Exception as e:
            self.log_signal.emit(f"❌ Error fatal en worker: {e}")
            self.finished_signal.emit("Error fatal")
    def stop(self):
        self.is_running = False


class GUID(ctypes.Structure):
    _fields_ = [
        ("Data1", wintypes.DWORD),
        ("Data2", wintypes.WORD),
        ("Data3", wintypes.WORD),
        ("Data4", wintypes.BYTE * 8)
    ]

def DEFINE_GUID(l, w1, w2, b1, b2, b3, b4, b5, b6, b7, b8):
    return GUID(l, w1, w2, (wintypes.BYTE * 8)(b1, b2, b3, b4, b5, b6, b7, b8))

CLSID_TaskbarList = DEFINE_GUID(0x56FDF344, 0xFD6D, 0x11d0, 0x95, 0x8A, 0x00, 0x60, 0x97, 0xC9, 0xA0, 0x90)
IID_ITaskbarList3 = DEFINE_GUID(0xEA1AFB91, 0x9E28, 0x4B86, 0x90, 0xE9, 0x9E, 0x9F, 0x8A, 0x5E, 0xEF, 0xAF)

TBPF_NOPROGRESS    = 0
TBPF_INDETERMINATE = 0x1
TBPF_NORMAL        = 0x2
TBPF_ERROR         = 0x4
TBPF_PAUSED        = 0x8

class TaskbarProgress:
    def __init__(self, hwnd=None):
        self.hwnd = hwnd
        self._ptr = None
        try:
            self._init_interface()
        except Exception as e:
            print(f"Error initializing TaskbarProgress: {e}")
            self._ptr = None

    def _init_interface(self):
        try:
            # S_FALSE = 1, S_OK = 0, RPC_E_CHANGED_MODE = 0x80010106
            # We don't really care if it fails due to changed mode, Qt handles COM usually.
            ctypes.windll.ole32.CoInitialize(None)
        except Exception:
            pass
        
        ptr = ctypes.c_void_p()
        CLSCTX_INPROC_SERVER = 1
        
        try:
            hr = ctypes.windll.ole32.CoCreateInstance(
                ctypes.byref(CLSID_TaskbarList),
                None,
                CLSCTX_INPROC_SERVER,
                ctypes.byref(IID_ITaskbarList3),
                ctypes.byref(ptr)
            )
            
            if hr == 0 and ptr:
                self._ptr = ptr
                # HrInit is at index 3 in ITaskbarList3 (IUnknown=3 + ITaskbarList=1?? No, ITaskbarList inherits IUnknown)
                # IUnknown: QueryInterface(0), AddRef(1), Release(2)
                # ITaskbarList: HrInit(3), AddTab(4), DeleteTab(5), ActivateTab(6), SetActiveAlt(7)
                # ITaskbarList2: MarkFullscreenWindow(8)
                # ITaskbarList3: SetProgressValue(9), SetProgressState(10), ...
                init_func = self._get_vtable_func(3, ctypes.HRESULT)
                if init_func:
                    init_func(self._ptr)
        except Exception as e:
            print(f"Failed to create ITaskbarList3: {e}")
            self._ptr = None

    def _get_vtable_func(self, index, res_type, *arg_types):
        if not self._ptr or not self._ptr.value: return None
        try:
            pInterface = self._ptr.value
            # Get VTable pointer (first value at interface address)
            pVTable = ctypes.c_void_p.from_address(pInterface).value
            if not pVTable: return None
            # Get Function address (index-th entry in VTable)
            func_addr = ctypes.c_void_p.from_address(pVTable + index * ctypes.sizeof(ctypes.c_void_p)).value
            if not func_addr: return None
            
            return ctypes.WINFUNCTYPE(res_type, ctypes.c_void_p, *arg_types)(func_addr)
        except Exception as e:
            print(f"Error getting vtable func: {e}")
            return None

    def set_progress_value(self, current, total):
        # 9 is SetProgressValue
        if not self._ptr or not self.hwnd: return
        try:
            func = self._get_vtable_func(9, ctypes.HRESULT, wintypes.HWND, ctypes.c_uint64, ctypes.c_uint64)
            if func:
                func(self._ptr, self.hwnd, current, total)
        except: pass

    def set_progress_state(self, state):
        # 10 is SetProgressState
        if not self._ptr or not self.hwnd: return
        try:
            func = self._get_vtable_func(10, ctypes.HRESULT, wintypes.HWND, wintypes.DWORD)
            if func:
                func(self._ptr, self.hwnd, state)
        except: pass
            
    def set_hwnd(self, hwnd):
        self.hwnd = hwnd

class InfoDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Información de Radio Checker")
        self.setMinimumSize(500, 400)
        self.setStyleSheet("""
            QDialog {
                background-color: #252525;
                color: white;
            }
            QLabel {
                color: #e0e0e0;
                font-size: 14px;
            }
            QPushButton#nav_btn {
                background-color: #333;
                border-radius: 20px;
                padding: 10px;
                font-weight: bold;
                font-size: 18px;
                color: white;
                border: 1px solid #444;
            }
            QPushButton#nav_btn:hover {
                background-color: #444;
                border: 1px solid #555;
            }
            QPushButton#nav_btn:pressed {
                background-color: #2a82da;
            }
            QPushButton#nav_btn:disabled {
                background-color: #1a1a1a;
                color: #444;
                border: 1px solid #222;
            }
        """)
        layout = QVBoxLayout(self)
        self.pages = QStackedWidget()
        p1 = QWidget()
        l1 = QVBoxLayout(p1)
        h1 = QHBoxLayout()
        icon1 = QLabel()
        icon1.setPixmap(self.style().standardIcon(QStyle.StandardPixmap.SP_MessageBoxInformation).pixmap(32, 32))
        h1.addWidget(icon1)
        h1.addWidget(QLabel("<h2 style='color: #42A5F5; margin: 0;'> Bienvenido a Radio Checker</h2>"))
        h1.addStretch()
        l1.addLayout(h1)
        lbl1 = QLabel("<div style='margin-top: 10px; text-align: justify;'>"
                           "<p>Esta herramienta ha sido diseñada para automatizar la gestión y el mantenimiento de una extensa lista de emisoras de radio argentinas. Su objetivo principal es garantizar que todos los enlaces de streaming funcionen correctamente y se mantengan actualizados de forma autónoma.</p>"
                           "<p>El proceso comienza descargando la información más reciente desde un repositorio central alojado en GitHub Gist, asegurando que siempre trabaje con la versión más reciente del listado oficial. Una vez obtenida la lista, el sistema analiza la estructura del archivo para identificar cada emisora, su frecuencia y su enlace actual, preparándolos para una verificación exhaustiva y veloz mediante procesos concurrentes.</p>"
                           "</div>")
        lbl1.setWordWrap(True)
        l1.addWidget(lbl1)
        l1.addStretch()
        self.pages.addWidget(p1)
        p2 = QWidget()
        l2 = QVBoxLayout(p2)
        h2 = QHBoxLayout()
        icon2 = QLabel()
        icon2.setPixmap(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogApplyButton).pixmap(32, 32))
        h2.addWidget(icon2)
        h2.addWidget(QLabel("<h2 style='color: #4CAF50; margin: 0;'> Verificación de Streams</h2>"))
        h2.addStretch()
        l2.addLayout(h2)
        lbl2 = QLabel("<div style='margin-top: 10px; text-align: justify;'>"
                           "<p>Durante la fase de verificación técnica, el sistema realiza una conexión directa con cada servidor de streaming para validar su estado de actividad en tiempo real. Para garantizar un diagnóstico preciso, se establece un tiempo de espera inteligente que evita que enlaces lentos bloqueen el flujo de trabajo.</p>"
                           "<p>No solo comprobamos la disponibilidad del servidor, sino que también inspeccionamos minuciosamente las cabeceras de respuesta para confirmar que el contenido sea realmente un flujo de audio válido. Además, utilizamos identificadores de navegador reales para simular conexiones legítimas, evitando bloqueos automáticos y asegurando la mayor tasa de éxito posible en la verificación.</p>"
                           "</div>")
        lbl2.setWordWrap(True)
        l2.addWidget(lbl2)
        l2.addStretch()
        self.pages.addWidget(p2)
        p3 = QWidget()
        l3 = QVBoxLayout(p3)
        h3 = QHBoxLayout()
        icon3 = QLabel()
        icon3.setPixmap(self.style().standardIcon(QStyle.StandardPixmap.SP_BrowserReload).pixmap(32, 32))
        h3.addWidget(icon3)
        h3.addWidget(QLabel("<h2 style='color: #FFCA28; margin: 0;'> Búsqueda Automática</h2>"))
        h3.addStretch()
        l3.addLayout(h3)
        lbl3 = QLabel("<div style='margin-top: 10px; text-align: justify;'>"
                           "<p>Cuando se detecta que una emisora está fuera de línea, la aplicación activa un proceso de recuperación inteligente por pasos. En primera instancia, consulta la base de datos de <b>Radio Browser API</b>, una plataforma global que permite localizar rápidamente streams verificados por la comunidad.</p>"
                           "<p>Si la API no devuelve resultados válidos, el sistema inicia automáticamente una instancia del navegador para explorar la web. Durante esta fase, el script realiza un monitoreo de red en tiempo real para capturar el enlace exacto del audio mientras simula interacciones humanas y clics en botones de reproducción, agotando todas las instancias para restaurar el servicio.</p>"
                           "</div>")
        lbl3.setWordWrap(True)
        l3.addWidget(lbl3)
        l3.addStretch()
        self.pages.addWidget(p3)
        p4 = QWidget()
        l4 = QVBoxLayout(p4)
        h4 = QHBoxLayout()
        icon4 = QLabel()
        icon4.setPixmap(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPlay).pixmap(32, 32))
        h4.addWidget(icon4)
        h4.addWidget(QLabel("<h2 style='color: #EF5350; margin: 0;'> Grabación Debug</h2>"))
        h4.addStretch()
        l4.addLayout(h4)
        lbl4 = QLabel("<div style='margin-top: 10px; text-align: justify;'>"
                           "<p>Para los usuarios que desean una supervisión total o necesitan resolver problemas complejos de detección, la aplicación ofrece un modo de grabación de depuración. Al activar esta función, el sistema captura un video completo de cada sesión de búsqueda realizada por el navegador automático.</p>"
                           "<p>Esto resulta extremadamente útil para visualizar exactamente qué sucede en el sitio web de una radio, permitiendo identificar cambios visuales o errores técnicos que impidieron la detección. Todos estos videos se organizan automáticamente y pueden ser revisados directamente desde el reproductor integrado en esta herramienta.</p>"
                           "</div>")
        lbl4.setWordWrap(True)
        l4.addWidget(lbl4)
        l4.addStretch()
        self.pages.addWidget(p4)
        layout.addWidget(self.pages)
        nav_layout = QHBoxLayout()
        self.btn_prev = QPushButton("←")
        self.btn_prev.setObjectName("nav_btn")
        self.btn_prev.setFixedSize(60, 40)
        self.btn_prev.clicked.connect(self.prev_page)
        self.page_label = QLabel(f"1 / {self.pages.count()}")
        self.page_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.page_label.setStyleSheet("font-weight: bold; font-size: 16px; color: #aaa;")
        self.btn_next = QPushButton("→")
        self.btn_next.setObjectName("nav_btn")
        self.btn_next.setFixedSize(60, 40)
        self.btn_next.clicked.connect(self.next_page)
        nav_layout.addWidget(self.btn_prev)
        nav_layout.addStretch()
        nav_layout.addWidget(self.page_label)
        nav_layout.addStretch()
        nav_layout.addWidget(self.btn_next)
        layout.addLayout(nav_layout)
        self.update_nav_buttons()
    def prev_page(self):
        curr = self.pages.currentIndex()
        if curr > 0:
            self.pages.setCurrentIndex(curr - 1)
            self.update_nav_buttons()
    def next_page(self):
        curr = self.pages.currentIndex()
        if curr < self.pages.count() - 1:
            self.pages.setCurrentIndex(curr + 1)
            self.update_nav_buttons()
    def update_nav_buttons(self):
        curr = self.pages.currentIndex()
        total = self.pages.count()
        self.btn_prev.setEnabled(curr > 0)
        self.btn_next.setEnabled(curr < total - 1)
        self.page_label.setText(f"{curr + 1} / {total}")

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Radio Checker")
        self.resize(1200, 800)
        self.redirector = StreamRedirector()
        self.redirector.text_written.connect(self.append_log)
        sys.stdout = self.redirector
        sys.stderr = self.redirector
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        self.worker = None
        self.worker = None
        self.setStyleSheet("""
            QMainWindow {
                background-color: #1e1e1e;
            }
            QWidget {
                color: #e0e0e0;
                font-family: 'Segoe UI', Arial;
            }
            QPushButton {
                background-color: #333333;
                color: white;
                border: 1px solid #444;
                border-radius: 4px;
                padding: 6px 14px;
                font-size: 13px;
                min-height: 24px;
            }
            QPushButton:hover {
                background-color: #444444;
                border: 1px solid #555;
            }
            QPushButton:pressed {
                background-color: #2a82da;
                border: 1px solid #2a82da;
            }
            QPushButton:disabled {
                background-color: #252525;
                color: #555;
                border: 1px solid #333;
            }
            QPushButton#btn_start {
                background-color: #2e7d32;
                border: 1px solid #1b5e20;
                font-weight: bold;
            }
            QPushButton#btn_start:hover {
                background-color: #388e3c;
            }
            QPushButton#btn_start:disabled {
                background-color: #1b331b;
                color: #444;
            }
            QPushButton#btn_stop {
                background-color: #c62828;
                border: 1px solid #b71c1c;
            }
            QPushButton#btn_stop:hover {
                background-color: #d32f2f;
            }
            QPushButton#btn_stop:disabled {
                background-color: #331b1b;
                color: #444;
            }
            QCheckBox {
                spacing: 8px;
                color: #e0e0e0;
            }
            QCheckBox::indicator {
                width: 18px;
                height: 18px;
                background-color: #333;
                border: 1px solid #555;
                border-radius: 3px;
            }
            QCheckBox::indicator:checked {
                background-color: #2a82da;
                border: 1px solid #2a82da;
                image: url(check_mark.png); /* Note: if we don't have the icon it will just be blue */
            }
            QTableWidget {
                background-color: #252525;
                alternate-background-color: #2a2a2a;
                gridline-color: #333;
                border: 1px solid #333;
                selection-background-color: #2a82da;
                outline: 0;
            }
            QHeaderView::section {
                background-color: #333;
                color: #aaa;
                padding: 6px;
                border: 1px solid #222;
                font-weight: bold;
            }
            QScrollBar:vertical {
                border: none;
                background: #1e1e1e;
                width: 10px;
                margin: 0px;
            }
            QScrollBar::handle:vertical {
                background: #444;
                min-height: 20px;
                border-radius: 5px;
            }
            QScrollBar::handle:vertical:hover {
                background: #555;
            }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
                height: 0px;
            }
            QProgressBar {
                border: 1px solid #333;
                border-radius: 4px;
                text-align: center;
                background-color: #252525;
            }
            QProgressBar::chunk {
                background-color: #2a82da;
                width: 10px;
            }
        """)
        control_panel = QHBoxLayout()
        control_panel.setContentsMargins(10, 10, 10, 10)
        control_panel.setSpacing(10)
        self.btn_start = QPushButton(" Iniciar Verificación")
        self.btn_start.setObjectName("btn_start")
        self.btn_start.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPlay))
        self.btn_start.clicked.connect(self.start_process)
        self.btn_stop = QPushButton(" Detener")
        self.btn_stop.setObjectName("btn_stop")
        self.btn_stop.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaStop))
        self.btn_stop.clicked.connect(self.stop_process)
        self.btn_stop.setEnabled(False)
        self.btn_info = QPushButton(" Información")
        self.btn_info.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MessageBoxInformation))
        self.btn_info.clicked.connect(self.show_info)
        self.btn_info.setToolTip("Cómo funciona este script")
        self.check_auto_search = QCheckBox("Auto-búsqueda")
        self.check_auto_search.setChecked(True)
        self.check_auto_search.setToolTip("Busca automáticamente nuevos streams para radios caídas")
        self.check_video = QCheckBox("Grabar Debug")
        self.check_video.setToolTip("Graba video de la búsqueda automática (Selenium)")
        self.btn_clean = QPushButton(" Limpiar Videos")
        self.btn_clean.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogDiscardButton))
        self.btn_clean.clicked.connect(self.limpiar_videos)
        self.btn_clean.setToolTip("Borra todos los videos de las carpetas temp y exported")
        control_panel.addWidget(self.btn_start)
        control_panel.addWidget(self.btn_stop)
        control_panel.addSpacing(10)
        control_panel.addWidget(self.btn_info)
        control_panel.addSpacing(20)
        control_panel.addWidget(self.check_auto_search)
        control_panel.addWidget(self.check_video)
        control_panel.addStretch()
        control_panel.addWidget(self.btn_clean)
        main_layout.addLayout(control_panel)
        splitter = QSplitter(Qt.Orientation.Vertical)
        self.table = QTableWidget()
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setColumnCount(4)
        self.table.setHorizontalHeaderLabels(["Radio/Frecuencia", "Estado", "URL Stream", "Info / Debug"])
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(1, 100)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        splitter.addWidget(self.table)
        self.log_console = QTextEdit()
        self.log_console.setReadOnly(True)
        self.log_console.setStyleSheet("background-color: #1e1e1e; color: #00ff00; font-family: Consolas;")
        splitter.addWidget(self.log_console)
        splitter.setSizes([500, 300])
        self.main_splitter = QSplitter(Qt.Orientation.Horizontal)
        self.main_splitter.addWidget(splitter)
        self.video_panel = QStackedWidget()
        self.video_panel.setMinimumWidth(350)
        self.video_list_page = QWidget()
        v_list_layout = QVBoxLayout(self.video_list_page)
        v_header_layout = QHBoxLayout()
        v_icon_label = QLabel()
        v_icon_label.setPixmap(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPlay).pixmap(20, 20))
        v_label = QLabel("Videos de la Sesión")
        v_label.setStyleSheet("font-weight: bold; font-size: 16px;")
        v_header_layout.addWidget(v_icon_label)
        v_header_layout.addWidget(v_label)
        v_header_layout.addStretch()
        v_list_layout.addLayout(v_header_layout)
        self.video_list = QListWidget()
        self.video_list.setStyleSheet("""
            QListWidget {
                background-color: #252525;
                border: 1px solid #333;
                border-radius: 5px;
                padding: 5px;
            }
            QListWidget::item {
                padding: 10px;
                border-bottom: 1px solid #333;
                border-radius: 4px;
            }
            QListWidget::item:hover {
                background-color: #333;
            }
            QListWidget::item:selected {
                background-color: #2a82da;
                color: white;
            }
        """)
        self.video_list.itemClicked.connect(self.play_selected_video)
        v_list_layout.addWidget(self.video_list)
        self.video_panel.addWidget(self.video_list_page)
        self.player_page = QWidget()
        self.player_page.setStyleSheet("background-color: #1a1a1a;")
        player_layout = QVBoxLayout(self.player_page)
        player_layout.setContentsMargins(10, 10, 10, 10)
        player_top_bar = QHBoxLayout()
        btn_back = QPushButton(" Volver")
        btn_back.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ArrowBack))
        btn_back.clicked.connect(self.stop_and_back)
        btn_back.setStyleSheet("padding: 5px 15px; background-color: #333;")
        self.current_video_label = QLabel("Reproduciendo: ...")
        self.current_video_label.setStyleSheet("font-weight: bold; color: #42A5F5; font-size: 14px;")
        player_top_bar.addWidget(btn_back)
        player_top_bar.addSpacing(15)
        player_top_bar.addWidget(self.current_video_label)
        player_top_bar.addStretch()
        player_layout.addLayout(player_top_bar)
        video_container = QWidget()
        video_container.setStyleSheet("border: 1px solid #333; background-color: black;")
        video_container_layout = QVBoxLayout(video_container)
        video_container_layout.setContentsMargins(0, 0, 0, 0)
        self.video_widget = QVideoWidget()
        self.video_widget.setMinimumHeight(400)
        video_container_layout.addWidget(self.video_widget)
        player_layout.addWidget(video_container)
        controls_panel = QWidget()
        controls_panel.setStyleSheet("background-color: #252525; border-radius: 8px;")
        controls_layout = QVBoxLayout(controls_panel)
        progress_layout = QHBoxLayout()
        self.lbl_time_current = QLabel("00:00")
        self.lbl_time_current.setStyleSheet("color: #aaa; font-family: Consolas;")
        self.video_slider = QSlider(Qt.Orientation.Horizontal)
        self.video_slider.setRange(0, 0)
        self.video_slider.sliderMoved.connect(self.set_position)
        self.video_slider.sliderReleased.connect(self.play_after_seek)
        self.video_slider.setStyleSheet("""
            QSlider {
                height: 30px;
                padding-left: 10px;
                padding-right: 10px;
            }
            QSlider::groove:horizontal {
                border: 1px solid #333;
                height: 6px;
                background: #444;
                margin: 2px 0;
                border-radius: 3px;
            }
            QSlider::handle:horizontal {
                background: #42A5F5;
                border: 1px solid #42A5F5;
                width: 14px;
                height: 14px;
                margin: -5px 0;
                border-radius: 7px;
            }
            QSlider::handle:horizontal:hover {
                background: #64B5F6;
                border: 1px solid #64B5F6;
            }
        """)
        self.lbl_time_total = QLabel("00:00")
        self.lbl_time_total.setStyleSheet("color: #aaa; font-family: Consolas;")
        progress_layout.addWidget(self.lbl_time_current)
        progress_layout.addWidget(self.video_slider)
        progress_layout.addWidget(self.lbl_time_total)
        controls_layout.addLayout(progress_layout)
        btns_layout = QHBoxLayout()
        self.btn_play_pause = QPushButton()
        self.btn_play_pause.setFixedSize(40, 40)
        self.btn_play_pause.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPlay))
        self.btn_play_pause.clicked.connect(self.toggle_playback)
        self.btn_play_pause.setStyleSheet("border-radius: 20px; background-color: #333;")
        btns_layout.addStretch()
        btns_layout.addWidget(self.btn_play_pause)
        btns_layout.addStretch()
        controls_layout.addLayout(btns_layout)
        player_layout.addWidget(controls_panel)
        self.media_player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.media_player.setAudioOutput(self.audio_output)
        self.media_player.setVideoOutput(self.video_widget)
        self.media_player.positionChanged.connect(self.update_position)
        self.media_player.durationChanged.connect(self.update_duration)
        self.media_player.playbackStateChanged.connect(self.update_play_button)
        self.media_player.errorOccurred.connect(self.handle_media_error)
        self.video_panel.addWidget(self.player_page)
        self.main_splitter.addWidget(self.video_panel)
        self.main_splitter.setSizes([800, 400])
        main_layout.addWidget(self.main_splitter)
        status_layout = QHBoxLayout()
        self.progress_bar = QProgressBar()
        self.status_label = QLabel("Listo")
        status_layout.addWidget(self.status_label)
        status_layout.addWidget(self.progress_bar)
        main_layout.addLayout(status_layout)
        self.worker = None
        self.taskbar_progress = TaskbarProgress()
    def show_info(self):
        diag = InfoDialog(self)
        diag.exec()
    def limpiar_videos(self):
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Acción no permitida", "No puedes limpiar los videos mientras el proceso está en ejecución.")
            return
        reply = QMessageBox.question(
            self, 'Confirmación',
            "¿Estás seguro de que deseas eliminar TODOS los videos de las carpetas 'temp' y 'exported'?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if reply == QMessageBox.StandardButton.Yes:
            eliminados = 0
            errores = 0
            for folder in [TEMP_DIR, EXPORTED_DIR]:
                if os.path.exists(folder):
                    for filename in os.listdir(folder):
                        file_path = os.path.join(folder, filename)
                        try:
                            if os.path.isfile(file_path) or os.path.islink(file_path):
                                os.unlink(file_path)
                                eliminados += 1
                            elif os.path.isdir(file_path):
                                shutil.rmtree(file_path)
                                eliminados += 1
                        except Exception as e:
                            print(f"No se pudo eliminar {file_path}. Razón: {e}")
                            errores += 1
            self.video_list.clear()
            self.append_log(f"🧹 Limpieza completada: {eliminados} archivos eliminados. Errores: {errores}")
            QMessageBox.information(self, "Limpieza completada", f"Se eliminaron {eliminados} archivos.")
    def start_process(self):
        self.table.setRowCount(0)
        self.log_console.clear()
        try:
            with open(ARCHIVO_LOG, "w", encoding="utf-8") as f:
                f.write(f"=== REPORTE DE EJECUCIÓN: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} ===\n\n")
        except Exception as e:
            print(f"Error al inicializar log: {e}")
        self.btn_start.setEnabled(False)
        self.btn_stop.setEnabled(True)
        self.btn_clean.setEnabled(False)
        self.check_auto_search.setEnabled(False)
        self.check_video.setEnabled(False)
        self.status_label.setText("Ejecutando...")
        self.progress_bar.setValue(0)
        if self.taskbar_progress:
            self.taskbar_progress.set_progress_state(TBPF_NORMAL)
            self.taskbar_progress.set_progress_value(0, 100)
        self.worker = RadioCheckWorker(self.check_auto_search.isChecked(), self.check_video.isChecked())
        self.worker.log_signal.connect(self.append_log)
        self.worker.progress_signal.connect(self.update_progress)
        self.worker.status_signal.connect(self.status_label.setText)
        self.worker.table_init_signal.connect(self.init_table)
        self.worker.row_update_signal.connect(self.update_row)
        self.worker.video_found_signal.connect(self.add_exported_video)
        self.worker.finished_signal.connect(self.process_finished)
        self.worker.start()
    def add_exported_video(self, radio_name, video_path):
        radio_nombre_limpio = radio_name.replace('*', '').strip()
        item = QListWidgetItem(radio_nombre_limpio)
        item.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileIcon))
        item.setData(Qt.ItemDataRole.UserRole, video_path)
        item.setToolTip(f"Ver video de: {radio_nombre_limpio}")
        self.video_list.addItem(item)
        self.append_log(f"INFO: Video de {radio_nombre_limpio} disponible en la lista.")
    def play_selected_video(self, item):
        video_path = item.data(Qt.ItemDataRole.UserRole)
        radio_name = item.text()
        if os.path.exists(video_path):
            self.current_video_label.setText(f"Reproduciendo: {radio_name}")
            self.media_player.setSource(QUrl.fromLocalFile(video_path))
            self.video_panel.setCurrentIndex(1)
            self.media_player.play()
        else:
            QMessageBox.warning(self, "Error", "No se pudo encontrar el archivo de video.")
    def stop_and_back(self):
        self.media_player.stop()
        self.video_panel.setCurrentIndex(0)
    def toggle_playback(self):
        if self.media_player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.media_player.pause()
        else:
            self.media_player.play()
    def update_play_button(self, state):
        if state == QMediaPlayer.PlaybackState.PlayingState:
            self.btn_play_pause.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPause))
        else:
            self.btn_play_pause.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaPlay))
    def update_position(self, position):
        self.video_slider.setValue(position)
        self.lbl_time_current.setText(self.format_time(position))
    def update_duration(self, duration):
        self.video_slider.setRange(0, duration)
        self.lbl_time_total.setText(self.format_time(duration))
    def set_position(self, position):
        self.media_player.setPosition(position)
    def play_after_seek(self):
        """Asegura que el video siga reproduciéndose tras soltar el slider"""
        if self.media_player.playbackState() != QMediaPlayer.PlaybackState.PlayingState:
            self.media_player.play()
    def format_time(self, ms):
        s = round(ms / 1000)
        m, s = divmod(s, 60)
        return f"{m:02d}:{s:02d}"
    def handle_media_error(self):
        err = self.media_player.errorString()
        self.append_log(f"ERROR Multimedia: {err}")
    def stop_process(self):
        if self.worker and self.worker.isRunning():
            self.worker.stop()
            if self.taskbar_progress:
                self.taskbar_progress.set_progress_state(TBPF_PAUSED)
            self.append_log("\n⚠️ Solicitando detención... esperando a que terminen los hilos actuales...")
            self.status_label.setText("Deteniendo...")
            self.btn_stop.setEnabled(False)
    def process_finished(self, msg):
        self.btn_start.setEnabled(True)
        self.btn_stop.setEnabled(False)
        self.btn_clean.setEnabled(True)
        self.check_auto_search.setEnabled(True)
        self.check_video.setEnabled(True)
        self.status_label.setText(f"Finalizado: {msg}")
        if self.taskbar_progress:
            self.taskbar_progress.set_progress_state(TBPF_NOPROGRESS)
        QMessageBox.information(self, "Proceso Completado", msg)
    @pyqtSlot(str)
    def append_log(self, text):
        text_str = str(text)
        self.log_console.moveCursor(QTextCursor.MoveOperation.End)
        self.log_console.insertPlainText(text_str)
        final_text = text_str
        if not text_str.endswith('\n'):
             self.log_console.insertPlainText('\n')
             final_text += '\n'
        self.log_console.moveCursor(QTextCursor.MoveOperation.End)
        try:
            with open(ARCHIVO_LOG, "a", encoding="utf-8") as f:
                f.write(final_text)
        except:
            pass
    @pyqtSlot(int, int)
    def update_progress(self, current, total):
        self.progress_bar.setMaximum(total)
        self.progress_bar.setValue(current)
        if self.taskbar_progress:
            self.taskbar_progress.set_progress_value(int(current), int(total))
    @pyqtSlot(list)
    def init_table(self, radios):
        self.table.setRowCount(len(radios))
        for i, radio in enumerate(radios):
            item_name = QTableWidgetItem(f"{radio['nombre']} ({radio['frecuencia']})")
            self.table.setItem(i, 0, item_name)
            item_status = QTableWidgetItem("PENDIENTE")
            item_status.setForeground(QColor("gray"))
            self.table.setItem(i, 1, item_status)
            self.table.setItem(i, 2, QTableWidgetItem(radio['url']))
            self.table.setItem(i, 3, QTableWidgetItem("-"))
    @pyqtSlot(int, str, str, str, str)
    def update_row(self, row, status, url, info, nombre):
        item_name = self.table.item(row, 0)
        if item_name:
            texto_actual = item_name.text()
            frecuencia = ""
            if '(' in texto_actual and ')' in texto_actual:
                frecuencia = texto_actual.split('(')[-1].split(')')[0]
            if frecuencia:
                item_name.setText(f"{nombre} ({frecuencia})")
            else:
                item_name.setText(nombre)
        item_status = self.table.item(row, 1)
        item_status.setText(status)
        item_status.setBackground(QColor(0, 0, 0, 0))
        icon = QIcon()
        msg_type = QStyle.StandardPixmap.SP_MessageBoxInformation
        text_color = QColor("white")
        if status == "ACTIVO":
            msg_type = QStyle.StandardPixmap.SP_DialogApplyButton
            text_color = QColor("#4CAF50")
        elif "CAIDO" in status or "NO_ENCONTRADO" in status:
            msg_type = QStyle.StandardPixmap.SP_DialogCancelButton
            text_color = QColor("#EF5350")
        elif "TIMEOUT" in status:
            msg_type = QStyle.StandardPixmap.SP_MessageBoxWarning
            text_color = QColor("#FFCA28")
        elif "ACTUALIZADO" in status:
            msg_type = QStyle.StandardPixmap.SP_BrowserReload
            text_color = QColor("#42A5F5")
        elif "ERROR_BUSQ" in status:
            msg_type = QStyle.StandardPixmap.SP_MessageBoxCritical
            text_color = QColor("#FF7043")
        item_status.setIcon(self.style().standardIcon(msg_type))
        item_status.setForeground(text_color)
        self.table.item(row, 2).setText(url)
        self.table.item(row, 3).setText(info)
        self.table.scrollToItem(self.table.item(row, 0))
    def showEvent(self, event):
        """Se ejecuta cuando la ventana se muestra por primera vez"""
        super().showEvent(event)
        if self.taskbar_progress:
            self.taskbar_progress.set_hwnd(int(self.winId()))
        if es_primera_vez():
            QMessageBox.warning(
                self,
                "Advertencia importante",
                "Esta herramienta puede equivocarse de URL a veces. "
                "NO SEAS DOLOBU y revisa las URLs nuevas, a ver si no metió la pata el programa."
            )
            marcar_primera_vez_completada()

def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    palette = QPalette()
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Window, QColor(53, 53, 53))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.WindowText, Qt.GlobalColor.white)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Base, QColor(25, 25, 25))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.AlternateBase, QColor(53, 53, 53))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.ToolTipBase, Qt.GlobalColor.white)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.ToolTipText, Qt.GlobalColor.white)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Text, Qt.GlobalColor.white)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Button, QColor(53, 53, 53))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.ButtonText, Qt.GlobalColor.white)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.BrightText, Qt.GlobalColor.red)
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Link, QColor(42, 130, 218))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.Highlight, QColor(42, 130, 218))
    palette.setColor(QPalette.ColorGroup.All, QPalette.ColorRole.HighlightedText, Qt.GlobalColor.black)
    app.setPalette(palette)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())
if __name__ == "__main__":
    main()