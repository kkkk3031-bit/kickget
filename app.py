from flask import Flask, request, jsonify, send_file, render_template
from flask_cors import CORS
import os, uuid, json, re, glob, threading, time, shutil, subprocess
import requests as req_lib
from collections import defaultdict

try:
    import static_ffmpeg
    static_ffmpeg.add_paths()
except Exception:
    pass

app = Flask(__name__)
CORS(app)

DOWNLOAD_DIR = '/tmp/kick_cache'
FILE_TTL     = 1800
RATE_LIMIT   = 10
MAX_DURATION = 60 * 60      # refuse downloads longer than 60 min (VODs can be huge)

os.makedirs(DOWNLOAD_DIR, exist_ok=True)

def _find_ytdlp():
    p = shutil.which('yt-dlp') or shutil.which('yt_dlp')
    if p:
        return p
    for d in os.environ.get('PATH', '').split(':'):
        for name in ('yt-dlp', 'yt_dlp'):
            fp = os.path.join(d, name)
            if os.path.isfile(fp):
                return fp
    return 'yt-dlp'

jobs        = {}
jobs_lock   = threading.Lock()
_rate_store = defaultdict(list)
_rate_lock  = threading.Lock()

_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
                  '(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
    'Accept-Language': 'en-US,en;q=0.9',
}


# ── Job persistence ───────────────────────────────────────────────────────────

def _job_path(job_id):
    return os.path.join(DOWNLOAD_DIR, f'job_{job_id}.json')

def _save_job(job_id, job):
    try:
        with open(_job_path(job_id), 'w') as f:
            json.dump(job, f)
    except Exception:
        pass

def _load_job_from_disk(job_id):
    try:
        with open(_job_path(job_id)) as f:
            return json.load(f)
    except Exception:
        return None

def _load_all_jobs():
    for p in glob.glob(os.path.join(DOWNLOAD_DIR, 'job_*.json')):
        try:
            with open(p) as f:
                job = json.load(f)
            job_id = os.path.basename(p)[4:-5]
            if job.get('status') in ('pending', 'processing'):
                job['status'] = 'error'
                job['error']  = 'Server restarted. Please try again.'
                _save_job(job_id, job)
            if job.get('status') == 'done' and not os.path.exists(job.get('file', '')):
                os.remove(p); continue
            jobs[job_id] = job
        except Exception:
            pass

_load_all_jobs()


# ── URL helpers ───────────────────────────────────────────────────────────────
# Kick public URL forms supported:
#   kick.com/<user>/clips/<clip_id>          — clip (newer style)
#   kick.com/<user>?clip=<clip_id>           — clip (legacy)
#   kick.com/<user>/videos/<uuid>            — VOD
#   kick.com/<user>                          — live page (only works while streaming)

_KICK_RE = re.compile(
    r'(?:^|[/.])kick\.com/'
    r'(?:[\w\-]+/(?:videos?|clips?)/[\w\-]+'  # /<user>/videos|clips/<id>
    r'|[\w\-]+\?clip=[\w]+'                   # /<user>?clip=<id>
    r'|[\w\-]+/?(?:$|\?|#)'                   # /<user>  (live page)
    r')',
    re.IGNORECASE)

# Slugs that should never be treated as usernames
_RESERVED = {'video', 'videos', 'category', 'categories', 'browse', 'login',
             'signup', 'subscriptions', 'following', 'channels', 'help',
             'about', 'tos', 'privacy', 'community', 'search', 'discover',
             'api', 'static', 'assets'}

def is_valid_url(url):
    if not _KICK_RE.search(url):
        return False
    # Reserved-slug guard, but only for bare "kick.com/<slug>" with no /clips|/videos|?clip=
    m = re.search(r'kick\.com/([\w\-]+)(?:/?$|\?(?!clip=))', url, re.IGNORECASE)
    if m and m.group(1).lower() in _RESERVED:
        return False
    return True

def normalize_url(url):
    url = url.strip()
    if not url.startswith('http'):
        url = 'https://' + url
    return url

def kind_for_url(url):
    if re.search(r'[?&]clip=',       url, re.IGNORECASE): return 'clip'
    if re.search(r'/clips?/',        url, re.IGNORECASE): return 'clip'
    if re.search(r'/videos?/',       url, re.IGNORECASE): return 'vod'
    return 'live'

def extract_kick_id(url):
    """Return (kind, id_string). id_string is either a clip_id (incl. 'clip_'
    prefix) or a VOD UUID. None when not extractable."""
    m = re.search(r'/clips?/(clip_[\w]+)',                       url, re.IGNORECASE)
    if m: return ('clip', m.group(1))
    m = re.search(r'[?&]clip=(clip_[\w]+)',                      url, re.IGNORECASE)
    if m: return ('clip', m.group(1))
    m = re.search(r'/videos?/([a-f0-9-]{36})',                   url, re.IGNORECASE)
    if m: return ('vod',  m.group(1))
    m = re.search(r'kick\.com/([\w\-]+)',                        url, re.IGNORECASE)
    if m and m.group(1).lower() not in _RESERVED: return ('live', m.group(1))
    return (None, None)

def build_kick_api_url(kind, id_str):
    if kind == 'clip': return f'https://kick.com/api/v2/clips/{id_str}'
    if kind == 'vod':  return f'https://kick.com/api/v1/video/{id_str}'
    if kind == 'live': return f'https://kick.com/api/v2/channels/{id_str}'
    return None

def make_filename(title, ext='mp4'):
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f#@]', '', title or 'kick').strip()
    name = re.sub(r'\s+', ' ', name)
    return (name[:80] or 'kick') + '.' + ext

def short_id_from_url(url):
    m = re.search(r'[?&]clip=([\w\-]+)', url, re.IGNORECASE)
    if m: return m.group(1)[-10:]
    m = re.search(r'(?:clips?/|videos?/)([\w\-]+)', url, re.IGNORECASE)
    if m: return m.group(1)[-10:]
    m = re.search(r'kick\.com/([\w\-]+)', url, re.IGNORECASE)
    return (m.group(1)[-10:] if m else 'kick')

def _find_ffmpeg():
    p = shutil.which('ffmpeg')
    if p: return p
    for d in ['/nix/var/nix/profiles/default/bin', '/usr/bin', '/usr/local/bin']:
        fp = os.path.join(d, 'ffmpeg')
        if os.path.isfile(fp): return fp
    nix = glob.glob('/nix/store/*/bin/ffmpeg')
    return nix[0] if nix else None


# ── yt-dlp metadata + download ────────────────────────────────────────────────

# ── kick-video.download proxy (bypasses Cloudflare for Kick API) ──────────────
# Trick: kick-video.download has a /api/get-kick-video endpoint that takes a
# Kick API URL and returns the JSON Kick.com would return — but routed through
# their Cloudflare-aware backend so we don't get 403'd. Same pattern InstaGet
# uses with snapsave.app.

KVD_API = 'https://kick-video.download/api/get-kick-video'
_KVD_HEADERS = {
    'User-Agent': _HEADERS['User-Agent'],
    'Accept': '*/*',
    'Accept-Language': 'en-US,en;q=0.9',
    'Referer': 'https://kick-video.download/',
    'Origin':  'https://kick-video.download',
}

def kvd_fetch(kick_api_url):
    """Hit kvd as proxy for a Kick API URL. Returns (parsed_json, error)."""
    try:
        r = req_lib.get(KVD_API,
                         params={'url': kick_api_url},
                         headers=_KVD_HEADERS,
                         timeout=25)
        body = r.text
        # On miss kvd returns plain text "No URL found for ..."
        if body.startswith('No URL found'):
            return None, 'Not found'
        if r.status_code >= 500:
            return None, f'Proxy error {r.status_code}'
        try:
            return json.loads(body), None
        except json.JSONDecodeError:
            return None, 'Bad response'
    except req_lib.Timeout:
        return None, 'Proxy timeout'
    except Exception as e:
        try: print('KVD_EXC:', repr(e), flush=True)
        except Exception: pass
        return None, 'Proxy unreachable'

def kick_info(url):
    """Return (info_dict_like_ytdlp, error_str). Uses kvd as Cloudflare bypass."""
    kind, ident = extract_kick_id(url)
    if not kind:
        return None, 'Could not parse Kick URL.'
    if kind == 'live':
        # Live streams need a different code-path — keep yt-dlp fallback for now
        return _ytdlp_info_fallback(url)

    api_url = build_kick_api_url(kind, ident)
    data, err = kvd_fetch(api_url)
    if err == 'Not found' or not data:
        return None, 'Clip or VOD not found. It may be deleted or private.'
    if err:
        return None, 'Kick is responding slowly. Please try again.'

    if kind == 'clip':
        clip = data.get('clip') or data
        m3u8 = clip.get('clip_url') or clip.get('video_url')
        if not m3u8:
            return None, 'No playable URL in clip metadata.'
        return {
            '_hls_url':  m3u8,
            'title':     clip.get('title') or 'Kick clip',
            'uploader':  (clip.get('channel') or {}).get('username')
                         or (clip.get('creator') or {}).get('username') or '',
            'thumbnail': clip.get('thumbnail_url') or '',
            'duration':  clip.get('duration') or 0,
        }, None

    if kind == 'vod':
        # Kick's VOD API JSON structure: {source: m3u8_url, livestream: {...}}
        m3u8 = data.get('source') or (data.get('video') or {}).get('source')
        livestream = data.get('livestream') or {}
        channel    = (data.get('livestream') or {}).get('channel') or {}
        if not m3u8:
            return None, 'No playable URL in VOD metadata.'
        return {
            '_hls_url':  m3u8,
            'title':     livestream.get('session_title') or data.get('title') or 'Kick VOD',
            'uploader':  (channel.get('user') or {}).get('username') or channel.get('slug') or '',
            'thumbnail': (livestream.get('thumbnail') or {}).get('src') or '',
            'duration':  (livestream.get('duration') or 0) // 1000,
        }, None

    return None, 'Unsupported Kick URL type.'

# ── Fallback yt-dlp for live streams (kvd doesn't proxy live HLS) ────────────

def _ytdlp_info_fallback(url):
    """For live streams only. yt-dlp with --impersonate may still get 403,
    in which case we tell the user to try again later."""
    ytdlp = _find_ytdlp()
    cmd = [ytdlp, '--no-warnings', '--no-playlist', '--skip-download',
           '--dump-single-json', '--geo-bypass', '--impersonate', 'chrome', url]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=35)
        if proc.returncode != 0:
            stderr = (proc.stderr or '').strip().lower()
            if 'offline' in stderr or 'not currently live' in stderr:
                return None, 'This channel is offline — try a clip or VOD URL instead.'
            return None, 'Live stream not available right now.'
        return json.loads(proc.stdout), None
    except subprocess.TimeoutExpired:
        return None, 'Kick is responding slowly. Please try again.'
    except Exception:
        return None, 'Could not fetch live channel info.'

def _ytdlp_live_fallback(url, output_mp4, job_id):
    """Record up to 5 minutes of a live Kick stream via yt-dlp."""
    ytdlp = _find_ytdlp()
    cmd = [ytdlp, '--geo-bypass', '--no-playlist', '--newline',
           '--impersonate', 'chrome',
           '--live-from-start', '--downloader', 'ffmpeg',
           '--downloader-args', 'ffmpeg_i:-t 300',
           '-f', 'best[ext=mp4]/best',
           '-o', output_mp4, url]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE, text=True, bufsize=1)
        _PROGRESS_RE = re.compile(r'\[download\]\s+([\d.]+)%')
        for line in proc.stderr:
            m = _PROGRESS_RE.search(line)
            if m:
                pct = min(int(float(m.group(1))), 90)
                with jobs_lock:
                    if jobs.get(job_id, {}).get('status') == 'processing':
                        jobs[job_id]['progress'] = pct
        proc.wait(timeout=600)
        return output_mp4 if (proc.returncode == 0 and os.path.exists(output_mp4)) else None
    except Exception:
        return None

# ── HLS → MP4 download via ffmpeg ─────────────────────────────────────────────

def hls_download(m3u8_url, output_mp4, job_id, max_seconds=None):
    """Download an HLS playlist to MP4 using ffmpeg. Returns mp4 path on success."""
    ffmpeg = _find_ffmpeg()
    if not ffmpeg:
        return None
    cmd = [ffmpeg, '-y', '-i', m3u8_url, '-c', 'copy',
           '-bsf:a', 'aac_adtstoasc',  # required when AAC is in TS container
           '-progress', 'pipe:2']
    if max_seconds:
        cmd[3:3] = ['-t', str(max_seconds)]
    cmd.append(output_mp4)

    _DUR_RE   = re.compile(r'Duration:\s*(\d+):(\d+):([\d.]+)')
    _TIME_RE  = re.compile(r'out_time_ms=(\d+)')
    total_us  = None

    try:
        proc = subprocess.Popen(cmd,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE,
                                text=True, bufsize=1)
        for line in proc.stderr:
            if total_us is None:
                m = _DUR_RE.search(line)
                if m:
                    h, mn, s = int(m.group(1)), int(m.group(2)), float(m.group(3))
                    total_us = int((h*3600 + mn*60 + s) * 1_000_000)
            m = _TIME_RE.search(line)
            if m and total_us:
                done_us = int(m.group(1))
                pct = min(int(done_us / total_us * 90), 90)
                with jobs_lock:
                    if jobs.get(job_id, {}).get('status') == 'processing':
                        jobs[job_id]['progress'] = max(jobs[job_id].get('progress', 0), pct)
        proc.wait(timeout=900)
        if proc.returncode != 0 or not os.path.exists(output_mp4):
            return None
        return output_mp4
    except Exception:
        return None


# ── Worker ────────────────────────────────────────────────────────────────────

def _set_job(job_id, updates):
    with jobs_lock:
        jobs[job_id].update(updates)
        _save_job(job_id, jobs[job_id])

def schedule_cleanup(job_id, path):
    def _cleanup():
        time.sleep(FILE_TTL)
        try:
            if os.path.isfile(path):  os.remove(path)
            elif os.path.isdir(path): shutil.rmtree(path, ignore_errors=True)
        except Exception: pass
        try: os.remove(_job_path(job_id))
        except Exception: pass
        with jobs_lock: jobs.pop(job_id, None)
    threading.Thread(target=_cleanup, daemon=True).start()

def do_download(job_id, url, title, fmt):
    _set_job(job_id, {'status': 'processing', 'progress': 5})
    try:
        kind     = kind_for_url(url)
        file_id  = str(uuid.uuid4())
        _set_job(job_id, {'progress': 10})

        # Get fresh info → HLS URL (kvd-proxied for clip/vod, yt-dlp for live)
        info, err = kick_info(url)
        if err or not info:
            _set_job(job_id, {'status': 'error',
                              'error': err or 'Could not fetch this Kick URL.'})
            return

        _set_job(job_id, {'progress': 18})
        mp4_path = os.path.join(DOWNLOAD_DIR, f'{file_id}.mp4')

        if '_hls_url' in info:
            # Clip / VOD path — direct HLS via ffmpeg
            max_s = 300 if kind == 'live' else (MAX_DURATION if kind == 'vod' else None)
            dl_path = hls_download(info['_hls_url'], mp4_path, job_id, max_seconds=max_s)
        else:
            # Live fallback via yt-dlp
            dl_path = _ytdlp_live_fallback(url, mp4_path, job_id)

        if not dl_path or not os.path.exists(dl_path):
            err = 'Could not download. The channel may be offline.' if kind == 'live' \
                  else 'Could not download this video. Try again in a moment.'
            _set_job(job_id, {'status': 'error', 'error': err})
            return

        _set_job(job_id, {'progress': 92})

        sid = short_id_from_url(url)
        t   = (title or kind).strip()
        base_title = f'{t}_{sid}' if sid not in t else t

        if fmt == 'mp3':
            mp3_path = os.path.join(DOWNLOAD_DIR, f'{file_id}.mp3')
            ffmpeg = _find_ffmpeg()
            if ffmpeg:
                subprocess.run([ffmpeg, '-i', dl_path, '-q:a', '0', '-map', 'a',
                                mp3_path, '-y'], capture_output=True, timeout=180)
                if os.path.exists(mp3_path):
                    try: os.remove(dl_path)
                    except Exception: pass
                    dl_path = mp3_path

        real_ext = os.path.splitext(dl_path)[1].lstrip('.') or 'mp4'
        filename = make_filename(base_title, real_ext)
        _set_job(job_id, {'status': 'done', 'file': dl_path,
                          'filename': filename, 'progress': 100})
        schedule_cleanup(job_id, dl_path)

    except Exception:
        _set_job(job_id, {'status': 'error', 'error': 'Download failed. Please try again.'})


# ── Rate limiter ──────────────────────────────────────────────────────────────

def _check_rate(ip):
    now = time.time()
    with _rate_lock:
        _rate_store[ip] = [t for t in _rate_store[ip] if now - t < 60]
        if len(_rate_store[ip]) >= RATE_LIMIT: return False
        _rate_store[ip].append(now)
        return True

def _client_ip():
    return (request.headers.get('X-Forwarded-For', '').split(',')[0].strip()
            or request.remote_addr or 'unknown')


# ── Security headers ──────────────────────────────────────────────────────────

@app.after_request
def add_security_headers(resp):
    resp.headers['X-Frame-Options']        = 'SAMEORIGIN'
    resp.headers['X-Content-Type-Options'] = 'nosniff'
    resp.headers['Referrer-Policy']        = 'strict-origin-when-cross-origin'
    return resp


# ── Routes ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/manifest.json')
def manifest():
    return jsonify({"name":"KickGet","short_name":"KickGet",
                    "description":"Download Kick.com clips and VODs",
                    "start_url":"/","display":"standalone",
                    "background_color":"#0a0a0a","theme_color":"#53FC18","icons":[]})

@app.route('/robots.txt')
def robots():
    body = ('User-agent: *\n'
            'Allow: /\n\n'
            'Sitemap: https://kickget-production.up.railway.app/sitemap.xml\n')
    return body, 200, {'Content-Type': 'text/plain'}

@app.route('/sitemap.xml')
def sitemap():
    today = time.strftime('%Y-%m-%d')
    xml = ('<?xml version="1.0" encoding="UTF-8"?>\n'
           '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
           '  <url>\n'
           '    <loc>https://kickget-production.up.railway.app/</loc>\n'
           f'    <lastmod>{today}</lastmod>\n'
           '    <changefreq>weekly</changefreq>\n'
           '    <priority>1.0</priority>\n'
           '  </url>\n'
           '</urlset>\n')
    return xml, 200, {'Content-Type': 'application/xml'}

@app.route('/ads.txt')
def ads_txt():
    return 'google.com, pub-3956390078338144, DIRECT, f08c47fec0942fa0\n', 200, {'Content-Type': 'text/plain'}

@app.route('/info', methods=['POST'])
def get_info():
    if not _check_rate(_client_ip()):
        return jsonify({'error': 'Too many requests. Please wait a moment.'}), 429
    data = request.get_json() or {}
    url  = normalize_url(data.get('url', '').strip())
    if not url or not is_valid_url(url):
        return jsonify({'error': 'Invalid Kick URL — paste a clip, VOD, or channel link.'}), 400

    info, err = kick_info(url)
    if err or not info:
        return jsonify({'error': err or 'Could not fetch this Kick URL.'}), 400

    title    = info.get('title') or info.get('description') or 'Kick video'
    uploader = info.get('uploader') or info.get('uploader_id') or info.get('channel') or ''
    thumb    = info.get('thumbnail') or ''
    dur      = info.get('duration') or 0
    mins, secs = divmod(int(dur), 60) if dur else (0, 0)
    dur_str = f'{mins}:{secs:02d}' if dur else '—'
    kind = kind_for_url(url)
    is_live = bool(info.get('is_live')) or kind == 'live'

    too_long = bool(dur and dur > MAX_DURATION and not is_live)

    return jsonify({
        'title':        str(title)[:200],
        'thumbnail':    thumb,
        'uploader':     str(uploader),
        'is_video':     True,
        'is_live':      is_live,
        'kind':         kind,
        'duration':     dur_str,
        'duration_sec': dur,
        'too_long':     too_long,
        'url':          url,
    })

@app.route('/start', methods=['POST'])
def start_convert():
    if not _check_rate(_client_ip()):
        return jsonify({'error': 'Too many requests. Please wait a moment.'}), 429
    data  = request.get_json() or {}
    url   = normalize_url(data.get('url', '').strip())
    title = data.get('title', '').strip()
    fmt   = data.get('format', 'mp4')
    if fmt not in ('mp4', 'mp3'): fmt = 'mp4'
    if not is_valid_url(url):
        return jsonify({'error': 'Invalid Kick URL'}), 400

    job_id = str(uuid.uuid4())
    with jobs_lock:
        jobs[job_id] = {'status': 'pending', 'file': None, 'filename': None,
                         'error': None, 'progress': 0}
        _save_job(job_id, jobs[job_id])

    threading.Thread(target=do_download,
                     args=(job_id, url, title or None, fmt),
                     daemon=True).start()
    return jsonify({'job_id': job_id})

@app.route('/status/<job_id>')
def get_status(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        job = _load_job_from_disk(job_id)
        if job:
            with jobs_lock: jobs[job_id] = job
    if not job:
        return jsonify({'error': 'Job not found'}), 404
    return jsonify({k: job.get(k) for k in ('status', 'error', 'filename', 'progress')})

@app.route('/download/<job_id>')
def download_file(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        job = _load_job_from_disk(job_id)
        if job:
            with jobs_lock: jobs[job_id] = job
    if not job or job['status'] != 'done':
        return jsonify({'error': 'File not ready — please try again.'}), 404
    path, filename = job['file'], job['filename']
    if not os.path.exists(path):
        return jsonify({'error': 'File expired. Please download again.'}), 410
    safe = re.sub(r'[^\w\s\-\.\(\)]', '', filename).strip() or 'kick.mp4'
    if safe.endswith('.mp3'):   mime = 'audio/mpeg'
    else:                       mime = 'video/mp4'
    return send_file(path, as_attachment=True, download_name=safe, mimetype=mime)


if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)
