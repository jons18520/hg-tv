# -*- coding: utf-8 -*-
"""
红果短剧 TVBox / 影视TV Python 源  ——  完整版（含播放）
======================================================

数据源：红果短剧官网 hongguoduanju.com 的 SSR 数据（_ROUTER_DATA），**无需签名**
播放源：番茄 App 接口 /novel/player/video_model/v1/（**自算 X-Gorgon 签名**）
        + CENC-AES-CTR 内容密钥解密（spade_a → AES-128 key）
        → 通过影视TV 的 drm(clearkey) 交给播放器

全程仅用标准库（hashlib/base64/json/urllib），兼容 Chaquopy。

X-Gorgon 算法（8404）：
    payload[0:4]  = md5(query)[:4]
    payload[4:8]  = md5(body)[:4]      （无 body 时为 0）
    payload[8:12] = 0
    payload[12:16]= 00 06 0b 1c
    payload[16:20]= 时间戳(大端)
    逐字节 XOR 固定 key
    再原地做  mixed=rotl8(payload[i],4)^payload[(i+1)%20]
              payload[i]=reverse8(mixed)^0xff^20
    前缀 84 04 40 1c 00 00  → 共 26 字节

extend 用法（可选）：
    {"license": "http://127.0.0.1:9978"}   覆盖 ClearKey 许可证基础地址
"""

import base64
import hashlib
import json
import re
import struct
import time
import urllib.parse
import urllib.request

try:
    from base.spider import Spider as _BaseSpider
except ImportError:
    class _BaseSpider(object):
        pass

# ---------------------------------------------------------------- 常量
GORGON_KEY = bytes([0x44, 0xb9, 0xb9, 0xd9, 0xa4, 0xae, 0xf9, 0xfc, 0xa4, 0x93,
                    0xaa, 0x75, 0x7c, 0xa3, 0xc2, 0xc4, 0xa4, 0x96, 0x93, 0x8f])

APP_UA = ("com.phoenix.read/73532 (Linux; U; Android 16; zh_CN; 25053RT47C; "
          "Build/BP2A.250605.031.A3; Cronet/TTNetVersion:04657795 2026-01-23 "
          "QuicVersion:c67e9834 2025-09-08")

APP_HOST = "https://api5-normal-sinfonlineb.fqnovel.com"

MEDIA_REFERER = "https://novel.snssdk.com/"


def _rotl8(x, n):
    return ((x << n) | (x >> (8 - n))) & 0xFF


def _popcount(x):
    return bin(x).count('1')


def _b64_any(value):
    """宽松 base64 解码（支持无 padding）"""
    value = (value or "").strip()
    if not value:
        return b""
    try:
        return base64.b64decode(value, validate=True)
    except Exception:
        return base64.b64decode(value + "=" * ((-len(value)) % 4))


try:
    from javax.crypto import Cipher as _JavaCipher
    from javax.crypto.spec import IvParameterSpec as _IvParameterSpec
    from javax.crypto.spec import SecretKeySpec as _SecretKeySpec
    _JAVA_CRYPTO = True
except Exception:
    _JAVA_CRYPTO = False


class _BoxView(object):
    __slots__ = ("start", "end", "size")

    def __init__(self, start, end, size):
        self.start = start
        self.end = end
        self.size = size


def _find_box(data, box_type, start=0):
    """按 box 类型查找（返回 box 内容视图）"""
    marker = box_type if isinstance(box_type, bytes) else box_type.encode("ascii")
    pos = data.find(marker, start)
    while pos >= 4:
        size = int.from_bytes(data[pos - 4:pos], "big")
        box_start = pos - 4
        if size >= 8 and box_start + size <= len(data):
            return _BoxView(box_start + 8, box_start + size, size)
        pos = data.find(marker, pos + 4)
    return None


def _find_boxes(data, box_type, start=0):
    marker = box_type if isinstance(box_type, bytes) else box_type.encode("ascii")
    views = []
    pos = data.find(marker, start)
    while pos >= 4:
        size = int.from_bytes(data[pos - 4:pos], "big")
        box_start = pos - 4
        if size >= 8 and box_start + size <= len(data):
            views.append(_BoxView(box_start + 8, box_start + size, size))
        pos = data.find(marker, pos + 4)
    return views


def _replace_all(data, old, new):
    return data.replace(old, new)


def _replace_sinf(data):
    """将整个 sinf 盒替换为 free（与 drpy JS 行为一致）"""
    offset = 0
    while True:
        pos = data.find(b"sinf", offset)
        if pos < 4:
            break
        size = int.from_bytes(data[pos - 4:pos], "big")
        end = pos - 4 + size
        if 8 <= size < 50000 and end <= len(data):
            data[pos:pos + 4] = b"free"
            for i in range(pos + 4, end):
                data[i] = 0
            offset = end
        else:
            offset = pos + 4
    return data


def _parse_range_header(value, total):
    if not value:
        return None
    match = re.match(r"bytes=(\d*)-(\d*)", str(value).strip(), re.I)
    if not match:
        return None
    start_txt, end_txt = match.group(1), match.group(2)
    if not start_txt:
        length = min(total, int(end_txt or "0"))
        if length <= 0:
            return None
        start, end = total - length, total - 1
    else:
        start = int(start_txt)
        end = int(end_txt) if end_txt else total - 1
    start = max(0, min(start, total - 1))
    end = max(start, min(end, total - 1))
    return start, end


def _add_counter(iv, blocks):
    value = int.from_bytes(iv, "big")
    value = (value + blocks) % (1 << 128)
    return value.to_bytes(16, "big")


def _aes_keystream(key, iv, length):
    """用 Java AES/CTR 生成密钥流（仅 Android/Chaquopy 可用）"""
    if not _JAVA_CRYPTO:
        raise RuntimeError("AES keystream requires Android/Chaquopy Java crypto")
    cipher = _JavaCipher.getInstance("AES/CTR/NoPadding")
    cipher.init(1, _SecretKeySpec(bytes(key), "AES"), _IvParameterSpec(bytes(iv)))
    result = cipher.doFinal(bytes(length))
    return bytes(result)


class Spider(_BaseSpider):
    site = "https://hongguoduanju.com"

    web_headers = {
        "User-Agent": ("Mozilla/5.0 (Linux; Android 12; TV) AppleWebKit/537.36 "
                       "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"),
        "Accept-Language": "zh-CN,zh;q=0.9",
    }

    CATEGORIES = [
        ("real-drama", "真人剧", "/category/real-drama"),
        ("ai-drama", "AI剧", "/category/ai-drama"),
        ("comic-drama", "漫剧", "/category/comic-drama"),
        ("all", "综合", "/category"),
    ]

    # 听书分类（数据来自番茄 App bookmall/tab 听书 tab + directory 章节目录）
    AUDIO_CATEGORIES = [
        ("audio-all", "听书", 0),
        ("audio-male", "男频听书", 1),
        ("audio-female", "女频听书", 2),
        ("audio-free", "免费听书", 3),
        ("audio-rank", "听书热播榜", 4),
    ]

    # 听书 API 端点（均经实测验证）
    AUDIO_API_HOST = "https://api5-normal-sinfonlineb.fqnovel.com"
    AUDIO_SEARCH_API = "https://api5-normal-sinfonlinea.fqnovel.com"
    AUDIO_PATHS = {
        # 听书 tab 推荐流：gender=2&tab_type=5，page / refresh_type 可翻页去重
        "tab": "/reading/bookapi/bookmall/tab/v1/",
        # 书籍详情 + 全量章节目录（catalog_data 里每章都有 item_id）
        "directory": "/reading/bookapi/directory/all_items/v1/",
        # 批量取播放地址（一次可带多章）
        "batch_play": "/reading/bookapi/audio/batch_play/",
        # 可用音色（TTS / 真人）
        "toneinfo": "/reading/bookapi/audio/toneinfo/",
        "search_page": "/reading/bookapi/search/page/v1/",
        "search_tab": "/reading/bookapi/search/tab/v1/",
        "hot_search": "/reading/bookapi/search/hot-search/v1/",
    }
    # 听书推荐流的翻页参数（服务端会轮换返回不同的一批书）
    AUDIO_TAB_PAGES = (1, 2, 3, 4, 5)
    AUDIO_TAB_REFRESH = (None, 2, 3)
    AUDIO_NOVEL_PAGES = (1, 3, 5)
    AUDIO_FEED_TTL = 600
    AUDIO_FEED_RETRY = 3
    # 播放时使用的音色（0 = 服务端推荐）
    AUDIO_TONE_ID = 0
    AUDIO_TONE_QUALITY = "HighQuality"

    def __init__(self):
        self._cache = {}
        self.device_id = "2104954905733967953"
        self.iid = "4382319046029658471"
        # ClearKey 许可证地址基础（FongMi 本地服务默认端口 9978，占用时自增）
        self.license_base = ""
        self._license_probed = False
        self.site_key = "hongguo"
        self._pending_key = {}
        self.play_mode = "clearkey"
        self._stream_cache = {}
        self._media_cache = {}
        # 听书：推荐流聚合缓存 + 章节目录缓存
        self._audio_feed_cache = (0, {})
        self._audio_chapter_cache = {}

    # ------------------------------------------------------------ 生命周期
    def getName(self):
        return "红果短剧"

    def init(self, extend=""):
        if isinstance(extend, dict):
            ext = extend
        elif extend:
            try:
                ext = json.loads(str(extend))
            except Exception:
                ext = {"license": str(extend).strip()} if str(extend).startswith("http") else {}
        else:
            ext = {}
        if ext.get("license"):
            self.license_base = str(ext["license"]).rstrip("/")
        if ext.get("siteKey"):
            self.site_key = str(ext["siteKey"])
        mode = ext.get("playback") or ext.get("mode") or self.play_mode
        if str(mode).lower() in ("stream", "localproxy", "proxy", "decrypt"):
            self.play_mode = "stream"
        else:
            self.play_mode = "clearkey"
        return self

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return False

    def destroy(self):
        return None

    # ------------------------------------------------------------- X-Gorgon
    def _sign(self, query, body, ts):
        if isinstance(body, str):
            body = body.encode("utf-8")
        p = bytearray(20)
        p[0:4] = hashlib.md5(query.encode()).digest()[:4]
        if body:
            p[4:8] = hashlib.md5(body).digest()[:4]
        p[12:16] = bytes([0, 6, 11, 28])
        p[16:20] = struct.pack('>I', ts)
        for i in range(20):
            p[i] ^= GORGON_KEY[i]
        # 必须原地修改：i=19 时取的是已被改写的 p[0]
        for i in range(20):
            p[i] = int(format(_rotl8(p[i], 4) ^ p[(i + 1) % 20], '08b')[::-1], 2) ^ 0xFF ^ 20
        return (bytes([0x84, 0x04, 0x40, 0x1c, 0x00, 0x00]) + bytes(p)).hex()

    def _app_params(self):
        return {
            "ac": "wifi", "aid": "8662", "app_name": "novelread", "channel": "update_64",
            "device_brand": "Redmi", "device_id": self.device_id, "device_platform": "android",
            "device_type": "25053RT47C", "dpi": "520", "iid": self.iid, "language": "zh",
            "manifest_version_code": "73532", "os": "android", "os_api": "36",
            "os_version": "16", "resolution": "1280*2772", "ssmix": "a",
            "update_version_code": "73532", "version_code": "73532", "version_name": "7.3.5.32",
        }

    def _post_signed(self, path, payload):
        body = json.dumps(payload, separators=(',', ':'), ensure_ascii=False)
        ts = int(time.time())
        params = self._app_params()
        params["_rticket"] = str(int(time.time() * 1000))
        query = urllib.parse.urlencode(sorted(params.items()))
        url = APP_HOST + path + "?" + query
        headers = {
            "User-Agent": APP_UA,
            "Content-Type": "application/json; charset=utf-8",
            "Accept": "application/json",
            "sdk-version": "2",
            "X-Gorgon": self._sign(query, body, ts),
            "X-Khronos": str(ts),
            "X-SS-Req-Ticket": params["_rticket"],
            "X-SS-STUB": hashlib.md5(body.encode("utf-8")).hexdigest().upper(),
            "Referer": self.site + "/",
            "x-argus": base64.b64encode(ts.to_bytes(4, "little")).decode(),
            "x-ladon": base64.b64encode(ts.to_bytes(4, "big")).decode(),
        }
        req = urllib.request.Request(url, data=body.encode("utf-8"),
                                     headers=headers, method="POST")
        with urllib.request.urlopen(req, timeout=20) as r:
            data = r.read()
        if not data:
            raise RuntimeError("video_model 空响应：风控头缺失或请求被拦截")
        return json.loads(data.decode("utf-8", "replace"))

    def _post_signed_audio(self, path, payload, host=None):
        """听书 API 调用（与 video_model 共享签名体系，但端点不同）"""
        body = json.dumps(payload, separators=(',', ':'), ensure_ascii=False)
        ts = int(time.time())
        params = self._app_params()
        params["_rticket"] = str(int(time.time() * 1000))
        query = urllib.parse.urlencode(sorted(params.items()))
        base = host or self.AUDIO_API_HOST
        url = base + path + "?" + query
        headers = {
            "User-Agent": APP_UA,
            "Content-Type": "application/json; charset=utf-8",
            "Accept": "application/json",
            "sdk-version": "2",
            "X-Gorgon": self._sign(query, body, ts),
            "X-Khronos": str(ts),
            "X-SS-Req-Ticket": params["_rticket"],
            "X-SS-STUB": hashlib.md5(body.encode("utf-8")).hexdigest().upper(),
            "Referer": self.site + "/",
            "x-argus": base64.b64encode(ts.to_bytes(4, "little")).decode(),
            "x-ladon": base64.b64encode(ts.to_bytes(4, "big")).decode(),
        }
        req = urllib.request.Request(url, data=body.encode("utf-8"),
                                     headers=headers, method="POST")
        with urllib.request.urlopen(req, timeout=20) as r:
            data = r.read()
        if not data:
            raise RuntimeError("audio API 空响应：风控头缺失或请求被拦截")
        return json.loads(data.decode("utf-8", "replace"))

    def _get_signed_audio(self, path, params_extra=None, host=None):
        """听书 GET 接口（bookmall/tab、directory/all_items、search/page 等）"""
        ts = int(time.time())
        params = self._app_params()
        params["_rticket"] = str(int(time.time() * 1000))
        if params_extra:
            params.update(params_extra)
        query = urllib.parse.urlencode(sorted(params.items()))
        base = host or self.AUDIO_API_HOST
        url = base + path + "?" + query
        headers = {
            "User-Agent": APP_UA,
            "Accept": "application/json",
            "sdk-version": "2",
            "X-Gorgon": self._sign(query, "", ts),
            "X-Khronos": str(ts),
            "X-SS-Req-Ticket": params["_rticket"],
            "Referer": self.site + "/",
            "x-argus": base64.b64encode(ts.to_bytes(4, "little")).decode(),
            "x-ladon": base64.b64encode(ts.to_bytes(4, "big")).decode(),
        }
        req = urllib.request.Request(url, headers=headers, method="GET")
        with urllib.request.urlopen(req, timeout=20) as r:
            data = r.read()
        if not data:
            # 番茄部分接口对参数敏感：参数不全时返回 HTTP 200 + 空 body
            return None
        return json.loads(data.decode("utf-8", "replace"))

    def _post_signed_audio_lenient(self, path, payload, host=None):
        """同 _post_signed_audio，但空响应返回 None 而不是抛异常"""
        try:
            return self._post_signed_audio(path, payload, host)
        except Exception:
            return None

    def _get_signed_audio_lenient(self, path, params_extra=None, host=None):
        try:
            return self._get_signed_audio(path, params_extra, host)
        except Exception:
            return None

    # ------------------------------------------------------- CENC 内容密钥
    @staticmethod
    def _content_key(spade_a):
        """spade_a -> CENC AES-128 密钥（纯变换，无需 AES）"""
        raw = _b64_any(spade_a)
        if len(raw) < 3:
            return None
        tag_length = (raw[0] ^ raw[1] ^ raw[2]) - 48
        content_length = len(raw) - tag_length - 1
        if tag_length < 1 or content_length < 33 or content_length >= len(raw):
            return None
        seed = raw[len(raw) - tag_length - 2] ^ raw[len(raw) - tag_length - 1]
        tag = bytes(b ^ seed for b in raw[len(raw) - tag_length:])
        if tag in (b"app_v2", b"web_v2"):
            return None
        decoded = bytearray(content_length)
        prev_even, prev_odd = 250, 85
        for index, current in enumerate(raw[1:1 + content_length]):
            if index % 2 == 0:
                previous = prev_even
                prev_even = current
            else:
                previous = prev_odd
                prev_odd = current
            decoded[index] = ((previous ^ current) - 21 - _popcount(index)) & 0xFF
        try:
            padding = int(decoded[:1].decode('latin1'), 36)
        except Exception:
            return None
        if content_length - padding - 1 != 32:
            return None
        try:
            return bytes.fromhex(decoded[1:33].decode('latin1'))
        except Exception:
            return None

    def _resolve_media(self, vid):
        """调 video_model 取播放地址 + 解出 CENC 密钥"""
        resp = self._post_signed("/novel/player/video_model/v1/", {
            "video_id": str(vid), "content_type": 1,
            "biz_param": {"need_all_video_definition": True, "video_platform": 3},
        })
        if resp.get("code") != 0:
            return None
        data = resp.get("data") or {}
        model = data.get("video_model")
        if isinstance(model, str):
            try:
                model = json.loads(model)
            except Exception:
                return None
        if not isinstance(model, dict):
            return None
        rows = model.get("video_list")
        if isinstance(rows, dict):
            rows = [rows[k] for k in sorted(rows.keys())]
        best = None
        for row in (rows or []):
            if not isinstance(row, dict):
                continue
            meta = row.get("video_meta") or {}
            if str(meta.get("codec_type", "")).lower() == "bytevc2":
                continue
            url = row.get("main_url") or row.get("backup_url")
            if not url:
                continue
            enc = row.get("encrypt_info") or {}
            key = None
            if enc.get("spade_a") or enc.get("encrypt") is True:
                key = self._content_key(enc.get("spade_a", ""))
                if not key:
                    continue
            try:
                height = int(re.sub(r'[^0-9]', '', str(meta.get("definition") or "")) or 0)
            except Exception:
                height = 0
            if best is None or height > best["height"]:
                best = {"url": url, "key": key, "kid": enc.get("kid"), "height": height}
        return best

    # ------------------------------------------------------------ 数据抓取
    def _fetch(self, url):
        req = urllib.request.Request(url, headers=self.web_headers)
        with urllib.request.urlopen(req, timeout=25) as r:
            return r.read().decode("utf-8", "replace")

    def _router_data(self, url):
        cached = self._cache.get(url)
        if cached and time.time() - cached[0] < 300:
            return cached[1]
        html = self._fetch(url)
        m = re.search(r'_ROUTER_DATA\s*=\s*(\{)', html)
        if not m:
            raise RuntimeError("页面数据格式已变化（未找到 _ROUTER_DATA）")
        start = m.start(1)
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(html)):
            ch = html[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
            else:
                if ch == '"':
                    in_str = True
                elif ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        data = json.loads(html[start:i + 1])
                        self._cache[url] = (time.time(), data)
                        return data
        raise RuntimeError("_ROUTER_DATA 解析失败")

    @staticmethod
    def _category_list(d):
        ld = d.get("loaderData", {}) or {}
        for key in ("category_$", "category_page"):
            node = ld.get(key)
            if isinstance(node, dict) and isinstance(node.get("recommendList"), list):
                return node
        for node in ld.values():
            if isinstance(node, dict) and isinstance(node.get("recommendList"), list):
                return node
        return {}

    @staticmethod
    def _vod(item):
        tags = item.get("tags") or []
        if isinstance(tags, list):
            tags = ",".join(str(t) for t in tags)
        cnt = item.get("episode_cnt") or len(item.get("vid_list") or [])
        return {
            "vod_id": str(item.get("series_id") or ""),
            "vod_name": str(item.get("series_name") or ""),
            "vod_pic": str(item.get("series_cover") or ""),
            "type_name": str(tags),
            "vod_remarks": str(item.get("episode_right_text") or ("全%s集" % cnt if cnt else "")),
            "vod_content": str(item.get("series_intro") or ""),
        }

    # -------------------------------------------------------------- 接口
    def homeContent(self, filter=False):
        classes = [{"type_id": t, "type_name": n} for t, n, _ in self.CATEGORIES]
        classes += [{"type_id": t, "type_name": n} for t, n, _ in self.AUDIO_CATEGORIES]
        return {"class": classes, "filters": {}}

    def homeVideoContent(self):
        try:
            d = self._router_data(self.site + "/category")
            return {"list": [self._vod(x) for x in (self._category_list(d).get("recommendList") or [])]}
        except Exception as exc:
            print("[红果] 首页失败:", exc)
            return {"list": []}

    def categoryContent(self, tid, pg, filter=False, extend=None):
        # 听书分类
        audio_cat = None
        for t, _n, _id in self.AUDIO_CATEGORIES:
            if t == str(tid):
                audio_cat = _id
                break
        if audio_cat is not None:
            return self._audio_category_content(audio_cat, pg, filter, extend)

        page = max(1, int(pg or 1))
        path = "/category"
        for t, _n, p in self.CATEGORIES:
            if t == str(tid):
                path = p
                break
        sep = "&" if "?" in path else "?"
        url = "%s%s%s%s%d" % (self.site, path, sep, "page=", page)
        try:
            cat = self._category_list(self._router_data(url))
            items = cat.get("recommendList") or []
            pg_info = cat.get("pagination") or {}
            return {
                "list": [self._vod(x) for x in items],
                "page": page,
                "pagecount": int(pg_info.get("totalPages") or 1),
                "limit": pg_info.get("pageSize") or len(items),
                "total": pg_info.get("total") or 0,
            }
        except Exception as exc:
            print("[红果] 分类失败:", exc)
            return {"list": [], "page": page, "pagecount": 1, "limit": 0, "total": 0}

    # ---------------------------------------------------------- 听书：推荐流
    def _audio_tab_books(self, tab_type, gender, page, refresh_type=None):
        """取 bookmall 指定 tab 的一批书（听书 tab 每批 12 本，小说 tab 每批约 26 本）"""
        extra = {"gender": gender, "tab_type": tab_type, "page": page}
        if refresh_type:
            extra["refresh_type"] = refresh_type
        resp = None
        for _ in range(self.AUDIO_FEED_RETRY):
            resp = self._get_signed_audio_lenient(self.AUDIO_PATHS["tab"], extra)
            if isinstance(resp, dict) and resp.get("code") == 0:
                break
        if not isinstance(resp, dict) or resp.get("code") != 0:
            return []
        books = []
        for tab in ((resp.get("data") or {}).get("tab_item") or []):
            if tab.get("tab_type") != tab_type:
                continue
            self._collect_books(tab, books)
        return books

    @classmethod
    def _collect_books(cls, node, out):
        """递归收集 tab cell 里嵌套的书籍对象"""
        if isinstance(node, dict):
            if node.get("book_id") and (node.get("book_name") or node.get("title")):
                out.append(node)
            for value in node.values():
                cls._collect_books(value, out)
        elif isinstance(node, list):
            for value in node:
                cls._collect_books(value, out)

    def _audio_feed(self):
        """聚合听书内容池（带 TTL 缓存）。

        两个来源合并去重：
          1) 听书 tab（tab_type=5）—— 番茄真正的听书推荐位
          2) 男频小说 tab（tab_type=2）—— 这些书 tts_status=1，
             在番茄里点「听书」即用 TTS 播放，同样能走 batch_play 出声音
        """
        now = time.time()
        cached_at, cached = self._audio_feed_cache
        if cached and now - cached_at < self.AUDIO_FEED_TTL:
            return cached
        books = {}

        def merge(rows):
            for item in rows:
                bid = str(item.get("book_id") or "")
                if not bid:
                    continue
                old = books.get(bid)
                if old is None or (not old.get("thumb_url") and item.get("thumb_url")):
                    books[bid] = item

        for page in self.AUDIO_TAB_PAGES:
            for refresh in self.AUDIO_TAB_REFRESH:
                merge(self._audio_tab_books(5, 2, page, refresh))
        for page in self.AUDIO_NOVEL_PAGES:
            merge(self._audio_tab_books(2, 1, page))
        self._audio_feed_cache = (now, books)
        return books

    def _audio_category_content(self, cat_id, pg, filter, extend):
        """听书分类列表：聚合推荐流后按分类筛选/排序"""
        page = max(1, int(pg or 1))
        per_page = 24
        try:
            books = list(self._audio_feed().values())
            if extend:
                try:
                    ext = json.loads(str(extend)) if not isinstance(extend, dict) else extend
                    books = self._audio_apply_extend(books, ext)
                except Exception:
                    pass
            if cat_id == 1:          # 男频
                books = [b for b in books if str(b.get("gender") or "") == "1"]
            elif cat_id == 2:        # 女频
                books = [b for b in books if str(b.get("gender") or "") != "1"]
            elif cat_id == 3:        # 免费
                free = [b for b in books if str(b.get("total_price") or "0") in ("0", "0.0")]
                books = free or books
            elif cat_id == 4:        # 热播榜
                books = sorted(books, key=self._audio_listen_key, reverse=True)

            total = len(books)
            start = (page - 1) * per_page
            return {
                "list": [self._audio_vod(b) for b in books[start:start + per_page]],
                "page": page,
                "pagecount": max(1, (total + per_page - 1) // per_page),
                "limit": per_page,
                "total": total,
            }
        except Exception as exc:
            print("[听书] 分类列表异常:", exc)
            return {"list": [], "page": page, "pagecount": 1, "limit": 0, "total": 0}

    @staticmethod
    def _audio_apply_extend(books, ext):
        """支持按分类 / 标签 / 排序做二次筛选（extend 透传）"""
        cid = str(ext.get("category_id") or "").strip()
        tag = str(ext.get("tag") or ext.get("category") or "").strip()
        sort = str(ext.get("sort_by") or "").strip()
        if cid and cid != "0":
            books = [b for b in books
                     if cid in str(b.get("category_v2_ids") or "")
                     or cid in re.findall(r'"category_id"\s*:\s*(\d+)',
                                          str(b.get("category_schema") or ""))]
        if tag:
            books = [b for b in books
                     if tag in str(b.get("category") or "")
                     or tag in str(b.get("tags") or "")
                     or tag in str(b.get("pure_category_tags") or "")]
        if sort == "1":
            books = sorted(books, key=lambda b: str(b.get("create_time") or ""), reverse=True)
        elif sort == "2":
            books = sorted(books, key=Spider._audio_listen_key, reverse=True)
        return books

    @staticmethod
    def _audio_listen_key(book):
        try:
            return int(str(book.get("listen_count") or "0").replace(",", "") or 0)
        except Exception:
            return 0

    @classmethod
    def _audio_vod(cls, book):
        tags = str(book.get("tags") or book.get("category") or "")
        author = str(book.get("author") or "")
        listen = cls._audio_listen_key(book)
        remarks = str(book.get("serial_count") or "") or str(book.get("word_number") or "")
        if remarks and remarks.isdigit():
            remarks = "全%s章" % remarks
        return {
            "vod_id": "audio_" + str(book.get("book_id") or ""),
            "vod_name": str(book.get("book_name") or book.get("title") or ""),
            "vod_pic": str(book.get("thumb_url") or book.get("audio_thumb_uri") or ""),
            "type_name": tags,
            "vod_remarks": "%s$%s" % (remarks, ("%.1f万人听" % (listen / 10000.0))
                                     if listen else ""),
            "vod_actor": author,
            "vod_content": str(book.get("abstract") or book.get("book_abstract_v2") or ""),
        }

    def detailContent(self, ids):
        series_id = str(ids[0] if isinstance(ids, list) else ids)
        # 判断是否为听书 ID（以 "audio_" 开头）
        if series_id.startswith("audio_"):
            return self._audio_detail_content(series_id[6:])
        url = self.site + "/detail?series_id=" + urllib.parse.quote(series_id)
        try:
            d = self._router_data(url)
            sd = ((d.get("loaderData", {}).get("detail_page") or {}).get("seriesDetail")) or {}
            vids = sd.get("vid_list") or []
            episodes = ["第%d集$%s" % (i + 1, v) for i, v in enumerate(vids) if str(v)]
            tags = sd.get("tags") or []
            if isinstance(tags, list):
                tags = ",".join(str(t) for t in tags)
            vod = {
                "vod_id": series_id,
                "vod_name": str(sd.get("series_name") or "红果短剧"),
                "vod_pic": str(sd.get("series_cover") or ""),
                "type_name": tags,
                "vod_remarks": str(sd.get("episode_right_text")
                                   or ("全%s集" % sd.get("episode_cnt") if sd.get("episode_cnt") else "")),
                "vod_actor": ",".join(str(c.get("nickname") or "")
                                      for c in (sd.get("celebrities") or [])
                                      if isinstance(c, dict)),
                "vod_content": str(sd.get("series_intro") or ""),
                "vod_play_from": "红果短剧",
                "vod_play_url": "#".join(episodes),
            }
            return {"list": [vod]}
        except Exception as exc:
            print("[红果] 详情失败:", exc)
            return {"list": []}

    def _audio_chapters(self, book_id):
        """章节目录：directory/all_items。

        catalog_data 给出「卷/章」目录（含卷名），但部分书该字段为 null，
        此时退回 item_data_list（同样带 item_id + title + volume_name）。
        """
        cached = self._audio_chapter_cache.get(book_id)
        if cached and time.time() - cached[0] < self.AUDIO_FEED_TTL:
            return cached[1]
        resp = self._get_signed_audio_lenient(self.AUDIO_PATHS["directory"],
                                              {"book_id": str(book_id)})
        chapters = []
        if isinstance(resp, dict) and resp.get("code") == 0:
            data = resp.get("data") or {}
            volumes = {}
            for item in data.get("item_data_list") or []:
                volumes[str(item.get("item_id"))] = str(item.get("volume_name") or "")
            catalog = data.get("catalog_data")
            if isinstance(catalog, list) and catalog:
                for cat in catalog:
                    item_id = str(cat.get("item_id") or "")
                    if not item_id:
                        continue
                    title = str(cat.get("catalog_title") or "")
                    vol = volumes.get(item_id)
                    if vol and not title.startswith(vol):
                        title = "%s %s" % (vol, title)
                    chapters.append((item_id, title))
            else:
                # 无目录数据时直接用 item_data_list
                for item in data.get("item_data_list") or []:
                    item_id = str(item.get("item_id") or "")
                    if not item_id:
                        continue
                    title = str(item.get("title") or "")
                    vol = str(item.get("volume_name") or "")
                    if vol and not title.startswith(vol):
                        title = "%s %s" % (vol, title)
                    chapters.append((item_id, title))
        self._audio_chapter_cache[book_id] = (time.time(), chapters)
        return chapters

    def _audio_detail_content(self, book_id):
        """听书详情：directory/all_items 同时返回 book_info 与章节目录"""
        chapters = self._audio_chapters(book_id)
        book_info = {}
        try:
            resp = self._get_signed_audio_lenient(self.AUDIO_PATHS["directory"],
                                                  {"book_id": str(book_id)})
            if isinstance(resp, dict) and resp.get("code") == 0:
                book_info = (resp.get("data") or {}).get("book_info") or {}
        except Exception:
            pass
        if not book_info:
            for book in self._audio_feed().values():
                if str(book.get("book_id")) == str(book_id):
                    book_info = book
                    break

        # 播放地址需要 book_id + item_id，用 "|" 一起编码进集号
        episodes = ["%s$%s|%s" % (title, book_id, item_id) for item_id, title in chapters]
        tags = str(book_info.get("tags") or book_info.get("category") or "")
        listen = self._audio_listen_key(book_info)
        total_ch = len(episodes)
        vod = {
            "vod_id": "audio_" + str(book_id),
            "vod_name": str(book_info.get("book_name") or ""),
            "vod_pic": str(book_info.get("thumb_url") or book_info.get("audio_thumb_uri") or ""),
            "type_name": tags,
            "vod_remarks": "全%d章" % total_ch if total_ch else "",
            "vod_year": str(book_info.get("create_time") or "")[:10].replace("-", ""),
            "vod_area": "番茄小说",
            "vod_actor": str(book_info.get("author") or ""),
            "vod_director": "%s$%s" % (str(book_info.get("score") or ""),
                                       ("%.1f万人听" % (listen / 10000.0)) if listen else ""),
            "vod_content": str(book_info.get("abstract") or book_info.get("book_abstract_v2") or ""),
            "vod_play_from": "番茄听书",
            "vod_play_url": "#".join(episodes),
        }
        return {"list": [vod]}

    def searchContent(self, key, quick=False, pg="1"):
        page = max(1, int(pg or 1))
        kw = str(key or "").strip().lower()
        if not kw:
            return {"list": [], "page": page, "pagecount": 1}
        # 听书搜索
        if kw.startswith("audio:"):
            return self._audio_search_content(kw[6:], page)
        per_page = 24
        found, seen = [], set()
        try:
            for _t, _n, path in self.CATEGORIES:
                for p in range(1, 4):
                    sep = "&" if "?" in path else "?"
                    try:
                        d = self._router_data("%s%s%s%spage=%d" % (self.site, path, sep, "", p))
                    except Exception:
                        continue
                    for x in (self._category_list(d).get("recommendList") or []):
                        sid = str(x.get("series_id") or "")
                        if not sid or sid in seen:
                            continue
                        hay = (str(x.get("series_name") or "") + " "
                               + str(x.get("series_intro") or "") + " "
                               + ",".join(str(t) for t in (x.get("tags") or []))).lower()
                        if kw in hay:
                            seen.add(sid)
                            found.append(self._vod(x))
        except Exception as exc:
            print("[红果] 搜索失败:", exc)

        # 同时并入听书结果（audio_ 前缀），让同一关键词能搜到有声书
        try:
            audio_hit = self._audio_search_feed(kw)
            for book in audio_hit:
                aid = "audio_" + str(book.get("book_id") or "")
                if aid in seen:
                    continue
                seen.add(aid)
                found.append(self._audio_vod(book))
        except Exception as exc:
            print("[红果] 听书搜索失败:", exc)

        start = (page - 1) * per_page
        return {"list": found[start:start + per_page], "page": page,
                "pagecount": max(1, (len(found) + per_page - 1) // per_page),
                "limit": per_page, "total": len(found)}

    def _audio_search_content(self, keyword, page):
        """听书搜索。

        search/page 需要服务端会话态的 search_id，直连多半返回空；
        因此优先调接口，取不到时退回「推荐流关键词匹配」，保证有结果。
        """
        page = max(1, int(page or 1))
        per_page = 24
        try:
            items = self._audio_search_api(keyword, page, per_page)
            source = "api"
        except Exception as exc:
            print("[听书] 搜索接口异常:", exc)
            items, source = [], "api"

        if not items:
            items = self._audio_search_feed(keyword)
            source = "feed"

        total = len(items)
        start = (page - 1) * per_page
        return {
            "list": [self._audio_vod(b) for b in items[start:start + per_page]],
            "page": page,
            "pagecount": max(1, (total + per_page - 1) // per_page),
            "limit": per_page,
            "total": total,
            "source": source,
        }

    def _audio_search_api(self, keyword, page, per_page):
        """search/page 直连尝试（query + 搜索会话参数）"""
        from uuid import uuid4
        params = {
            "query": keyword,
            "offset": (max(1, int(page)) - 1) * per_page,
            "count": per_page,
            "search_id": uuid4().hex,
            "search_source": "BOOKSTORE",
            "tab_type": "Voice",
        }
        resp = self._get_signed_audio_lenient(self.AUDIO_PATHS["search_page"], params,
                                              self.AUDIO_SEARCH_API)
        items = []
        if isinstance(resp, dict) and resp.get("code") == 0:
            data = resp.get("data")
            if isinstance(data, dict):
                for key in ("book_list", "item_list", "list", "search_result"):
                    rows = data.get(key)
                    if isinstance(rows, list):
                        items.extend(r for r in rows if isinstance(r, dict))
                        break
            elif isinstance(data, list):
                items.extend(r for r in data if isinstance(r, dict))
        return items

    def _audio_search_feed(self, keyword):
        """兜底：在听书推荐流里按书名 / 作者 / 标签匹配"""
        kw = str(keyword or "").strip().lower()
        if not kw:
            return []
        matched = []
        for book in self._audio_feed().values():
            hay = " ".join(str(book.get(k) or "") for k in
                           ("book_name", "author", "category", "tags",
                            "pure_category_tags", "role", "original_book_name")).lower()
            if kw in hay:
                matched.append(book)
        return matched

    # -------------------------------------------------------------- 播放
    def playerContent(self, flag, pid, vipFlags=None):
        # 听书播放
        if str(pid).startswith("audio_"):
            return self._audio_player_content(pid[6:])
        vid = str(pid)
        try:
            media = self._resolve_media(vid)
        except Exception as exc:
            print("[红果] 取流失败:", exc)
            media = None
        if not media or not media.get("url"):
            print("[红果] 未取到可播放地址 vid=%s" % vid)
            return {"parse": 0, "url": "", "header": {}}

        result = {
            "parse": 0,
            "url": media["url"],
            "header": {"User-Agent": APP_UA, "Referer": MEDIA_REFERER},
        }
        if self.play_mode == "stream":
            base = self.license_base or self._detect_license_base()
            query = urllib.parse.urlencode({
                "do": "py", "siteKey": self.site_key,
                "type": "stream", "vid": vid, "q": "auto",
            })
            result["url"] = base + "/proxy?" + query
            return result
        if media.get("key"):
            kid = str(media.get("kid") or "").lower()
            self._pending_key[kid] = media["key"].hex()
            result["drm"] = {
                "type": "clearkey",
                "key": self._license_url(kid, media["key"].hex()),
                "forceKey": True,
            }
        return result

    def _audio_player_content(self, chapter_key):
        """听书播放：POST audio/batch_play 批量换真实音频流地址。

        chapter_key 形如 "<book_id>|<item_id>"（由详情页集号编码而来）
        """
        book_id, _, item_id = str(chapter_key).partition("|")
        if not item_id:
            item_id = book_id
            book_id = ""
        if not book_id:
            print("[听书] 缺少 book_id: %s" % chapter_key)
            return {"parse": 0, "url": "", "header": {}}

        payload = {"book_play_requests": [{
            "book_id": int(book_id),
            "item_id": int(item_id),
            "req_type": "PLAY",
            "tone_quality": self.AUDIO_TONE_QUALITY,
            "tone_id": int(self.AUDIO_TONE_ID),
            "is_local_book": False,
        }]}
        try:
            resp = self._post_signed_audio_lenient(self.AUDIO_PATHS["batch_play"], payload)
        except Exception as exc:
            print("[听书] 播放异常:", exc)
            return {"parse": 0, "url": "", "header": {}}

        audio_url = ""
        if isinstance(resp, dict) and resp.get("code") == 0:
            for item in (resp.get("data") or []):
                if not isinstance(item, dict):
                    continue
                if str(item.get("item_id")) not in (item_id, ""):
                    continue
                info = item.get("play_info_data") or {}
                audio_url = info.get("main_url") or info.get("backup_url") or ""
                if audio_url:
                    break
        if not audio_url:
            print("[听书] 未取到音频流地址 resp=%s" % json.dumps(resp, ensure_ascii=False)[:200])
            return {"parse": 0, "url": "", "header": {}}

        return {
            "parse": 0,
            "url": audio_url,
            "header": {
                "User-Agent": APP_UA,
                "Referer": "https://novel.snssdk.com/",
            },
        }

    def _license_url(self, kid, key_hex):
        base = self.license_base or self._detect_license_base()
        q = urllib.parse.urlencode({"do": "py", "siteKey": self.site_key,
                                    "type": "clearkey", "kid": kid, "key": key_hex})
        return base + "/proxy?" + q

    def _detect_license_base(self):
        """探测影视TV 内置本地服务端口（默认从 9978 起，被占用则自增）"""
        if self._license_probed and self.license_base:
            return self.license_base
        for port in range(9978, 9999):
            try:
                req = urllib.request.Request("http://127.0.0.1:%d/device" % port)
                with urllib.request.urlopen(req, timeout=0.4) as r:
                    if r.status == 200:
                        self.license_base = "http://127.0.0.1:%d" % port
                        self._license_probed = True
                        return self.license_base
            except Exception:
                continue
        self._license_probed = True
        self.license_base = self.license_base or "http://127.0.0.1:9978"
        return self.license_base

    def localProxy(self, params):
        """响应影视TV 内置本地服务的代理请求"""
        try:
            if isinstance(params, str):
                params = dict(urllib.parse.parse_qsl(params))
            proxy_type = str(params.get("type") or "")
            if proxy_type == "stream":
                return self._proxy_stream(params)
            if proxy_type != "clearkey":
                return [404, "text/plain", "not found"]
            kid = str(params.get("kid") or "")
            key_hex = str(params.get("key") or "")
            if not key_hex:
                key_hex = self._pending_key.get(kid, "")
            if not key_hex:
                return [404, "text/plain", "no key"]
            b64url = lambda b: base64.urlsafe_b64encode(b).decode().rstrip("=")
            payload = {
                "keys": [{"kty": "oct", "k": b64url(bytes.fromhex(key_hex)),
                          "kid": b64url(bytes.fromhex(kid)) if kid else ""}],
                "type": "temporary",
            }
            return [200, "application/json", json.dumps(payload, separators=(',', ':'))]
        except Exception as exc:
            print("[红果] localProxy 失败:", exc)
            return [500, "text/plain", "error"]

    # ------------------------------------------------------------ 流解密代理
    SEGMENT_LIMIT = 1 << 20

    def _remote_total(self, url, headers):
        try:
            req = urllib.request.Request(url, headers=headers, method="HEAD")
            with urllib.request.urlopen(req, timeout=20) as r:
                return int(r.headers.get("Content-Length") or 0)
        except Exception:
            return 0

    def _fetch_range(self, url, start, end, headers):
        """循环读满请求的字节数，避免短读导致 Content-Range 与 body 不一致"""
        req = urllib.request.Request(url, headers=headers)
        req.add_header("Range", "bytes=%d-%d" % (start, end))
        with urllib.request.urlopen(req, timeout=30) as r:
            want = end - start + 1
            chunks = []
            got = 0
            while got < want:
                chunk = r.read(want - got)
                if not chunk:
                    break
                chunks.append(chunk)
                got += len(chunk)
            data = b"".join(chunks)
            content_range = r.headers.get("Content-Range") or ""
            status = getattr(r, "status", None) or getattr(r, "code", 200)
        total = 0
        match = re.search(r"bytes\s+\d+-\d+/(\d+)", content_range)
        if match:
            total = int(match.group(1))
        return data, total, status

    def _stream_media(self, vid):
        """按 vid 缓存解析结果，避免每个 Range 请求重复调签名接口"""
        cached = self._media_cache.get(vid)
        if cached and time.time() - cached[1] < 300:
            return cached[0]
        media = self._resolve_media(vid)
        if media:
            self._media_cache[vid] = (media, time.time())
        return media

    @staticmethod
    def _range_header(params):
        for key, value in (params or {}).items():
            if str(key).lower() in ("__range", "range"):
                return value
        return None

    def _parse_cenc_tracks(self, data):
        """从 moov 解析 encv 轨道 stbl/senc 样本信息"""
        moov = _find_box(data, b"moov")
        if not moov:
            raise RuntimeError("moov box not found")
        moov_data = data[moov.start:moov.end]
        samples = []
        for trak in _find_boxes(moov_data, b"trak"):
            trak_data = moov_data[trak.start:trak.end]
            if b"encv" not in trak_data and b"enca" not in trak_data:
                continue
            stbl = _find_box(trak_data, b"stbl")
            if not stbl:
                continue
            stbl_data = trak_data[stbl.start:stbl.end]

            stsz = _find_box(stbl_data, b"stsz")
            stsc = _find_box(stbl_data, b"stsc")
            stco = _find_box(stbl_data, b"stco") or _find_box(stbl_data, b"co64")
            saiz = _find_box(stbl_data, b"saiz")
            saio = _find_box(stbl_data, b"saio")
            if not stsz or not stsc or not stco or not saiz or not saio:
                continue

            stsz_body = stbl_data[stsz.start:stsz.end]
            default_sample_size = int.from_bytes(stsz_body[4:8], "big")
            sample_count = int.from_bytes(stsz_body[8:12], "big")
            sizes = []
            if default_sample_size:
                sizes = [default_sample_size] * sample_count
            else:
                for i in range(sample_count):
                    at = 12 + i * 4
                    sizes.append(int.from_bytes(stsz_body[at:at + 4], "big"))
            if len(sizes) != sample_count:
                raise RuntimeError("stsz sample count mismatch")

            stsc_body = stbl_data[stsc.start:stsc.end]
            entry_count = int.from_bytes(stsc_body[4:8], "big")
            entries = []
            for i in range(entry_count):
                at = 8 + i * 12
                entries.append((
                    int.from_bytes(stsc_body[at:at + 4], "big"),
                    int.from_bytes(stsc_body[at + 4:at + 8], "big"),
                ))

            co64 = stbl_data.find(b"co64", stco.start) == stco.start
            stco_body = stbl_data[stco.start:stco.end]
            chunk_count = int.from_bytes(stco_body[4:8], "big")
            offsets = []
            for i in range(chunk_count):
                at = 8 + i * (8 if co64 else 4)
                offsets.append(int.from_bytes(stco_body[at:at + (8 if co64 else 4)], "big"))

            samples_per_chunk = []
            for chunk_index in range(chunk_count):
                selected = 0
                for first_chunk, count in entries:
                    if first_chunk <= chunk_index + 1:
                        selected = count
                samples_per_chunk.append(selected)

            saiz_body = stbl_data[saiz.start:saiz.end]
            aux_default = saiz_body[4]
            aux_count = int.from_bytes(saiz_body[5:9], "big")
            aux_sizes = []
            if aux_default:
                aux_sizes = [aux_default] * aux_count
            else:
                for i in range(aux_count):
                    at = 9 + i
                    if at >= len(saiz_body):
                        break
                    aux_sizes.append(saiz_body[at])
            if len(aux_sizes) != aux_count:
                raise RuntimeError("saiz sample count mismatch")

            saio_body = stbl_data[saio.start:saio.end]
            offset_size = 8 if saio_body[0] == 1 else 4
            saio_count = int.from_bytes(saio_body[4:8], "big")
            aux_offset = int.from_bytes(saio_body[8:8 + offset_size], "big")

            aux_total = sum(max(size, 8) for size in aux_sizes)
            if aux_offset < 0 or aux_offset + aux_total > len(data):
                raise RuntimeError("MP4 auxiliary data out of range")
            aux = data[aux_offset:aux_offset + aux_total]

            track_samples = []
            aux_pos = 0
            sample_index = 0
            for chunk_index, offset in enumerate(offsets):
                count = samples_per_chunk[chunk_index] or 0
                for _ in range(count):
                    if sample_index >= sample_count:
                        break
                    size = sizes[sample_index]
                    aux_size = max(aux_sizes[sample_index], 8)
                    iv = bytearray(16)
                    take = min(8, aux_size)
                    if aux_pos + take <= len(aux):
                        iv[:take] = aux[aux_pos:aux_pos + take]
                    track_samples.append({
                        "start": offset,
                        "end": offset + size,
                        "iv": bytes(iv),
                    })
                    offset += size
                    sample_index += 1
                    aux_pos += aux_size
            samples.extend(track_samples)
        samples.sort(key=lambda item: item["start"])
        return samples

    def _prepare_stream(self, url, headers):
        """抓取 moov、规范化四cc、解析 CENC 样本"""
        cached = self._stream_cache.get(url)
        if cached:
            return cached

        data, total, status = self._fetch_range(url, 0, (1 << 20) - 1, headers)
        if not data:
            raise RuntimeError("empty stream response")
        moov = _find_box(data, b"moov")
        if not moov:
            raise RuntimeError("moov not found in first 1MB")
        if moov.end > len(data):
            data, more_total, _ = self._fetch_range(url, 0, moov.end - 1, headers)
            total = more_total or total
        if moov.end > len(data):
            raise RuntimeError("moov range incomplete")

        samples = self._parse_cenc_tracks(data)
        header = bytearray(data[:moov.end])
        header = _replace_all(header, b"encv", b"hvc1")
        header = _replace_all(header, b"enca", b"mp4a")
        header = _replace_sinf(header)
        if not total:
            total = self._remote_total(url, headers) or len(data)
        prepared = {
            "header": bytes(header),
            "samples": samples,
            "total": total,
        }
        self._stream_cache[url] = prepared
        return prepared

    def _decrypt_partial(self, data, start, key, prepared):
        output = bytearray(data)
        end = start + len(output)
        header = prepared.get("header") or b""
        if start < len(header):
            overlap_end = min(end, len(header))
            output[0:overlap_end - start] = header[start:overlap_end]
        if not key:
            return bytes(output)
        for sample in prepared.get("samples") or []:
            if sample["end"] <= start:
                continue
            if sample["start"] >= end:
                break
            overlap_start = max(start, sample["start"])
            overlap_end = min(end, sample["end"])
            if overlap_start >= overlap_end:
                continue
            relative = overlap_start - sample["start"]
            block = relative // 16
            block_byte_start = block * 16
            relative_end = overlap_end - sample["start"]
            block_byte_end = ((relative_end + 15) // 16) * 16
            keystream = _aes_keystream(
                key, _add_counter(sample["iv"], block),
                block_byte_end - block_byte_start,
            )
            for cursor in range(overlap_start, overlap_end):
                output[cursor - start] ^= keystream[cursor - sample["start"] - block_byte_start]
        return bytes(output)

    def _proxy_stream(self, params):
        vid = str(params.get("vid") or "")
        if not vid or not vid.isdigit():
            return [400, "text/plain", "bad vid"]
        media = self._stream_media(vid)
        if not media or not media.get("url"):
            return [502, "text/plain", "stream unavailable"]
        url = media["url"]
        key = media.get("key")
        headers = {"User-Agent": APP_UA, "Referer": MEDIA_REFERER}
        try:
            prepared = self._prepare_stream(url, headers)
            total = prepared.get("total") or 0
            range_pair = _parse_range_header(self._range_header(params), total)
            if range_pair is None:
                start = 0
                end = min(total, self.SEGMENT_LIMIT) - 1
            else:
                start, end = range_pair
                end = min(end, start + self.SEGMENT_LIMIT - 1, total - 1)
            remote_data, remote_total, status = self._fetch_range(url, start, end, headers)
            if status == 416 or not remote_data:
                return [416, "text/plain", "range not satisfiable"]
            output = self._decrypt_partial(remote_data, start, key, prepared)
            actual_end = start + len(output) - 1
            return [206, "video/mp4", output, {
                "Content-Range": "bytes %d-%d/%d" % (start, actual_end, total),
                "Accept-Ranges": "bytes",
            }]
        except Exception as exc:
            print("[红果] 流解密代理失败:", exc)
            return [502, "text/plain", "stream decrypt failed: %s" % exc]
