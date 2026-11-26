/*
 * محرك شاشة داخل المتصفح (Web Worker)
 *
 * يقرأ ملف الفيديو من السيرفر على دفعات (HTTP Range)، ويفتحه بمكتبة FFmpeg (libav.js / WebAssembly)،
 * وينسخ الصورة كما هي، والصوت: ينسخه لو الجهاز يشغّله، وإلا يحوّله لـ AAC.
 * الناتج MP4 مجزّأ يشغّله المشغّل عن طريق MediaSource.
 * وفوق كذا يقيس طاقة الكلام في الصوت (للمزامنة التلقائية للترجمة) ويطلّع الترجمات المضمّنة في الملف.
 *
 * مكتوب بـ JavaScript عادي (بدون ?. و ??) عشان يشتغل على متصفحات التلفزيونات القديمة (Chromium 68).
 */
"use strict";

var LIBAV_FILE = "libav-6.0.0-shasha.js";
var DT = 0.05; // نفس دقة المزامنة في الواجهة (50ms)
var AHEAD = 75; // كم ثانية نجهّز قدّام مكان التشغيل
var AVDISCARD_ALL = 48;
var AV_SAMPLE_FMT_FLTP = 8;
var TEXT_SUBS = { subrip: 1, ass: 1, ssa: 1, webvtt: 1, mov_text: 1, text: 1 };

var lib = null;
var fmt = 0;
var inPkt = 0;
var media = null; // معلومات الملف
var src = null; // القارئ من السيرفر
var session = null; // التشغيل الحالي
var playhead = 0;
var wantSpeech = false;
var queue = Promise.resolve(); // نرتّب الأوامر وحدة وحدة

function post(msg, transfer) {
  self.postMessage(msg, transfer || []);
}

function log() {
  // console.log.apply(console, ["[engine]"].concat([].slice.call(arguments)));
}

function sleep(ms) {
  return new Promise(function (r) { setTimeout(r, ms); });
}

/* ───── الأرقام 64-bit تجي من libav.js كجزئين ───── */
var NOPTS_HI = -2147483648;
function i64(lo, hi) {
  if (hi === NOPTS_HI && lo === 0) return null;
  return hi * 4294967296 + (lo >>> 0);
}
function split64(v) {
  var hi = Math.floor(v / 4294967296);
  return [(v - hi * 4294967296) | 0, hi];
}

/* ───── قراءة الملف من السيرفر ─────
 * نخلي اتصال واحد مفتوح يقرأ للأمام (bytes=pos-)، ولو المكتبة طلبت مكان بعيد نفتح اتصال جديد.
 * ونحتفظ بآخر القطع اللي أرسلناها عشان لو رجعت المكتبة خطوة لورا ما نحتاج اتصال جديد. */
var lowMemory = false; // الجوال: كاش ودفعات أصغر

function Source(url, size) {
  this.url = url;
  this.size = size;
  this.conn = null; // {pos, reader, ctrl, left: Uint8Array|null}
  this.cache = []; // [{pos, data}]
  this.seq = 0; // كم قراءة متتالية (عشان نكبّر الدفعات)
  this.closed = false;
}

Source.prototype.close = function () {
  this.closed = true;
  this.drop();
};

Source.prototype.drop = function () {
  var c = this.conn;
  this.conn = null;
  if (c) {
    try { c.ctrl.abort(); } catch (e) { /* ignore */ }
  }
};

Source.prototype.open = function (pos) {
  this.drop();
  var ctrl = new AbortController();
  var self_ = this;
  var conn = { pos: pos, reader: null, ctrl: ctrl, left: null, ready: null };
  conn.ready = fetch(this.url, { headers: { Range: "bytes=" + pos + "-" }, signal: ctrl.signal, cache: "no-store" }).then(function (res) {
    if (res.status !== 206 && !(res.status === 200 && pos === 0)) throw new Error("HTTP " + res.status);
    if (!res.body) throw new Error("no body");
    conn.reader = res.body.getReader();
  });
  this.conn = conn;
  log("open", pos);
  return conn;
};

/** يقرأ قطعة من الاتصال (مع مهلة لو السيرفر علّق) */
Source.prototype.chunk = function (conn) {
  if (conn.left) {
    var l = conn.left;
    conn.left = null;
    return Promise.resolve(l);
  }
  return conn.ready.then(function () {
    var timer;
    return Promise.race([
      conn.reader.read().then(function (r) { clearTimeout(timer); return r.done ? null : r.value; }),
      new Promise(function (_r, rej) { timer = setTimeout(function () { rej(new Error("timeout")); }, 20000); }),
    ]);
  });
};

Source.prototype.fromCache = function (pos) {
  for (var i = this.cache.length - 1; i >= 0; i--) {
    var c = this.cache[i];
    if (pos >= c.pos && pos < c.pos + c.data.length) return c.data.subarray(pos - c.pos);
  }
  return null;
};

Source.prototype.remember = function (pos, data) {
  this.cache.push({ pos: pos, data: data });
  var total = 0;
  for (var i = this.cache.length - 1; i >= 0; i--) {
    total += this.cache[i].data.length;
    if (total > (lowMemory ? 4 : 12) * 1024 * 1024) {
      this.cache.splice(0, i);
      break;
    }
  }
};

/** يرجّع بيانات تبدأ من pos (طولها على الأقل want لو الملف ما خلص) */
Source.prototype.read = async function (pos, want) {
  var cached = this.fromCache(pos);
  // بدون نسخ: libav ينسخ البيانات لذاكرته بنفسه، والنسخ الزايدة كانت تعبّي ذاكرة الجوال
  if (cached && cached.length >= Math.min(want, 65536)) return cached;
  var attempt = 0;
  for (;;) {
    if (this.closed) throw new Error("closed");
    try {
      return await this.readNet(pos, want);
    } catch (e) {
      this.drop();
      if (this.closed || ++attempt > 4) throw e;
      log("retry", pos, String(e));
      await sleep(400 * attempt);
    }
  }
};

Source.prototype.readNet = async function (pos, want) {
  var conn = this.conn;
  // الاتصال الحالي ينفع لو كان قبل المكان المطلوب بشوي (نرمي الفرق)
  if (!conn || conn.pos > pos || pos - conn.pos > 3 * 1024 * 1024) {
    conn = this.open(pos);
    this.seq = 0;
  } else {
    this.seq++;
  }
  while (conn.pos < pos) {
    var skip = await this.chunk(conn);
    if (!skip) throw new Error("eof while skipping");
    var need = pos - conn.pos;
    if (skip.length > need) {
      conn.left = skip.subarray(need);
      conn.pos = pos;
    } else {
      conn.pos += skip.length;
    }
  }
  // أول قراءات (رأس الملف) صغيرة وسريعة، وبعدها نكبّر الدفعة
  var target = Math.min(this.size - pos, Math.max(want, this.seq > 3 ? (lowMemory ? 1024 * 1024 : 2 * 1024 * 1024) : 256 * 1024));
  var parts = [];
  var got = 0;
  while (got < target) {
    var c = await this.chunk(conn);
    if (!c) break;
    if (got + c.length > target && got >= want) {
      var take = target - got;
      parts.push(c.subarray(0, take));
      conn.left = c.subarray(take);
      got += take;
      break;
    }
    parts.push(c);
    got += c.length;
  }
  if (!got) throw new Error("eof");
  var out = parts.length === 1 ? parts[0] : new Uint8Array(got);
  if (parts.length > 1) {
    var o = 0;
    for (var i = 0; i < parts.length; i++) {
      out.set(parts[i], o);
      o += parts[i].length;
    }
  }
  conn.pos += got;
  this.remember(pos, out);
  return out;
};

/* ───── تحميل المكتبة وفتح الملف ───── */

async function loadLib(base) {
  if (lib) return lib;
  self.LibAV = { base: base };
  importScripts(base + "/" + LIBAV_FILE);
  lib = await self.LibAV.LibAV({ noworker: true, base: base });
  lib.av_log_set_level_sync(16); // أخطاء بس
  lib.onblockread = function (name, pos, len) {
    if (!src) return;
    return src.read(pos, len).then(
      function (data) { return lib.ff_block_reader_dev_send(name, pos, data); },
      function (err) { return lib.ff_block_reader_dev_send(name, pos, null, { error: err }); }
    );
  };
  lib.onwrite = function (_name, pos, data) {
    if (session && session.out) session.out.write(pos, data);
  };
  return lib;
}

function codecName(id) {
  return lib.avcodec_get_name_sync(id);
}

function hex2(n) {
  return (n < 16 ? "0" : "") + n.toString(16);
}

/** نص الترميز اللي يحتاجه MediaSource (avc1.640029 أو hvc1.2.4.L153.B0) من بيانات الملف */
function videoCodecString(name, extradata, profile, level) {
  if (name === "h264") {
    if (extradata && extradata.length > 4 && extradata[0] === 1)
      return "avc1." + hex2(extradata[1]) + hex2(extradata[2]) + hex2(extradata[3]);
    var p = { 66: "4200", 77: "4d40", 88: "5800", 100: "6400", 110: "6e00", 122: "7a00", 244: "f400" }[profile] || "6400";
    return "avc1." + p + hex2(level > 0 ? level : 40);
  }
  if (name === "hevc") {
    if (extradata && extradata.length > 22 && extradata[0] === 1) {
      var b = extradata;
      var space = ["", "A", "B", "C"][b[1] >> 6];
      var tier = (b[1] >> 5) & 1 ? "H" : "L";
      var prof = b[1] & 31;
      // أعلام التوافق مقلوبة البتات حسب المواصفة
      var compat = ((b[2] << 24) | (b[3] << 16) | (b[4] << 8) | b[5]) >>> 0;
      var rev = 0;
      for (var i = 0; i < 32; i++) if (compat & (1 << i)) rev |= 1 << (31 - i);
      var cons = [b[6], b[7], b[8], b[9], b[10], b[11]];
      while (cons.length && cons[cons.length - 1] === 0) cons.pop();
      var s = "hvc1." + space + prof + "." + (rev >>> 0).toString(16).toUpperCase() + "." + tier + b[12];
      for (var k = 0; k < cons.length; k++) s += "." + cons[k].toString(16).toUpperCase();
      return s;
    }
    var main10 = profile === 2;
    return main10 ? "hvc1.2.4.L" + (level > 0 ? level : 120) + ".B0" : "hvc1.1.6.L" + (level > 0 ? level : 120) + ".B0";
  }
  return name;
}

async function openFile(msg) {
  await loadLib(msg.base);
  if (src) src.close();
  src = new Source(msg.url, msg.size);
  try { lib.unlink_sync("in"); } catch (e) { /* ignore */ }
  await lib.mkblockreaderdev("in", msg.size);
  var opts = lib.av_dict_set_js_sync(0, "probesize", "2500000", 0);
  opts = lib.av_dict_set_js_sync(opts, "analyzeduration", "3000000", 0);
  fmt = await lib.avformat_open_input_js("in", 0, opts);
  if (!fmt) throw new Error("open failed");
  var r = await lib.avformat_find_stream_info(fmt, 0);
  if (r < 0) throw new Error("stream info failed");
  inPkt = lib.av_packet_alloc_sync();

  var n = lib.AVFormatContext_nb_streams_sync(fmt);
  var streams = [];
  for (var i = 0; i < n; i++) {
    var st = lib.AVFormatContext_streams_a_sync(fmt, i);
    var par = lib.AVStream_codecpar_sync(st);
    var type = lib.AVCodecParameters_codec_type_sync(par);
    var id = lib.AVCodecParameters_codec_id_sync(par);
    var name = codecName(id);
    var exSize = lib.AVCodecParameters_extradata_size_sync(par);
    var exPtr = lib.AVCodecParameters_extradata_sync(par);
    var extradata = exSize > 0 && exPtr ? lib.copyout_u8_sync(exPtr, Math.min(exSize, 512)) : null;
    var profile = lib.AVCodecParameters_profile_sync(par);
    var level = lib.AVCodecParameters_level_sync(par);
    var s = {
      index: i,
      st: st,
      par: par,
      type: type === 0 ? "video" : type === 1 ? "audio" : type === 3 ? "subtitle" : "other",
      codec: name,
      codecId: id,
      tbNum: lib.AVStream_time_base_num_sync(st),
      tbDen: lib.AVStream_time_base_den_sync(st),
      profile: profile,
      level: level,
      width: lib.AVCodecParameters_width_sync(par),
      height: lib.AVCodecParameters_height_sync(par),
      channels: lib.AVCodecParameters_ch_layout_nb_channels_sync(par),
      sampleRate: lib.AVCodecParameters_sample_rate_sync(par),
      language: lib.shasha_meta_sync(fmt, i, "language") || "",
      title: lib.shasha_meta_sync(fmt, i, "title") || "",
      isDefault: (lib.shasha_disposition_sync(fmt, i) & 1) === 1,
      forced: (lib.shasha_disposition_sync(fmt, i) & 0x40) !== 0,
      attached: (lib.shasha_disposition_sync(fmt, i) & 0x400) !== 0, // صورة الغلاف
      delay: lib.shasha_video_delay_sync(par),
      fps: 0,
    };
    if (s.type === "video") {
      var fn = lib.AVStream_avg_frame_rate_num_sync(st), fd = lib.AVStream_avg_frame_rate_den_sync(st);
      if (!(fn > 0 && fd > 0)) {
        fn = lib.AVStream_r_frame_rate_num_sync(st);
        fd = lib.AVStream_r_frame_rate_den_sync(st);
      }
      s.fps = fn > 0 && fd > 0 ? fn / fd : 24;
    }
    if (s.type === "video") s.codecString = videoCodecString(name, extradata, profile, level);
    if (s.type === "video" && name === "hevc") s.tenBit = profile === 2 || (extradata && extradata.length > 1 && (extradata[1] & 31) === 2);
    streams.push(s);
  }
  var chapters = [];
  var nc = lib.shasha_nb_chapters_sync(fmt);
  for (var c = 0; c < nc; c++) {
    chapters.push({
      start: lib.shasha_chapter_time_sync(fmt, c, 0),
      end: lib.shasha_chapter_time_sync(fmt, c, 1),
      title: lib.shasha_chapter_title_sync(fmt, c) || "",
    });
  }
  var video = null;
  for (var v = 0; v < streams.length; v++) {
    if (streams[v].type === "video" && !streams[v].attached && (streams[v].codec === "h264" || streams[v].codec === "hevc")) {
      video = streams[v];
      break;
    }
  }
  media = {
    streams: streams,
    video: video,
    audio: streams.filter(function (x) { return x.type === "audio"; }),
    subs: streams.filter(function (x) { return x.type === "subtitle" && TEXT_SUBS[x.codec]; }),
    container: lib.shasha_fmt_name_sync(fmt) || "",
    duration: lib.shasha_fmt_duration_sync(fmt),
    startTime: lib.shasha_fmt_start_sync(fmt),
    chapters: chapters,
  };
  media.noDts = /matroska|webm/.test(media.container);
  var plain = function (x) {
    return {
      index: x.index, type: x.type, codec: x.codec, codecString: x.codecString, profile: x.profile, level: x.level,
      width: x.width, height: x.height, channels: x.channels, sampleRate: x.sampleRate, language: x.language,
      title: x.title, isDefault: x.isDefault, forced: x.forced, tenBit: !!x.tenBit,
    };
  };
  return {
    container: media.container,
    duration: media.duration,
    startTime: media.startTime,
    chapters: chapters,
    video: video ? plain(video) : null,
    audio: media.audio.map(plain),
    subs: media.subs.map(plain),
  };
}

/* ───── الناتج (MP4 مجزّأ) ───── */
function Out() {
  this.parts = [];
  this.size = 0;
  this.pos = 0;
}
Out.prototype.write = function (pos, data) {
  // movenc مع empty_moov يكتب للأمام بس
  if (pos !== this.pos) log("non-sequential write", pos, this.pos);
  this.parts.push(data.slice());
  this.size += data.length;
  this.pos = pos + data.length;
};
Out.prototype.take = function () {
  if (!this.size) return null;
  var buf = new Uint8Array(this.size);
  var o = 0;
  for (var i = 0; i < this.parts.length; i++) {
    buf.set(this.parts[i], o);
    o += this.parts[i].length;
  }
  this.parts = [];
  this.size = 0;
  return buf;
};

/* ───── تحليل الكلام (للمزامنة) ─────
 * نفلتر الصوت لنطاق الكلام (300–3400Hz) ونحسب الطاقة لكل 50ms */
function Speech(rate) {
  this.rate = rate;
  this.win = Math.round(rate * DT);
  // مرشّحين biquad: تمرير عالي 300Hz وتمرير منخفض 3400Hz
  this.hp = biquad("hp", 300, rate);
  this.lp = biquad("lp", 3400, rate);
  this.idx = -1;
  this.acc = 0;
  this.n = 0;
  this.out = [];
  this.first = -1;
}
function biquad(kind, f, rate) {
  var w = (2 * Math.PI * f) / rate;
  var cos = Math.cos(w);
  var alpha = Math.sin(w) / (2 * Math.SQRT1_2);
  var b0, b1, b2;
  if (kind === "lp") {
    b0 = (1 - cos) / 2; b1 = 1 - cos; b2 = (1 - cos) / 2;
  } else {
    b0 = (1 + cos) / 2; b1 = -(1 + cos); b2 = (1 + cos) / 2;
  }
  var a0 = 1 + alpha;
  return { b0: b0 / a0, b1: b1 / a0, b2: b2 / a0, a1: (-2 * cos) / a0, a2: (1 - alpha) / a0, x1: 0, x2: 0, y1: 0, y2: 0 };
}
function run(f, x) {
  var y = f.b0 * x + f.b1 * f.x1 + f.b2 * f.x2 - f.a1 * f.y1 - f.a2 * f.y2;
  f.x2 = f.x1; f.x1 = x; f.y2 = f.y1; f.y1 = y;
  return y;
}
Speech.prototype.push = function (startSec, planes, count) {
  var L = planes[0];
  var R = planes.length > 1 ? planes[1] : planes[0];
  // نمشي بعدّاد عيّنات متصل (أوقات الإطارات متذبذبة شوي)، ونرجع لوقت الإطار بس لو فيه فجوة حقيقية
  var startSample = Math.round(startSec * this.rate);
  if (this.next === undefined || this.next === null || Math.abs(startSample - this.next) > this.rate * 0.15) this.next = startSample;
  var pos = this.next;
  this.next += count;
  var hp = this.hp, lp = this.lp;
  var hb0 = hp.b0, hb1 = hp.b1, hb2 = hp.b2, ha1 = hp.a1, ha2 = hp.a2;
  var lb0 = lp.b0, lb1 = lp.b1, lb2 = lp.b2, la1 = lp.a1, la2 = lp.a2;
  var hx1 = hp.x1, hx2 = hp.x2, hy1 = hp.y1, hy2 = hp.y2;
  var lx1 = lp.x1, lx2 = lp.x2, ly1 = lp.y1, ly2 = lp.y2;
  var win = this.win;
  var i = 0;
  while (i < count) {
    var idx = Math.floor((pos + i) / win);
    if (idx !== this.idx) {
      this.flush();
      this.idx = idx;
    }
    // كم عيّنة باقية في نفس الجزء الزمني
    var stop = Math.min(count, (idx + 1) * win - pos);
    var acc = 0;
    var from = i;
    for (; i < stop; i++) {
      var x = (L[i] + R[i]) * 0.5;
      var y = hb0 * x + hb1 * hx1 + hb2 * hx2 - ha1 * hy1 - ha2 * hy2;
      hx2 = hx1; hx1 = x; hy2 = hy1; hy1 = y;
      var z = lb0 * y + lb1 * lx1 + lb2 * lx2 - la1 * ly1 - la2 * ly2;
      lx2 = lx1; lx1 = y; ly2 = ly1; ly1 = z;
      acc += z * z;
    }
    this.acc += acc;
    this.n += i - from;
  }
  hp.x1 = hx1; hp.x2 = hx2; hp.y1 = hy1; hp.y2 = hy2;
  lp.x1 = lx1; lp.x2 = lx2; lp.y1 = ly1; lp.y2 = ly2;
};
Speech.prototype.flush = function () {
  if (this.idx >= 0 && this.n > this.win * 0.5) {
    if (this.first < 0 || this.idx !== this.first + this.out.length) {
      this.send();
      this.first = this.idx;
    }
    this.out.push(10 * Math.log10(this.acc / this.n + 1e-12));
  }
  this.acc = 0;
  this.n = 0;
};
Speech.prototype.send = function () {
  if (this.out.length) {
    var v = new Float32Array(this.out);
    post({ t: "speech", i0: this.first, v: v }, [v.buffer]);
  }
  this.out = [];
  this.first = -1;
};

/* ───── التشغيل ───── */

function tsSec(v, s) {
  return v === null ? null : (v * s.tbNum) / s.tbDen;
}

/** محوّل الصوت: يفك أي صوت ويرجّعه 48kHz (stereo أو 5.1) ويحوّله AAC لو مطلوب */
async function makeAudioChain(s, opt) {
  var ch = {};
  var codec = lib.avcodec_find_decoder_sync(s.codecId);
  if (!codec) throw new Error("no decoder for " + s.codec);
  var c = lib.avcodec_alloc_context3_sync(codec);
  lib.avcodec_parameters_to_context_sync(c, s.par);
  lib.shasha_set_pkt_timebase_sync(c, s.tbNum, s.tbDen);
  // نخفف الحمل: DTS-HD نفك الطبقة الأساسية بس، و TrueHD/AC3 ننزلها لعدد القنوات اللي نحتاجه
  if (s.codec === "dts") lib.av_opt_set_sync(c, "core_only", "1", 1);
  if (opt.channels === 2 && (s.codec === "truehd" || s.codec === "mlp" || s.codec === "ac3" || s.codec === "eac3"))
    lib.av_opt_set_sync(c, "downmix", "stereo", 1);
  // TrueHD 7.1/Atmos: نفك طبقة 5.1 بس (أخف بكثير)
  if (opt.channels === 6 && (s.codec === "truehd" || s.codec === "mlp")) lib.av_opt_set_sync(c, "downmix", "5.1(side)", 1);
  if (lib.avcodec_open2_sync(c, codec, 0) < 0) throw new Error("decoder open failed");
  ch.dec = c;
  ch.decPkt = lib.av_packet_alloc_sync();
  ch.decFrame = lib.av_frame_alloc_sync();
  ch.channels = opt.channels;
  ch.encode = opt.encode; // "aac" | "ac3" | null
  // AC3 (للتلفزيون) أسرع بكثير من AAC ويحافظ على 5.1 للسماعات
  ch.layout = opt.channels === 6 ? (opt.encode === "ac3" ? 0x60f : 0x3f) : 3;
  if (opt.encode) {
    var isAc3 = opt.encode === "ac3";
    var enc = await lib.ff_init_encoder(isAc3 ? "ac3" : "aac", {
      ctx: {
        bit_rate: isAc3 ? (opt.channels === 6 ? 640000 : 224000) : opt.channels === 6 ? 384000 : 192000,
        sample_fmt: AV_SAMPLE_FMT_FLTP,
        sample_rate: 48000,
        channel_layout: ch.layout,
        channels: opt.channels,
      },
      time_base: [1, 48000],
      options: isAc3 ? {} : { aac_coder: "fast" },
    });
    ch.enc = enc[1];
    ch.encFrame = enc[2];
    ch.encPkt = enc[3];
    ch.frameSize = enc[4] || 1024;
    ch.par = lib.avcodec_parameters_alloc_sync();
    lib.avcodec_parameters_from_context_sync(ch.par, ch.enc);
  }
  return ch;
}

async function initFilter(ch, frame, s) {
  var inLayout = frame.channel_layout || (frame.channels === 1 ? 4 : frame.channels === 2 ? 3 : 0);
  var g = await lib.ff_init_filter_graph(
    "aresample",
    {
      sample_rate: frame.sample_rate,
      sample_fmt: frame.format,
      channel_layout: inLayout,
      channels: frame.channels,
      time_base: [s.tbNum, s.tbDen],
    },
    {
      sample_rate: 48000,
      sample_fmt: AV_SAMPLE_FMT_FLTP,
      channel_layout: ch.layout,
      channels: ch.channels,
      frame_size: ch.encode ? ch.frameSize : 0,
      time_base: [1, 48000],
    }
  );
  ch.graph = g[0];
  ch.fsrc = g[1];
  ch.fsink = g[2];
  ch.inKey = frame.sample_rate + "/" + frame.format + "/" + inLayout + "/" + frame.channels;
}

function freeAudioChain(ch) {
  if (!ch) return;
  try {
    if (ch.graph) lib.avfilter_graph_free_js_sync(ch.graph);
    lib.ff_free_decoder_sync(ch.dec, ch.decPkt, ch.decFrame);
    if (ch.enc) lib.ff_free_encoder_sync(ch.enc, ch.encFrame, ch.encPkt);
    if (ch.par) lib.avcodec_parameters_free_js_sync(ch.par);
  } catch (e) { /* ignore */ }
}

/** يفك الصوت ويرجّع الإطارات (48kHz) + يحلل الكلام */
async function audioFrames(ss, packets, fin) {
  var ch = ss.chain;
  var frames = await lib.ff_decode_multi(ch.dec, ch.decPkt, ch.decFrame, packets, { fin: fin, ignoreErrors: true });
  if (!frames.length && !fin) return [];
  if (!ch.graph && frames.length) await initFilter(ch, frames[0], ss.audio);
  if (!ch.graph) return [];
  var out = await lib.ff_filter_multi(ch.fsrc, ch.fsink, ch.decFrame, frames, { fin: fin });
  if (ss.speech) {
    for (var i = 0; i < out.length; i++) {
      var f = out[i];
      var p = i64(f.pts, f.ptshi);
      if (p === null) continue;
      ss.speech.push(p / 48000 - media.startTime, f.data, f.nb_samples);
    }
  }
  return out;
}

function Session(msg) {
  this.sid = msg.sid;
  this.at = msg.at || 0;
  this.cancel = false;
  this.audio = msg.audio >= 0 ? media.streams[msg.audio] : null;
  this.audioMode = msg.audioMode; // "copy" | "aac" | "ac3" | "none"
  this.channels = msg.channels || 2;
  this.hevcTag = !!msg.hevcTag;
  this.subs = msg.subs !== false;
  this.ahead = msg.ahead > 0 ? msg.ahead : AHEAD;
  this.out = null;
  this.chain = null;
  this.speech = null;
  this.lastOut = 0; // آخر وقت (ثواني) طلع في الناتج
  this.lastVideoDts = null;
  this.aNext = null; // وقت إطار الصوت الجاي (بوحدة الناتج)
}

function setDiscard(ss) {
  for (var i = 0; i < media.streams.length; i++) {
    var s = media.streams[i];
    var keep = s === media.video || s === ss.audio || (ss.subs && s.type === "subtitle" && TEXT_SUBS[s.codec]);
    lib.AVStream_discard_s_sync(s.st, keep ? 0 : AVDISCARD_ALL);
  }
}

async function startMuxer(ss) {
  ss.out = new Out();
  try { lib.unlink_sync("out.mp4"); } catch (e) { /* ignore */ }
  await lib.mkwriterdev("out.mp4");
  var tracks = [];
  if (media.video) tracks.push([media.video.par, media.video.tbNum, media.video.tbDen]);
  if (ss.audio && ss.audioMode === "copy") tracks.push([ss.audio.par, ss.audio.tbNum, ss.audio.tbDen]);
  if (ss.audio && (ss.audioMode === "aac" || ss.audioMode === "ac3")) tracks.push([ss.chain.par, 1, 48000]);
  var m = lib.ff_init_muxer_sync({ format_name: "mp4", filename: "out.mp4", open: true, codecpars: true }, tracks);
  ss.oc = m[0];
  ss.pb = m[2];
  ss.ost = m[3];
  ss.vOut = media.video ? 0 : -1;
  ss.aOut = ss.audio && ss.audioMode !== "none" ? (media.video ? 1 : 0) : -1;
  if (media.video && media.video.codec === "hevc" && ss.hevcTag) {
    // MKTAG('h','v','c','1') عشان Safari والتلفزيونات
    lib.AVCodecParameters_codec_tag_s_sync(lib.AVStream_codecpar_sync(ss.ost[0]), 0x31637668);
  }
  // AC3/E-AC3 المنسوخ يحتاج معلومات من أول حزمة قبل رأس الملف (delay_moov)
  var flags = "frag_keyframe+empty_moov+default_base_moof+frag_discont";
  if (ss.audio && ((ss.audioMode === "copy" && (ss.audio.codec === "ac3" || ss.audio.codec === "eac3")) || ss.audioMode === "ac3")) flags += "+delay_moov";
  var d = lib.av_dict_set_js_sync(0, "movflags", flags, 0);
  d = lib.av_dict_set_js_sync(d, "frag_duration", "1000000", 0);
  d = lib.av_dict_set_js_sync(d, "avoid_negative_ts", "disabled", 0);
  // avformat_write_header تبي مؤشر لمؤشر القاموس
  var dp = lib.ff_malloc_int32_list_sync([d]);
  var r = lib.avformat_write_header_sync(ss.oc, dp);
  lib.free_sync(dp);
  if (r < 0) throw new Error("write header failed: " + lib.ff_error_sync(r));
  ss.tbOut = ss.ost.map(function (st) {
    return [lib.AVStream_time_base_num_sync(st), lib.AVStream_time_base_den_sync(st)];
  });
  lib.avio_flush_sync(ss.pb);
  var init = ss.out.take();
  if (init) post({ t: "media", sid: ss.sid, data: init, end: 0 }, [init.buffer]);
}

function writePacket(ss, outIndex, data, pts, dts, dur, flags, tbNum, tbDen) {
  var to = ss.tbOut[outIndex];
  var k = (tbNum * to[1]) / (tbDen * to[0]);
  var p = pts === null ? null : Math.round(pts * k);
  var d = dts === null ? p : Math.round(dts * k);
  var du = Math.round((dur || 0) * k);
  var pp = p === null ? [0, NOPTS_HI] : split64(p);
  var dd = d === null ? [0, NOPTS_HI] : split64(d);
  var uu = split64(du);
  lib.ff_copyin_packet_sync(inPkt, {
    data: data, pts: pp[0], ptshi: pp[1], dts: dd[0], dtshi: dd[1],
    duration: uu[0], durationhi: uu[1], stream_index: outIndex, flags: flags,
  });
  var r = lib.av_interleaved_write_frame_sync(ss.oc, inPkt);
  lib.av_packet_unref_sync(inPkt);
  if (r < 0) log("write error", outIndex, lib.ff_error_sync(r));
}

/**
 * الصوت: أوقات MKV بالملي ثانية فتجي متذبذبة (1008/1056 بدل 1024 عيّنة)، و Safari يرمي الأجزاء
 * اللي فيها تداخل. فنكتب أوقات متصلة بالضبط (كل إطار يبدأ لما يخلص اللي قبله)،
 * ونرجع لوقت الملف بس لو فيه فجوة حقيقية (أكثر من 150ms).
 */
function writeAudio(ss, data, pts, dur, flags, tbNum, tbDen) {
  var to = ss.tbOut[ss.aOut];
  var k = (tbNum * to[1]) / (tbDen * to[0]);
  var p = pts === null ? null : Math.round(pts * k);
  var d = Math.round((dur || 0) * k);
  var perSec = to[1] / to[0];
  // وحدة الوقت = عيّنة: نقرّب المدة لأقرب 256 (AAC = 1024، AC3 = 1536)
  if (to[0] === 1 && d > 0) d = Math.max(256, Math.round(d / 256) * 256);
  var exp = ss.aNext;
  if (p !== null && (exp === null || Math.abs(p - exp) > perSec * 0.15)) exp = p;
  if (exp === null) return;
  ss.aNext = exp + (d > 0 ? d : 0);
  // إطار التهيئة في AAC يجي قبل الصفر: ما نحتاجه
  if (exp < 0) return;
  var pp = split64(exp);
  var uu = split64(d);
  lib.ff_copyin_packet_sync(inPkt, {
    data: data, pts: pp[0], ptshi: pp[1], dts: pp[0], dtshi: pp[1],
    duration: uu[0], durationhi: uu[1], stream_index: ss.aOut, flags: flags,
  });
  var r = lib.av_interleaved_write_frame_sync(ss.oc, inPkt);
  lib.av_packet_unref_sync(inPkt);
  if (r < 0) log("audio write error", lib.ff_error_sync(r));
}

/**
 * الفيديو في MKV ما فيه DTS (وقت الفك): نحسبه من ترتيب الـ PTS (نفس فكرة FFmpeg).
 * نبدأ النافذة بقيم وهمية قبل أول إطار عشان الأوقات تطلع منتظمة من البداية.
 */
function videoDts(ss, pts) {
  var delay = ss.reorder;
  if (!ss.ptsBuf) {
    ss.ptsBuf = [];
    for (var i = delay; i >= 1; i--) ss.ptsBuf.push(pts - i * ss.frameDur);
  }
  var buf = ss.ptsBuf;
  buf.push(pts);
  buf.sort(function (a, b) { return a - b; });
  if (buf.length > delay + 1) buf.shift();
  var d = buf[0];
  if (d > pts) d = pts;
  if (ss.lastVideoDts !== null && d <= ss.lastVideoDts) d = ss.lastVideoDts + 1;
  ss.lastVideoDts = d;
  return d;
}

function sendSubs(ss, list) {
  if (!list.length) return;
  post({ t: "subs", sid: ss.sid, cues: list });
}

function subText(codec, bytes) {
  var text = new TextDecoder("utf-8").decode(bytes);
  if (codec === "ass" || codec === "ssa") {
    // ReadOrder,Layer,Style,Name,MarginL,MarginR,MarginV,Effect,Text
    var parts = text.split(",");
    if (parts.length >= 9) text = parts.slice(8).join(",");
  }
  return text;
}

async function runSession(ss) {
  var v = media.video;
  var a = ss.audio;
  // نقطة البداية: أقرب نقطة مفتاحية قبل المكان المطلوب
  var target = Math.max(0, ss.at + media.startTime);
  if (ss.at > 0.5 || session.readAny) {
    var us = Math.floor(target * 1e6);
    var t = split64(us);
    var r = await lib.avformat_seek_file_max(fmt, -1, t[0], t[1], 0);
    if (r < 0) {
      t = split64(0);
      await lib.avformat_seek_file_max(fmt, -1, t[0], t[1], 0);
    }
  }
  setDiscard(ss);
  var encoding = ss.audioMode === "aac" || ss.audioMode === "ac3";
  if (a && (encoding || wantSpeech)) {
    ss.chain = await makeAudioChain(a, { channels: ss.channels, encode: ss.audioMode === "aac" || ss.audioMode === "ac3" ? ss.audioMode : null });
    if (wantSpeech) ss.speech = new Speech(48000);
  }
  await startMuxer(ss);
  if (v) {
    ss.reorder = Math.max(v.delay || 0, 3);
    ss.frameDur = Math.max(1, Math.round(v.tbDen / (v.tbNum * (v.fps || 24))));
  }

  var audioQueue = [];
  var lastPost = Date.now();
  for (;;) {
    // نفسح المجال للرسائل (تقديم/تأخير ومكان التشغيل): بدون هذا الحلقة ممكن تحجزها لين تخلص
    await sleep(0);
    if (ss.cancel) break;
    // ما نسبق التشغيل بأكثر من AHEAD ثانية
    while (!ss.cancel && ss.lastOut - playhead > ss.ahead) await sleep(300);
    if (ss.cancel) break;
    // الجوال: لو جاهز قدّام ١٢ ثانية، نجهّز الباقي بهدوء (٦ أضعاف سرعة التشغيل بالكثير) بدل دفعة وحدة،
    // عشان الذاكرة المؤقتة ما تتكدّس مرة وحدة (Safari يقفل الصفحة لو كبرت فجأة)
    if (lowMemory && ss.lastOut - playhead > 12) {
      if (ss.paceT == null) { ss.paceT = Date.now(); ss.paceM = ss.lastOut; }
      while (!ss.cancel && ss.lastOut - ss.paceM > ((Date.now() - ss.paceT) / 1000) * 6 + 2) await sleep(100);
      if (ss.cancel) break;
    } else {
      ss.paceT = null;
    }
    // أول القراءات صغيرة عشان الصورة تطلع بسرعة، بعدها دفعات أكبر
    ss.reads = (ss.reads || 0) + 1;
    var res = await lib.ff_read_frame_multi(fmt, inPkt, { limit: ss.reads < 4 ? 256 * 1024 : 768 * 1024, unify: true });
    if (ss.cancel) break;
    session.readAny = true;
    var code = res[0];
    var pkts = res[1][0] || [];
    var cues = [];
    for (var i = 0; i < pkts.length; i++) {
      var p = pkts[i];
      var s = media.streams[p.stream_index];
      var pts = i64(p.pts, p.ptshi);
      var dts = i64(p.dts, p.dtshi);
      var dur = i64(p.duration, p.durationhi);
      if (s === v) {
        if (pts === null) pts = dts;
        if (pts === null) continue;
        // لو الملف ما فيه DTS نحسبه لكل الإطارات (ما نخلط بين المحسوب واللي من الملف)
        if (dts === null) media.noDts = true;
        if (media.noDts || (ss.lastVideoDts !== null && dts <= ss.lastVideoDts)) dts = videoDts(ss, pts);
        else ss.lastVideoDts = dts;
        writePacket(ss, ss.vOut, p.data, pts, dts, dur, p.flags, s.tbNum, s.tbDen);
        var sec = tsSec(pts, s) - media.startTime;
        if (sec > ss.lastOut) ss.lastOut = sec;
      } else if (s === a) {
        if (ss.audioMode === "copy") {
          writeAudio(ss, p.data, pts === null ? dts : pts, dur, p.flags, s.tbNum, s.tbDen);
          if (!v) {
            var as = tsSec(pts, s) - media.startTime;
            if (as > ss.lastOut) ss.lastOut = as;
          }
        }
        if (ss.chain) audioQueue.push(p);
      } else if (s && s.type === "subtitle") {
        if (pts === null) continue;
        var start = tsSec(pts, s) - media.startTime;
        cues.push({ stream: s.index, start: start, end: start + (dur ? (dur * s.tbNum) / s.tbDen : 3), text: subText(s.codec, p.data) });
      }
    }
    if (ss.cancel) break;
    if (ss.chain && (audioQueue.length || code === lib.AVERROR_EOF)) {
      var eof = code === lib.AVERROR_EOF;
      var frames = await audioFrames(ss, audioQueue, eof);
      audioQueue = [];
      if (encoding && (frames.length || eof)) {
        var enc = await lib.ff_encode_multi(ss.chain.enc, ss.chain.encFrame, ss.chain.encPkt, frames, eof);
        for (var e = 0; e < enc.length; e++) {
          var ep = enc[e];
          var epts = i64(ep.pts, ep.ptshi);
          var edts = i64(ep.dts, ep.dtshi);
          writeAudio(ss, ep.data, epts === null ? edts : epts, i64(ep.duration, ep.durationhi), ep.flags, 1, 48000);
        }
      }
    }
    sendSubs(ss, cues);
    if (code === lib.AVERROR_EOF) {
      lib.av_write_trailer_sync(ss.oc);
      lib.avio_flush_sync(ss.pb);
      flushOut(ss, true);
      if (ss.speech) {
        ss.speech.flush();
        ss.speech.send();
      }
      post({ t: "eos", sid: ss.sid });
      break;
    }
    if (code < 0 && code !== -lib.EAGAIN) throw new Error("read failed: " + lib.ff_error_sync(code));
    lib.avio_flush_sync(ss.pb);
    flushOut(ss, false);
    if (ss.speech && Date.now() - lastPost > 1500) {
      ss.speech.send();
      lastPost = Date.now();
    }
  }
}

function flushOut(ss, force) {
  var buf = ss.out.size >= 64 * 1024 || force ? ss.out.take() : null;
  if (buf) post({ t: "media", sid: ss.sid, data: buf, end: ss.lastOut }, [buf.buffer]);
}

function closeSession(ss) {
  if (!ss) return;
  try {
    if (ss.oc) lib.ff_free_muxer_sync(ss.oc, ss.pb);
  } catch (e) { /* ignore */ }
  freeAudioChain(ss.chain);
  ss.oc = 0;
  ss.chain = null;
}

var running = null;

async function play(msg) {
  if (session) {
    session.cancel = true;
    var prev = running;
    if (prev) await prev.catch(function () {});
    closeSession(session);
  }
  var readAny = session ? session.readAny : false;
  var ss = new Session(msg);
  ss.readAny = readAny;
  session = ss;
  playhead = ss.at;
  running = runSession(ss).catch(function (e) {
    if (ss.cancel) return;
    post({ t: "error", sid: ss.sid, msg: String((e && e.message) || e), stack: e && e.stack });
  });
}

self.onmessage = function (ev) {
  var m = ev.data;
  if (m.t === "pos") {
    playhead = m.time;
    return;
  }
  if (m.t === "speech") {
    wantSpeech = !!m.on;
    return;
  }
  queue = queue.then(async function () {
    try {
      if (m.t === "open") {
        wantSpeech = !!m.speech;
        lowMemory = !!m.lowMemory;
        var info = await openFile(m);
        post({ t: "info", info: info });
      } else if (m.t === "play") {
        await play(m);
      } else if (m.t === "close") {
        if (session) session.cancel = true;
        if (src) src.close();
        self.close();
      }
    } catch (e) {
      post({ t: "error", sid: m.sid, msg: String((e && e.message) || e), fatal: m.t === "open" });
    }
  });
};
