/* ================================================================
   KDPEasy PDF Assembler — app.js
   Single classic script, IIFE-wrapped. No modules, no fetch, no CDN:
   everything must run by double-clicking index.html over file://.
   The PDF container itself is written by pdf.js (window.KDPPdf).

   Much of this file is ported from KDPEasy Margin Fixer's app.js so the
   two tools can never disagree: the TRIM_SIZES table, EXIF handling,
   border analysis (Auto fill), Fit/Cover geometry, the stepped-downscale
   safeguard, the blur background, the crop-safety threshold and wording,
   the DPI quality bands, and the Before/After compare slider.
   ================================================================ */
(function () {
  'use strict';

  /* ---- 1. CONSTANTS & PRESETS ---- */

  var DPI = 300;
  var PT_PER_PX = 72 / DPI;          // PDF points per 300-DPI pixel
  var BLEED_IN = 0.125;              // KDP bleed, per bleeding edge
  var MIN_MARGIN_NO_BLEED = 0.25;    // KDP outside minimum, no bleed
  var MIN_MARGIN_BLEED = 0.375;      // KDP outside minimum, with bleed
  var VARIANCE_THRESHOLD = 900;      // ~30 std-dev per channel
  var NEAR_WHITE_CUTOFF = 250;       // per channel
  var WORK_LONG_EDGE = 1000;         // border-analysis working copy cap
  var PREVIEW_LONG_EDGE = 1400;      // preview render cap
  var THUMB_LONG_EDGE = 240;         // page-card thumbnail
  var KDP_MAX_BYTES = 650 * 1000 * 1000;   // KDP's 650 MB manuscript cap
  var SIZE_WARN_FRACTION = 0.85;           // meter turns amber from here
  var PAGE_OVERHEAD_BYTES = 600;           // page + content objects, xref line
  var KDP_MIN_PAGES = 24;

  // All 16 official KDP paperback trim sizes, in KDP's own order/groups.
  // COPIED VERBATIM from KDPEasy Margin Fixer's app.js — the two tools must
  // never disagree about what "8.5 x 11" means in pixels. If you edit this
  // list, make the same edit in Margin Fixer (and vice versa).
  var TRIM_SIZES = [
    { w: 5,    h: 8,     group: 'Standard' },
    { w: 5.06, h: 7.81,  group: 'Standard' },
    { w: 5.25, h: 8,     group: 'Standard' },
    { w: 5.5,  h: 8.5,   group: 'Standard' },
    { w: 6,    h: 9,     group: 'Standard' },
    { w: 6.14, h: 9.21,  group: 'Large' },
    { w: 6.69, h: 9.61,  group: 'Large' },
    { w: 7,    h: 10,    group: 'Large' },
    { w: 7.44, h: 9.69,  group: 'Large' },
    { w: 7.5,  h: 9.25,  group: 'Large' },
    { w: 8,    h: 10,    group: 'Large' },
    { w: 8.25, h: 6,     group: 'Large' },
    { w: 8.25, h: 8.25,  group: 'Large' },
    { w: 8.5,  h: 8.5,   group: 'Large' },
    { w: 8.5,  h: 11,    group: 'Large' },
    { w: 8.27, h: 11.69, group: 'Large', note: 'A4' }
  ];

  // KDP inside (gutter) margin by page count. Verified against
  // kdp.amazon.com/en_US/help/topic/GVBQ3CMEQW3W2VL6 on 2026-09-29.
  var GUTTER_TABLE = [
    { max: 150,      w: 0.375, label: 'for up to 150 pages' },
    { max: 300,      w: 0.5,   label: 'for 151–300 pages' },
    { max: 500,      w: 0.625, label: 'for 301–500 pages' },
    { max: 700,      w: 0.75,  label: 'for 501–700 pages' },
    { max: Infinity, w: 0.875, label: 'for 701–828 pages' }
  ];

  var FILL_HINTS = {
    auto:  'Looks at the edge of each image and chooses White, Solid, or Blur.',
    white: 'Clean white border. Best for line art and coloring pages.',
    solid: "Fills with the average color from each image's edge.",
    blur:  'Stretches and blurs your image behind itself. Best for full-color art.'
  };

  var JPEG_QUALITY = 0.92;           // Margin Fixer's default
  var FORMAT_HINTS = {
    png: 'Sharpest quality, best for line art. Files are larger.',
    jpg: 'Much smaller files (often 5–10× smaller), good for books with many pages. Print quality stays high.'
  };

  var BLEED_HINTS = {
    off: 'Your artwork sits inside the page with white space around it. This is what most coloring books use.',
    on:  'Your artwork runs off the edge of the page with no white border. Choose this only if your book is set up for bleed in KDP.'
  };

  var PLACEMENT_HINTS = {
    fit:  'Fit — never crops. Your whole image is kept, scaled to fit inside the safe area, with a padded border around it.',
    fill: 'Fill — fills the page, may crop. Your artwork covers the page edge-to-edge; a thin strip at the outer edge may be trimmed off. The dashed line in the preview shows what stays safe.'
  };

  var CROP_WARNING = 'Your image’s shape is quite different from this page’s shape, so Fill would crop into your artwork, not just the outer edge. Consider Fit for this page instead.';

  // Size estimate: each page is sampled once at import — three small tiles
  // of the real artwork, rendered at the scale(s) it will be printed at and
  // encoded with the real encoders — then interpolated for the actual
  // scale/quality, so the estimate follows every setting without
  // re-encoding anything.
  var PROBE_QUALITIES = [0.7, 0.85, 0.95, 1];
  var PROBE_TILE = 320;

  /* ---- 2. STATE ---- */

  var state = {
    trimIndex: -1,           // -1 = not chosen yet (Steps 2-4 locked)
    bleed: false,
    pageCountTyped: null,    // null = follow the number of uploaded pages
    gutter: true,
    firstPage: 1,            // page number of the first uploaded page (parity)
    placement: 'fit',        // book-level mode for pages that need resizing
    fill: 'auto',
    customSolidColor: null,
    format: 'png',
    jpegQuality: JPEG_QUALITY,
    items: [],
    nextId: 1,
    selectedId: null,
    dividerPct: 50,
    guides: true,
    building: false
  };

  /*
   * An item is one uploaded file:
   *   id, file, name, size
   *   status     'loading' | 'ready' | 'error'
   *   kind       'jpeg' | 'png'
   *   w, h       upright pixel size (after EXIF orientation)
   *   jpeg       KDPPdf.parseJpeg() result;  orientation  EXIF 1..8
   *   png        KDPPdf.parsePng() result
   *   embed      how an as-is page is embedded: 'jpeg' (byte-for-byte),
   *              'png' (IDAT pass-through) or 'pixels' (lossless repack)
   *   thumb      small canvas;  analysis  border analysis (Auto fill)
   *   probe      encoded-size samples for the size estimate
   *   placement  'default' | 'fit' | 'fill'  (per-page override)
   *   el         its card in the page grid
   */

  var el = {};
  var previewRaf = 0;
  var resizeDebounce = 0;
  var toastTimer = 0;
  var importQueue = [];
  var importing = false;
  var dragId = null;
  var preview = { id: null, canvas: null, pyramid: null, loading: null };

  /* -- small helpers -- */

  function $(id) { return document.getElementById(id); }

  function newCanvas(w, h) {
    var c = document.createElement('canvas');
    c.width = Math.max(1, Math.round(w));
    c.height = Math.max(1, Math.round(h));
    return c;
  }

  // Frees a big canvas's backing store right away instead of waiting for GC
  // — matters when a book has dozens of 3000-px pages.
  function releaseCanvas(c) {
    if (c && c.width) { c.width = 0; c.height = 0; }
  }

  function smooth(ctx) {
    ctx.imageSmoothingEnabled = true;
    if ('imageSmoothingQuality' in ctx) ctx.imageSmoothingQuality = 'high';
  }

  // Fill-white-first: every surface the image is drawn on starts white,
  // so transparent PNGs never carry alpha (or black) into analysis or export.
  function whiteCtx(canvas) {
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    smooth(ctx);
    return ctx;
  }

  // Inches, trailing zeros stripped: 8.5 -> "8.5", 11 -> "11", 5.06 -> "5.06"
  function fmtIn(n) { return String(parseFloat(n.toFixed(4))); }

  function trimLabelInches(t) { return fmtIn(t.w) + '" × ' + fmtIn(t.h) + '"'; }

  // Decimal MB, matching how KDP states its 650 MB limit.
  function fmtMB(b) {
    var mb = b / 1e6;
    return (mb < 10 ? mb.toFixed(1) : String(Math.round(mb))) + ' MB';
  }

  function fmtFileSize(b) {
    return b < 1e6 ? Math.max(1, Math.round(b / 1000)) + ' KB' : (b / 1e6).toFixed(1) + ' MB';
  }

  function toHex(n) {
    var s = Math.max(0, Math.min(255, Math.round(n))).toString(16);
    return s.length === 1 ? '0' + s : s;
  }

  function plural(n, one, many) { return n + ' ' + (n === 1 ? one : (many || one + 's')); }

  function nextFrame() {
    return new Promise(function (resolve) {
      requestAnimationFrame(function () { setTimeout(resolve, 0); });
    });
  }

  function toBlobP(canvas, type, quality) {
    return new Promise(function (resolve, reject) {
      canvas.toBlob(function (b) { if (b) resolve(b); else reject(new Error('encode')); }, type, quality);
    });
  }

  function readBuffer(file) {
    if (file.arrayBuffer) return file.arrayBuffer();
    return new Promise(function (resolve, reject) {
      var r = new FileReader();
      r.onload = function () { resolve(r.result); };
      r.onerror = function () { reject(r.error); };
      r.readAsArrayBuffer(file);
    });
  }

  /* ---- 3. EXIF ORIENTATION (ported from Margin Fixer) ---- */

  // Minimal EXIF reader: finds tag 0x0112 (Orientation) in IFD0. Returns 1..8,
  // defaulting to 1 for PNGs, EXIF-less JPEGs and anything unparseable.
  function readOrientation(buf) {
    var view = new DataView(buf);
    var len = view.byteLength;
    if (len < 4 || view.getUint16(0, false) !== 0xFFD8) return 1;   // not a JPEG

    var offset = 2;
    while (offset + 4 <= len) {
      var marker = view.getUint16(offset, false);
      if ((marker & 0xFF00) !== 0xFF00) break;
      if (marker === 0xFFD8 || (marker >= 0xFFD0 && marker <= 0xFFD9)) { offset += 2; continue; }
      offset += 2;
      var size = view.getUint16(offset, false);
      if (marker === 0xFFE1) {
        if (offset + 10 > len) break;
        if (view.getUint32(offset + 2, false) !== 0x45786966) {      // "Exif"
          offset += size; continue;
        }
        var tiff = offset + 8;                                       // skip "Exif\0\0"
        if (tiff + 8 > len) return 1;
        var little = view.getUint16(tiff, false) === 0x4949;         // "II" / "MM"
        var dir = tiff + view.getUint32(tiff + 4, little);
        if (dir + 2 > len) return 1;
        var count = view.getUint16(dir, little);
        for (var i = 0; i < count; i++) {
          var entry = dir + 2 + i * 12;
          if (entry + 12 > len) break;
          if (view.getUint16(entry, little) === 0x0112) {
            var v = view.getUint16(entry + 8, little);
            return (v >= 1 && v <= 8) ? v : 1;
          }
        }
        return 1;
      }
      if (marker === 0xFFDA) break;                                  // start of scan
      offset += size;
    }
    return 1;
  }

  // Produces the upright source canvas. For 5-8 width/height are swapped.
  function applyOrientation(img, w, h, o) {
    var swap = (o >= 5 && o <= 8);
    var canvas = newCanvas(swap ? h : w, swap ? w : h);
    var ctx = whiteCtx(canvas);
    switch (o) {
      case 2: ctx.transform(-1, 0, 0, 1, w, 0); break;               // flip horizontal
      case 3: ctx.transform(-1, 0, 0, -1, w, h); break;              // rotate 180
      case 4: ctx.transform(1, 0, 0, -1, 0, h); break;               // flip vertical
      case 5: ctx.transform(0, 1, 1, 0, 0, 0); break;                // transpose
      case 6: ctx.transform(0, 1, -1, 0, h, 0); break;               // rotate 90 CW
      case 7: ctx.transform(0, -1, -1, 0, h, w); break;              // transverse
      case 8: ctx.transform(0, -1, 1, 0, 0, w); break;               // rotate 270 CW
      default: break;                                                // 1: none
    }
    ctx.drawImage(img, 0, 0, w, h);
    return canvas;
  }

  /* ---- 4. IMAGE DECODING (ported from Margin Fixer) ---- */

  // A 2x1 JPEG carrying EXIF Orientation=6 (rotate 90 CW). A browser that
  // applies EXIF by itself reads it back as 1x2. We probe ONCE so that we
  //  - never rotate an image the browser has already rotated (double rotation), and
  //  - never trust an `imageOrientation` option an old Safari silently ignores.
  var PROBE_JPEG = '/9j/4AAQSkZJRgABAQAAAQABAAD/4QAiRXhpZgAATU0AKgAAAAgAAQESAAMAAAABAAYAAAAAAAD/2wBDAAMCAgMCAgMDAwMEAwMEBQgFBQQEBQoHBwYIDAoMDAsKCwsNDhIQDQ4RDgsLEBYQERMUFRUVDA8XGBYUGBIUFRT/2wBDAQMEBAUEBQkFBQkUDQsNFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBT/wAARCAABAAIDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwD50ooor8MP9Uz/2Q==';
  var orientProbe = null;

  function probeOrientationSupport() {
    if (orientProbe) return orientProbe;
    orientProbe = new Promise(function (resolve) {
      // Safe defaults if the probe cannot run: modern browsers auto-rotate <img>.
      var result = { imgAuto: true, bitmapOk: typeof createImageBitmap === 'function' };
      var settled = false;
      function finish() { if (!settled) { settled = true; resolve(result); } }
      setTimeout(finish, 1500);
      try {
        var bin = atob(PROBE_JPEG), bytes = new Uint8Array(bin.length);
        for (var i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
        var blob = new Blob([bytes], { type: 'image/jpeg' });
        var img = new Image();
        img.onload = function () {
          result.imgAuto = img.naturalWidth < img.naturalHeight;
          if (typeof createImageBitmap !== 'function') { result.bitmapOk = false; finish(); return; }
          try {
            createImageBitmap(blob, { imageOrientation: 'from-image' }).then(function (bm) {
              result.bitmapOk = bm.width < bm.height;
              if (bm.close) bm.close();
              finish();
            }, function () { result.bitmapOk = false; finish(); });
          } catch (e) { result.bitmapOk = false; finish(); }
        };
        img.onerror = finish;
        img.src = 'data:image/jpeg;base64,' + PROBE_JPEG;
      } catch (e) { finish(); }
    });
    return orientProbe;
  }

  // Primary path: createImageBitmap with orientation handling (only if the
  // probe proved the browser honours it). Fallback: decode via <img> and, only
  // if the browser does not auto-rotate, apply EXIF by hand.
  // `raw` asks for the file's own sample values (no color-profile conversion,
  // no premultiplied alpha) — used for the lossless as-is repack.
  function decodeUpright(file, raw) {
    return probeOrientationSupport().then(function (sup) {
      return new Promise(function (resolve, reject) {
        if (sup.bitmapOk) {
          var p, opts = { imageOrientation: 'from-image' };
          if (raw) { opts.colorSpaceConversion = 'none'; opts.premultiplyAlpha = 'none'; }
          try {
            p = createImageBitmap(file, opts);
          } catch (e) {
            p = null;
          }
          if (p && typeof p.then === 'function') {
            p.then(function (bitmap) {
              var c = newCanvas(bitmap.width, bitmap.height);
              whiteCtx(c).drawImage(bitmap, 0, 0);
              if (bitmap.close) bitmap.close();
              resolve(c);
            }).catch(function () { decodeFallback(file, sup).then(resolve, reject); });
            return;
          }
        }
        decodeFallback(file, sup).then(resolve, reject);
      });
    });
  }

  function decodeFallback(file, sup) {
    // Browser already rotated the <img> -> treat as orientation 1 (no double rotation).
    var orientationP = (sup && sup.imgAuto) ? Promise.resolve(1) : readOrientationFromFile(file);
    return orientationP.then(function (orientation) {
      return new Promise(function (resolve, reject) {
        var url = URL.createObjectURL(file);
        var img = new Image();
        img.onload = function () {
          try {
            resolve(applyOrientation(img, img.naturalWidth, img.naturalHeight, orientation));
          } catch (e) {
            reject(e);
          } finally {
            URL.revokeObjectURL(url);
          }
        };
        img.onerror = function () { URL.revokeObjectURL(url); reject(new Error('decode')); };
        img.src = url;
      });
    });
  }

  function readOrientationFromFile(file) {
    return new Promise(function (resolve) {
      if (file.type !== 'image/jpeg' && !/\.jpe?g$/i.test(file.name || '')) { resolve(1); return; }
      var slice = file.slice(0, 128 * 1024);
      var reader = new FileReader();
      reader.onload = function () {
        var o = 1;
        try { o = readOrientation(reader.result); } catch (e) { o = 1; }
        resolve(o);
      };
      reader.onerror = function () { resolve(1); };
      reader.readAsArrayBuffer(slice);
    });
  }

  /* ---- 5. BORDER ANALYSIS (ported from Margin Fixer) ---- */

  // Runs on the downscaled working copy. Result is cached per page.
  function analyzeBorder(work) {
    var w = work.width, h = work.height;
    var data;
    try {
      data = work.getContext('2d').getImageData(0, 0, w, h).data;
    } catch (e) {
      return { variance: 0, r: 255, g: 255, b: 255, decision: 'white', color: '#ffffff' };
    }

    var band = Math.max(1, Math.round(Math.min(w, h) / 50));
    var sum = [0, 0, 0], sumSq = [0, 0, 0], n = 0;

    function take(x, y) {
      var i = (y * w + x) * 4;
      for (var c = 0; c < 3; c++) {
        var v = data[i + c];
        sum[c] += v;
        sumSq[c] += v * v;
      }
      n++;
    }

    // Simple non-deduped ring walk: corner pixels fall in two strips and are
    // counted twice. That does not materially change a mean/variance of a
    // border band, and keeps this loop trivial to read.
    var x, y;
    for (y = 0; y < band && y < h; y++) for (x = 0; x < w; x++) take(x, y);                 // top
    for (y = Math.max(0, h - band); y < h; y++) for (x = 0; x < w; x++) take(x, y);         // bottom
    for (x = 0; x < band && x < w; x++) for (y = 0; y < h; y++) take(x, y);                 // left
    for (x = Math.max(0, w - band); x < w; x++) for (y = 0; y < h; y++) take(x, y);         // right

    if (!n) n = 1;
    var mean = [sum[0] / n, sum[1] / n, sum[2] / n];
    var varc = [
      (sumSq[0] / n) - mean[0] * mean[0],
      (sumSq[1] / n) - mean[1] * mean[1],
      (sumSq[2] / n) - mean[2] * mean[2]
    ];
    var variance = (varc[0] + varc[1] + varc[2]) / 3;

    var decision;
    if (variance < VARIANCE_THRESHOLD) {
      decision = (mean[0] >= NEAR_WHITE_CUTOFF &&
                  mean[1] >= NEAR_WHITE_CUTOFF &&
                  mean[2] >= NEAR_WHITE_CUTOFF) ? 'white' : 'solid';
    } else {
      decision = 'blur';
    }

    return {
      variance: variance,
      r: mean[0], g: mean[1], b: mean[2],
      decision: decision,
      color: '#' + toHex(mean[0]) + toHex(mean[1]) + toHex(mean[2])
    };
  }

  // The fill mode actually used for a page (resolves 'auto' per page).
  function effectiveFill(item) {
    if (state.fill !== 'auto') return state.fill;
    return item.analysis ? item.analysis.decision : 'white';
  }

  // Snap-to-white: a near-white border prints as a faint visible rectangle
  // on an otherwise pure-white page.
  function solidColor(item) {
    if (state.customSolidColor) return state.customSolidColor;
    var a = item && item.analysis;
    if (!a) return '#ffffff';
    if (a.r >= NEAR_WHITE_CUTOFF && a.g >= NEAR_WHITE_CUTOFF && a.b >= NEAR_WHITE_CUTOFF) {
      return '#ffffff';
    }
    return a.color;
  }

  /* ---- 6. BOOK & PAGE GEOMETRY ---- */

  function pageItems() {
    return state.items.filter(function (it) { return it.status !== 'error'; });
  }

  function bookPageCount() {
    return state.pageCountTyped !== null ? state.pageCountTyped : pageItems().length;
  }

  function gutterBand() {
    var n = Math.max(1, bookPageCount());
    for (var i = 0; i < GUTTER_TABLE.length; i++) if (n <= GUTTER_TABLE[i].max) return GUTTER_TABLE[i];
    return GUTTER_TABLE[GUTTER_TABLE.length - 1];
  }

  function gutterInches() { return state.gutter ? gutterBand().w : 0; }

  // Odd page numbers are right-hand (recto) pages: spine on their LEFT.
  function spineLeftAt(pageIndex) { return (state.firstPage + pageIndex) % 2 === 1; }

  /*
   * The book's fixed numbers.
   *  - The CANVAS is Margin Fixer's canvas: trim + 0.125" bleed on all four
   *    sides (symmetric), a whole number of pixels at 300 DPI.
   *  - The PDF PAGE is KDP's official size: bleed only on the outside edge,
   *    top and bottom — trim + 0.125" wide, trim + 0.25" tall. The extra
   *    0.125" of canvas on the spine side hangs off the page (§6.4): the
   *    bitmap stays whole, only the visible area is set to KDP's size.
   */
  function book() {
    var t = TRIM_SIZES[state.trimIndex];
    var B = state.bleed ? BLEED_IN : 0;
    return {
      trim: t,
      B: B,
      fullW: Math.round((t.w + B * 2) * DPI),
      fullH: Math.round((t.h + B * 2) * DPI),
      pageWin: t.w + B,
      pageHin: t.h + B * 2,
      pageWpt: (t.w + B) * 72,
      pageHpt: (t.h + B * 2) * 72
    };
  }

  function itemMatches(item, b) {
    return item.status === 'ready' && item.w === b.fullW && item.h === b.fullH;
  }

  // 'asis' | 'fit' | 'fill' — how this page will actually be built.
  function effectiveMode(item, b) {
    if (item.placement === 'fit' || item.placement === 'fill') return item.placement;
    return itemMatches(item, b) ? 'asis' : state.placement;
  }

  /*
   * ONE geometry function, used by the preview, the status badges, the size
   * estimate and the export — so none of them can ever disagree. All rects
   * are in full-resolution canvas pixels; callers scale them.
   *
   * Gutter (§6.5): the PDF page is never made wider than KDP's official size
   * (KDP rejects a page that doesn't match the trim size). Instead the
   * gutter is a keep-clear strip on the spine side of the page: Fit places
   * artwork beside it, Fill covers everything except it.
   */
  function computeGeometry(item, spineLeft) {
    var b = book();
    var bPx = b.B * DPI;
    var mPx = (state.bleed ? MIN_MARGIN_BLEED : MIN_MARGIN_NO_BLEED) * DPI;
    var gPx = gutterInches() * DPI;
    var insidePx = gPx > 0 ? gPx : mPx;
    var trimW = b.trim.w * DPI, trimH = b.trim.h * DPI;
    var leftM = spineLeft ? insidePx : mPx;
    var rightM = spineLeft ? mPx : insidePx;

    var geo = {
      book: b,
      fullW: b.fullW, fullH: b.fullH,
      spineLeft: spineLeft,
      bPx: bPx, mPx: mPx, gPx: gPx,
      trim: { x: bPx, y: bPx, w: trimW, h: trimH },
      safe: {
        x: bPx + leftM, y: bPx + mPx,
        w: Math.max(1, trimW - leftM - rightM),
        h: Math.max(1, trimH - mPx * 2)
      },
      // what KDP will see: the canvas minus the spine-side bleed
      visible: { x: spineLeft ? bPx : 0, y: 0, w: b.fullW - bPx, h: b.fullH },
      gutter: gPx > 0
        ? { x: spineLeft ? bPx : bPx + trimW - gPx, y: 0, w: gPx, h: b.fullH }
        : null,
      blurRadius: Math.max(1, Math.round(0.03 * Math.max(b.fullW, b.fullH)))
    };

    // Fill covers the whole canvas (like Margin Fixer's Cover), minus the
    // gutter strip and anything beyond it on the spine side.
    geo.area = !geo.gutter
      ? { x: 0, y: 0, w: b.fullW, h: b.fullH }
      : spineLeft
        ? { x: bPx + gPx, y: 0, w: b.fullW - bPx - gPx, h: b.fullH }
        : { x: 0, y: 0, w: bPx + trimW - gPx, h: b.fullH };

    if (item && item.w) {
      var imgW = item.w, imgH = item.h;
      // Fit, never fill: never cropped, never distorted. Not clamped to 1 —
      // an undersized source is scaled up and the DPI readout says so.
      var fit = Math.min(geo.safe.w / imgW, geo.safe.h / imgH);
      var pw = imgW * fit, ph = imgH * fit;
      geo.fitScale = fit;
      geo.placed = {
        x: geo.safe.x + (geo.safe.w - pw) / 2,
        y: geo.safe.y + (geo.safe.h - ph) / 2,
        w: pw, h: ph
      };

      var a = geo.area;
      var cover = Math.max(a.w / imgW, a.h / imgH);
      var cw = imgW * cover, ch = imgH * cover;
      geo.coverScale = cover;
      geo.coverPlaced = { x: a.x + (a.w - cw) / 2, y: a.y + (a.h - ch) / 2, w: cw, h: ch };

      // Margin Fixer's crop-safety rule: only the ring outside the safe area
      // (bleed + margin) is meant to be sacrificed.
      var cropX = Math.max(0, (cw - a.w) / 2);
      var cropY = Math.max(0, (ch - a.h) / 2);
      var ring = bPx + mPx;
      geo.cropTooMuch = cropX > ring + 1 || cropY > ring + 1;

      geo.dpiFit = DPI / fit;
      geo.dpiFill = DPI / cover;
    }
    return geo;
  }

  function scaleRect(r, s, offX) {
    return { x: (r.x - (offX || 0)) * s, y: r.y * s, w: r.w * s, h: r.h * s };
  }

  function modeDPI(mode, geo) {
    if (mode === 'asis') return DPI;
    return mode === 'fill' ? geo.dpiFill : geo.dpiFit;
  }

  /* ---- 7. RENDERING (ported from Margin Fixer) ---- */

  function supportsFilter(ctx) {
    if (typeof ctx.filter !== 'string') return false;
    ctx.filter = 'blur(2px)';
    var ok = ctx.filter !== 'none' && ctx.filter !== '';
    ctx.filter = 'none';
    return ok;
  }

  // Stepped downscale: a single big drawImage aliases line art badly, and
  // aliasing is exactly what this tool's audience would notice first.
  // `pyramid` is a per-source array of halved levels, [source, 1/2, 1/4, ...].
  function halfStep(pyramid, dw) {
    if (!(dw > 0)) return pyramid[0];
    var i = 0;
    while (pyramid[i].width > 1 && pyramid[i].width / 2 > dw) {
      if (!pyramid[i + 1]) {
        var prev = pyramid[i];
        var nw = Math.max(1, Math.floor(prev.width / 2));
        var nh = Math.max(1, Math.floor(prev.height / 2));
        var step = newCanvas(nw, nh);
        whiteCtx(step).drawImage(prev, 0, 0, nw, nh);
        pyramid[i + 1] = step;
      }
      i++;
    }
    return pyramid[i];
  }

  function releasePyramid(pyramid) {
    if (pyramid) pyramid.forEach(releaseCanvas);
  }

  function drawArtwork(ctx, pyramid, dx, dy, dw, dh) {
    smooth(ctx);
    ctx.drawImage(halfStep(pyramid, dw), dx, dy, dw, dh);
  }

  // Stepped downscale to a small copy (working copy, thumbnail).
  function shrinkTo(src, longEdge) {
    var s = Math.min(1, longEdge / Math.max(src.width, src.height));
    var w = Math.max(1, Math.round(src.width * s));
    var h = Math.max(1, Math.round(src.height * s));
    var pyr = [src];
    var out = newCanvas(w, h);
    whiteCtx(out).drawImage(halfStep(pyr, w), 0, 0, w, h);
    for (var i = 1; i < pyr.length; i++) releaseCanvas(pyr[i]);
    return out;
  }

  // The blurred layer is a SECOND, cover-scaled copy used only as
  // background. It is cropped; the sharp copy the reader sees never is.
  function drawBlurBackground(ctx, src, w, h, r) {
    var pad = r * 2;                          // real pixels past every edge, so a
    var tw = w + pad * 2;                     // canvas blur at the rim has something
    var th = h + pad * 2;                     // to sample and does not fade/darken
    var tmp = newCanvas(tw, th);
    var tctx = whiteCtx(tmp);

    var cover = Math.max(tmp.width / src.width, tmp.height / src.height);
    var dw = src.width * cover, dh = src.height * cover;
    tctx.drawImage(src, (tmp.width - dw) / 2, (tmp.height - dh) / 2, dw, dh);

    if (r >= 1 && supportsFilter(ctx)) {
      ctx.filter = 'blur(' + r + 'px)';
      ctx.drawImage(tmp, -pad, -pad);
      ctx.filter = 'none';
      releaseCanvas(tmp);
      return;
    }

    // Fallback (old Safari): downscale-then-upscale, twice.
    var shrink = Math.max(1, Math.round(r / 2));
    var sw = Math.max(1, Math.round(tmp.width / shrink));
    var sh = Math.max(1, Math.round(tmp.height / shrink));
    var cur = tmp;
    for (var i = 0; i < 2; i++) {
      var small = newCanvas(sw, sh);
      whiteCtx(small).drawImage(cur, 0, 0, sw, sh);
      var big = newCanvas(tmp.width, tmp.height);
      whiteCtx(big).drawImage(small, 0, 0, tmp.width, tmp.height);
      releaseCanvas(small);
      if (cur !== tmp) releaseCanvas(cur);
      cur = big;
    }
    ctx.drawImage(cur, -pad, -pad);
    releaseCanvas(cur);
    releaseCanvas(tmp);
  }

  // Composes one page at scale `s`. `offX` (canvas px) shifts the drawing
  // left so a preview can show only the visible part of the canvas; the
  // export always renders the full canvas (offX = 0). Guides are never
  // drawn here — see drawGuides().
  function renderPage(ctx, item, pyramid, geo, s, mode, offX) {
    var W = geo.fullW * s, H = geo.fullH * s;
    ctx.save();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.filter = 'none';
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, ctx.canvas.width, ctx.canvas.height);
    ctx.translate(-(offX || 0) * s, 0);
    smooth(ctx);

    if (mode === 'asis') {
      drawArtwork(ctx, pyramid, 0, 0, W, H);
      ctx.restore();
      return;
    }

    // Background: the Fit padding, and the gutter strip in Fill mode.
    // Fill without a gutter covers 100% of the canvas — nothing to fill.
    if (mode === 'fit' || geo.gutter) {
      var fm = effectiveFill(item);
      if (fm === 'solid') {
        ctx.fillStyle = solidColor(item);
        ctx.fillRect(0, 0, W, H);
      } else if (fm === 'blur') {
        drawBlurBackground(ctx, pyramid[0], W, H, Math.max(1, Math.round(geo.blurRadius * s)));
      }
    }

    if (mode === 'fit') {
      var p = scaleRect(geo.placed, s);
      drawArtwork(ctx, pyramid, p.x, p.y, p.w, p.h);
    } else {
      var a = scaleRect(geo.area, s), c = scaleRect(geo.coverPlaced, s);
      ctx.save();
      ctx.beginPath();
      ctx.rect(a.x, a.y, a.w, a.h);
      ctx.clip();
      drawArtwork(ctx, pyramid, c.x, c.y, c.w, c.h);
      ctx.restore();
    }
    ctx.restore();
  }

  /* ---- 8. IMPORT PIPELINE ---- */

  function isSupportedType(file) {
    if (file.type === 'image/png' || file.type === 'image/jpeg') return true;
    return /\.(png|jpe?g)$/i.test(file.name || '');
  }

  function handleFiles(list) {
    if (!list || !list.length) return;
    if (state.trimIndex < 0) {
      showBanner("Choose your book's trim size first (Step 1) — then add your pages.");
      return;
    }
    var files = Array.prototype.slice.call(list);
    files.forEach(function (file) {
      var item = {
        id: state.nextId++, file: file, name: file.name || 'image', size: file.size,
        status: 'loading', placement: 'default'
      };
      state.items.push(item);
      if (isSupportedType(file)) {
        importQueue.push(item);
      } else {
        item.status = 'error';
        item.errorMsg = "Not a PNG or JPG — this file will be skipped.";
      }
    });
    el.bannerHost.innerHTML = '';
    refresh();
    pumpImport();
  }

  function pumpImport() {
    if (importing) return;
    var item = importQueue.shift();
    if (!item) { refresh(); return; }
    if (state.items.indexOf(item) < 0) { pumpImport(); return; }   // removed while queued
    importing = true;
    loadItem(item).then(function () {
      item.status = 'ready';
    }, function () {
      item.status = 'error';
      item.errorMsg = "We couldn't open this image. It may be damaged — try re-saving it. It will be skipped.";
    }).then(function () {
      importing = false;
      if (!state.selectedId && item.status === 'ready' && state.items.indexOf(item) >= 0) {
        state.selectedId = item.id;
      }
      refresh();
      // yield a frame so the grid paints between pages
      requestAnimationFrame(pumpImport);
    });
  }

  function loadItem(item) {
    var work = null, pyramid = null;
    return readBuffer(item.file).then(function (buf) {
      var bytes = new Uint8Array(buf);
      var jp = KDPPdf.parseJpeg(bytes);
      var pn = jp ? null : KDPPdf.parsePng(bytes);
      if (!jp && !pn) throw new Error('type');
      if (jp) {
        item.kind = 'jpeg';
        item.jpeg = jp;
        var o = 1;
        try { o = readOrientation(buf); } catch (e) { o = 1; }
        item.orientation = o;
      } else {
        item.kind = 'png';
        item.png = pn;
        item.orientation = 1;
      }
      return decodeUpright(item.file);
    }).then(function (canvas) {
      item.w = canvas.width;
      item.h = canvas.height;

      // How the page would be embedded if it's used as-is. Pass-through is
      // only trusted when the header agrees with what the browser decoded.
      if (item.kind === 'jpeg') {
        var j = item.jpeg, swap = item.orientation >= 5;
        var sameSize = swap ? (j.height === item.w && j.width === item.h)
                            : (j.width === item.w && j.height === item.h);
        item.embed = (j.supported && sameSize) ? 'jpeg' : 'pixels';
      } else {
        var p = item.png;
        item.embed = (p.passthrough && p.width === item.w && p.height === item.h) ? 'png' : 'pixels';
      }

      pyramid = [canvas];
      var ws = Math.min(1, WORK_LONG_EDGE / Math.max(item.w, item.h));
      work = newCanvas(item.w * ws, item.h * ws);
      whiteCtx(work).drawImage(halfStep(pyramid, work.width), 0, 0, work.width, work.height);
      item.analysis = analyzeBorder(work);
      item.thumb = shrinkTo(work, THUMB_LONG_EDGE);
      releaseCanvas(work);
      return probeSizes(pyramid, probeScalesFor(item));
    }).then(function (probe) {
      item.probe = probe;
      releasePyramid(pyramid);
    }, function (err) {
      releaseCanvas(work);
      releasePyramid(pyramid);
      throw err;
    });
  }

  // The book size is chosen before upload, so we already know the scales
  // this page will be drawn at (Fit and Fill). Probe just those — one or two
  // probes instead of a fixed ladder. If the book size changes later, the
  // estimate interpolates/extrapolates from them.
  function probeScalesFor(item) {
    if (state.trimIndex < 0) return [1];
    var g = computeGeometry(item, true);
    var a = Math.min(g.fitScale, g.coverScale), b = Math.max(g.fitScale, g.coverScale);
    return b / a < 1.15 ? [Math.sqrt(a * b)] : [a, b];
  }

  // Renders three tiles of the artwork (along the diagonal) at each probe
  // scale, exactly as the export would draw them, and records bytes per
  // output pixel for PNG (our own lossless packer) and for JPG at each probe
  // quality. Returns null if probing fails — the estimate then falls back
  // to rough defaults.
  function probeSizes(pyramid, scales) {
    var src = pyramid[0], W = src.width, H = src.height;
    var probe = { scales: scales, png: [], jpg: [] };
    var chain = Promise.resolve();
    scales.forEach(function (f, si) {
      chain = chain.then(function () {
        var t = Math.max(8, Math.min(PROBE_TILE, Math.floor(Math.min(W, H) * f)));
        var region = t / f;                                   // source px per tile edge
        var level = halfStep(pyramid, W * f);
        var ls = level.width / W;
        var strip = newCanvas(t * 3, t);
        var ctx = whiteCtx(strip);
        [0.3, 0.5, 0.7].forEach(function (c, k) {
          var sx = Math.max(0, Math.min(W - region, c * W - region / 2));
          var sy = Math.max(0, Math.min(H - region, c * H - region / 2));
          ctx.drawImage(level, sx * ls, sy * ls, region * ls, region * ls, k * t, 0, t, t);
        });
        var px = strip.width * strip.height;
        var rgba = ctx.getImageData(0, 0, strip.width, strip.height).data;
        probe.jpg[si] = [];
        var c2 = KDPPdf.packPixels(rgba, strip.width, strip.height).then(function (r) {
          probe.png[si] = r.blob.size / px;
        });
        PROBE_QUALITIES.forEach(function (q, qi) {
          c2 = c2.then(function () { return toBlobP(strip, 'image/jpeg', q); })
                 .then(function (b) { probe.jpg[si][qi] = b.size / px; });
        });
        return c2.then(function () { releaseCanvas(strip); });
      });
    });
    return chain.then(function () { return probe; }, function () { return null; });
  }

  /* ---- 9. STATUS & SIZE ESTIMATE ---- */

  // Measured bytes per output pixel at probe scale index `si`, for the
  // current format (JPG interpolated across the probed qualities).
  function probeBpp(p, si) {
    if (state.format === 'png') return p.png[si];
    var q = state.jpegQuality, qs = PROBE_QUALITIES, js = p.jpg[si];
    if (q <= qs[0]) return js[0];
    for (var i = 1; i < qs.length; i++) {
      if (q <= qs[i]) return js[i - 1] + (js[i] - js[i - 1]) * (q - qs[i - 1]) / (qs[i] - qs[i - 1]);
    }
    return js[js.length - 1];
  }

  // Bytes per output pixel when the artwork is drawn at scale `f`. With one
  // probe that's the answer; with two, linear in log-log space between them,
  // extrapolated past them (clamped to a sane band).
  function bytesPerPixel(item, f) {
    var p = item.probe;
    if (!p) return state.format === 'png' ? 1.5 : 0.4;
    var n = p.scales.length;
    var ys = p.scales.map(function (s, i) { return Math.log(Math.max(1e-4, probeBpp(p, i))); });
    if (n === 1) return Math.exp(ys[0]);
    var x0 = Math.log(p.scales[0]), x1 = Math.log(p.scales[1]);
    var y = ys[0] + (ys[1] - ys[0]) * (Math.log(Math.max(1e-3, f)) - x0) / (x1 - x0);
    var lo = Math.min(ys[0], ys[1]) - Math.log(3), hi = Math.max(ys[0], ys[1]) + Math.log(3);
    return Math.exp(Math.max(lo, Math.min(hi, y)));
  }

  // Estimated bytes this page adds to the PDF.
  function estimateBytes(item, pageIndex, b) {
    if (item.status === 'error') return 0;
    if (item.status !== 'ready') return item.size + PAGE_OVERHEAD_BYTES;
    var mode = effectiveMode(item, b);
    if (mode === 'asis') {
      if (item.embed === 'jpeg') return item.size + PAGE_OVERHEAD_BYTES;
      if (item.embed === 'png') return item.png.idatBytes + PAGE_OVERHEAD_BYTES;
      return item.size + PAGE_OVERHEAD_BYTES;
    }
    var geo = computeGeometry(item, spineLeftAt(pageIndex));
    var canvasPx = geo.fullW * geo.fullH;
    var artPx = mode === 'fit' ? geo.placed.w * geo.placed.h : geo.area.w * geo.area.h;
    var scale = mode === 'fit' ? geo.fitScale : geo.coverScale;
    var est = bytesPerPixel(item, scale) * artPx;

    var bgPx = mode === 'fit' ? canvasPx - artPx : (geo.gutter ? canvasPx - artPx : 0);
    var fm = effectiveFill(item);
    var bgBpp = fm === 'blur' ? (state.format === 'png' ? 1.2 : 0.05)
                              : (state.format === 'png' ? 0.002 : 0.01);
    return Math.round(est + bgPx * bgBpp) + PAGE_OVERHEAD_BYTES;
  }

  // Page-card status for a ready item.
  function pageStatus(item, pageIndex, b) {
    var mode = effectiveMode(item, b);
    var geo = computeGeometry(item, spineLeftAt(pageIndex));
    var dpi = Math.round(modeDPI(mode, geo));
    var st = { mode: mode, geo: geo, dpi: dpi, crop: mode === 'fill' && geo.cropTooMuch };
    if (mode === 'asis') {
      st.cls = 'status-ok'; st.label = '✅ Right size';
      st.title = 'Already the right size — used as-is.';
    } else if (dpi < 200) {
      st.cls = 'status-low'; st.label = '⛔ Low res · ' + dpi + ' DPI';
      st.title = 'Will be resized using your Fit/Fill choice. At ' + dpi + ' DPI this is likely to look blurry in print.';
    } else {
      st.cls = 'status-resize'; st.label = '⚠️ Resize · ' + dpi + ' DPI';
      st.title = 'Will be resized using your Fit/Fill choice.';
    }
    return st;
  }

  /* ---- 10. PAGE GRID ---- */

  function ensureCard(item) {
    if (item.el) return item.el;
    var li = document.createElement('li');
    li.className = 'page-card';
    li.tabIndex = 0;
    li.draggable = true;
    li.setAttribute('data-id', item.id);
    li.innerHTML =
      '<div class="card-top">' +
        '<span class="card-handle" aria-hidden="true" title="Drag to reorder">⋮⋮</span>' +
        '<span class="card-num"></span>' +
        '<button type="button" class="card-x" aria-label="Remove page">×</button>' +
      '</div>' +
      '<div class="card-thumb"></div>' +
      '<div class="card-name"></div>' +
      '<div class="card-dims"></div>' +
      '<span class="status"></span>' +
      '<div class="card-flags"></div>';
    li.querySelector('.card-name').textContent = item.name;
    li.querySelector('.card-name').title = item.name;
    li.querySelector('.card-x').addEventListener('click', function (e) {
      e.stopPropagation();
      removeItem(item.id);
    });
    li.addEventListener('click', function () { selectItem(item.id); });
    li.addEventListener('keydown', function (e) { onCardKey(e, item); });
    wireCardDrag(li, item);
    item.el = li;
    return li;
  }

  function updateCard(item, pageIndex, b) {
    var li = ensureCard(item);
    li.classList.toggle('is-selected', item.id === state.selectedId);
    li.classList.toggle('is-error', item.status === 'error');
    li.setAttribute('aria-selected', item.id === state.selectedId ? 'true' : 'false');

    var num = li.querySelector('.card-num');
    var thumb = li.querySelector('.card-thumb');
    var dims = li.querySelector('.card-dims');
    var badge = li.querySelector('.status');
    var flags = li.querySelector('.card-flags');

    if (item.status === 'error') {
      num.textContent = 'Skipped';
      if (!thumb.firstChild) thumb.textContent = '⛔';
      dims.textContent = fmtFileSize(item.size);
      badge.className = 'status status-error';
      badge.textContent = "⛔ Can't read";
      badge.title = item.errorMsg || '';
      flags.innerHTML = '';
      li.setAttribute('aria-label', item.name + ': ' + (item.errorMsg || 'skipped'));
      return;
    }

    var pageNo = state.firstPage + pageIndex;
    num.innerHTML = '';
    num.appendChild(document.createTextNode('p. ' + pageNo + ' '));
    var side = document.createElement('span');
    side.className = 'card-side';
    side.textContent = pageNo % 2 === 1 ? '· right' : '· left';
    num.appendChild(side);

    if (item.thumb && thumb.firstChild !== item.thumb) {
      thumb.innerHTML = '';
      thumb.appendChild(item.thumb);
    }

    if (item.status === 'loading') {
      dims.textContent = fmtFileSize(item.size);
      badge.className = 'status status-loading';
      badge.textContent = 'Loading…';
      badge.title = '';
      flags.innerHTML = '';
      return;
    }

    dims.textContent = item.w + ' × ' + item.h + ' px';
    if (!b) {
      badge.className = 'status status-loading';
      badge.textContent = 'Choose a size';
      flags.innerHTML = '';
      return;
    }
    var st = pageStatus(item, pageIndex, b);
    badge.className = 'status ' + st.cls;
    badge.textContent = st.label;
    badge.title = st.title;

    flags.innerHTML = '';
    if (item.placement !== 'default') addFlag(flags, item.placement === 'fit' ? 'Fit' : 'Fill', '');
    if (st.crop) addFlag(flags, '✂ Crops art', 'flag-crop');
    li.setAttribute('aria-label', 'Page ' + pageNo + ', ' + item.name + ': ' + st.title);
  }

  function addFlag(host, text, cls) {
    var f = document.createElement('span');
    f.className = 'flag ' + cls;
    f.textContent = text;
    host.appendChild(f);
  }

  function renderGrid() {
    var b = state.trimIndex >= 0 ? book() : null;
    var grid = el.pageGrid;
    var pageIndex = 0;
    state.items.forEach(function (item) {
      updateCard(item, pageIndex, b);
      if (item.status !== 'error') pageIndex++;
    });
    // Keep DOM order == state order, moving only the cards that are out of
    // place (moving a node drops keyboard focus from it).
    for (var i = 0; i < state.items.length; i++) {
      if (grid.children[i] !== state.items[i].el) grid.insertBefore(state.items[i].el, grid.children[i] || null);
    }
    while (grid.children.length > state.items.length) grid.removeChild(grid.lastChild);
  }

  function findItem(id) {
    for (var i = 0; i < state.items.length; i++) if (state.items[i].id === id) return state.items[i];
    return null;
  }

  function pageIndexOf(item) {
    var n = 0;
    for (var i = 0; i < state.items.length; i++) {
      if (state.items[i] === item) return n;
      if (state.items[i].status !== 'error') n++;
    }
    return -1;
  }

  function selectItem(id) {
    if (state.selectedId === id) return;
    state.selectedId = id;
    renderGrid();
    updatePreviewPanel();
  }

  function removeItem(id) {
    var idx = -1;
    for (var i = 0; i < state.items.length; i++) if (state.items[i].id === id) idx = i;
    if (idx < 0) return;
    var item = state.items[idx];
    state.items.splice(idx, 1);
    if (item.el && item.el.parentNode) item.el.parentNode.removeChild(item.el);
    releaseCanvas(item.thumb);
    if (preview.id === id) dropPreviewSource();
    if (state.selectedId === id) {
      var next = state.items[idx] || state.items[idx - 1];
      state.selectedId = next ? next.id : null;
      if (next && next.el) next.el.focus();
    }
    refresh();
  }

  function clearAll() {
    importQueue.length = 0;
    state.items.forEach(function (it) { releaseCanvas(it.thumb); });
    state.items = [];
    state.selectedId = null;
    el.pageGrid.innerHTML = '';
    dropPreviewSource();
    refresh();
  }

  function moveItem(id, toIndex) {
    var from = -1;
    for (var i = 0; i < state.items.length; i++) if (state.items[i].id === id) from = i;
    if (from < 0) return;
    var item = state.items.splice(from, 1)[0];
    if (toIndex > from) toIndex--;
    toIndex = Math.max(0, Math.min(state.items.length, toIndex));
    state.items.splice(toIndex, 0, item);
    refresh();
  }

  function onCardKey(e, item) {
    var idx = state.items.indexOf(item);
    if (e.key === 'Enter' || e.key === ' ' || e.key === 'Spacebar') {
      e.preventDefault();
      selectItem(item.id);
    } else if (e.key === 'Delete' || e.key === 'Backspace') {
      e.preventDefault();
      removeItem(item.id);
    } else if (e.altKey && (e.key === 'ArrowLeft' || e.key === 'ArrowUp')) {
      e.preventDefault();
      if (idx > 0) { moveItem(item.id, idx - 1); item.el.focus(); }
    } else if (e.altKey && (e.key === 'ArrowRight' || e.key === 'ArrowDown')) {
      e.preventDefault();
      if (idx < state.items.length - 1) { moveItem(item.id, idx + 2); item.el.focus(); }
    } else if (e.key === 'ArrowLeft' || e.key === 'ArrowRight') {
      e.preventDefault();
      var n = state.items[idx + (e.key === 'ArrowLeft' ? -1 : 1)];
      if (n) { selectItem(n.id); n.el.focus(); }
    }
  }

  /* -- drag to reorder (HTML5 drag & drop) -- */

  function clearDropMarks() {
    state.items.forEach(function (it) {
      if (it.el) it.el.classList.remove('drop-before', 'drop-after');
    });
  }

  function wireCardDrag(li, item) {
    li.addEventListener('dragstart', function (e) {
      dragId = item.id;
      li.classList.add('is-dragging');
      e.dataTransfer.effectAllowed = 'move';
      try { e.dataTransfer.setData('text/plain', String(item.id)); } catch (err) { /* IE */ }
    });
    li.addEventListener('dragend', function () {
      dragId = null;
      li.classList.remove('is-dragging');
      clearDropMarks();
    });
    li.addEventListener('dragover', function (e) {
      if (dragId === null) return;
      e.preventDefault();
      e.stopPropagation();
      e.dataTransfer.dropEffect = 'move';
      var r = li.getBoundingClientRect();
      var after = e.clientX > r.left + r.width / 2;
      clearDropMarks();
      if (dragId !== item.id) li.classList.add(after ? 'drop-after' : 'drop-before');
    });
    li.addEventListener('drop', function (e) {
      if (dragId === null) return;
      e.preventDefault();
      e.stopPropagation();
      var r = li.getBoundingClientRect();
      var after = e.clientX > r.left + r.width / 2;
      var id = dragId;
      dragId = null;
      clearDropMarks();
      if (id === item.id) return;
      var target = state.items.indexOf(item) + (after ? 1 : 0);
      moveItem(id, target);
    });
  }

  /* ---- 11. PREVIEW & COMPARE SLIDER ---- */

  function selectedItem() { return state.selectedId ? findItem(state.selectedId) : null; }

  function dropPreviewSource() {
    releasePyramid(preview.pyramid);
    preview.id = null;
    preview.pyramid = null;
    preview.loading = null;
  }

  // Full-size decode of the selected page only — never all pages at once.
  function ensurePreviewSource(item) {
    if (preview.id === item.id && preview.pyramid) return true;
    if (preview.loading === item.id) return false;
    releasePyramid(preview.pyramid);
    preview.pyramid = null;
    preview.id = item.id;
    preview.loading = item.id;
    decodeUpright(item.file).then(function (canvas) {
      if (preview.loading !== item.id) { releaseCanvas(canvas); return; }
      preview.loading = null;
      preview.pyramid = [canvas];
      schedulePreview();
    }, function () {
      if (preview.loading === item.id) preview.loading = null;
      el.stageLoading.hidden = true;
    });
    return false;
  }

  function schedulePreview() {
    if (previewRaf) return;
    previewRaf = requestAnimationFrame(function () {
      previewRaf = 0;
      renderPreview();
    });
  }

  function updatePreviewPanel() {
    var item = selectedItem();
    var show = !!item && item.status === 'ready' && state.trimIndex >= 0;
    el.previewPanel.hidden = !show;
    if (show) schedulePreview();
  }

  function renderPreview() {
    var item = selectedItem();
    if (!item || item.status !== 'ready' || state.trimIndex < 0) return;
    var b = book();
    var pageIndex = pageIndexOf(item);
    var st = pageStatus(item, pageIndex, b);
    var geo = st.geo;
    updatePageReadout(item, pageIndex, st, b);

    var ready = ensurePreviewSource(item);
    el.stageLoading.hidden = ready;
    if (!ready) return;

    var single = st.mode === 'asis';
    el.compare.classList.toggle('single', single);
    el.cmpButtons.hidden = single;

    var stageRect = el.stage.getBoundingClientRect();
    var availW = Math.max(40, stageRect.width - 32);
    var availH = Math.max(40, stageRect.height - 32);

    var vis = geo.visible;
    var aspect = vis.w / vis.h;
    var dispH = availH, dispW = dispH * aspect;
    if (dispW > availW) { dispW = availW; dispH = dispW / aspect; }

    var dpr = Math.min(2, window.devicePixelRatio || 1);
    var longEdge = Math.max(vis.w, vis.h);
    var s = Math.min(1, PREVIEW_LONG_EDGE / longEdge, (Math.max(dispW, dispH) * dpr) / longEdge);

    el.sheet.style.width = dispW + 'px';
    el.sheet.style.height = dispH + 'px';

    var cw = Math.max(1, Math.round(vis.w * s)), ch = Math.max(1, Math.round(vis.h * s));
    if (el.previewCanvas.width !== cw) el.previewCanvas.width = cw;
    if (el.previewCanvas.height !== ch) el.previewCanvas.height = ch;
    renderPage(el.previewCanvas.getContext('2d'), item, preview.pyramid, geo, s, st.mode, vis.x);

    if (!single) drawBefore(availW, availH, dpr);
    drawGuides(geo, s, dispW, st.mode);
    setDivider(state.dividerPct);
  }

  function drawBefore(availW, availH, dpr) {
    var src = preview.pyramid[0];
    var fit = Math.min(availW / src.width, availH / src.height);
    var cssW = src.width * fit, cssH = src.height * fit;
    var w = Math.max(1, Math.round(Math.min(cssW * dpr, PREVIEW_LONG_EDGE, src.width)));
    var h = Math.max(1, Math.round(w * (src.height / src.width)));

    var c = el.beforeCanvas;
    if (c.width !== w) c.width = w;
    if (c.height !== h) c.height = h;
    c.style.width = cssW + 'px';
    c.style.height = cssH + 'px';
    var ctx = whiteCtx(c);
    drawArtwork(ctx, preview.pyramid, 0, 0, w, h);
  }

  // Guides live on their own overlay canvas, drawn on top of the preview.
  // The export path never calls this function — guides can therefore never
  // appear in the PDF.
  function drawGuides(geo, s, dispW, mode) {
    var c = el.overlayCanvas;
    var cw = el.previewCanvas.width, ch = el.previewCanvas.height;
    if (c.width !== cw) c.width = cw;
    if (c.height !== ch) c.height = ch;
    var ctx = c.getContext('2d');
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, cw, ch);
    if (!state.guides) return;

    var offX = geo.visible.x;
    var k = dispW > 0 ? (cw / dispW) : 1;          // px per CSS px
    ctx.font = Math.round(10 * k) + 'px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Arial, sans-serif';
    ctx.textBaseline = 'top';

    // Gutter: a shaded, hatched strip on the spine side.
    if (geo.gutter) {
      var g = scaleRect(geo.gutter, s, offX);
      ctx.save();
      ctx.beginPath();
      ctx.rect(g.x, g.y, g.w, g.h);
      ctx.clip();
      ctx.fillStyle = 'rgba(234,88,12,0.10)';
      ctx.fillRect(g.x, g.y, g.w, g.h);
      ctx.strokeStyle = 'rgba(234,88,12,0.35)';
      ctx.lineWidth = 1 * k;
      var step = 8 * k;
      for (var d = -g.h; d < g.w + g.h; d += step) {
        ctx.beginPath();
        ctx.moveTo(g.x + d, g.y + g.h);
        ctx.lineTo(g.x + d + g.h, g.y);
        ctx.stroke();
      }
      ctx.restore();
      ctx.strokeStyle = 'rgba(234,88,12,0.7)';
      ctx.lineWidth = 1 * k;
      var innerX = geo.spineLeft ? g.x + g.w : g.x;
      ctx.beginPath();
      ctx.moveTo(innerX, 0);
      ctx.lineTo(innerX, ch);
      ctx.stroke();
      if (g.w > 12 * k) {
        ctx.save();
        ctx.translate(g.x + g.w / 2, g.y + g.h / 2);
        ctx.rotate(-Math.PI / 2);
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillStyle = '#c2410c';
        ctx.fillText('GUTTER · SPINE SIDE', 0, 0);
        ctx.restore();
      }
    }

    // Trim line: only meaningful with bleed. Without bleed the trim line IS
    // the page edge, and drawing it is noise.
    if (state.bleed) {
      var t = scaleRect(geo.trim, s, offX);
      ctx.strokeStyle = '#94a3b8';
      ctx.setLineDash([]);
      ctx.lineWidth = 1 * k;
      ctx.strokeRect(t.x, t.y, t.w, t.h);
      ctx.fillStyle = '#94a3b8';
      ctx.fillText('TRIM', t.x + (geo.spineLeft && geo.gutter ? t.w - 30 * k : 3 * k), t.y + 3 * k);
    }

    var sf = scaleRect(geo.safe, s, offX);
    ctx.strokeStyle = '#ea580c';
    ctx.setLineDash([6 * k, 5 * k]);
    ctx.lineWidth = 2 * k;
    ctx.strokeRect(sf.x, sf.y, sf.w, sf.h);
    ctx.setLineDash([]);
    ctx.fillStyle = '#ea580c';
    ctx.fillText('SAFE', sf.x + 3 * k, sf.y + 3 * k);
  }

  function setDivider(pct) {
    pct = Math.max(0, Math.min(100, pct));
    state.dividerPct = pct;
    el.divider.style.left = pct + '%';
    el.layerAfter.style.clipPath = 'inset(0 0 0 ' + pct + '%)';
    el.layerAfter.style.webkitClipPath = 'inset(0 0 0 ' + pct + '%)';
    el.handle.setAttribute('aria-valuenow', Math.round(pct));
    el.btnBefore.setAttribute('aria-pressed', pct >= 100 ? 'true' : 'false');
    el.btnBefore.classList.toggle('is-on', pct >= 100);
    el.btnAfter.setAttribute('aria-pressed', pct <= 0 ? 'true' : 'false');
    el.btnAfter.classList.toggle('is-on', pct <= 0);
  }

  function pointerToPct(clientX) {
    var r = el.compare.getBoundingClientRect();
    if (!r.width) return state.dividerPct;
    return ((clientX - r.left) / r.width) * 100;
  }

  function updatePageReadout(item, pageIndex, st, b) {
    var pageNo = state.firstPage + pageIndex;
    var right = pageNo % 2 === 1;
    el.previewTitle.textContent = 'Page ' + pageNo + ' · ' + item.name;

    el.outMain.textContent = 'Page ' + pageNo + ' · ' +
      (right ? 'right-hand page (spine on the left)' : 'left-hand page (spine on the right)');

    if (st.mode === 'asis') {
      el.outSub.textContent = '✅ Already the right size — used as-is.';
    } else {
      el.outSub.textContent = '⚠️ Will be resized using your Fit/Fill choice (' +
        (st.mode === 'fit' ? 'Fit — never crops' : 'Fill — fills the page, may crop') + ').';
    }

    // Gutter only ever actually applies to pages we place ourselves (Fit/Fill).
    // An as-is page keeps whatever margin Margin Fixer already gave it — say
    // so plainly instead of claiming gutter was added when it wasn't.
    var gutterApplies = st.mode !== 'asis' && st.geo.gutter;
    el.outSub2.textContent = 'Your image: ' + item.w + ' × ' + item.h + ' px · ' + fmtFileSize(item.size) +
      '  →  PDF page ' + fmtIn(b.pageWin) + '" × ' + fmtIn(b.pageHin) + '"' +
      (state.bleed ? ' (KDP bleed size)' : '') +
      (gutterApplies ? ' · ' + fmtIn(st.geo.gPx / DPI) + '" gutter' : '');

    el.pageCropWarn.hidden = !st.crop;
    if (st.crop) el.pageCropWarn.textContent = CROP_WARNING;

    var needsGutterNote = st.mode === 'asis' && st.geo.gutter;
    el.pageGutterNote.hidden = !needsGutterNote;
    if (needsGutterNote) {
      el.pageGutterNote.textContent = 'This page is already the right size, so we can’t add gutter ' +
        'to it after the fact. Make sure you used at least ' + fmtIn(st.geo.gPx / DPI) +
        '" margin in Margin Fixer for a book this long — resize this one page (Fit) if you need to check.';
    }

    // per-page placement override
    var matches = itemMatches(item, b);
    var bookMode = state.placement === 'fit' ? 'Fit' : 'Fill';
    var opts = matches
      ? [['default', 'Use as-is (already the right size)'], ['fit', 'Resize anyway: Fit'], ['fill', 'Resize anyway: Fill']]
      : [['default', 'Use the book setting (' + bookMode + ')'], ['fit', 'Fit — never crops'], ['fill', 'Fill — fills the page, may crop']];
    var sel = el.overrideSelect;
    var sig = opts.map(function (o) { return o[1]; }).join('|');
    if (sel.getAttribute('data-sig') !== sig) {
      sel.innerHTML = '';
      opts.forEach(function (o) {
        var op = document.createElement('option');
        op.value = o[0];
        op.textContent = o[1];
        sel.appendChild(op);
      });
      sel.setAttribute('data-sig', sig);
    }
    sel.value = item.placement;

    updateQuality(st.mode === 'asis' ? null : st.dpi);
  }

  function updateQuality(dpi) {
    if (dpi === null) {
      el.quality.hidden = false;
      el.quality.className = 'quality q-ok';
      el.qTitle.textContent = '✅ Print quality: Excellent';
      el.qCopy.textContent = 'Embedded exactly as you made it — no resizing, no recompression (300 DPI).';
      return;
    }
    el.quality.hidden = false;
    el.quality.className = 'quality';
    if (dpi >= 300) {
      el.quality.classList.add('q-ok');
      el.qTitle.textContent = '✅ Print quality: Excellent';
      el.qCopy.textContent = 'Your image is sharp enough for print at this size (' + dpi + ' DPI).';
    } else if (dpi >= 200) {
      el.quality.classList.add('q-warn');
      el.qTitle.textContent = '⚠️ Print quality: Acceptable';
      el.qCopy.textContent = 'At ' + dpi + ' DPI this will print a little soft. Fine for most coloring pages, but a larger original would look crisper.';
    } else {
      el.quality.classList.add('q-bad');
      el.qTitle.textContent = '⛔ Print quality: Low';
      el.qCopy.textContent = 'At ' + dpi + ' DPI this is likely to look blurry in print. Try starting from a larger version of your image.';
    }
  }

  /* ---- 12. EXPORT ---- */

  function exportFilename() {
    var t = TRIM_SIZES[state.trimIndex];
    var name = 'kdp-interior-' + fmtIn(t.w) + 'x' + fmtIn(t.h);
    if (t.note === 'A4') name += '-a4';
    if (state.bleed) name += '-bleed';
    return name + '.pdf';
  }

  function onDownloadClick() {
    if (state.building) return;
    var loading = state.items.some(function (it) { return it.status === 'loading'; });
    if (loading) {
      showBanner('Some pages are still loading. Please wait a moment, then try again.');
      return;
    }
    var est = totalEstimate();
    if (est > KDP_MAX_BYTES) {
      showBanner('This PDF will likely be over 650 MB, and KDP won’t accept it. Switching resized pages to JPG (Step 4) usually fixes this.',
                 'Build it anyway', buildPdf);
      return;
    }
    buildPdf();
  }

  function buildPdf() {
    var pages = pageItems().filter(function (it) { return it.status === 'ready'; });
    if (!pages.length || state.trimIndex < 0) return;
    state.building = true;
    setDownloadBusy(true, 0, pages.length);
    el.bannerHost.innerHTML = '';

    var b = book();
    var writer = new KDPPdf.PdfWriter();
    var chain = nextFrame();
    pages.forEach(function (item, i) {
      chain = chain.then(function () {
        setDownloadBusy(true, i + 1, pages.length);
        return buildPageImage(item, i, b);
      }).then(function (r) {
        writer.addImagePage({ width: b.pageWpt, height: b.pageHpt }, r.image, r.matrix);
        return nextFrame();                      // keep the page responsive
      });
    });

    chain.then(function () {
      var blob = writer.finish();
      var url = URL.createObjectURL(blob);
      var a = document.createElement('a');
      a.href = url;
      a.download = exportFilename();
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      setTimeout(function () { URL.revokeObjectURL(url); }, 60000);
      showToast(exportFilename(), pages.length, blob.size);
      if (blob.size > KDP_MAX_BYTES) {
        showBanner('Heads up: this PDF is ' + fmtMB(blob.size) + ' — over KDP’s 650 MB limit. Switch resized pages to JPG or lower the quality in Step 4, then download again.');
      }
    }).catch(function () {
      showBanner('Something went wrong while creating the PDF. Please try again.');
    }).then(function () {
      state.building = false;
      setDownloadBusy(false);
    });
  }

  // Produces the embedded image + placement for one page.
  function buildPageImage(item, pageIndex, b) {
    var geo = computeGeometry(item, spineLeftAt(pageIndex));
    var mode = effectiveMode(item, b);
    // The whole canvas, in points, shifted so the spine-side bleed (if any)
    // falls off the page — the page's MediaBox is KDP's official size.
    var xPt = -geo.visible.x * PT_PER_PX;
    var wPt = geo.fullW * PT_PER_PX, hPt = geo.fullH * PT_PER_PX;

    if (mode === 'asis' && item.embed === 'jpeg') {
      var j = item.jpeg;
      return Promise.resolve({
        image: {
          width: j.width, height: j.height, bits: 8,
          colorSpace: j.components === 1 ? 'DeviceGray' : (j.components === 4 ? 'DeviceCMYK' : 'DeviceRGB'),
          invertCmyk: j.components === 4 && j.adobe,
          filter: 'DCTDecode',
          parts: [item.file],                   // byte-for-byte, never decoded
          length: item.file.size
        },
        matrix: KDPPdf.placementMatrix(xPt, 0, wPt, hPt, item.orientation)
      });
    }

    if (mode === 'asis' && item.embed === 'png') {
      var p = item.png;
      return Promise.resolve({
        image: {
          width: p.width, height: p.height, bits: p.bitDepth,
          colorSpace: p.colorType === 2 ? 'DeviceRGB' : (p.colorType === 3 ? 'Indexed' : 'DeviceGray'),
          palette: p.palette,
          filter: 'FlateDecode',
          predictorColors: p.colorType === 2 ? 3 : 1,
          parts: p.idat.map(function (r) { return item.file.slice(r[0], r[1]); }),
          length: p.idatBytes
        },
        matrix: KDPPdf.placementMatrix(xPt, 0, wPt, hPt, 1)
      });
    }

    var matrix = KDPPdf.placementMatrix(xPt, 0, wPt, hPt, 1);

    if (mode === 'asis') {
      // Lossless repack: same pixels, new container.
      return decodeUpright(item.file, true).then(function (canvas) {
        return pixelsImage(canvas).then(function (image) {
          releaseCanvas(canvas);
          return { image: image, matrix: matrix };
        });
      });
    }

    // Resize once, encode once.
    return decodeUpright(item.file).then(function (src) {
      var pyramid = [src];
      var out = newCanvas(geo.fullW, geo.fullH);
      renderPage(out.getContext('2d'), item, pyramid, geo, 1, mode, 0);
      releasePyramid(pyramid);
      var done = state.format === 'jpg'
        ? toBlobP(out, 'image/jpeg', state.jpegQuality).then(function (blob) {
            return {
              width: out.width, height: out.height, bits: 8, colorSpace: 'DeviceRGB',
              filter: 'DCTDecode', parts: [blob], length: blob.size
            };
          })
        : pixelsImage(out);
      return done.then(function (image) {
        releaseCanvas(out);
        return { image: image, matrix: matrix };
      });
    });
  }

  function pixelsImage(canvas) {
    var w = canvas.width, h = canvas.height;
    var rgba = canvas.getContext('2d').getImageData(0, 0, w, h).data;
    return KDPPdf.packPixels(rgba, w, h).then(function (r) {
      return {
        width: w, height: h, bits: 8,
        colorSpace: r.colors === 1 ? 'DeviceGray' : 'DeviceRGB',
        filter: r.predictor ? 'FlateDecode' : null,
        predictorColors: r.predictor ? r.colors : 0,
        parts: [r.blob], length: r.blob.size
      };
    });
  }

  function setDownloadBusy(busy, i, n) {
    el.downloadBtn.disabled = busy || !canDownload();
    if (busy) {
      el.downloadBtn.innerHTML = '<span class="spinner" aria-hidden="true"></span><span>' +
        (i ? 'Building page ' + i + ' of ' + n + '…' : 'Starting…') + '</span>';
    } else {
      el.downloadBtn.innerHTML = '<span>Download PDF</span>';
    }
  }

  function canDownload() {
    return state.trimIndex >= 0 && !state.building &&
      state.items.some(function (it) { return it.status === 'ready'; });
  }

  function showToast(name, pages, bytes) {
    var host = el.previewPanel.hidden ? null : el.toast;
    var msg = '"' + name + '" — ' + plural(pages, 'page') + ', ' + fmtMB(bytes) + ', ready for KDP.';
    if (!host) { showBanner('Saved! ' + msg); return; }
    host.innerHTML = '';
    var strong = document.createElement('strong');
    strong.textContent = 'Saved! ';
    host.appendChild(strong);
    host.appendChild(document.createTextNode(msg));
    host.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { host.hidden = true; }, 6000);
  }

  /* ---- 13. SIDEBAR UI ---- */

  function totalEstimate() {
    if (state.trimIndex < 0) return 0;
    var b = book(), total = 0, pageIndex = 0;
    state.items.forEach(function (it) {
      if (it.status === 'error') return;
      total += estimateBytes(it, pageIndex, b);
      pageIndex++;
    });
    return total;
  }

  function updateSizeMeter() {
    var est = totalEstimate();
    var frac = est / KDP_MAX_BYTES;
    el.sizeVal.textContent = (est ? '≈ ' + fmtMB(est) : '0 MB') + ' / 650 MB';
    el.sizeFill.style.width = Math.min(100, frac * 100) + '%';
    el.sizeMeter.classList.toggle('is-warn', frac >= SIZE_WARN_FRACTION && frac <= 1);
    el.sizeMeter.classList.toggle('is-bad', frac > 1);
    if (frac > 1) {
      el.sizeCopy.textContent = 'Over KDP’s 650 MB limit — KDP won’t accept this file. ' +
        (state.format === 'png' ? 'Switch resized pages to JPG in Step 4.' : 'Lower the JPG quality in Step 4, or split the book.');
    } else if (frac >= SIZE_WARN_FRACTION) {
      el.sizeCopy.textContent = 'Getting close to KDP’s 650 MB limit.' +
        (state.format === 'png' ? ' Switching resized pages to JPG (Step 4) would shrink it a lot.' : '');
    } else {
      el.sizeCopy.textContent = 'KDP won’t accept a file over 650 MB. We’ll warn you here before you find out the hard way.';
    }
  }

  function updateGutterUI() {
    var band = gutterBand();
    el.gutterReadout.textContent = state.gutter
      ? fmtIn(band.w) + '″ per KDP’s table ' + band.label
      : 'Off — the spine side keeps only the ' + (state.bleed ? '0.375' : '0.25') + '″ minimum margin';

    var uploaded = pageItems().length;
    // Auto mode shows the uploaded count as a placeholder, so the box can be
    // cleared and typed into freely.
    el.pageCount.placeholder = String(uploaded);
    if (state.pageCountTyped === null) {
      if (document.activeElement !== el.pageCount) el.pageCount.value = '';
      el.pageCountHint.textContent = uploaded
        ? 'Counting your uploaded pages. Type a number if the finished book will have more.'
        : "We'll count your uploaded pages until you type a number.";
    } else {
      el.pageCountHint.textContent = 'Clear the box to go back to counting your uploaded pages.';
    }
    var n = bookPageCount(), warn = '';
    if (n > 0 && n < KDP_MIN_PAGES) warn = 'KDP paperbacks need at least ' + KDP_MIN_PAGES + ' pages.';
    else if (state.pageCountTyped !== null && state.pageCountTyped < uploaded) {
      warn = "You've uploaded more pages (" + uploaded + ') than this.';
    }
    el.pageCountWarn.hidden = !warn;
    el.pageCountWarn.textContent = warn;
  }

  function updateSteps() {
    var sized = state.trimIndex >= 0;
    var b = sized ? book() : null;
    var ready = state.items.filter(function (it) { return it.status === 'ready'; });
    var needResize = 0, crop = 0, asis = 0, pageIndex = 0;
    state.items.forEach(function (it) {
      if (it.status === 'error') return;
      if (it.status === 'ready' && b) {
        var st = pageStatus(it, pageIndex, b);
        if (st.mode === 'asis') asis++; else needResize++;
        if (st.crop) crop++;
      }
      pageIndex++;
    });
    var allMatch = sized && ready.length > 0 && needResize === 0;

    setLocked('step2', !sized, [el.chooseBtn]);
    setLocked('step3', !sized || allMatch, [el.placeFit, el.placeFill, el.fillSelect, el.colorSwatchBtn]);
    setLocked('step4', !sized || allMatch, [el.fmtPng, el.fmtJpg, el.jpegQuality]);
    el.allMatchNote.hidden = !allMatch;

    el.cropSummary.hidden = !crop;
    if (crop) {
      el.cropSummary.textContent = plural(crop, 'page') + (crop === 1 ? ' has' : ' have') +
        ' a very different shape from your book, so Fill would crop into the artwork. They’re marked ✂ in your page list — consider Fit for them.';
    }

    // upload summary
    var total = state.items.length;
    var loading = state.items.filter(function (it) { return it.status === 'loading'; }).length;
    var errors = state.items.filter(function (it) { return it.status === 'error'; }).length;
    el.uploadSummary.hidden = !total;
    if (total) {
      var parts = [plural(total - errors, 'page')];
      if (loading) parts.push('loading ' + loading + '…');
      if (asis) parts.push(asis + ' used as-is');
      if (needResize) parts.push(needResize + ' to resize');
      if (errors) parts.push(errors + ' skipped');
      el.uploadSummaryText.textContent = parts.join(' · ');
    }

    el.emptyHead.textContent = sized ? 'Drop your page images here' : 'Choose your book size first';
    el.emptySub.textContent = sized
      ? 'or click to browse — PNG or JPG, as many as you like, any mix of sizes.'
      : 'Then drop your page images here — PNG or JPG, as many as you like.';
  }

  function setLocked(id, locked, controls) {
    $(id).classList.toggle('locked', locked);
    controls.forEach(function (c) { c.disabled = locked; });
  }

  // One entry point after any change: every derived bit of UI is recomputed
  // from state, so nothing can drift out of sync.
  function refresh() {
    var has = state.items.length > 0;
    el.emptyState.hidden = has;
    el.pageGrid.hidden = !has;
    el.reorderHint.hidden = state.items.length < 2;
    var pages = pageItems().length;
    el.pageTotal.textContent = has ? '(' + pages + ')' : '';

    el.targetHint.hidden = state.trimIndex < 0;
    if (state.trimIndex >= 0) {
      var b = book();
      el.targetHint.textContent = 'Pages exactly ' + b.fullW + ' × ' + b.fullH + ' px are used as-is';
    }

    updateGutterUI();
    updateSteps();
    renderGrid();
    updateSizeMeter();
    if (!state.building) setDownloadBusy(false);
    updatePreviewPanel();
  }

  function buildTrimOptions() {
    var groups = {};
    var order = [];
    TRIM_SIZES.forEach(function (t, i) {
      if (!groups[t.group]) { groups[t.group] = []; order.push(t.group); }
      groups[t.group].push(i);
    });
    order.forEach(function (g) {
      var og = document.createElement('optgroup');
      og.label = g;
      groups[g].forEach(function (i) {
        var t = TRIM_SIZES[i];
        // At 300 DPI every official size lands on a whole pixel.
        var px = Math.round(t.w * DPI) + ' × ' + Math.round(t.h * DPI) + ' px';
        var o = document.createElement('option');
        o.value = String(i);
        o.textContent = trimLabelInches(t) + (t.note ? ' (' + t.note + ')' : '') + ' — ' + px;
        og.appendChild(o);
      });
      el.trimSelect.appendChild(og);
    });
  }

  function showBanner(message, actionLabel, onAction) {
    el.bannerHost.innerHTML = '';
    var box = document.createElement('div');
    box.className = 'banner';

    var body = document.createElement('div');
    body.className = 'banner-body';
    var p = document.createElement('p');
    p.textContent = message;
    body.appendChild(p);

    if (actionLabel) {
      var act = document.createElement('button');
      act.type = 'button';
      act.className = 'link-btn';
      act.style.marginTop = '6px';
      act.textContent = actionLabel;
      act.addEventListener('click', function () {
        el.bannerHost.innerHTML = '';
        onAction();
      });
      body.appendChild(act);
    }

    var x = document.createElement('button');
    x.type = 'button';
    x.className = 'banner-x';
    x.setAttribute('aria-label', 'Dismiss');
    x.innerHTML = '&times;';
    x.addEventListener('click', function () { el.bannerHost.innerHTML = ''; });

    box.appendChild(body);
    box.appendChild(x);
    el.bannerHost.appendChild(box);
  }

  function setSeg(onBtn, offBtn) {
    onBtn.classList.add('is-on');
    onBtn.setAttribute('aria-pressed', 'true');
    offBtn.classList.remove('is-on');
    offBtn.setAttribute('aria-pressed', 'false');
  }

  function setBleed(on) {
    state.bleed = on;
    if (on) setSeg(el.bleedOn, el.bleedOff); else setSeg(el.bleedOff, el.bleedOn);
    el.bleedHint.textContent = on ? BLEED_HINTS.on : BLEED_HINTS.off;
    refresh();
  }

  function setPlacement(mode) {
    state.placement = mode;
    if (mode === 'fit') setSeg(el.placeFit, el.placeFill); else setSeg(el.placeFill, el.placeFit);
    el.placementHint.textContent = PLACEMENT_HINTS[mode];
    refresh();
  }

  function setFormat(fmt) {
    state.format = fmt;
    if (fmt === 'png') setSeg(el.fmtPng, el.fmtJpg); else setSeg(el.fmtJpg, el.fmtPng);
    el.formatHint.textContent = FORMAT_HINTS[fmt];
    el.qualityField.hidden = fmt !== 'jpg';
    refresh();
  }

  function updateSolidColorRow() {
    var show = state.fill === 'solid';
    el.solidColorRow.hidden = !show;
    if (!show) return;
    var col = state.customSolidColor || solidColor(selectedItem());
    el.colorSwatchPreview.style.background = col;
    el.colorSwatchLabel.textContent = state.customSolidColor ? col : 'Pick color';
    el.colorResetBtn.hidden = !state.customSolidColor;
  }

  // EyeDropper samples any pixel on screen — Chrome/Edge only. Firefox/Safari
  // fall back to the native <input type="color"> swatch picker.
  function openColorPicker() {
    if (typeof window.EyeDropper === 'function') {
      new window.EyeDropper().open().then(function (result) {
        state.customSolidColor = result.sRGBHex;
        updateSolidColorRow();
        refresh();
      }).catch(function () { /* user cancelled — no-op */ });
      return;
    }
    el.colorFallbackInput.value = state.customSolidColor || solidColor(selectedItem());
    el.colorFallbackInput.click();
  }

  function closePopovers(except) {
    [['help1', 'pop1'], ['help3', 'pop3']].forEach(function (pair) {
      if (pair[1] === except) return;
      $(pair[1]).hidden = true;
      $(pair[0]).setAttribute('aria-expanded', 'false');
    });
  }

  function wirePopover(btnId, popId) {
    var btn = $(btnId), pop = $(popId);
    btn.addEventListener('click', function (e) {
      e.stopPropagation();
      var open = pop.hidden;
      closePopovers(open ? popId : null);
      pop.hidden = !open;
      btn.setAttribute('aria-expanded', open ? 'true' : 'false');
    });
    pop.addEventListener('click', function (e) { e.stopPropagation(); });
  }

  function openPicker() {
    if (state.trimIndex < 0) {
      showBanner("Choose your book's trim size first (Step 1) — then add your pages.");
      el.trimSelect.focus();
      return;
    }
    el.fileInput.click();
  }

  function parseIntInput(v, min, max) {
    var n = parseInt(v, 10);
    if (!isFinite(n)) return null;
    return Math.max(min, Math.min(max, n));
  }

  /* ---- 14. INIT ---- */

  function init() {
    ['bannerHost', 'trimSelect', 'bleedOn', 'bleedOff', 'bleedHint', 'targetHint',
     'pageCount', 'pageCountHint', 'pageCountWarn', 'gutterToggle', 'gutterReadout', 'firstPage',
     'chooseBtn', 'fileInput', 'uploadSummary', 'uploadSummaryText', 'clearAllBtn',
     'allMatchNote', 'placeFit', 'placeFill', 'placementHint', 'cropSummary',
     'fillSelect', 'fillHint', 'solidColorRow', 'colorSwatchBtn', 'colorSwatchPreview',
     'colorSwatchLabel', 'colorResetBtn', 'colorFallbackInput',
     'fmtPng', 'fmtJpg', 'formatHint', 'qualityField', 'jpegQuality', 'jpegQualityVal',
     'sizeMeter', 'sizeVal', 'sizeFill', 'sizeCopy', 'downloadBtn',
     'content', 'pageTotal', 'reorderHint', 'emptyState', 'emptyHead', 'emptySub', 'pageGrid',
     'previewPanel', 'cmpButtons', 'btnBefore', 'btnAfter', 'previewTitle', 'guidesToggle',
     'stage', 'compare', 'beforeCanvas', 'layerAfter', 'sheet', 'previewCanvas', 'overlayCanvas',
     'divider', 'handle', 'stageLoading', 'toast',
     'outMain', 'outSub', 'outSub2', 'pageCropWarn', 'pageGutterNote', 'overrideSelect',
     'quality', 'qTitle', 'qCopy'].forEach(function (id) { el[id] = $(id); });

    buildTrimOptions();
    el.placementHint.textContent = PLACEMENT_HINTS.fit;
    setDivider(50);
    refresh();

    /* -- step 1: book -- */
    el.trimSelect.addEventListener('change', function () {
      state.trimIndex = parseInt(el.trimSelect.value, 10);
      if (!(state.trimIndex >= 0)) state.trimIndex = -1;
      el.bannerHost.innerHTML = '';
      refresh();
    });
    el.bleedOff.addEventListener('click', function () { setBleed(false); });
    el.bleedOn.addEventListener('click', function () { setBleed(true); });
    el.pageCount.addEventListener('input', function () {
      state.pageCountTyped = el.pageCount.value === '' ? null : parseIntInput(el.pageCount.value, 1, 2000);
      refresh();
    });
    el.pageCount.addEventListener('blur', function () {
      if (state.pageCountTyped !== null) el.pageCount.value = String(state.pageCountTyped);
    });
    el.gutterToggle.addEventListener('change', function () {
      state.gutter = el.gutterToggle.checked;
      refresh();
    });
    el.firstPage.addEventListener('input', function () {
      var v = parseIntInput(el.firstPage.value, 1, 2000);
      if (v !== null) { state.firstPage = v; refresh(); }
    });
    el.firstPage.addEventListener('blur', function () { el.firstPage.value = String(state.firstPage); });

    /* -- step 2: upload -- */
    el.chooseBtn.addEventListener('click', openPicker);
    el.fileInput.addEventListener('change', function () {
      handleFiles(el.fileInput.files);
      el.fileInput.value = '';                 // allow re-picking the same files
    });
    el.clearAllBtn.addEventListener('click', clearAll);

    el.emptyState.addEventListener('click', openPicker);
    el.emptyState.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' || e.key === ' ' || e.key === 'Spacebar') {
        e.preventDefault();
        openPicker();
      }
    });

    // A stray drop must never navigate away from the page.
    window.addEventListener('dragover', function (e) { e.preventDefault(); });
    window.addEventListener('drop', function (e) { e.preventDefault(); });

    var pagesPanel = el.content.querySelector('.pages-panel');
    function isFileDrag(e) {
      var types = e.dataTransfer && e.dataTransfer.types;
      if (!types) return false;
      for (var i = 0; i < types.length; i++) if (types[i] === 'Files') return true;
      return false;
    }
    pagesPanel.addEventListener('dragover', function (e) {
      if (!isFileDrag(e)) return;
      e.preventDefault();
      pagesPanel.classList.add('dragover');
    });
    pagesPanel.addEventListener('dragleave', function (e) {
      if (!pagesPanel.contains(e.relatedTarget)) pagesPanel.classList.remove('dragover');
    });
    pagesPanel.addEventListener('drop', function (e) {
      pagesPanel.classList.remove('dragover');
      if (!isFileDrag(e)) return;
      e.preventDefault();
      handleFiles(e.dataTransfer.files);
    });

    document.addEventListener('paste', function (e) {
      if (e.clipboardData && e.clipboardData.files && e.clipboardData.files.length) {
        handleFiles(e.clipboardData.files);
      }
    });

    /* -- step 3: placement & fill -- */
    el.placeFit.addEventListener('click', function () { setPlacement('fit'); });
    el.placeFill.addEventListener('click', function () { setPlacement('fill'); });
    el.fillSelect.addEventListener('change', function () {
      state.fill = el.fillSelect.value;
      el.fillHint.textContent = FILL_HINTS[state.fill];
      updateSolidColorRow();
      refresh();
    });
    el.colorSwatchBtn.addEventListener('click', openColorPicker);
    el.colorFallbackInput.addEventListener('input', function () {
      state.customSolidColor = el.colorFallbackInput.value;
      updateSolidColorRow();
      refresh();
    });
    el.colorResetBtn.addEventListener('click', function () {
      state.customSolidColor = null;
      updateSolidColorRow();
      refresh();
    });

    /* -- step 4: format -- */
    el.fmtPng.addEventListener('click', function () { setFormat('png'); });
    el.fmtJpg.addEventListener('click', function () { setFormat('jpg'); });
    el.jpegQuality.addEventListener('input', function () {
      state.jpegQuality = parseInt(el.jpegQuality.value, 10) / 100;
      el.jpegQualityVal.textContent = el.jpegQuality.value + '%';
      updateSizeMeter();
    });

    /* -- per-page override -- */
    el.overrideSelect.addEventListener('change', function () {
      var item = selectedItem();
      if (!item) return;
      item.placement = el.overrideSelect.value;
      refresh();
    });

    /* -- tooltips -- */
    wirePopover('help1', 'pop1');
    wirePopover('help3', 'pop3');
    document.addEventListener('click', function () { closePopovers(null); });
    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') closePopovers(null);
    });

    /* -- preview toolbar -- */
    el.guidesToggle.addEventListener('change', function () {
      state.guides = el.guidesToggle.checked;
      schedulePreview();
    });
    el.btnBefore.addEventListener('click', function () { setDivider(100); });
    el.btnAfter.addEventListener('click', function () { setDivider(0); });

    /* -- compare divider -- */
    var dragging = false;
    el.handle.addEventListener('pointerdown', function (e) {
      dragging = true;
      if (el.handle.setPointerCapture) el.handle.setPointerCapture(e.pointerId);
      e.preventDefault();
    });
    el.handle.addEventListener('pointermove', function (e) {
      if (!dragging) return;
      setDivider(pointerToPct(e.clientX));
    });
    function endDrag(e) {
      if (!dragging) return;
      dragging = false;
      if (el.handle.releasePointerCapture && e.pointerId !== undefined) {
        try { el.handle.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
      }
    }
    el.handle.addEventListener('pointerup', endDrag);
    el.handle.addEventListener('pointercancel', endDrag);
    el.handle.addEventListener('keydown', function (e) {
      var p = state.dividerPct;
      if (e.key === 'ArrowLeft') { setDivider(p - 2); e.preventDefault(); }
      else if (e.key === 'ArrowRight') { setDivider(p + 2); e.preventDefault(); }
      else if (e.key === 'Home') { setDivider(0); e.preventDefault(); }
      else if (e.key === 'End') { setDivider(100); e.preventDefault(); }
    });

    /* -- export -- */
    el.downloadBtn.addEventListener('click', onDownloadClick);

    /* -- responsive re-render -- */
    window.addEventListener('resize', function () {
      clearTimeout(resizeDebounce);
      resizeDebounce = setTimeout(schedulePreview, 120);
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
