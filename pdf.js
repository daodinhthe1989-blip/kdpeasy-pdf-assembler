/* ================================================================
   KDPEasy PDF Assembler — pdf.js
   A hand-rolled minimal PDF 1.4 writer for exactly one job: one image
   per page, no text, no fonts. Same idea as img2pdf — wrap image bytes
   that are already encoded in the smallest valid PDF container, and
   never touch the pixels.

   Classic script (no modules) so it runs from file://. Exposes
   window.KDPPdf, used by app.js.
   ================================================================ */
(function (root) {
  'use strict';

  /* ---- 1. SMALL HELPERS ---- */

  function ascii(s) {
    var u = new Uint8Array(s.length);
    for (var i = 0; i < s.length; i++) u[i] = s.charCodeAt(i) & 0xFF;
    return u;
  }

  // PDF real number: at most 4 decimals, no trailing zeros, no "-0".
  // toFixed(4) always has a '.', so the regex only ever strips decimals.
  function num(n) {
    if (Math.abs(n) < 0.00005) return '0';
    return n.toFixed(4).replace(/\.?0+$/, '');
  }

  function pad10(n) {
    var s = String(n);
    while (s.length < 10) s = '0' + s;
    return s;
  }

  function hex2(n) { return (n < 16 ? '0' : '') + n.toString(16); }

  /* ---- 2. JPEG HEADER ---- */

  // Reads just enough of a JPEG to embed it as /DCTDecode: size, component
  // count, and whether an Adobe APP14 marker is present (CMYK JPEGs written
  // by Adobe apps store inverted values). Returns null if not a JPEG.
  // `supported` is false for arithmetic-coded / lossless / hierarchical
  // JPEGs, which PDF readers don't reliably decode.
  function parseJpeg(bytes) {
    var len = bytes.length;
    if (len < 4 || bytes[0] !== 0xFF || bytes[1] !== 0xD8) return null;
    var i = 2, adobe = false;
    while (i + 4 <= len) {
      if (bytes[i] !== 0xFF) return null;
      var m = bytes[i + 1];
      if (m === 0xFF) { i++; continue; }                               // fill byte
      if (m === 0x01 || (m >= 0xD0 && m <= 0xD8)) { i += 2; continue; } // no length
      var size = (bytes[i + 2] << 8) | bytes[i + 3];
      if (m === 0xEE && i + 9 <= len &&
          bytes[i + 4] === 0x41 && bytes[i + 5] === 0x64 && bytes[i + 6] === 0x6F &&
          bytes[i + 7] === 0x62 && bytes[i + 8] === 0x65) {             // "Adobe"
        adobe = true;
      }
      if (m >= 0xC0 && m <= 0xCF && m !== 0xC4 && m !== 0xC8 && m !== 0xCC) {
        if (i + 10 > len) return null;
        return {
          width: (bytes[i + 7] << 8) | bytes[i + 8],
          height: (bytes[i + 5] << 8) | bytes[i + 6],
          bits: bytes[i + 4],
          components: bytes[i + 9],
          adobe: adobe,
          // baseline, extended sequential, progressive — all DCTDecode-safe
          supported: (m === 0xC0 || m === 0xC1 || m === 0xC2) && bytes[i + 4] === 8 &&
                     (bytes[i + 9] === 1 || bytes[i + 9] === 3 || bytes[i + 9] === 4)
        };
      }
      if (m === 0xDA) return null;                                      // scan before SOF
      i += 2 + size;
    }
    return null;
  }

  /* ---- 3. PNG HEADER ---- */

  // Walks the PNG chunk list. Records where every IDAT's data lives in the
  // file so a compatible PNG can be embedded with its compressed data passed
  // straight through (/FlateDecode + PNG predictors — exactly what IDAT is).
  // PNGs with alpha, transparency, interlacing, 16-bit samples or an eXIf
  // orientation can't be passed through and take the decode-and-repack path.
  function parsePng(bytes) {
    var len = bytes.length;
    var sig = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];
    if (len < 33) return null;
    for (var s = 0; s < 8; s++) if (bytes[s] !== sig[s]) return null;

    var info = {
      width: 0, height: 0, bitDepth: 0, colorType: 0, interlace: 0,
      palette: null, hasTrns: false, hasExif: false, idat: [], idatBytes: 0
    };
    var p = 8;
    while (p + 8 <= len) {
      var clen = ((bytes[p] << 24) >>> 0) + (bytes[p + 1] << 16) + (bytes[p + 2] << 8) + bytes[p + 3];
      var type = String.fromCharCode(bytes[p + 4], bytes[p + 5], bytes[p + 6], bytes[p + 7]);
      var d = p + 8;
      if (d + clen > len) break;                                        // truncated
      if (type === 'IHDR') {
        info.width = ((bytes[d] << 24) >>> 0) + (bytes[d + 1] << 16) + (bytes[d + 2] << 8) + bytes[d + 3];
        info.height = ((bytes[d + 4] << 24) >>> 0) + (bytes[d + 5] << 16) + (bytes[d + 6] << 8) + bytes[d + 7];
        info.bitDepth = bytes[d + 8];
        info.colorType = bytes[d + 9];
        info.interlace = bytes[d + 12];
      } else if (type === 'PLTE') {
        info.palette = bytes.slice(d, d + clen);
      } else if (type === 'tRNS') {
        info.hasTrns = true;
      } else if (type === 'eXIf') {
        info.hasExif = true;
      } else if (type === 'IDAT') {
        info.idat.push([d, d + clen]);
        info.idatBytes += clen;
      } else if (type === 'IEND') {
        break;
      }
      p = d + clen + 4;                                                 // + CRC
    }
    if (!info.width || !info.height || !info.idat.length) return null;

    var ct = info.colorType, bd = info.bitDepth;
    var lowDepth = bd === 1 || bd === 2 || bd === 4 || bd === 8;
    info.passthrough = info.interlace === 0 && !info.hasTrns && !info.hasExif && (
      (ct === 0 && lowDepth) ||
      (ct === 2 && bd === 8) ||
      (ct === 3 && lowDepth && !!info.palette));
    return info;
  }

  /* ---- 4. LOSSLESS PIXEL REPACK ---- */

  // RGBA (from a canvas, already composited on white — every print page is
  // opaque) -> PNG-filtered rows -> zlib deflate. Pages whose pixels are all
  // neutral gray (most line art) are stored as 1-channel DeviceGray: the
  // same pixels, a third of the data.
  // Returns a Promise of { blob, colors, predictor } — predictor is false
  // when CompressionStream is unavailable and the raw bytes are stored
  // unfiltered (valid PDF, just bigger; quality never degrades).
  function packPixels(rgba, w, h) {
    var n = w * h, i, gray = true;
    for (i = 0; i < n * 4; i += 4) {
      if (rgba[i] !== rgba[i + 1] || rgba[i] !== rgba[i + 2]) { gray = false; break; }
    }
    var colors = gray ? 1 : 3;
    var canDeflate = typeof root.CompressionStream === 'function';
    var rowLen = w * colors;

    if (!canDeflate) {
      var raw = new Uint8Array(n * colors);
      for (i = 0; i < n; i++) {
        if (gray) raw[i] = rgba[i * 4];
        else { raw[i * 3] = rgba[i * 4]; raw[i * 3 + 1] = rgba[i * 4 + 1]; raw[i * 3 + 2] = rgba[i * 4 + 2]; }
      }
      return Promise.resolve({ blob: new Blob([raw]), colors: colors, predictor: false });
    }

    // Paeth on every row: a good general-purpose PNG filter for both flat
    // line art and photographic pages.
    var out = new Uint8Array(h * (rowLen + 1));
    var prev = new Uint8Array(rowLen), cur = new Uint8Array(rowLen);
    for (var y = 0; y < h; y++) {
      var base = y * w * 4;
      if (gray) {
        for (var x = 0; x < w; x++) cur[x] = rgba[base + x * 4];
      } else {
        for (var x2 = 0, k = 0; x2 < w; x2++, k += 3) {
          var s4 = base + x2 * 4;
          cur[k] = rgba[s4]; cur[k + 1] = rgba[s4 + 1]; cur[k + 2] = rgba[s4 + 2];
        }
      }
      var o = y * (rowLen + 1);
      out[o] = 4;                                                       // Paeth
      for (var j = 0; j < rowLen; j++) {
        var a = j >= colors ? cur[j - colors] : 0;
        var b = prev[j];
        var c = j >= colors ? prev[j - colors] : 0;
        var pp = a + b - c;
        var pa = pp > a ? pp - a : a - pp;
        var pb = pp > b ? pp - b : b - pp;
        var pc = pp > c ? pp - c : c - pp;
        var pred = (pa <= pb && pa <= pc) ? a : (pb <= pc ? b : c);
        out[o + 1 + j] = (cur[j] - pred) & 0xFF;
      }
      var t = prev; prev = cur; cur = t;
    }

    var cs = new root.CompressionStream('deflate');                     // zlib = FlateDecode
    var writer = cs.writable.getWriter();
    writer.write(out);
    writer.close();
    return new Response(cs.readable).blob().then(function (blob) {
      return { blob: blob, colors: colors, predictor: true };
    });
  }

  /* ---- 5. IMAGE PLACEMENT MATRIX ---- */

  // PDF draws an image into the unit square. This returns the `cm` matrix
  // that maps it onto the upright rectangle (x, y, w, h) in page points
  // (y measured from the bottom), undoing a JPEG's EXIF orientation 1..8 as
  // pure page geometry — the embedded bytes stay exactly as they were.
  function placementMatrix(x, y, w, h, orientation) {
    switch (orientation) {
      case 2: return [-w, 0, 0, h, x + w, y];
      case 3: return [-w, 0, 0, -h, x + w, y + h];
      case 4: return [w, 0, 0, -h, x, y + h];
      case 5: return [0, -h, -w, 0, x + w, y + h];
      case 6: return [0, -h, w, 0, x, y + h];
      case 7: return [0, h, w, 0, x, y];
      case 8: return [0, h, -w, 0, x + w, y];
      default: return [w, 0, 0, h, x, y];
    }
  }

  /* ---- 6. THE WRITER ---- */

  // Parts may be Uint8Arrays or Blobs (including File objects and file
  // slices) — a JPEG that is embedded as-is is never even read into memory,
  // the browser streams it from disk straight into the final Blob.
  function PdfWriter() {
    this.parts = [];
    this.offset = 0;
    this.xref = [];              // object number -> byte offset
    this.nextId = 3;             // 1 = Catalog, 2 = Pages
    this.kids = [];
    this.push(ascii('%PDF-1.4\n%\xE2\xE3\xCF\xD3\n'));
  }

  PdfWriter.prototype.push = function (part) {
    this.parts.push(part);
    this.offset += (part instanceof Uint8Array) ? part.length : part.size;
  };

  PdfWriter.prototype.obj = function (id, body) {
    this.xref[id] = this.offset;
    this.push(ascii(id + ' 0 obj\n' + body + '\nendobj\n'));
  };

  PdfWriter.prototype.stream = function (id, dict, dataParts, length) {
    this.xref[id] = this.offset;
    this.push(ascii(id + ' 0 obj\n<< ' + dict + ' /Length ' + length + ' >>\nstream\n'));
    for (var i = 0; i < dataParts.length; i++) this.push(dataParts[i]);
    this.push(ascii('\nendstream\nendobj\n'));
  };

  /*
   * Adds one page holding one image.
   *   page:  { width, height }            page size in points (the MediaBox)
   *   image: { width, height,             stored sample size
   *            colorSpace,                'DeviceRGB' | 'DeviceGray' | 'DeviceCMYK' | 'Indexed'
   *            palette,                   Uint8Array (Indexed only)
   *            bits,                      bits per component
   *            filter,                    'DCTDecode' | 'FlateDecode' | null
   *            predictorColors,           set -> /DecodeParms PNG predictor
   *            invertCmyk,                Adobe CMYK JPEG
   *            parts, length }            the encoded bytes
   *   matrix: [a b c d e f]               from placementMatrix()
   */
  PdfWriter.prototype.addImagePage = function (page, image, matrix) {
    var imgId = this.nextId++, contentId = this.nextId++, pageId = this.nextId++;

    var cs;
    if (image.colorSpace === 'Indexed') {
      var pal = image.palette, hex = '';
      for (var i = 0; i < pal.length; i++) hex += hex2(pal[i]);
      cs = '[/Indexed /DeviceRGB ' + (pal.length / 3 - 1) + ' <' + hex + '>]';
    } else {
      cs = '/' + image.colorSpace;
    }
    var dict = '/Type /XObject /Subtype /Image /Width ' + image.width +
      ' /Height ' + image.height + ' /ColorSpace ' + cs +
      ' /BitsPerComponent ' + image.bits;
    if (image.filter) dict += ' /Filter /' + image.filter;
    if (image.predictorColors) {
      dict += ' /DecodeParms << /Predictor 15 /Colors ' + image.predictorColors +
        ' /BitsPerComponent ' + image.bits + ' /Columns ' + image.width + ' >>';
    }
    if (image.invertCmyk) dict += ' /Decode [1 0 1 0 1 0 1 0]';
    this.stream(imgId, dict, image.parts, image.length);

    var content = ascii('q\n' + matrix.map(num).join(' ') + ' cm\n/Im0 Do\nQ\n');
    this.stream(contentId, '', [content], content.length);

    this.obj(pageId, '<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ' +
      num(page.width) + ' ' + num(page.height) + '] /Resources << /XObject << /Im0 ' +
      imgId + ' 0 R >> >> /Contents ' + contentId + ' 0 R >>');
    this.kids.push(pageId);
  };

  PdfWriter.prototype.finish = function () {
    this.obj(1, '<< /Type /Catalog /Pages 2 0 R >>');
    this.obj(2, '<< /Type /Pages /Kids [' +
      this.kids.map(function (k) { return k + ' 0 R'; }).join(' ') +
      '] /Count ' + this.kids.length + ' >>');

    var size = this.nextId;
    var xrefAt = this.offset;
    var x = 'xref\n0 ' + size + '\n0000000000 65535 f \n';
    for (var id = 1; id < size; id++) x += pad10(this.xref[id]) + ' 00000 n \n';
    x += 'trailer\n<< /Size ' + size + ' /Root 1 0 R >>\nstartxref\n' + xrefAt + '\n%%EOF\n';
    this.push(ascii(x));
    return new Blob(this.parts, { type: 'application/pdf' });
  };

  root.KDPPdf = {
    parseJpeg: parseJpeg,
    parsePng: parsePng,
    packPixels: packPixels,
    placementMatrix: placementMatrix,
    PdfWriter: PdfWriter,
    fmtNum: num
  };

})(window);
