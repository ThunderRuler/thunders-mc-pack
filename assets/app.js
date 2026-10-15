/* ThundersMC Pack page: dither background, load wave, password-protected downloads, live player count.
   Downloads are AES-256-GCM encrypted files in dl/ (built by thunder-mc/tools/site/build_site.py);
   the password never leaves the browser. */
(function () {
  'use strict';
  var reduce = window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches;

  /* ------------------------------------------------------------------ dither */
  var CELL = 3;                                   // CSS pixels per dither cell
  var BAYER = [0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5].map(function (v) { return (v + 0.5) / 16; });
  var DOT = 0xFFC1C4C4;                           // #c4c4c1 as little-endian ABGR
  var BOLT = 0xFFB4B6B9;                          // a touch darker for the lightning
  var cv = document.getElementById('dither');
  var ctx = cv.getContext('2d');
  var W = 0, H = 0, base, field, boltMask, img, px;
  var mouse = { x: -999, y: -999, tx: -999, ty: -999, amp: 0, moved: 0 };
  var ripples = [];
  var flash = 0, t0 = performance.now();
  var front = reduce ? 1e9 : -10;                 // load wave position, in cells
  var WAVE_MS = 1700, BOLT_AT = 450;
  var running = false;

  function resize() {
    W = Math.max(1, Math.ceil((innerWidth || document.documentElement.clientWidth || 1) / CELL));
    H = Math.max(1, Math.ceil((innerHeight || document.documentElement.clientHeight || 1) / CELL));
    cv.width = W; cv.height = H;
    img = ctx.createImageData(W, H); px = new Uint32Array(img.data.buffer);
    base = new Float32Array(W * H); field = new Float32Array(W * H);
    var cx = W / 2, cy = H * 0.42;
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
      // Soft rolling bands of denser and lighter dither, lighter in the middle where the content sits.
      var p = Math.sin(x * 0.045 + Math.sin(y * 0.03) * 2.2) * Math.cos(y * 0.038 - x * 0.012) * 0.5 + 0.5;
      var q = Math.sin((x + y) * 0.021) * 0.5 + 0.5;
      var dx = (x - cx) / W, dy = (y - cy) / H;
      var edge = Math.min(1, Math.sqrt(dx * dx * 1.6 + dy * dy) * 1.9);
      base[y * W + x] = 0.03 + (0.10 + 0.20 * edge) * (0.55 * p + 0.45 * q * q);
    }
    makeBolt();
    kick();
  }

  function makeBolt() {
    boltMask = [];
    var seed = 7;
    function rnd() { seed = (seed * 16807) % 2147483647; return seed / 2147483647; }
    var x = W * (0.62 + rnd() * 0.2), y = -2, pts = [[x, y]];
    while (y < H * 0.95) { y += 6 + rnd() * 10; x += (rnd() - 0.5) * 22; pts.push([x, y]); }
    var branch = [pts[Math.floor(pts.length * 0.35)].slice()];
    for (var i = 0; i < 9; i++) { var b = branch[branch.length - 1]; branch.push([b[0] - 4 - rnd() * 9, b[1] + 5 + rnd() * 8]); }
    var acc = new Float32Array(W * H);
    function stamp(path, wCore, wGlow, k) {
      for (var i = 1; i < path.length; i++) {
        var a = path[i - 1], b = path[i], n = Math.ceil(Math.hypot(b[0] - a[0], b[1] - a[1]));
        for (var s = 0; s <= n; s++) {
          var sx = a[0] + (b[0] - a[0]) * s / n, sy = a[1] + (b[1] - a[1]) * s / n;
          for (var yy = Math.floor(sy - wGlow); yy <= sy + wGlow; yy++) {
            if (yy < 0 || yy >= H) continue;
            for (var xx = Math.floor(sx - wGlow); xx <= sx + wGlow; xx++) {
              if (xx < 0 || xx >= W) continue;
              var d = Math.hypot(xx - sx, yy - sy);
              var v = k * (d < wCore ? 1 : Math.max(0, 0.35 * (1 - d / wGlow)));
              var j = yy * W + xx; if (v > acc[j]) acc[j] = v;
            }
          }
        }
      }
    }
    stamp(pts, 1.6, 12, 1); stamp(branch, 1.1, 8, 0.7);
    for (var j = 0; j < acc.length; j++) if (acc[j] > 0.01) boltMask.push(j, acc[j]);
  }

  function addBlob(cx, cy, r, amp, ring, width) {
    var R = ring ? r + width * 3 : r * 2.2;
    var x0 = Math.max(0, Math.floor(cx - R)), x1 = Math.min(W - 1, Math.ceil(cx + R));
    var y0 = Math.max(0, Math.floor(cy - R)), y1 = Math.min(H - 1, Math.ceil(cy + R));
    for (var y = y0; y <= y1; y++) for (var x = x0; x <= x1; x++) {
      var d = Math.hypot(x - cx, y - cy), v;
      if (ring) { var k = (d - r) / width; v = amp * Math.exp(-k * k); }
      else v = amp * Math.exp(-(d * d) / (r * r));
      field[y * W + x] += v;
    }
  }

  function frame(now) {
    var t = now - t0, busy = false;
    field.set(base);

    // Load wave: rows above the front are drawn, a brighter band rides on the front.
    if (front < H + 30) {
      var e = Math.min(1, t / WAVE_MS); e = 1 - Math.pow(1 - e, 3);
      front = -10 + e * (H + 40); busy = true;
      revealUpTo(front * CELL);
    }
    // Lightning: a faint flicker through the dither shortly after load.
    if (!reduce && t > BOLT_AT && t < BOLT_AT + 1300) {
      var u = (t - BOLT_AT) / 1300;
      flash = 0.42 * (u < 0.06 ? 1 : u < 0.12 ? 0.25 : u < 0.2 ? 0.8 : Math.max(0, 1 - u) * 0.7);
      busy = true;
    } else flash = 0;
    if (flash > 0) for (var b = 0; b < boltMask.length; b += 2) field[boltMask[b]] += boltMask[b + 1] * flash;

    // Mouse: dither thickens around the pointer, eases back when it stops.
    if (mouse.tx > -900) {
      mouse.x += (mouse.tx - mouse.x) * 0.25; mouse.y += (mouse.ty - mouse.y) * 0.25;
      var target = now - mouse.moved < 140 ? 1 : 0.35;
      mouse.amp += (target - mouse.amp) * 0.08;
      addBlob(mouse.x, mouse.y, 20, 0.26 * mouse.amp, false);
      if (Math.abs(target - mouse.amp) > 0.01 || Math.abs(mouse.tx - mouse.x) > 0.3 || Math.abs(mouse.ty - mouse.y) > 0.3) busy = true;
    }
    // Click ripples.
    for (var i = ripples.length - 1; i >= 0; i--) {
      var rp = ripples[i], age = (now - rp.t) / 900;
      if (age >= 1) { ripples.splice(i, 1); continue; }
      addBlob(rp.x, rp.y, 6 + age * rp.max, 0.55 * (1 - age), true, 3 + age * 4);
      busy = true;
    }

    var j = 0, frontRow = Math.floor(front);
    for (var y = 0; y < H; y++) {
      var by = (y & 3) * 4;
      if (y > frontRow) { for (var x0 = 0; x0 < W; x0++) px[j++] = 0; continue; }
      var band = frontRow - y < 6 && front < H + 30 ? 0.35 * (1 - (frontRow - y) / 6) : 0;
      for (var x = 0; x < W; x++, j++) {
        var v = field[j] + band;
        px[j] = v > BAYER[by + (x & 3)] ? (flash > 0 && v > 0.55 ? BOLT : DOT) : 0;
      }
    }
    ctx.putImageData(img, 0, 0);
    if (busy) requestAnimationFrame(frame); else running = false;
  }

  function kick() { if (!running) { running = true; requestAnimationFrame(frame); } }

  addEventListener('resize', function () { clearTimeout(resize.t); resize.t = setTimeout(resize, 120); });
  addEventListener('pointermove', function (e) {
    if (reduce) return;
    mouse.tx = e.clientX / CELL; mouse.ty = e.clientY / CELL; mouse.moved = performance.now();
    if (mouse.x < -900) { mouse.x = mouse.tx; mouse.y = mouse.ty; }
    kick();
  }, { passive: true });
  document.addEventListener('pointerleave', function () { mouse.tx = mouse.ty = -999; mouse.x = mouse.y = -999; kick(); });

  function ripple(el, ev) {
    if (reduce) return;
    var x, y;
    if (ev && ev.clientX) { x = ev.clientX; y = ev.clientY; }
    else { var r = el.getBoundingClientRect(); x = r.left + r.width / 2; y = r.top + r.height / 2; }
    ripples.push({ x: x / CELL, y: y / CELL, t: performance.now(), max: Math.max(W, H) * 0.45 });
    kick();
  }
  document.addEventListener('click', function (e) {
    var el = e.target.closest && e.target.closest('[data-ripple]');
    if (el) ripple(el, e);
  });

  /* ------------------------------------------------------------ load reveal */
  var pending = Array.prototype.slice.call(document.querySelectorAll('[data-reveal]'));
  function revealUpTo(yPx) {
    for (var i = pending.length - 1; i >= 0; i--) {
      var top = pending[i].getBoundingClientRect().top;
      if (top < yPx) { pending[i].classList.add('in'); pending.splice(i, 1); }
      else if (top > innerHeight) watch(pending.splice(i, 1)[0]);
    }
  }
  var io = 'IntersectionObserver' in window ? new IntersectionObserver(function (es) {
    es.forEach(function (en) { if (en.isIntersecting) { en.target.classList.add('in'); io.unobserve(en.target); } });
  }, { rootMargin: '0px 0px -8% 0px' }) : null;
  function watch(el) { if (io) io.observe(el); else el.classList.add('in'); }
  if (reduce) pending.forEach(function (el) { el.classList.add('in'); });

  // The background is decoration: if it fails, the downloads below must still work.
  try { resize(); } catch (err) { pending.forEach(function (el) { el.classList.add('in'); }); }

  /* ------------------------------------------------------------- downloads */
  var form = document.getElementById('unlock'), pw = document.getElementById('pw');
  var label = document.getElementById('pw-label'), msg = document.getElementById('unlock-msg');
  var NAMES = { mac: 'macOS', windows: 'Windows' };
  var platform = null, key = null, address = null, meta = null;

  function say(text, cls) { msg.textContent = text; msg.className = 'unlock-msg' + (cls ? ' ' + cls : ''); }

  document.querySelectorAll('[data-platform]').forEach(function (btn) {
    btn.addEventListener('click', function () {
      platform = btn.getAttribute('data-platform');
      document.querySelectorAll('[data-platform]').forEach(function (b) { b.setAttribute('aria-pressed', String(b === btn)); });
      if (key) { download(); return; }
      form.hidden = false; form.setAttribute('data-platform', platform);
      label.textContent = 'Password for the ' + NAMES[platform] + ' download';
      say('');
      pw.focus();
    });
  });

  // #demo opens the password box without unlocking anything (used for the step 2 screenshot).
  if (location.hash === '#demo') {
    front = 1e9; pending.forEach(function (el) { el.classList.add('in'); }); pending = []; kick();
    platform = 'windows'; form.hidden = false; form.setAttribute('data-platform', platform);
    label.textContent = 'Password for the Windows download'; pw.value = 'password';
    document.querySelector('[data-platform="windows"]').setAttribute('aria-pressed', 'true');
  }

  function bytes(r) { if (!r.ok) throw new Error('HTTP ' + r.status); return r.arrayBuffer(); }
  function b64(s) { return Uint8Array.from(atob(s), function (c) { return c.charCodeAt(0); }); }
  function decrypt(buf) {
    var u = new Uint8Array(buf);
    return crypto.subtle.decrypt({ name: 'AES-GCM', iv: u.slice(0, 12) }, key, u.slice(12));
  }

  form.addEventListener('submit', function (e) {
    e.preventDefault();
    if (!window.crypto || !crypto.subtle) { say('This browser can\'t unlock the download. Try Chrome, Edge, Safari or Firefox.', 'err'); return; }
    say('Unlocking...');
    (meta ? Promise.resolve(meta) : fetch('dl/meta.json', { cache: 'no-cache' }).then(function (r) { return r.json(); }))
      .then(function (m) {
        meta = m;
        return crypto.subtle.importKey('raw', new TextEncoder().encode(pw.value), 'PBKDF2', false, ['deriveKey'])
          .then(function (raw) {
            return crypto.subtle.deriveKey({ name: 'PBKDF2', hash: 'SHA-256', salt: b64(m.salt), iterations: m.iterations },
              raw, { name: 'AES-GCM', length: 256 }, false, ['decrypt']);
          });
      })
      .then(function (k) { key = k; return fetch('dl/server.bin', { cache: 'no-cache' }).then(bytes); })
      .then(decrypt)
      .then(function (plain) {
        address = JSON.parse(new TextDecoder().decode(plain)).address;
        pw.value = '';
        startOnline();
        return download();
      })
      .catch(function (err) {
        key = null;
        say(err && err.name === 'OperationError' ? 'Wrong password. Ask Thunder for it.' : 'Couldn\'t unlock: ' + (err && err.message || err), 'err');
        ripple(form);
      });
  });

  function download() {
    var info = meta.files[platform];
    form.hidden = false; form.setAttribute('data-platform', platform);
    label.textContent = NAMES[platform] + ' download';
    say('Downloading ' + info.name + '...');
    return fetch('dl/' + platform + '.bin', { cache: 'no-cache' }).then(bytes).then(decrypt).then(function (plain) {
      var url = URL.createObjectURL(new Blob([plain], { type: 'application/zip' }));
      var a = document.createElement('a'); a.href = url; a.download = info.name;
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(function () { URL.revokeObjectURL(url); }, 60000);
      say('Saved ' + info.name + '. Next: import it into Prism (step 3 below).', 'ok');
      document.querySelector('.unlock-row').hidden = true;
      ripple(document.querySelector('[data-platform="' + platform + '"]'));
    }).catch(function (err) { say('Download failed: ' + (err && err.message || err) + '. Try again.', 'err'); });
  }

  /* --------------------------------------------------------- player count */
  var onlineEl = document.getElementById('online'), onlineText = document.getElementById('online-text');
  function startOnline() { if (!startOnline.on) { startOnline.on = true; poll(); setInterval(poll, 60000); } }
  function poll() {
    fetch('https://api.mcsrvstat.us/3/' + encodeURIComponent(address))
      .then(function (r) { return r.json(); })
      .then(function (s) {
        if (!s.online) { onlineEl.classList.remove('live'); onlineText.textContent = 'Server is offline right now'; return; }
        var n = s.players ? s.players.online : 0, names = (s.players && s.players.list || []).map(function (p) { return p.name; });
        onlineEl.classList.add('live');
        onlineText.textContent = n === 0 ? 'Nobody online right now' :
          n + ' online now' + (names.length ? ': ' + names.join(', ') : '');
      })
      .catch(function () { onlineText.textContent = 'Couldn\'t check who\'s online'; });
  }
})();
