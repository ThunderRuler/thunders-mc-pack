/* ThundersMC Pack page: dither background, load wave, password-protected downloads, live player count.
   Downloads are AES-256-GCM encrypted files in dl/ (built by thunder-mc/tools/site/build_site.py);
   the password never leaves the browser. */
(function () {
  'use strict';
  var reduce = window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches;

  /* ------------------------------------------------------------------ dither */
  var CELL = 3;                                   // CSS pixels per dither cell
  var BAYER = [0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5].map(function (v) { return (v + 0.5) / 16; });
  var DOT = 0xFFCBCECE;                           // #cecece (little-endian ABGR): 20% less contrast than before
  var BOLT = 0xFFCDA08C;                          // lightning dots (#8ca0cd): an electric blue-grey, clearly stronger than the sky
  var SKY_MAX = 0.42, SKY_REACH = 0.78;           // night sky: dot density at the top, and how far down (fraction of the window) it fades to white
  var cv = document.getElementById('dither');
  var ctx = cv.getContext('2d');
  var W = 0, H = 0, noise, base, field, img, px;
  var mouse = { x: -999, y: -999 };
  var trail = [];                                 // recent pointer positions; each fades out over TRAIL_MS
  var TRAIL_MS = 1100, TRAIL_R = 40;
  var ripples = [];
  var bolts = [];                                 // lightning strikes for this page load (random every time)
  var t0 = performance.now();
  var demo = /^#demo/.test(location.hash);
  var front = (reduce || demo) ? 1e9 : -10;       // load wave position, in cells
  var WAVE_MS = 1700, STORM_MS = 5000;
  var running = false;

  function resize() {
    W = Math.max(1, Math.ceil((innerWidth || document.documentElement.clientWidth || 1) / CELL));
    H = Math.max(1, Math.ceil((innerHeight || document.documentElement.clientHeight || 1) / CELL));
    cv.width = W; cv.height = H;
    img = ctx.createImageData(W, H); px = new Uint32Array(img.data.buffer);
    noise = new Float32Array(W * H); base = new Float32Array(W * H); field = new Float32Array(W * H);
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
      // Slow clumps, so the star-field looks like cloud cover and not a flat gradient.
      var p = Math.sin(x * 0.045 + Math.sin(y * 0.03) * 2.2) * Math.cos(y * 0.038 - x * 0.012) * 0.5 + 0.5;
      var q = Math.sin((x + y) * 0.021) * 0.5 + 0.5;
      noise[y * W + x] = 0.55 * p + 0.45 * q * q;
    }
    if (!bolts.length && !reduce && !demo) planStorm();
    bolts.forEach(function (b) { b.mask = makeBolt(b); });
    kick();
  }

  // Night sky: densest at the top of the page, thinning out until it is plain white. Tied to the page, so it scrolls away.
  function computeBase() {
    var reach = innerHeight * SKY_REACH, sy = window.pageYOffset || 0;
    for (var y = 0; y < H; y++) {
      var t = 1 - (y * CELL + sy) / reach, row = y * W;
      if (t <= 0) { for (var x0 = 0; x0 < W; x0++) base[row + x0] = 0; continue; }
      var prof = SKY_MAX * Math.pow(t, 1.35);
      for (var x = 0; x < W; x++) base[row + x] = prof * (0.55 + 0.9 * noise[row + x]);
    }
  }

  /* Lightning: 2-4 strikes at random times in the first 5 seconds, each a different jagged bolt with branches. */
  function rand(a, b) { return a + Math.random() * (b - a); }
  function planStorm() {
    // ?strike=MS: one fixed strike starting at MS milliseconds (default 300), for checking the effect in screenshots
    var fixed = /[?&]strike(?:=(\d+))?/.exec(location.search);
    if (fixed) { bolts = [{ start: +fixed[1] || 300, dur: 900, seed: 12345, x: 0.68, mask: null }]; return; }
    var n = 2 + Math.floor(Math.random() * 3), times = [];
    for (var i = 0; i < n; i++) times.push(rand(700, STORM_MS - 600));
    times.sort(function (a, b) { return a - b; });
    for (var k = 1; k < times.length; k++) if (times[k] - times[k - 1] < 600) times[k] = times[k - 1] + 600;   // at least 600 ms apart
    bolts = times.map(function (t) {
      return { start: t, dur: rand(650, 950), seed: Math.floor(rand(1, 2e9)), x: rand(0.1, 0.9), mask: null };
    });
  }
  function makeBolt(b) {
    var seed = b.seed;
    function rnd() { seed = (seed * 16807) % 2147483647; return seed / 2147483647; }
    var out = [], acc = new Float32Array(W * H);
    var x = W * b.x, y = -2, pts = [[x, y]], bottom = H * rand(0.55, 0.95);
    while (y < bottom) { y += 5 + rnd() * 10; x += (rnd() - 0.5) * 24; pts.push([x, y]); }
    var paths = [pts];
    for (var br = 0; br < 2 + Math.floor(rnd() * 2); br++) {
      var from = pts[1 + Math.floor(rnd() * (pts.length - 2))], dir = rnd() < 0.5 ? -1 : 1, bp = [from.slice()];
      for (var i = 0; i < 5 + rnd() * 6; i++) { var last = bp[bp.length - 1]; bp.push([last[0] + dir * (3 + rnd() * 9), last[1] + 4 + rnd() * 8]); }
      paths.push(bp);
    }
    function stamp(path, core, glow, k) {
      for (var i = 1; i < path.length; i++) {
        var a = path[i - 1], c = path[i], n = Math.ceil(Math.hypot(c[0] - a[0], c[1] - a[1]));
        for (var s = 0; s <= n; s++) {
          var sx = a[0] + (c[0] - a[0]) * s / n, sy = a[1] + (c[1] - a[1]) * s / n;
          for (var yy = Math.floor(sy - glow); yy <= sy + glow; yy++) {
            if (yy < 0 || yy >= H) continue;
            for (var xx = Math.floor(sx - glow); xx <= sx + glow; xx++) {
              if (xx < 0 || xx >= W) continue;
              var d = Math.hypot(xx - sx, yy - sy);
              var v = k * (d < core ? 1 : Math.max(0, 0.32 * (1 - d / glow)));
              var j = yy * W + xx; if (v > acc[j]) acc[j] = v;
            }
          }
        }
      }
    }
    stamp(paths[0], 2.2, 14, 1);
    for (var q = 1; q < paths.length; q++) stamp(paths[q], 1.3, 8, 0.7);
    // a wide, faint halo lights up the sky around the strike
    var halo = 46;
    for (var h = 0; h < pts.length; h++) {
      var hx = pts[h][0], hy = pts[h][1];
      for (var yy2 = Math.max(0, Math.floor(hy - halo)); yy2 <= Math.min(H - 1, hy + halo); yy2++) {
        for (var xx2 = Math.max(0, Math.floor(hx - halo)); xx2 <= Math.min(W - 1, hx + halo); xx2++) {
          var dd = Math.hypot(xx2 - hx, yy2 - hy); if (dd >= halo) continue;
          var vv = 0.2 * (1 - dd / halo) * (1 - dd / halo), jj = yy2 * W + xx2;
          if (vv > acc[jj]) acc[jj] = vv;
        }
      }
    }
    for (var j2 = 0; j2 < acc.length; j2++) if (acc[j2] > 0.01) out.push(j2, acc[j2]);
    return out;
  }
  // Brightness over a strike's life: hard flash, dark gap, second flash, then a slow fade (like a real return stroke).
  function strike(u) {
    if (u < 0 || u > 1) return 0;
    if (u < 0.10) return 1;
    if (u < 0.18) return 0.1;
    if (u < 0.34) return 0.9;
    if (u < 0.42) return 0.25;
    if (u < 0.52) return 0.6;
    return Math.max(0, 1 - (u - 0.52) / 0.48) * 0.4;
  }

  // ring: an expanding ring (click ripple), added on top. Otherwise a soft round patch; with peak=true
  // overlapping patches don't stack (the strongest wins), so the mouse trail stays light.
  function addBlob(cx, cy, r, amp, ring, width, peak) {
    var R = ring ? r + width * 3 : r;
    var x0 = Math.max(0, Math.floor(cx - R)), x1 = Math.min(W - 1, Math.ceil(cx + R));
    var y0 = Math.max(0, Math.floor(cy - R)), y1 = Math.min(H - 1, Math.ceil(cy + R));
    for (var y = y0; y <= y1; y++) for (var x = x0; x <= x1; x++) {
      var d = Math.hypot(x - cx, y - cy), v;
      if (ring) { var k = (d - r) / width; v = amp * Math.exp(-k * k); }
      else { if (d >= r) continue; var f = 1 - (d * d) / (r * r); v = amp * f * f; }
      var j = y * W + x;
      if (peak) { if (base[j] + v > field[j]) field[j] = base[j] + v; } else field[j] += v;
    }
  }

  var strikeNow = 0;
  function frame(now) {
    var t = now - t0, busy = false;
    computeBase();
    field.set(base);

    // Load wave: rows above the front are drawn, a brighter band rides on the front.
    if (front < H + 30) {
      var e = Math.min(1, t / WAVE_MS); e = 1 - Math.pow(1 - e, 3);
      front = -10 + e * (H + 40); busy = true;
      revealUpTo(front * CELL);
    }
    // Lightning.
    strikeNow = 0;
    for (var s = 0; s < bolts.length; s++) {
      var bo = bolts[s], lvl = strike((t - bo.start) / bo.dur);
      if (t < bo.start + bo.dur) busy = true;
      if (lvl > 0 && bo.mask) {
        if (lvl > strikeNow) strikeNow = lvl;
        var m = bo.mask;
        for (var b = 0; b < m.length; b += 2) field[m[b]] += m[b + 1] * lvl * 0.9;
      }
    }

    // The whole night sky flashes with each strike.
    if (strikeNow > 0) for (var f = 0; f < field.length; f++) if (base[f] > 0) field[f] += base[f] * 0.8 * strikeNow;

    // Mouse: every recent pointer position leaves a soft patch of dither that shrinks and fades, so moving leaves a trail.
    for (var mi = trail.length - 1; mi >= 0; mi--) {
      var ma = (now - trail[mi].t) / TRAIL_MS;
      if (ma >= 1) { trail.splice(mi, 1); continue; }
      var life = 1 - ma;
      addBlob(trail[mi].x, trail[mi].y, TRAIL_R * (0.45 + 0.55 * life), 0.30 * life * life, false, 0, true);
      busy = true;
    }
    if (mouse.x > -900) addBlob(mouse.x, mouse.y, TRAIL_R, 0.30, false, 0, true);
    // Click ripples.
    for (var i = ripples.length - 1; i >= 0; i--) {
      var rp = ripples[i], age = (now - rp.t) / 900;
      if (age >= 1) { ripples.splice(i, 1); continue; }
      addBlob(rp.x, rp.y, 6 + age * rp.max, 0.55 * (1 - age), true, 3 + age * 4);
      busy = true;
    }

    clearText();
    var j = 0, frontRow = Math.floor(front);
    for (var y = 0; y < H; y++) {
      var by = (y & 3) * 4;
      if (y > frontRow) { for (var x0 = 0; x0 < W; x0++) px[j++] = 0; continue; }
      var band = frontRow - y < 6 && front < H + 30 ? 0.22 * (1 - (frontRow - y) / 6) : 0;
      for (var x = 0; x < W; x++, j++) {
        var v = field[j] + band;
        px[j] = v > BAYER[by + (x & 3)] ? (strikeNow > 0 && v > 0.62 ? BOLT : DOT) : 0;
      }
    }
    ctx.putImageData(img, 0, 0);
    if (busy) requestAnimationFrame(frame); else running = false;
  }

  // Keep text readable: no dither under elements marked data-clear, with a soft edge around them.
  var clearEls = document.querySelectorAll('[data-clear]');
  function clearText() {
    var PAD = 3, FADE = 6;
    for (var c = 0; c < clearEls.length; c++) {
      var r = clearEls[c].getBoundingClientRect();
      if (r.bottom < 0 || r.top > innerHeight || !r.width) continue;
      var l = r.left / CELL - PAD, rt = r.right / CELL + PAD, tp = r.top / CELL - PAD, bt = r.bottom / CELL + PAD;
      var x0 = Math.max(0, Math.floor(l - FADE)), x1 = Math.min(W - 1, Math.ceil(rt + FADE));
      var y0 = Math.max(0, Math.floor(tp - FADE)), y1 = Math.min(H - 1, Math.ceil(bt + FADE));
      for (var y = y0; y <= y1; y++) {
        var dy = y < tp ? tp - y : y > bt ? y - bt : 0;
        for (var x = x0; x <= x1; x++) {
          var dx = x < l ? l - x : x > rt ? x - rt : 0;
          var d = Math.max(dx, dy);
          if (d < FADE) field[y * W + x] *= d / FADE;
        }
      }
    }
  }

  function kick() { if (!running) { running = true; requestAnimationFrame(frame); } }

  addEventListener('resize', function () { clearTimeout(resize.t); resize.t = setTimeout(resize, 120); });
  addEventListener('pointermove', function (e) {
    if (reduce) return;
    mouse.x = e.clientX / CELL; mouse.y = e.clientY / CELL;
    var last = trail[trail.length - 1], now = performance.now();
    if (!last || Math.hypot(mouse.x - last.x, mouse.y - last.y) > 5 || now - last.t > 60) {
      trail.push({ x: mouse.x, y: mouse.y, t: now });
      if (trail.length > 48) trail.shift();
    }
    kick();
  }, { passive: true });
  document.addEventListener('pointerleave', function () { mouse.x = mouse.y = -999; kick(); });
  addEventListener('scroll', kick, { passive: true });
  // Text can move when fonts or images arrive; redraw so the clear areas follow it.
  addEventListener('load', kick);
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(kick);

  function ripple(el, ev) {
    if (reduce) return;
    var x, y;
    if (ev && (ev.clientX || ev.clientY)) { x = ev.clientX; y = ev.clientY; }
    else { var r = el.getBoundingClientRect(); x = r.left + r.width / 2; y = r.top + r.height / 2; }
    ripples.push({ x: x / CELL, y: y / CELL, t: performance.now(), max: Math.max(W, H) * 0.45 });
    kick();
  }
  // A click anywhere ripples through the dither (keyboard "clicks" ripple from the element's centre).
  document.addEventListener('click', function (e) {
    ripple(e.target.closest ? (e.target.closest('button, a, input') || document.body) : document.body, e);
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

  /* Prism's /download page always opens on Windows, so link straight to the visitor's own OS page. */
  (function () {
    var a = document.getElementById('prism-link');
    if (!a) return;
    var ua = (navigator.userAgentData && navigator.userAgentData.platform) || navigator.platform || '';
    var all = ua + ' ' + navigator.userAgent;
    var os = /Mac|iPhone|iPad/i.test(all) && !/Windows/i.test(all) ? 'macos' : /Linux|X11/i.test(all) && !/Android/i.test(all) ? 'linux' : 'windows';
    a.href = 'https://prismlauncher.org/download/' + os + '/';
  })();

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

  // #demo-hero / #demo-mac / #demo-win[-typed|-done] only show the password box in a given state (used to make the step 2 pictures).
  var dm = /^#demo-(mac|win|hero)(-typed|-done)?$/.exec(location.hash);
  if (dm && dm[1] === 'hero') {
    front = 1e9; pending.forEach(function (el) { el.classList.add('in'); }); pending = []; kick();
  } else if (dm) {
    front = 1e9; pending.forEach(function (el) { el.classList.add('in'); }); pending = []; kick();
    platform = dm[1] === 'mac' ? 'mac' : 'windows'; form.hidden = false; form.setAttribute('data-platform', platform);
    label.textContent = 'Password for the ' + NAMES[platform] + ' download';
    document.querySelector('[data-platform="' + platform + '"]').setAttribute('aria-pressed', 'true');
    if (dm[2]) pw.value = 'creeper-obsidian-emerald16';
    if (dm[2] === '-done') {
      pw.value = '';
      document.querySelector('.unlock-row').hidden = true;
      label.textContent = NAMES[platform] + ' download';
      say('Saved ' + (platform === 'mac' ? 'Thunders-MC-Pack-26.3-Mac.zip' : 'Thunders-MC-Pack-26.3.zip') + '. Next: import it into Prism (step 3 below).', 'ok');
    }
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
