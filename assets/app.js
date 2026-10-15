/* ThundersMC Pack page: dither background, load wave, password-protected downloads, live player count.
   Downloads are AES-256-GCM encrypted files in dl/ (built by thunder-mc/tools/site/build_site.py);
   the password never leaves the browser. */
(function () {
  'use strict';
  var reduce = window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches;

  /* ------------------------------------------------------------------ dither */
  var CELL = 2;                                   // CSS pixels per dither cell (fine grain)
  var K = 3 / CELL;                               // effect sizes below were tuned for 3 px cells; K keeps them the same size on screen
  // 8x8 ordered-dither matrix: 64 grey levels, so gradients and cloud shading look smooth instead of banded.
  var BAYER = (function () {
    var m = [0, 2, 3, 1], n = 2;
    while (n < 8) {
      var o = [], N = n * 2;
      for (var y = 0; y < N; y++) for (var x = 0; x < N; x++) {
        var q = (y >= n ? 2 : 0) + (x >= n ? 1 : 0);
        o.push(4 * m[(y % n) * n + (x % n)] + [0, 2, 3, 1][q]);
      }
      m = o; n = N;
    }
    return m.map(function (v) { return (v + 0.5) / 64; });
  })();
  // Smooth random noise (value noise, several octaves): used for the sky haze and the cloud shapes.
  function hash(x, y, s) {
    var h = Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(s, 1442695041) | 0;
    h = Math.imul(h ^ (h >>> 15), 0x85ebca6b);   // thorough mixing, so no stripes or grids show up in the noise
    h = Math.imul(h ^ (h >>> 13), 0xc2b2ae35);
    return ((h ^ (h >>> 16)) >>> 0) / 4294967296;
  }
  function vnoise(x, y, s) {
    var xi = Math.floor(x), yi = Math.floor(y), fx = x - xi, fy = y - yi;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
    var a = hash(xi, yi, s), b = hash(xi + 1, yi, s), c = hash(xi, yi + 1, s), d = hash(xi + 1, yi + 1, s);
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }
  function fbm(x, y, s) {
    var v = 0, amp = 0.5, f = 1;
    for (var o = 0; o < 4; o++) { v += amp * vnoise(x * f, y * f, s + o * 17); f *= 2.03; amp *= 0.5; }
    return v / 0.9375;
  }
  function smooth(a, b, x) { var u = Math.max(0, Math.min(1, (x - a) / (b - a))); return u * u * (3 - 2 * u); }
  // Colours. Light mode: a blue daytime sky on white; clouds are white with grey-blue shadows.
  // Dark mode: dusk, just after the sun has set. The sky runs from deep indigo at the top through violet and rose
  // to a warm orange glow low down; clouds have dusky lavender tops and undersides lit pink-orange by the sun below the horizon.
  function rgb(hex) { var n = parseInt(hex.slice(1), 16); return [n >> 16, (n >> 8) & 255, n & 255]; }
  function pack(c) { return (0xFF000000 | (c[2] << 16) | (c[1] << 8) | c[0]) >>> 0; }   // canvas pixels are little-endian ABGR
  var LIGHT = { sky: ['#b4d0ed'], bolt: '#8ca0cd', cloud: null, shade: '#c6d3e2', flash: 0.6, flat: false };
  var DARK = { sky: ['#252a5e', '#4b3a7c', '#8a4a82', '#c8607a', '#e88a5c'], bolt: '#b9a6d8',
               cloud: '#6e6890', shade: '#d98a7a', flash: 0.25, flat: true };
  var dark = window.matchMedia && matchMedia('(prefers-color-scheme: dark)');
  var SKY, BOLT, CLOUD, SHADE, FLASH, FLAT;
  function pickTheme() {
    var c = dark && dark.matches ? DARK : LIGHT;
    SKY = c.sky.map(rgb); BOLT = pack(rgb(c.bolt)); CLOUD = c.cloud ? pack(rgb(c.cloud)) : 0;
    SHADE = pack(rgb(c.shade)); FLASH = c.flash; FLAT = c.flat;
  }
  // Sky colour at u (0 = top of the sky, 1 = where it fades out), blended between the theme's colour stops.
  function skyColour(u) {
    if (SKY.length === 1) return pack(SKY[0]);
    var s = Math.max(0, Math.min(1, u)) * (SKY.length - 1), i = Math.min(SKY.length - 2, Math.floor(s)), f = s - i;
    var a = SKY[i], b = SKY[i + 1];
    return pack([Math.round(a[0] + (b[0] - a[0]) * f), Math.round(a[1] + (b[1] - a[1]) * f), Math.round(a[2] + (b[2] - a[2]) * f)]);
  }
  pickTheme();
  var SKY_MAX = 0.42, SKY_REACH = 0.78;           // sky: dot density at the top, and how far down (fraction of the window) it fades out
  var cv = document.getElementById('dither');
  var ctx = cv.getContext('2d');
  // The canvas is part of the page (it scrolls with it, so the picture is locked to the page). Each frame draws only a
  // window of it: the visible part plus half a screen above and below, so a quick scroll never shows an undrawn edge.
  // W x H = that window in cells; WY = page position (CSS px) of its top row; VH = screen height in cells; M = margin rows.
  // rowCol: the sky dot colour for each row. vis: 1, or less near text.
  var W = 0, H = 0, VH = 0, M = 0, WY = 0, PR = 0, noise, base, field, img, px, rowCol, vis;
  var mouse = { x: -999, y: -999, cx: -999, cy: -999 };   // cx, cy: last pointer position on screen (CSS px)
  var trail = [];                                 // recent pointer positions (x in cells, py = page px); each fades out over TRAIL_MS
  var TRAIL_MS = 1100, TRAIL_R = 40 * K;
  var ripples = [];
  var bolts = [];                                 // lightning strikes for this page load (random every time)
  var t0 = performance.now();
  var demo = /^#demo/.test(location.hash);
  var front = (reduce || demo) ? 1e9 : -10;       // load wave position, in cells from the top of the screen
  var WAVE_MS = 1700, STORM_MS = 5000;
  var running = false;
  // Small clouds drifting left to right through the sky; cloud = coverage per cell.
  // boltOn = cells the bolt itself covers this frame (only they get the lightning colour).
  // shade = how deep in a cloud's shadow each cell is.
  var clouds = [], cloud, shade, boltOn;

  function pageHeight() {   // the page's own height (measured from the content, so the canvas never props it up)
    var m = document.querySelector('main');
    return Math.max(innerHeight, m ? m.getBoundingClientRect().bottom + (window.pageYOffset || 0) : innerHeight);
  }
  function sizeCanvas() {
    PR = Math.ceil(pageHeight() / CELL) + 1;
    if (cv.width !== W || cv.height !== PR) {
      cv.width = W; cv.height = PR;
      cv.style.width = W * CELL + 'px'; cv.style.height = PR * CELL + 'px';
      return true;
    }
    return false;
  }

  function resize() {
    W = Math.max(1, Math.ceil((document.documentElement.clientWidth || innerWidth || 1) / CELL));
    VH = Math.max(1, Math.ceil((innerHeight || document.documentElement.clientHeight || 1) / CELL));
    M = Math.ceil(VH / 2); H = VH + 2 * M;
    sizeCanvas();
    img = ctx.createImageData(W, H); px = new Uint32Array(img.data.buffer); rowCol = new Uint32Array(H); vis = new Float32Array(W * H);
    noise = new Float32Array(W * PR); cloud = new Float32Array(W * H); shade = new Float32Array(W * H); boltOn = new Uint8Array(W * H); base = new Float32Array(W * H); field = new Float32Array(W * H);
    for (var y = 0; y < PR; y++) for (var x = 0; x < W; x++) {   // tied to the page, not the screen
      // Faint large-scale haze so the sky isn't a perfectly flat gradient, plus a little per-dot jitter that hides
      // the contour lines an ordered dither draws where a smooth gradient crosses from one pattern to the next.
      // (two broad layers at an angle: finer noise layers line up with the screen and show as a plaid pattern)
      var px0 = x * CELL, py0 = y * CELL, u0 = (px0 * 0.8 + py0 * 0.6), v0 = (py0 * 0.8 - px0 * 0.6);
      noise[y * W + x] = 0.65 * vnoise(u0 / 520, v0 / 300, 3) + 0.35 * vnoise(u0 / 230, v0 / 160, 4) + 0.35 * (hash(x, y, 77) - 0.5);
    }
    if (!bolts.length && !reduce && !demo) planStorm();
    if (!clouds.length) planClouds();
    bolts.forEach(function (b) { b.mask = makeBolt(b); });
    buildWorld();
    kick();
  }

  // Sky: densest at the top of the page, thinning out smoothly until it is plain background. Tied to the page, so it scrolls away.
  function computeBase() {
    var reach = world ? world.surf : innerHeight * SKY_REACH, sy = WY, r0 = WY / CELL;
    for (var y = 0; y < H; y++) {
      var t = 1 - (y * CELL + sy) / reach, row = y * W;
      rowCol[y] = skyColour(1 - t);
      if (world) t = Math.max(0.001, t);           // with the world below, the sky runs all the way down to the horizon
      if (t <= 0) { for (var x0 = 0; x0 < W; x0++) base[row + x0] = 0; continue; }
      // Day: thins out steadily. Dusk: stays fuller lower down, so the warm glow near the horizon shows.
      var prof = FLAT ? SKY_MAX * (0.55 * Math.pow(t, 1.2) + 0.45 * smooth(0, 0.55, t)) : SKY_MAX * Math.pow(t, 1.35);
      if (world) prof = FLAT ? SKY_MAX * (0.5 + 0.5 * Math.pow(t, 1.2)) : SKY_MAX * (0.22 + 0.78 * Math.pow(t, 1.35));
      var nrow = Math.max(0, Math.min(PR - 1, r0 + y)) * W;
      for (var x = 0; x < W; x++) base[row + x] = prof * (0.8 + 0.4 * noise[nrow + x]);
    }
  }

  /* Clouds: small cumulus clouds drifting left to right and wrapping around. Each one is drawn once, when the page
     loads, into its own little sprite: a cluster of round puffs sitting on a flat base, with noisy, wispy edges and a
     shadow that deepens towards the underside (light comes from above). Each frame only copies the sprites into place.
     Positions are in CSS pixels on the page, so the clouds scroll away with the sky. */
  function planClouds() {
    var n = Math.max(3, Math.min(6, Math.round(innerWidth / 300)));
    var scale = Math.max(0.6, Math.min(1, innerWidth / 1100));
    var first = document.querySelector('[data-clear]');
    var textTop = first ? first.getBoundingClientRect().top + (window.pageYOffset || 0) : innerHeight * 0.3;
    for (var i = 0; i < n; i++) {
      var wpx = rand(130, 280) * scale, hpx = wpx * 0.55;
      // keep clouds above the title so they never sit behind text
      var lowest = Math.max(10, textTop - hpx - 6);
      clouds.push({ x: (i + rand(0.1, 0.9)) / n * (innerWidth + 400), y: rand(Math.min(10, lowest), lowest),
                    v: rand(6, 14) * (wpx / 200), sprite: makeCloud(wpx, Math.floor(rand(1, 1e6))) });
    }
  }
  function makeCloud(wpx, seed) {
    var cw = Math.ceil(wpx / CELL), ch = Math.ceil(cw * 0.55), yb = ch * 0.8;   // yb = the flat base
    var puffs = [], k = 4 + Math.floor(rand(0, 4));
    for (var p = 0; p < k; p++) {
      var u = 0.14 + 0.72 * (p + rand(0.2, 0.8)) / k, bump = Math.sin(u * Math.PI);
      var r = cw * (0.09 + 0.17 * bump) * rand(0.8, 1.2);
      puffs.push({ x: u * cw, y: yb - r * rand(0.45, 0.8), r: r });
      if (bump > 0.75 && Math.random() < 0.7) {   // a smaller puff piled on top of the big middle ones
        var r2 = r * rand(0.45, 0.65);
        puffs.push({ x: u * cw + rand(-0.4, 0.4) * r, y: yb - r * rand(0.9, 1.3) - r2 * 0.3, r: r2 });
      }
    }
    // Grow the sprite to fit every puff plus its wispy edge, so no cloud gets a straight cut-off side or top.
    var minX = 0, maxX = cw, minY = 0;
    puffs.forEach(function (pf) {
      minX = Math.min(minX, pf.x - pf.r * 1.3); maxX = Math.max(maxX, pf.x + pf.r * 1.3); minY = Math.min(minY, pf.y - pf.r * 1.3);
    });
    var dx0 = Math.ceil(-minX), dy0 = Math.ceil(-minY);
    puffs.forEach(function (pf) { pf.x += dx0; pf.y += dy0; });
    yb += dy0; cw = Math.ceil(maxX) + dx0; ch = Math.ceil(yb + 4);
    var dens = new Float32Array(cw * ch), shd = new Float32Array(cw * ch), f = CELL / 26;
    for (var y = 0; y < ch; y++) for (var x = 0; x < cw; x++) {
      var best = -1, top = yb, rr = 1;
      for (var q = 0; q < puffs.length; q++) {
        var pf = puffs[q], v = 1 - Math.hypot(x - pf.x, y - pf.y) / pf.r;
        if (v > best) { best = v; top = pf.y - pf.r; rr = pf.r; }
      }
      var nz = fbm(x * f, y * f, seed);
      var d = best + 0.42 * (nz - 0.5);                         // noisy, wispy edge
      d *= smooth(yb + 1.5, yb - 2.5 + 3 * (nz - 0.5), y);       // flat, slightly ragged bottom
      var c = smooth(0, 0.22, d);
      if (c <= 0) continue;
      var j = y * cw + x;
      dens[j] = c;
      // shadow: deeper further below the top of each puff, strongest along the base, a little texture inside
      var depth = (y - top) / (rr * 2);
      shd[j] = Math.max(0, Math.min(1, 0.85 * smooth(0.25, 1.0, depth) + 0.3 * smooth(yb - (yb - dy0) * 0.38, yb, y)
                                        + 0.35 * (fbm(x * f * 2, y * f * 2, seed + 9) - 0.5)));
    }
    return { w: cw, h: ch, dx: dx0 * CELL, dy: dy0 * CELL, dens: dens, shade: shd };
  }
  function drawClouds(t) {
    cloud.fill(0); shade.fill(0);
    var span = innerWidth + 400, sy = WY, moving = !reduce;
    for (var i = 0; i < clouds.length; i++) {
      var c = clouds[i], s = c.sprite;
      var ox = Math.round(((((c.x + (moving ? c.v * t / 1000 : 0)) % span) + span) % span - 200 - s.dx) / CELL);
      var oy = Math.round((c.y - sy - s.dy) / CELL);
      for (var y = 0; y < s.h; y++) {
        var gy = oy + y; if (gy < 0 || gy >= H) continue;
        for (var x = 0; x < s.w; x++) {
          var gx = ox + x; if (gx < 0 || gx >= W) continue;
          var v = s.dens[y * s.w + x]; if (!v) continue;
          var j = gy * W + gx;
          if (v > cloud[j]) { cloud[j] = v; shade[j] = s.shade[y * s.w + x]; }
        }
      }
    }
  }

  /* ------------------------------------------------------------------ world
     Below the sky the page is a slice of a Minecraft world: grass, dirt and a few trees at the surface, then stone with
     caves, ores and an old mineshaft, deepslate (with the diamonds) lower down, lava lakes near the bottom and bedrock at
     the very end of the page. Underground is pitch black: daylight only reaches a few blocks into the ground. Move the
     mouse into an empty space (a cave, cavern or the mineshaft) and that whole space lights up, as if you'd walked in with
     a torch; it fades again when you leave. On phones the middle of the screen does the same as you scroll. Clicking an
     empty spot places a torch there for good.
     Blocks are 32 CSS px: 16 x 16 texels, one dither cell each, so every block has a real texture. */
  var BS = 16, BPX = BS * CELL;
  var AIR = 0, GRASS = 1, DIRT = 2, STONE = 3, DEEP = 4, BEDROCK = 5, PLANKS = 6, FENCE = 7, RAIL = 8, TORCH = 9,
      LAVA = 10, COBWEB = 11, LOG = 12, LEAVES = 13, ORE = 16;     // ores: ORE + 2 * kind (+1 when set in deepslate)
  // coal, iron, lapis, gold, redstone, diamond
  var ORES = [['#2b2b2b', '#4a4a4a'], ['#e3b896', '#b98c69'], ['#2f62d6', '#1f3f94'], ['#fde24e', '#d6a420'],
              ['#e5301f', '#a01510'], ['#6ff0f0', '#2bbcc4']];
  var SEETHRU = new Uint8Array(32);                                // blocks light passes through
  [AIR, FENCE, RAIL, TORCH, LAVA, COBWEB, LEAVES].forEach(function (b) { SEETHRU[b] = 1; });
  var worldSeed = Math.floor(Math.random() * 1e6), world = null, placed = [];
  var touchTorch = window.matchMedia && matchMedia('(hover: none)').matches;

  function makeTextures() {
    var P = {
      stone: ['#8e8e8e', '#767676', '#616161'], dirt: ['#8b5e3b', '#6c4529', '#a3714b'], grass: ['#6db33f', '#55962f'],
      deep: ['#5a5a62', '#48484f', '#38383e'], bedrock: ['#9a9a9a', '#5a5a5a', '#2c2c2c'],
      planks: ['#b08d55', '#94733f', '#6f5329'], log: ['#6e5433', '#54402a'], leaves: ['#4a9a32', '#367a24'],
      lava: ['#ffc23a', '#ff8a1e', '#e0501a'], torch: ['#8a6b3b', '#ffe066', '#ffa22e'], rail: ['#a8a8a8', '#6f5329'], web: '#e6e6e6'
    };
    function T(fn) {
      var tone = new Float32Array(256), col = new Uint32Array(256);
      for (var y = 0; y < 16; y++) for (var x = 0; x < 16; x++) {
        var r = fn(x, y); if (r) { tone[y * 16 + x] = r[1]; col[y * 16 + x] = pack(rgb(r[0])); }
      }
      return { tone: tone, col: col };
    }
    function stoneFn(x, y) { var n = vnoise(x / 2.6, y / 2.6, 11) * 0.7 + hash(x, y, 12) * 0.3; return [n > 0.62 ? P.stone[0] : n < 0.38 ? P.stone[2] : P.stone[1], 0.9]; }
    function deepFn(x, y) { var n = vnoise(x / 4, y / 1.4, 41) * 0.7 + hash(x, y, 42) * 0.3; return [n > 0.62 ? P.deep[0] : n < 0.4 ? P.deep[2] : P.deep[1], 0.9]; }
    function dirtFn(x, y) { var h = hash(x, y, 21); return [h < 0.18 ? P.dirt[1] : h > 0.9 ? P.dirt[2] : P.dirt[0], 0.9]; }
    var t = [];
    t[STONE] = T(stoneFn); t[DEEP] = T(deepFn); t[DIRT] = T(dirtFn);
    t[GRASS] = T(function (x, y) {   // green top with a ragged edge hanging down into the dirt
      if (y < 3 + Math.floor(hash(x, 0, 31) * 3)) return [hash(x, y, 32) < 0.3 ? P.grass[1] : P.grass[0], 0.95];
      return dirtFn(x, y);
    });
    t[BEDROCK] = T(function (x, y) { var n = vnoise(x / 1.8, y / 1.8, 51); return [n > 0.6 ? P.bedrock[0] : n > 0.35 ? P.bedrock[1] : P.bedrock[2], 0.95]; });
    t[PLANKS] = T(function (x, y) {
      var seam = (y & 3) === 3 || x === ((y >> 2) * 5 + 3) % 16;
      return [seam ? P.planks[2] : hash(x, y, 61) < 0.2 ? P.planks[1] : P.planks[0], 0.9];
    });
    t[FENCE] = T(function (x) { return x >= 6 && x <= 9 ? [x === 9 ? P.planks[2] : P.planks[0], 0.9] : null; });
    t[LOG] = T(function (x, y) { return [(x % 4 === 0 || hash(x, y, 71) < 0.12) ? P.log[1] : P.log[0], 0.9]; });
    t[LEAVES] = T(function (x, y) { var h = hash(x, y, 81); return h < 0.22 ? null : [h < 0.5 ? P.leaves[1] : P.leaves[0], 0.9]; });
    t[LAVA] = T(function (x, y) { var n = vnoise(x / 3, y / 3, 91); return [n > 0.62 ? P.lava[0] : n > 0.38 ? P.lava[1] : P.lava[2], 1]; });
    t[TORCH] = T(function (x, y) {
      if (x < 7 || x > 8) return null;
      if (y >= 7) return [P.torch[0], 1];
      if (y >= 5) return [y === 5 ? P.torch[1] : P.torch[2], 1];
      return null;
    });
    t[RAIL] = T(function (x, y) { if (y === 13) return [P.rail[0], 0.95]; if (y >= 14 && (x & 3) < 2) return [P.rail[1], 0.9]; return null; });
    t[COBWEB] = T(function (x, y) { return (x === y || x === 15 - y || x === 8 || y === 8) && hash(x, y, 101) < 0.75 ? [P.web, 0.8] : null; });
    ORES.forEach(function (o, k) {
      [stoneFn, deepFn].forEach(function (baseFn, dp) {
        var seed = 120 + k * 7 + dp;
        t[ORE + k * 2 + dp] = T(function (x, y) {
          for (var c = 0; c < 4; c++) {   // four little clusters of ore in the stone
            var cx = 2 + hash(c, seed, 111) * 12, cy = 2 + hash(seed, c, 112) * 12;
            if (Math.hypot(x - cx, y - cy) < 1.4 + hash(c, c, seed)) return [hash(x, y, seed) < 0.6 ? o[0] : o[1], 1];
          }
          return baseFn(x, y);
        });
      });
    });
    return t;
  }
  var TEX = makeTextures();

  function buildWorld() {
    // The ground starts just under the "Four steps" heading, so the heading stands in the sky on the horizon.
    var sy = window.pageYOffset || 0, mark = document.querySelector('.steps h2') || document.querySelector('.hero');
    var surf = mark ? mark.getBoundingClientRect().bottom + sy + 10 : innerHeight;
    var docH = pageHeight();
    var cols = Math.ceil(innerWidth / BPX) + 1, sr = 8, top = surf - sr * BPX, rows = Math.ceil((docH - top) / BPX);
    if (rows < sr + 24) { world = null; return; }
    var S = worldSeed, ids = new Uint8Array(cols * rows), hcol = new Int16Array(cols), under = rows - sr;
    var mainEl = document.querySelector('main'), mr = mainEl ? mainEl.getBoundingClientRect() : { left: 0, right: innerWidth };
    for (var c = 0; c < cols; c++) hcol[c] = sr + Math.round(vnoise(c / 5, 0.5, S) * 3);   // gentle hills
    for (var r = 0; r < rows; r++) for (c = 0; c < cols; c++) {
      var h = hcol[c], id = AIR, d = (r - h) / under;                  // d: 0 at the surface, 1 at bedrock
      if (r === h) id = GRASS;
      else if (r > h && r <= h + 2 + (hash(c, 0, S) < 0.5 ? 1 : 0)) id = DIRT;
      else if (r > h) {
        id = d > 0.62 + 0.08 * (vnoise(c / 4, r / 4, S + 5) - 0.5) ? DEEP : STONE;
        if (r > h + 5 && r < rows - 4) {                              // caves: big caverns plus long winding tunnels
          var cheese = fbm(c / 9, r / 6, S + 1), spag = Math.abs(fbm(c / 14, r / 9, S + 2) - 0.5);
          if (cheese > 0.69 - 0.08 * d || spag < 0.03) id = AIR;
        }
        if (id !== AIR) {                                             // ores, rarer and richer the deeper you go
          var o = hash(c, r, S + 3), kind = -1;
          if (o < 0.05 && d < 0.65) kind = 0;
          else if (o < 0.085 && d > 0.08 && d < 0.8) kind = 1;
          else if (o < 0.097 && d > 0.4) kind = 2;
          else if (o < 0.11 && d > 0.45) kind = 3;
          else if (o < 0.13 && d > 0.6) kind = 4;
          else if (o < 0.139 && d > 0.75) kind = 5;
          if (kind >= 0) id = ORE + kind * 2 + (id === DEEP ? 1 : 0);
        }
        if (id === AIR && r >= rows - 9) id = LAVA;                   // the lowest caves are flooded with lava
      }
      var fb = rows - 1 - r, hb = hash(c, r, S + 4);                  // a ragged bedrock floor
      if (fb === 0 || (fb === 1 && hb < 0.8) || (fb === 2 && hb < 0.45) || (fb === 3 && hb < 0.15)) id = BEDROCK;
      ids[r * cols + c] = id;
    }
    // Abandoned mineshafts: a 3-high corridor with rails, wooden supports every 5 blocks, torches and cobwebs.
    var shafts = under > 60 ? 2 : 1;
    for (var m = 0; m < shafts; m++) {
      var ms = sr + Math.round(under * (0.28 + 0.34 * m + 0.08 * hash(m, 1, S)));
      if (ms > rows - 12) continue;
      var c0 = Math.floor(hash(m, 2, S) * cols * 0.25), c1 = cols - 1 - Math.floor(hash(m, 3, S) * cols * 0.25);
      for (c = c0; c <= c1; c++) {
        for (var rr = ms - 2; rr <= ms; rr++) ids[rr * cols + c] = AIR;
        if ((c - c0) % 5 === 2) { ids[(ms - 2) * cols + c] = PLANKS; ids[(ms - 1) * cols + c] = FENCE; ids[ms * cols + c] = FENCE; }
        else {
          ids[ms * cols + c] = RAIL;
          if (hash(c, ms, S + 6) < 0.12) ids[(ms - 2) * cols + c] = COBWEB;
        }
        if ((c - c0) % 5 === 3 && hash(c, m, S + 7) < 0.6) ids[(ms - 1) * cols + c] = TORCH;
        var below = (ms + 1) * cols + c;
        if (ids[below] === AIR || ids[below] === LAVA) ids[below] = PLANKS;   // plank bridges over caves
      }
    }
    // A few oak trees, only beside the page content (never behind the title or buttons).
    var lastTree = -9;
    for (c = 2; c < cols - 2; c++) {
      var xl = (c - 2) * BPX, xr = (c + 3) * BPX;
      if (!(xr < mr.left - 8 || xl > mr.right + 8)) continue;
      if (c - lastTree < 6 || hash(c, 9, S) > 0.35) continue;
      lastTree = c;
      var g = hcol[c], th = 4 + Math.floor(hash(c, 10, S) * 2);
      for (var k = 1; k <= th; k++) ids[(g - k) * cols + c] = LOG;
      for (var ly = g - th - 2; ly <= g - th + 1; ly++) for (var lx = c - 2; lx <= c + 2; lx++) {
        var far = Math.abs(lx - c);
        if ((far === 2 && (ly === g - th - 2 || ly === g - th + 1)) || (ly === g - th - 2 && far > 1) || ly < 0) continue;
        if (!ids[ly * cols + lx]) ids[ly * cols + lx] = LEAVES;
      }
    }
    world = { cols: cols, rows: rows, top: top, surf: surf, ids: ids, hcol: hcol, wc: cols * BS, hc: rows * BS };
    // smooth lighting: each texel column blends the two nearest block centres (tables so the frame loop stays cheap)
    var wc = cols * BS; world.c0 = new Int16Array(wc); world.c1 = new Int16Array(wc); world.tx = new Float32Array(wc);
    for (var xx = 0; xx < wc; xx++) {
      var fx = (xx - 7.5) / BS, a0 = Math.max(0, Math.floor(fx));
      world.c0[xx] = a0; world.c1[xx] = Math.min(cols - 1, a0 + 1); world.tx[xx] = Math.max(0, Math.min(1, fx - a0));
    }
    placed.forEach(function (p) { setTorch(p.x, p.y); });
    lightWorld();
    // #demo-cave (for screenshots): park the "mouse" in the biggest cavern on screen
    if (/^#demo-cave/.test(location.hash)) {
      var best = -1, bestN = 0;
      for (var bi = 0; bi < ids.length; bi += 3) {
        var bxp = (bi % cols) * BPX + BPX / 2, byp = top + ((bi / cols) | 0) * BPX + BPX / 2 - sy;
        if (byp < 0 || byp > innerHeight || blockAt(bxp, byp + sy) < 0) continue;
        var cnt = caveLight(bi).idx.length; if (cnt > bestN) { bestN = cnt; best = bi; }
      }
      if (best >= 0) { mouse.cx = (best % cols) * BPX + BPX / 2; mouse.cy = top + ((best / cols) | 0) * BPX + BPX / 2 - sy; }
    }
  }

  // Light like the game: levels 0-15 spread one block at a time through air (and other see-through blocks).
  function spread(lv, q) {
    var w = world, cols = w.cols, n = lv.length;
    for (var h = 0; h < q.length; h++) {
      var i = q[h], l = lv[i] - 1; if (l <= 0) continue;
      var c = i % cols;
      var nb = [c > 0 ? i - 1 : -1, c < cols - 1 ? i + 1 : -1, i - cols, i + cols];
      for (var k = 0; k < 4; k++) {
        var m = nb[k];
        if (m < 0 || m >= n || lv[m] >= l) continue;
        lv[m] = l;
        if (SEETHRU[w.ids[m]]) q.push(m);
      }
    }
  }
  // Fixed light: daylight on the surface (fading out a few blocks down, and into caves that open to the sky) and
  // the torches the visitor placed. Everything else underground stays black until the mouse lights it.
  function lightWorld() {
    var w = world; if (!w) return;
    var n = w.cols * w.rows, sky = new Uint8Array(n), qs = [], i;
    for (var c = 0; c < w.cols; c++) for (var r = 0; r < w.hcol[c]; r++) {
      i = r * w.cols + c; if (SEETHRU[w.ids[i]]) { sky[i] = 15; qs.push(i); }
    }
    spread(sky, qs);
    var base = new Float32Array(n), DAY = FLAT ? 0.75 : 1;            // dusk daylight is dimmer
    for (i = 0; i < n; i++) {
      var depth = ((i / w.cols) | 0) - w.hcol[i % w.cols];
      var L = Math.pow(sky[i] / 15, 2.2) * DAY;
      if (depth >= 0) L = Math.max(L, DAY * Math.exp(-depth / 1.3));
      base[i] = L;
    }
    w.cache = {};
    placed.forEach(function (p) {
      var k = blockAt(p.x, p.y); if (k < 0) return;
      var s = caveLight(k); for (var m = 0; m < s.idx.length; m++) if (s.v[m] > base[s.idx[m]]) base[s.idx[m]] = s.v[m];
    });
    w.base = base; w.lit = new Float32Array(n);
  }
  // Light from one spot in a cave: like a torch held there, spreading block by block through the open cave (and onto
  // its walls), fading with distance. Reaches about 22 blocks, so a whole cavern lights up. Cached per spot.
  var REACH = 22;
  function caveLight(i0) {
    var w = world;
    if (w.cache[i0]) return w.cache[i0];
    var cols = w.cols, n = w.ids.length, lv = new Uint8Array(n), q = [i0], idx = [], v = [];
    lv[i0] = REACH;
    for (var h = 0; h < q.length; h++) {
      var i = q[h], l = lv[i] - 1; if (l <= 0) continue;
      var c = i % cols, nb = [c > 0 ? i - 1 : -1, c < cols - 1 ? i + 1 : -1, i - cols, i + cols];
      for (var k = 0; k < 4; k++) {
        var m = nb[k];
        if (m < 0 || m >= n || lv[m] >= l) continue;
        lv[m] = l;
        if (SEETHRU[w.ids[m]] && ((m / cols) | 0) > w.hcol[m % cols]) q.push(m);   // stays underground
      }
    }
    // bright near you, with a gentle fade towards the far end of the cave
    for (var j = 0; j < n; j++) if (lv[j]) { idx.push(j); v.push(Math.min(1, 1.15 * Math.pow(lv[j] / REACH, 0.55))); }
    return (w.cache[i0] = { idx: idx, v: v });
  }
  // The underground see-through block at a page position, or -1 (rock, sky, or outside the world).
  function blockAt(x, y) {
    var w = world, c = Math.floor(x / BPX), r = Math.floor((y - w.top) / BPX);
    if (c < 0 || c >= w.cols || r < 0 || r >= w.rows || r <= w.hcol[c]) return -1;
    var i = r * w.cols + c;
    return SEETHRU[w.ids[i]] ? i : -1;
  }
  var glows = [], lastNow = 0;   // caverns lit by the mouse: each fades in while the mouse is inside, then fades out
  function updateGlows(now, sy, flick) {
    var w = world, dt = Math.min(100, now - (lastNow || now)); lastNow = now;
    var hx = touchTorch ? innerWidth * 0.5 : mouse.cx, hy = touchTorch ? innerHeight * 0.55 : mouse.cy;
    var hov = (touchTorch || mouse.cx > -900) ? blockAt(hx, hy + sy) : -1, found = false;
    for (var g = 0; g < glows.length; g++) if (glows[g].i === hov) found = true;
    if (hov >= 0 && !found) glows.push({ i: hov, a: 0 });
    var lit = w.lit; lit.set(w.base);
    for (g = glows.length - 1; g >= 0; g--) {
      var s = glows[g], on = s.i === hov;
      s.a += ((on ? 1 : 0) - s.a) * (1 - Math.exp(-dt / (on ? 90 : 500)));
      if (!on && s.a < 0.01) { glows.splice(g, 1); continue; }
      var L = caveLight(s.i), f = s.a * (on ? flick : 1);
      for (var m = 0; m < L.idx.length; m++) { var val = L.v[m] * f; if (val > lit[L.idx[m]]) lit[L.idx[m]] = val; }
    }
    return glows.length > 0;
  }
  function setTorch(x, y) {   // page coordinates; only into an empty underground spot
    var w = world, c = Math.floor(x / BPX), r = Math.floor((y - w.top) / BPX);
    if (c < 0 || c >= w.cols || r < 0 || r >= w.rows || r <= w.hcol[c]) return false;
    var i = r * w.cols + c;
    if (w.ids[i] !== AIR) return false;
    w.ids[i] = TORCH; return true;
  }
  function placeTorch(x, y) {
    if (!world || !setTorch(x, y)) return;
    placed.push({ x: x, y: y }); lightWorld(); kick();
  }
  if ('ResizeObserver' in window) {   // images and fonts change the page height: rebuild so bedrock stays at the bottom
    var lastDocH = 0;
    new ResizeObserver(function () {
      var hgt = pageHeight();
      if (Math.abs(hgt - lastDocH) < 4) return;
      lastDocH = hgt; clearTimeout(buildWorld.t);
      buildWorld.t = setTimeout(function () { try { resize(); } catch (err) { world = null; } kick(); }, 150);
    }).observe(document.body);
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
    var x = W * b.x, y = M - 2, pts = [[x, y]], bottom = M + VH * rand(0.55, 0.95);
    while (y < bottom) { y += (5 + rnd() * 10) * K; x += (rnd() - 0.5) * 24 * K; pts.push([x, y]); }
    var paths = [pts];
    for (var br = 0; br < 2 + Math.floor(rnd() * 2); br++) {
      var from = pts[1 + Math.floor(rnd() * (pts.length - 2))], dir = rnd() < 0.5 ? -1 : 1, bp = [from.slice()];
      for (var i = 0; i < 5 + rnd() * 6; i++) { var last = bp[bp.length - 1]; bp.push([last[0] + dir * (3 + rnd() * 9) * K, last[1] + (4 + rnd() * 8) * K]); }
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
    stamp(paths[0], 2.2 * K, 14 * K, 1);
    for (var q = 1; q < paths.length; q++) stamp(paths[q], 1.3 * K, 8 * K, 0.7);
    // a wide, faint halo lights up the sky around the strike
    var halo = 46 * K;
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
    var t = now - t0, busy = false, sy = window.pageYOffset || 0;
    WY = (Math.floor(sy / CELL) - M) * CELL;
    var off = (sy - WY) / CELL;                     // screen top, in window rows
    if (mouse.cx > -900) { mouse.x = mouse.cx / CELL; mouse.y = (mouse.cy + sy - WY) / CELL; } else mouse.x = mouse.y = -999;
    computeBase();
    drawClouds(t);
    field.set(base);
    if (clouds.length && !reduce) busy = true;

    // Load wave: rows above the front are drawn, a brighter band rides on the front.
    if (front < VH + 30) {
      var e = Math.min(1, t / WAVE_MS); e = 1 - Math.pow(1 - e, 3);
      front = -10 + e * (VH + 40); busy = true;
      revealUpTo(front * CELL);
      if (e >= 1) front = 1e9;
    }
    // Lightning.
    strikeNow = 0; boltOn.fill(0);
    for (var s = 0; s < bolts.length; s++) {
      var bo = bolts[s], lvl = strike((t - bo.start) / bo.dur);
      if (t < bo.start + bo.dur) busy = true;
      if (lvl > 0 && bo.mask) {
        if (lvl > strikeNow) strikeNow = lvl;
        var m = bo.mask;
        for (var b = 0; b < m.length; b += 2) { field[m[b]] += m[b + 1] * lvl * 0.9; if (m[b + 1] * lvl > 0.3) boltOn[m[b]] = 1; }
      }
    }

    // The whole night sky flashes with each strike.
    if (strikeNow > 0) for (var f = 0; f < field.length; f++) if (base[f] > 0) field[f] += base[f] * FLASH * strikeNow;

    // Mouse: every recent pointer position leaves a soft patch of dither that shrinks and fades, so moving leaves a trail.
    for (var mi = trail.length - 1; mi >= 0; mi--) {
      var ma = (now - trail[mi].t) / TRAIL_MS;
      if (ma >= 1) { trail.splice(mi, 1); continue; }
      var life = 1 - ma;
      addBlob(trail[mi].x, (trail[mi].py - WY) / CELL, TRAIL_R * (0.45 + 0.55 * life), 0.30 * life * life, false, 0, true);
      busy = true;
    }
    if (mouse.x > -900) addBlob(mouse.x, mouse.y, TRAIL_R, 0.30, false, 0, true);
    // Click ripples.
    for (var i = ripples.length - 1; i >= 0; i--) {
      var rp = ripples[i], age = (now - rp.t) / 900;
      if (age >= 1) { ripples.splice(i, 1); continue; }
      addBlob(rp.x, (rp.py - WY) / CELL, 6 * K + age * rp.max, 0.55 * (1 - age), true, (3 + age * 4) * K);
      busy = true;
    }

    clearText();
    var j = 0, frontRow = Math.floor(front + off), sy2 = WY, wd = world;
    // the torch flickers a little
    var flick = reduce ? 1 : 0.88 + 0.12 * vnoise(now * 0.006, 0.5, 5);
    if (wd && wd.base && updateGlows(now, sy, flick)) busy = true;
    var pr0 = WY / CELL;                            // page row of the window's first row
    for (var y = 0; y < H; y++) {
      var by = ((pr0 + y) & 7) * 8;                 // dither grid counted from the top of the page, so it scrolls with the page
      if (y > frontRow) { for (var x0 = 0; x0 < W; x0++) px[j++] = 0; continue; }
      var band = frontRow - y < 6 * K && front < VH + 30 ? 0.22 * (1 - (frontRow - y) / (6 * K)) : 0;
      var wy = wd ? Math.floor((y * CELL + sy2 - wd.top) / CELL) : -1, inW = wy >= 0;
      if (inW && wy >= wd.hc) { for (x0 = 0; x0 < W; x0++) px[j++] = 0; continue; }
      var br = wy >> 4, tyy = (wy & 15) * 16, ro0 = 0, ro1 = 0, ty = 0;
      if (inW) {
        var fy = (wy - 7.5) / BS, r0 = Math.max(0, Math.floor(fy));
        ty = Math.max(0, Math.min(1, fy - r0)); ro0 = r0 * wd.cols; ro1 = Math.min(wd.rows - 1, r0 + 1) * wd.cols;
      }
      for (var x = 0; x < W; x++, j++) {
        var th = BAYER[by + (x & 7)];
        if (inW && (x >> 4) < wd.cols) {
          // a block of the world (or underground air); sky air above the ground falls through to the sky below
          var bc = x >> 4, id = wd.ids[br * wd.cols + bc], underground = br >= wd.hcol[bc];
          var k2 = tyy + (x & 15), T = id ? TEX[id] : null, tone = T ? T.tone[k2] : 0;
          if (tone || underground) {
            // Unlit underground is dark. In dark mode that is just the page background; in light mode it is drawn
            // in a near-black (except right around text, which keeps a soft pocket of page colour so it stays readable).
            if (!tone) { px[j] = 0; continue; }                   // underground air: black
            var LT = wd.lit, C0 = wd.c0[x], C1 = wd.c1[x], tx = wd.tx[x];
            var la = LT[ro0 + C0], lb = LT[ro0 + C1], le = LT[ro1 + C0], ld = LT[ro1 + C1];
            if (!(la || lb || le || ld)) { px[j] = 0; continue; }   // unlit rock: black
            var tp = la + (lb - la) * tx, L = tp + (le + (ld - le) * tx - tp) * ty;
            px[j] = tone * L * vis[j] > th ? T.col[k2] : 0;
            continue;
          }
        }
        var v = field[j] + band, c = cloud[j];
        if (c > th) {
          // inside a cloud: lit parts are white (light mode) or pale grey (dark mode); shadows dither in a darker tone
          // (th / c re-spreads the same dither threshold over just the cloud's cells, so the shading dithers cleanly)
          px[j] = shade[j] * 0.8 > th / c ? SHADE : CLOUD;
        } else px[j] = v > th ? (boltOn[j] ? BOLT : rowCol[y]) : 0;
      }
    }
    ctx.putImageData(img, 0, WY / CELL);
    if (trail.length || ripples.length || front < VH + 30 || strikeNow > 0) requestAnimationFrame(frame);
    else if (busy) setTimeout(function () { requestAnimationFrame(frame); }, 50);   // only clouds moving: 20 fps is plenty
    else running = false;
  }

  // Keep text readable: no dither under elements marked data-clear, with a soft edge around them.
  var clearEls = document.querySelectorAll('[data-clear]');
  function clearText() {
    var PAD = 2 * K, FADE = 12 * K;   // a soft, round-cornered glow around text rather than a hard box
    vis.fill(1);
    for (var c = 0; c < clearEls.length; c++) {
      var r = clearEls[c].getBoundingClientRect();
      var dyw = (window.pageYOffset || 0) - WY;      // screen -> window offset, CSS px
      if (r.bottom + dyw < 0 || r.top + dyw > H * CELL || !r.width) continue;
      var l = r.left / CELL - PAD, rt = r.right / CELL + PAD, tp = (r.top + dyw) / CELL - PAD, bt = (r.bottom + dyw) / CELL + PAD;
      var x0 = Math.max(0, Math.floor(l - FADE)), x1 = Math.min(W - 1, Math.ceil(rt + FADE));
      var y0 = Math.max(0, Math.floor(tp - FADE)), y1 = Math.min(H - 1, Math.ceil(bt + FADE));
      for (var y = y0; y <= y1; y++) {
        var dy = y < tp ? tp - y : y > bt ? y - bt : 0;
        for (var x = x0; x <= x1; x++) {
          var dx = x < l ? l - x : x > rt ? x - rt : 0;
          var d = Math.hypot(dx, dy);
          if (d < FADE) { var f = d / FADE, jj = y * W + x; field[jj] *= f; cloud[jj] *= f; if (f < vis[jj]) vis[jj] = f; }
        }
      }
    }
  }

  if (dark && dark.addEventListener) dark.addEventListener('change', function () { pickTheme(); lightWorld(); kick(); });

  function kick() { if (!running) { running = true; requestAnimationFrame(frame); } }

  addEventListener('resize', function () { clearTimeout(resize.t); resize.t = setTimeout(resize, 120); });
  addEventListener('pointermove', function (e) {
    if (reduce) return;
    mouse.cx = e.clientX; mouse.cy = e.clientY;
    var x = e.clientX / CELL, py = e.clientY + (window.pageYOffset || 0);
    var last = trail[trail.length - 1], now = performance.now();
    if (!last || Math.hypot(x - last.x, (py - last.py) / CELL) > 5 * K || now - last.t > 60) {
      trail.push({ x: x, py: py, t: now });
      if (trail.length > 48) trail.shift();
    }
    kick();
  }, { passive: true });
  document.addEventListener('pointerleave', function () { mouse.cx = mouse.cy = -999; kick(); });
  addEventListener('scroll', kick, { passive: true });
  // Text can move when fonts or images arrive; redraw so the clear areas follow it.
  addEventListener('load', kick);
  document.addEventListener('transitionend', kick);   // text finished sliding in: move its clear area with it
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(kick);

  function ripple(el, ev) {
    if (reduce) return;
    var x, y;
    if (ev && (ev.clientX || ev.clientY)) { x = ev.clientX; y = ev.clientY; }
    else { var r = el.getBoundingClientRect(); x = r.left + r.width / 2; y = r.top + r.height / 2; }
    ripples.push({ x: x / CELL, py: y + (window.pageYOffset || 0), t: performance.now(), max: Math.max(W, VH) * 0.45 });
    kick();
  }
  // A click anywhere ripples through the dither (keyboard "clicks" ripple from the element's centre).
  document.addEventListener('click', function (e) {
    var ui = e.target.closest ? e.target.closest('button, a, input, label, .step, .unlock, .foot p') : null;
    ripple(ui || document.body, e);
    if (!ui && (e.clientX || e.clientY)) placeTorch(e.clientX, e.clientY + (window.pageYOffset || 0));   // click a cave: place a torch
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
  var platform = null, key = null, address = null, meta = null, openPw = null;
  // Open mode: when dl/meta.json carries "open" (the password itself), the buttons download without asking.
  // Remove the field (or rebuild dl/ with build_site.py) to ask for the password again.
  fetch('dl/meta.json', { cache: 'no-cache' }).then(function (r) { return r.json(); }).then(function (m) {
    meta = m; openPw = m.open || null;
    if (openPw) { document.querySelectorAll('.pw-only').forEach(function (el) { el.hidden = true; }); pw.value = openPw; unlock(true); }
  }).catch(function () {});

  function say(text, cls) { msg.textContent = text; msg.className = 'unlock-msg' + (cls ? ' ' + cls : ''); }

  document.querySelectorAll('[data-platform]').forEach(function (btn) {
    btn.addEventListener('click', function () {
      platform = btn.getAttribute('data-platform');
      document.querySelectorAll('[data-platform]').forEach(function (b) { b.setAttribute('aria-pressed', String(b === btn)); });
      if (key) { download(); return; }
      form.hidden = false; form.setAttribute('data-platform', platform);
      if (openPw) {                                  // open mode: no password needed, download straight away
        label.textContent = NAMES[platform] + ' download';
        document.querySelector('.unlock-row').hidden = true;
        pw.value = openPw; unlock(); return;
      }
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

  form.addEventListener('submit', function (e) { e.preventDefault(); unlock(); });
  function unlock(quiet) {   // quiet: just unlock (shows who's online), no download
    if (!window.crypto || !crypto.subtle) { if (quiet) return; say('This browser can\'t unlock the download. Try Chrome, Edge, Safari or Firefox.', 'err'); return; }
    if (!quiet) say('Unlocking...');
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
        return quiet ? null : download();
      })
      .catch(function (err) {
        key = null;
        say(err && err.name === 'OperationError' ? 'Wrong password. Ask Thunder for it.' : 'Couldn\'t unlock: ' + (err && err.message || err), 'err');
        ripple(form);
      });
  }

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
