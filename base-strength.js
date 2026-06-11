/* ===========================================================================
 * base-strength.js  —  CuteDefense base (room) defensibility model
 * ---------------------------------------------------------------------------
 * Pure, dependency-free. Loaded by cutedefense-map-editor.html as a classic
 * <script> (exposes window.BaseStrength) and require()-able in Node for tests.
 *
 * WHAT "STRENGTH" MEANS
 *   How hard a walled base (room) is to break into / how easily it's defended,
 *   in the spirit of Cute Defense: you win by minimising the
 *   number of fronts you must hold, keeping a deep safe core, and leaning on
 *   neighbouring strength. Higher score = stronger (harder to attack).
 *
 * FLOWERS -> BEST / WORST CASE
 *   Red & blue flowers are walls only in their own phase (the game shows one
 *   colour at a time, 50/50). So a base's openings differ per phase. We score
 *   each phase independently:
 *     worst = the more-open phase (most attackable)   -> lowest strength
 *     best  = the more-sealed phase                    -> highest strength
 *     avg   = mean of the two (each phase is 50%)      -> expected strength
 *
 * FACTORS (each documented at its use site)
 *   + depth      cells far from any opening are worth more (deep safe core)
 *   + size/open  big base vs small openings is stronger (falls out of depth)
 *   + fewOpen    fewer entry FRONTS is much stronger  (1×[2x4] beats 2×[2x2])
 *   + narrow     a narrow opening is mildly stronger than a wide one
 *   + corners    openings FAR from corners are stronger (corners are exposed)
 *   + support    powerful bases NEARBY make this base easier to defend
 *   - routes     openings on CONNECTED bases add enemy routes here (weaker)
 * =========================================================================== */
(function (root) {
  'use strict';

  var DEFAULT_WEIGHTS = {
    depthExp: 1.0,      // value of a cell at opening-distance d  =  d ^ depthExp
    route: 1.0,         // openings penalty: routeMult = 1 / nOpen ^ route   (>=1 => one wide opening beats two narrow)
    width: 0.18,        // mild wide-opening penalty: widthMult = 1 / (1 + width*(avgWidth-2)); kept small so it never flips the fewer-openings ordering
    cornerBase: 0.55,   // cornerMult = cornerBase + cornerSpan * cornerFactor   (cornerFactor in [0,1], 1 = central opening)
    cornerSpan: 0.90,
    sealedBonus: 5.0,   // a base with NO opening in a phase is impenetrable that phase -> big multiplier on its perimeter-depth
    supportSigma: 55,   // neighbour-support falloff in cells (exp(-dist/sigma))
    support: 0.60,      // weight of neighbour support (raises strength)
    routes: 0.30,       // weight of connected-base route penalty (lowers strength)
  };

  function neigh4(i, x, y, G) {
    var a = [];
    if (x > 0) a.push(i - 1);
    if (x < G - 1) a.push(i + 1);
    if (y > 0) a.push(i - G);
    if (y < G - 1) a.push(i + G);
    return a;
  }

  // 4-connected components of a cell list; each run's width = the larger bbox side.
  function groupRuns(cells, G) {
    var set = new Set(cells), seen = new Set(), runs = [];
    for (var k = 0; k < cells.length; k++) {
      var start = cells[k];
      if (seen.has(start)) continue;
      var minx = G, maxx = -1, miny = G, maxy = -1, comp = [], stack = [start];
      seen.add(start);
      while (stack.length) {
        var idx = stack.pop(), x = idx % G, y = (idx - (idx % G)) / G;
        comp.push(idx);
        if (x < minx) minx = x; if (x > maxx) maxx = x;
        if (y < miny) miny = y; if (y > maxy) maxy = y;
        var nb = neigh4(idx, x, y, G);
        for (var j = 0; j < nb.length; j++) if (set.has(nb[j]) && !seen.has(nb[j])) { seen.add(nb[j]); stack.push(nb[j]); }
      }
      runs.push({
        cells: comp,
        width: Math.max(maxx - minx + 1, maxy - miny + 1),
        cx: (minx + maxx) / 2,
        cy: (miny + maxy) / 2,
      });
    }
    return runs;
  }

  // ---- per-phase analysis of one base ------------------------------------
  // occP[i] === 1  => cell i is a wall in this phase.
  function analyzePhase(base, occP, playable, G, W) {
    var cells = base.cells, set = base.set;
    var openP = function (i) { return playable[i] === 1 && occP[i] === 0; };

    // Mouth = base cells touching open, NON-base space this phase (a doorway).
    // (A genuine no-tile gap is open every phase; an off-colour flower opens this
    // phase — both turn the adjacent base cell into a mouth automatically.)
    var mouth = [];
    for (var c = 0; c < cells.length; c++) {
      var i = cells[c], x = i % G, y = (i - (i % G)) / G, nb = neigh4(i, x, y, G), isMouth = false;
      for (var j = 0; j < nb.length; j++) { var m = nb[j]; if (!set.has(m) && openP(m)) { isMouth = true; break; } }
      if (isMouth) mouth.push(i);
    }
    var openings = groupRuns(mouth, G);
    var nOpen = openings.length;

    // Depth field: BFS from the mouth inward through the base. Deep cells (far
    // from every opening) are the safe core and are worth the most.
    var dist = new Map();
    if (nOpen > 0) {
      var q = [], head = 0;
      for (var o = 0; o < mouth.length; o++) { dist.set(mouth[o], 0); q.push(mouth[o]); }
      while (head < q.length) {
        var cur = q[head++], cx = cur % G, cy = (cur - (cur % G)) / G, d = dist.get(cur);
        var cn = neigh4(cur, cx, cy, G);
        for (var p = 0; p < cn.length; p++) { var nn = cn[p]; if (set.has(nn) && !dist.has(nn)) { dist.set(nn, d + 1); q.push(nn); } }
      }
    }

    // For a SEALED phase (no opening) there is no opening-distance; fall back to
    // distance from the base PERIMETER so a bigger sealed base still scores more.
    var sealed = nOpen === 0, depthValue = 0, maxDepth = 0;
    if (sealed) {
      var q2 = [], h2 = 0, d2 = new Map();
      for (var s = 0; s < cells.length; s++) {
        var ii = cells[s], xx = ii % G, yy = (ii - (ii % G)) / G, nb2 = neigh4(ii, xx, yy, G), edge = nb2.length < 4;
        for (var jj = 0; jj < nb2.length; jj++) if (!set.has(nb2[jj])) { edge = true; break; }
        if (edge) { d2.set(ii, 0); q2.push(ii); }
      }
      while (h2 < q2.length) {
        var cu = q2[h2++], cux = cu % G, cuy = (cu - (cu % G)) / G, dd = d2.get(cu), c2 = neigh4(cu, cux, cuy, G);
        for (var z = 0; z < c2.length; z++) { var n2 = c2[z]; if (set.has(n2) && !d2.has(n2)) { d2.set(n2, dd + 1); q2.push(n2); } }
      }
      dist = d2;
    }
    dist.forEach(function (d) { depthValue += Math.pow(d, W.depthExp); if (d > maxDepth) maxDepth = d; });

    // Corner factor: openings far from the base's bbox corners are more
    // defensible. cornerFactor in [0,1] — 1 = opening dead-centre, 0 = in a corner.
    var corners = [[base.minx, base.miny], [base.maxx, base.miny], [base.minx, base.maxy], [base.maxx, base.maxy]];
    var halfDiag = 0.5 * Math.hypot(base.maxx - base.minx, base.maxy - base.miny) || 1;
    var cornerFactor = 1, wsum = 0, cacc = 0;
    for (var g = 0; g < openings.length; g++) {
      var op = openings[g], near = Infinity;
      for (var cc = 0; cc < 4; cc++) { var dx = op.cx - corners[cc][0], dy = op.cy - corners[cc][1], dd2 = Math.hypot(dx, dy); if (dd2 < near) near = dd2; }
      var f = Math.max(0, Math.min(1, near / halfDiag)), w = op.width;
      cacc += f * w; wsum += w;
    }
    if (wsum > 0) cornerFactor = cacc / wsum;

    var totalWidth = 0; for (var t = 0; t < openings.length; t++) totalWidth += openings[t].width;
    var avgWidth = nOpen > 0 ? totalWidth / nOpen : 0;

    // Intrinsic phase strength.
    var intrinsic;
    if (sealed) {
      intrinsic = depthValue * W.sealedBonus;          // impenetrable this phase
    } else {
      var routeMult = 1 / Math.pow(nOpen, W.route);     // FEWER FRONTS dominate (1×wide beats 2×narrow)
      var widthMult = 1 / (1 + W.width * (avgWidth - 2)); // mild: narrower slightly better
      var cornerMult = W.cornerBase + W.cornerSpan * cornerFactor;
      intrinsic = depthValue * routeMult * widthMult * cornerMult;
    }

    return {
      nOpen: nOpen, openings: openings.map(function (o) { return { width: o.width, cx: o.cx, cy: o.cy }; }),
      totalWidth: totalWidth, avgWidth: avgWidth, sealed: sealed,
      depthValue: depthValue, maxDepth: maxDepth, cornerFactor: cornerFactor, intrinsic: intrinsic,
    };
  }

  function computeBaseStrengths(input, weightsIn) {
    var W = Object.assign({}, DEFAULT_WEIGHTS, weightsIn || {});
    var G = input.GRID, playable = input.playable, redOcc = input.redOcc, blueOcc = input.blueOcc;
    var total = G * G;

    // ---- per-base geometry ----
    var bases = input.bases.map(function (b) {
      var set = new Set(b.cells), minx = G, maxx = -1, miny = G, maxy = -1, sx = 0, sy = 0;
      for (var k = 0; k < b.cells.length; k++) {
        var i = b.cells[k], x = i % G, y = (i - (i % G)) / G;
        sx += x; sy += y; if (x < minx) minx = x; if (x > maxx) maxx = x; if (y < miny) miny = y; if (y > maxy) maxy = y;
      }
      var n = b.cells.length || 1;
      return { id: b.id, cells: b.cells, set: set, area: b.cells.length, minx: minx, maxx: maxx, miny: miny, maxy: maxy, cx: sx / n, cy: sy / n };
    });

    // ---- per-phase intrinsic strength ----
    bases.forEach(function (b) {
      b.red = analyzePhase(b, redOcc, playable, G, W);
      b.blue = analyzePhase(b, blueOcc, playable, G, W);
      b.intrinsicBest = Math.max(b.red.intrinsic, b.blue.intrinsic);
      b.intrinsicWorst = Math.min(b.red.intrinsic, b.blue.intrinsic);
      b.intrinsicAvg = (b.red.intrinsic + b.blue.intrinsic) / 2;
      b.avgOpenings = (b.red.nOpen + b.blue.nOpen) / 2;
    });

    // ---- connectivity: which bases share an open-field network (enemy routes) ----
    // Label the field = open-in-either-phase cells that are NOT inside any base.
    var inBase = new Uint8Array(total);
    bases.forEach(function (b) { for (var k = 0; k < b.cells.length; k++) inBase[b.cells[k]] = 1; });
    var openEither = function (i) { return playable[i] === 1 && (redOcc[i] === 0 || blueOcc[i] === 0); };
    var fieldComp = new Int32Array(total).fill(0), nf = 0, q = new Int32Array(total);
    for (var s = 0; s < total; s++) {
      if (fieldComp[s] || inBase[s] || !openEither(s)) continue;
      nf++; var head = 0, tail = 0; q[tail++] = s; fieldComp[s] = nf;
      while (head < tail) {
        var idx = q[head++], x = idx % G, y = (idx - (idx % G)) / G, nb = neigh4(idx, x, y, G);
        for (var j = 0; j < nb.length; j++) { var m = nb[j]; if (!fieldComp[m] && !inBase[m] && openEither(m)) { fieldComp[m] = nf; q[tail++] = m; } }
      }
    }
    // each base -> the set of field components its cells touch
    bases.forEach(function (b) {
      var comps = new Set();
      for (var k = 0; k < b.cells.length; k++) {
        var i = b.cells[k], x = i % G, y = (i - (i % G)) / G, nb = neigh4(i, x, y, G);
        for (var j = 0; j < nb.length; j++) { var fc = fieldComp[nb[j]]; if (fc) comps.add(fc); }
      }
      b.comps = comps;
    });
    // routes(b) = total avg-openings of OTHER bases sharing any field component
    bases.forEach(function (b) {
      var routes = 0, connected = [];
      bases.forEach(function (o) {
        if (o.id === b.id) return;
        var share = false; o.comps.forEach(function (c) { if (b.comps.has(c)) share = true; });
        if (share) { routes += o.avgOpenings; connected.push(o.id); }
      });
      b.routes = routes; b.connectedTo = connected;
    });

    // ---- neighbour support: strong bases nearby make this one easier to hold ----
    var maxIntrinsic = 1; bases.forEach(function (b) { if (b.intrinsicAvg > maxIntrinsic) maxIntrinsic = b.intrinsicAvg; });
    var meanOpen = 0; bases.forEach(function (b) { meanOpen += b.avgOpenings; }); meanOpen = (meanOpen / (bases.length || 1)) || 1;
    bases.forEach(function (b) {
      var support = 0;
      bases.forEach(function (o) {
        if (o.id === b.id) return;
        var d = Math.hypot(b.cx - o.cx, b.cy - o.cy);
        support += o.intrinsicAvg * Math.exp(-d / W.supportSigma);
      });
      b.support = support;
      b.supportNorm = support / maxIntrinsic;            // ~ number of strong close neighbours
      b.routesNorm = b.routes / meanOpen;                // ~ extra routes vs a typical base
      b.modifier = (1 + W.support * b.supportNorm) / (1 + W.routes * b.routesNorm);
      b.strength = b.intrinsicAvg * b.modifier;
      b.strengthBest = b.intrinsicBest * b.modifier;
      b.strengthWorst = b.intrinsicWorst * b.modifier;
    });

    // ---- normalise to 0..100 (relative to the strongest base) + aggregate ----
    var maxStrength = 1; bases.forEach(function (b) { if (b.strength > maxStrength) maxStrength = b.strength; });
    var sum = 0, weakest = null;
    bases.forEach(function (b) {
      b.strength100 = 100 * b.strength / maxStrength;
      sum += b.strength;
      if (!weakest || b.strength < weakest.strength) weakest = b;
    });

    return {
      weights: W,
      bases: bases.map(function (b) {
        return {
          id: b.id, area: b.area, centroid: { x: b.cx, y: b.cy },
          red: b.red, blue: b.blue,
          intrinsicBest: b.intrinsicBest, intrinsicWorst: b.intrinsicWorst, intrinsicAvg: b.intrinsicAvg,
          avgOpenings: b.avgOpenings, support: b.support, routes: b.routes, connectedTo: b.connectedTo,
          modifier: b.modifier,
          strength: b.strength, strengthBest: b.strengthBest, strengthWorst: b.strengthWorst, strength100: b.strength100,
        };
      }),
      aggregate: {
        count: bases.length,
        avgStrength: bases.length ? sum / bases.length : 0,
        weakest: weakest ? { id: weakest.id, strength: weakest.strength } : null,
      },
    };
  }

  var api = { computeBaseStrengths: computeBaseStrengths, DEFAULT_WEIGHTS: DEFAULT_WEIGHTS, groupRuns: groupRuns };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.BaseStrength = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
