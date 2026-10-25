"use strict";

/* =========================================================
 * Pure helpers (no DOM) — kept at top so they are testable.
 * ========================================================= */

const SIZE = 5;
const CELLS = 25;

/* All 12 winning lines of a 5x5 board (cell indices, row-major). */
const LINES = (() => {
  const lines = [];
  for (let r = 0; r < SIZE; r++) {
    lines.push([0, 1, 2, 3, 4].map((c) => r * SIZE + c));
  }
  for (let c = 0; c < SIZE; c++) {
    lines.push([0, 1, 2, 3, 4].map((r) => r * SIZE + c));
  }
  lines.push([0, 6, 12, 18, 24]); // main diagonal
  lines.push([4, 8, 12, 16, 20]); // anti-diagonal
  return lines;
})();

/* Parse a reveal-code / grid string like "12,5,23,..." or "12 5 23 ...".
 * Returns an array of 25 ints 1..25 (no repeats) or null if invalid. */
function parseGrid(text) {
  if (typeof text !== "string") return null;
  const parts = text.trim().split(/[\s,;]+/).filter(Boolean);
  if (parts.length !== CELLS) return null;
  const seen = new Set();
  const out = [];
  for (const p of parts) {
    if (!/^\d{1,2}$/.test(p)) return null;
    const n = parseInt(p, 10);
    if (n < 1 || n > 25 || seen.has(n)) return null;
    seen.add(n);
    out.push(n);
  }
  return out;
}

function isValidGrid(arr) {
  if (!Array.isArray(arr) || arr.length !== CELLS) return false;
  const seen = new Set();
  for (const n of arr) {
    if (!Number.isInteger(n) || n < 1 || n > 25 || seen.has(n)) return false;
    seen.add(n);
  }
  return true;
}

/* ---------- SHA-256 ---------- */

const K256 = [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const rotr = (x, n) => ((x >>> n) | (x << (32 - n))) >>> 0;

/* Pure-JS SHA-256 fallback (used when crypto.subtle is unavailable). */
function sha256Fallback(input) {
  const bytes = new TextEncoder().encode(input);
  const bitLenHi = Math.floor((bytes.length / 0x20000000)) >>> 0; // len*8 / 2^32
  const bitLenLo = (bytes.length * 8) >>> 0;
  const total = Math.ceil((bytes.length + 9) / 64) * 64;
  const msg = new Uint8Array(total);
  msg.set(bytes);
  msg[bytes.length] = 0x80;
  const dv = new DataView(msg.buffer);
  dv.setUint32(total - 8, bitLenHi);
  dv.setUint32(total - 4, bitLenLo);

  const H = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
  ];
  const w = new Uint32Array(64);

  for (let off = 0; off < total; off += 64) {
    for (let i = 0; i < 16; i++) w[i] = dv.getUint32(off + i * 4);
    for (let i = 16; i < 64; i++) {
      const a15 = w[i - 15], a2 = w[i - 2];
      const s0 = rotr(a15, 7) ^ rotr(a15, 18) ^ (a15 >>> 3);
      const s1 = rotr(a2, 17) ^ rotr(a2, 19) ^ (a2 >>> 10);
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) >>> 0;
    }
    let a = H[0], b = H[1], c = H[2], d = H[3];
    let e = H[4], f = H[5], g = H[6], h = H[7];
    for (let i = 0; i < 64; i++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + K256[i] + w[i]) >>> 0;
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) >>> 0;
      h = g; g = f; f = e;
      e = (d + t1) >>> 0;
      d = c; c = b; b = a;
      a = (t1 + t2) >>> 0;
    }
    const add = (x, y) => (x + y) >>> 0;
    H[0] = add(H[0], a); H[1] = add(H[1], b); H[2] = add(H[2], c); H[3] = add(H[3], d);
    H[4] = add(H[4], e); H[5] = add(H[5], f); H[6] = add(H[6], g); H[7] = add(H[7], h);
  }
  return H.map((x) => x.toString(16).padStart(8, "0")).join("");
}

/* Hex-encoded SHA-256 of a UTF-8 string.
 * Uses the browser's native crypto.subtle when available (HTTPS / secure
 * context), otherwise falls back to the pure-JS implementation. */
async function sha256Hex(str) {
  if (typeof crypto !== "undefined" && crypto.subtle) {
    try {
      const buf = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(str));
      return Array.from(new Uint8Array(buf), (b) => b.toString(16).padStart(2, "0")).join("");
    } catch (e) { /* fall through to JS fallback */ }
  }
  return sha256Fallback(str);
}

/* Canonical string that is hashed: the grid in row-major order. */
const canonical = (grid) => grid.join(",");

/* Allow simple Node-based unit tests of the pure helpers. */
if (typeof module !== "undefined" && module.exports) {
  module.exports = { LINES, parseGrid, isValidGrid, sha256Fallback, sha256Hex, canonical };
}

/* =========================================================
 * App (DOM) code — only runs in the browser.
 * ========================================================= */

if (typeof document !== "undefined" && document.getElementById) {

  const STATE_KEY = "bingo25_state";
  const state = loadState(); // { grid: [], crossed: [], won: false, hash: "" }

  /* ---------- state ---------- */

  function loadState() {
    try {
      const s = JSON.parse(localStorage.getItem(STATE_KEY));
      if (s && isValidGrid(s.grid) && Array.isArray(s.crossed)) {
        const valid = (n) => Number.isInteger(n) && n >= 1 && n <= 25;
        return {
          grid: s.grid,
          crossed: s.crossed.filter((n) => s.grid.includes(n)),
          pool: Array.isArray(s.pool) ? s.pool.filter(valid) : [],
          won: !!s.won,
          hash: typeof s.hash === "string" ? s.hash : "",
        };
      }
    } catch (e) { /* ignore */ }
    return { grid: [], crossed: [], pool: [], won: false, hash: "" };
  }

  function saveState() {
    try {
      localStorage.setItem(STATE_KEY, JSON.stringify(state));
    } catch (e) { /* ignore (private mode etc.) */ }
  }

  /* ---------- screen switching ---------- */

  let lastScreen = "screen-setup";
  function show(id) {
    if (id !== "screen-verify") lastScreen = id;
    document.querySelectorAll("main section").forEach((s) => { s.hidden = s.id !== id; });
  }

  /* ---------- setup screen ---------- */

  const setupGridEl = document.getElementById("setup-grid");
  const setupStatus = document.getElementById("setup-status");
  const setupError = document.getElementById("setup-error");
  const btnHash = document.getElementById("btn-hash");
  const setupInputs = [];

  for (let i = 0; i < CELLS; i++) {
    const inp = document.createElement("input");
    inp.type = "text";
    inp.inputMode = "numeric";
    inp.autocomplete = "off";
    inp.maxLength = 2;
    inp.setAttribute("aria-label", "Cell " + (i + 1));
    inp.dataset.idx = i;
    setupInputs.push(inp);
    setupGridEl.appendChild(inp);
    inp.addEventListener("input", onSetupInput);
    inp.addEventListener("keydown", onSetupKey);
  }

  function prefillSetup() {
    if (isValidGrid(state.grid)) {
      setupInputs.forEach((inp, i) => { inp.value = String(state.grid[i]); });
    }
    refreshSetup();
  }

  function focusCell(idx) {
    if (idx >= 0 && idx < CELLS) setupInputs[idx].focus();
  }

  function onSetupInput(e) {
    const inp = e.target;
    const cleaned = inp.value.replace(/\D/g, "").slice(0, 2);
    inp.value = cleaned;
    if (cleaned.length === 2) focusCell(Number(inp.dataset.idx) + 1);
    refreshSetup();
  }

  function onSetupKey(e) {
    const idx = Number(e.target.dataset.idx);
    if (e.key === "Enter") { e.preventDefault(); focusCell(idx + 1); }
    else if (e.key === "Backspace" && e.target.value === "") focusCell(idx - 1);
    else if (e.key === "ArrowRight" || e.key === "ArrowDown") { e.preventDefault(); focusCell(idx + 1); }
    else if (e.key === "ArrowLeft" || e.key === "ArrowUp") { e.preventDefault(); focusCell(idx - 1); }
  }

  function readSetupValues() {
    return setupInputs.map((inp) => {
      const v = inp.value;
      return /^\d{1,2}$/.test(v) ? parseInt(v, 10) : null;
    });
  }

  function refreshSetup() {
    const vals = readSetupValues();
    setupInputs.forEach((inp) => inp.classList.remove("dup", "bad"));

    const filled = vals.filter((v) => v !== null).length;
    const duplicates = new Set(
      vals.filter((v, i) => v !== null && vals.indexOf(v) !== i)
    );
    const outOfRange = new Set(
      vals.filter((v) => v !== null && (v < 1 || v > 25))
    );

    setupInputs.forEach((inp, i) => {
      const v = vals[i];
      if (v === null) return;
      if (duplicates.has(v)) inp.classList.add("dup");
      if (outOfRange.has(v)) inp.classList.add("bad");
    });

    setupStatus.textContent = filled === CELLS
      ? "All 25 filled ✓"
      : `${filled} / ${CELLS} filled`;
    setupStatus.classList.toggle("ok", filled === CELLS);

    if (duplicates.size > 0 || outOfRange.size > 0 || filled < CELLS) {
      const problems = [];
      if (outOfRange.size > 0) problems.push("numbers must be 1–25");
      if (duplicates.size > 0) {
        problems.push("duplicates found: " + [...duplicates].sort((a, b) => a - b).join(", "));
      }
      if (filled < CELLS) setupError.textContent = "Fill all 25 cells. " + problems.join("; ");
      else setupError.textContent = "Fix to generate hash: " + problems.join("; ");
      setupError.hidden = false;
      btnHash.disabled = true;
    } else {
      setupError.hidden = true;
      btnHash.disabled = false;
    }
  }

  /* generate hash */
  document.getElementById("btn-hash").addEventListener("click", async () => {
    const vals = readSetupValues();
    if (!isValidGrid(vals)) return;
    state.grid = vals;
    state.crossed = [];
    state.pool = [];
    state.won = false;
    state.hash = await sha256Hex(canonical(vals));
    saveState();
    document.getElementById("hash-out").textContent = state.hash;
    refreshPlay();
    show("screen-hash");
  });

  document.getElementById("btn-clear").addEventListener("click", () => {
    setupInputs.forEach((inp) => { inp.value = ""; });
    state.grid = [];
    state.crossed = [];
    state.pool = [];
    state.won = false;
    state.hash = "";
    saveState();
    refreshSetup();
    setupInputs[0].focus();
  });

  /* random grid: shuffled permutation of 1..25 */
  document.getElementById("btn-random").addEventListener("click", () => {
    const bag = Array.from({ length: CELLS }, (_, i) => i + 1);
    if (typeof crypto !== "undefined" && crypto.getRandomValues) {
      const rnd = crypto.getRandomValues(new Uint32Array(CELLS));
      for (let i = bag.length - 1; i > 0; i--) {
        const j = Math.floor((rnd[i] / 4294967296) * (i + 1));
        [bag[i], bag[j]] = [bag[j], bag[i]];
      }
    } else {
      for (let i = bag.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [bag[i], bag[j]] = [bag[j], bag[i]];
      }
    }
    setupInputs.forEach((inp, i) => { inp.value = String(bag[i]); });
    refreshSetup();
  });

  document.getElementById("btn-start-play").addEventListener("click", () => {
    refreshPlay();
    show("screen-play");
  });

  document.getElementById("btn-edit-grid").addEventListener("click", () => {
    if (!confirmEditGrid()) return;
    prefillSetup();
    show("screen-setup");
  });

  document.getElementById("btn-go-verify").addEventListener("click", () => {
    prefillVerify();
    show("screen-verify");
  });

  function confirmEditGrid() {
    const hasProgress = state.crossed.length > 0 || state.won;
    return !hasProgress ||
      confirm("Editing your grid resets your crosses and makes a new hash. Continue?");
  }

  /* ---------- play screen ---------- */

  const playGridEl = document.getElementById("play-grid");
  const playStatus = document.getElementById("play-status");
  const callMsg = document.getElementById("call-msg");
  const callInput = document.getElementById("call-input");
  const poolEl = document.getElementById("pool");
  const cellEls = [];

  for (let i = 0; i < CELLS; i++) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "cell";
    btn.dataset.idx = i;
    playGridEl.appendChild(btn);
    cellEls.push(btn);
    btn.addEventListener("click", () => toggleCross(i));
  }

  function refreshPlay() {
    for (let i = 0; i < CELLS; i++) {
      cellEls[i].textContent = isValidGrid(state.grid) ? String(state.grid[i]) : "?";
    }
    renderPlay();
  }

  function renderPlay() {
    const winLine = findWinLine();
    for (let i = 0; i < CELLS; i++) {
      cellEls[i].classList.toggle("crossed", state.crossed.includes(state.grid[i]));
      cellEls[i].classList.toggle("win", !!winLine && winLine.includes(i));
    }
    if (winLine) {
      playStatus.textContent = "🎉 BINGO! You win — send the reveal code to your friend for verification.";
      playStatus.classList.add("ok");
    } else {
      const best = bestLineCount();
      playStatus.textContent = `${state.crossed.length} of 25 crossed · closest line: ${best} / 5`;
      playStatus.classList.remove("ok");
    }
    renderPool();
  }

  function renderPool() {
    poolEl.innerHTML = "";
    if (!state.pool.length) {
      const empty = document.createElement("span");
      empty.className = "chip empty";
      empty.textContent = "nothing called yet";
      poolEl.appendChild(empty);
      return;
    }
    state.pool.forEach((n, i) => {
      const chip = document.createElement("span");
      chip.className = "chip";
      chip.textContent = n;
      if (state.crossed.includes(n)) chip.classList.add("hit");
      if (i === state.pool.length - 1) chip.classList.add("latest");
      poolEl.appendChild(chip);
    });
  }

  function toggleCross(idx) {
    if (!isValidGrid(state.grid)) return;
    const num = state.grid[idx];
    const pos = state.crossed.indexOf(num);
    if (pos !== -1) {
      // uncross: drop the number from the draw pool as well (middle entries keep order)
      state.crossed.splice(pos, 1);
      const ppos = state.pool.indexOf(num);
      if (ppos !== -1) state.pool.splice(ppos, 1);
      callMsg.textContent = "";
      if (!findWinLine()) state.won = false; // re-arm Bingo if win line undone
    } else {
      // re-cross: append at the end = logged at its last call position
      if (!state.pool.includes(num)) state.pool.push(num);
      state.crossed.push(num);
      if (checkWin()) return; // checkWin saves/renders itself
      callMsg.textContent = "";
    }
    saveState();
    renderPlay();
  }

  function doCall() {
    if (!isValidGrid(state.grid)) { show("screen-setup"); return; }
    callMsg.classList.remove("error");
    const raw = callInput.value.trim();
    const n = /^\d{1,2}$/.test(raw) ? parseInt(raw, 10) : NaN;
    if (isNaN(n) || n < 1 || n > 25) {
      callMsg.textContent = "Enter a number from 1 to 25.";
      callMsg.classList.add("error");
      return;
    }
    const inPool = state.pool.includes(n);
    const idx = state.grid.indexOf(n);
    if (idx === -1) {
      if (!inPool) { state.pool.push(n); saveState(); renderPlay(); }
      callMsg.textContent = inPool ? `${n} was called but is not in your grid.`
                                   : `${n} is not in your grid (noted in the draw pool).`;
      callMsg.classList.add("error");
      return;
    }
    if (state.crossed.includes(n)) {
      callMsg.textContent = `${n} is already crossed.`;
      callMsg.classList.add("error");
      return;
    }
    if (!inPool) state.pool.push(n);
    state.crossed.push(n);
    callInput.value = "";
    if (checkWin()) return;
    callMsg.textContent = `Crossed ${n}.`;
    saveState();
    renderPlay();
    callInput.focus();
  }

  document.getElementById("btn-call").addEventListener("click", doCall);
  callInput.addEventListener("keydown", (e) => {
    if (e.key === "Enter") { e.preventDefault(); doCall(); }
  });

  /* undo the most recent call: remove from pool and un-cross if crossed */
  document.getElementById("btn-undo-call").addEventListener("click", () => {
    if (!state.pool.length) {
      callMsg.textContent = "Nothing to undo — the draw pool is empty.";
      return;
    }
    const n = state.pool.pop();
    callMsg.classList.remove("error");
    callMsg.textContent = `Undid call ${n}.`;
    const pos = state.crossed.indexOf(n);
    if (pos !== -1) {
      state.crossed.splice(pos, 1);
      if (!findWinLine()) state.won = false;
    }
    saveState();
    renderPlay();
  });

  document.getElementById("btn-reset-crosses").addEventListener("click", () => {
    if (state.crossed.length && !confirm("Clear all crosses and restart the game?")) return;
    state.crossed = [];
    state.pool = [];
    state.won = false;
    saveState();
    callMsg.textContent = "";
    renderPlay();
  });

  document.getElementById("btn-go-verify-2").addEventListener("click", () => {
    prefillVerify();
    show("screen-verify");
  });

  document.getElementById("btn-edit-grid-2").addEventListener("click", () => {
    if (!confirmEditGrid()) return;
    prefillSetup();
    show("screen-setup");
  });

  /* ---------- win detection ---------- */

  function crossedIdxSet() {
    return new Set(state.grid.map((n, i) => (state.crossed.includes(n) ? i : -1)).filter((i) => i >= 0));
  }

  function findWinLine() {
    const idxSet = crossedIdxSet();
    for (const line of LINES) {
      if (line.every((i) => idxSet.has(i))) return line;
    }
    return null;
  }

  function bestLineCount() {
    const idxSet = crossedIdxSet();
    let best = 0;
    for (const line of LINES) {
      let c = 0;
      for (const i of line) if (idxSet.has(i)) c++;
      if (c > best) best = c;
    }
    return best;
  }

  function checkWin() {
    const line = findWinLine();
    if (!line) return false;
    const firstWin = !state.won; // avoid re-popping the overlay mid-game
    state.won = true;
    saveState();
    renderPlay();
    if (firstWin) {
      document.getElementById("reveal-code").textContent = canonical(state.grid);
      document.getElementById("bingo-overlay").hidden = false;
    }
    return firstWin;
  }

  document.getElementById("btn-bingo-close").addEventListener("click", () => {
    document.getElementById("bingo-overlay").hidden = true;
    show("screen-play");
  });

  /* ---------- verify screen ---------- */

  const verifyHashIn = document.getElementById("verify-hash");
  const verifyRevealIn = document.getElementById("verify-reveal");
  const verifyResult = document.getElementById("verify-result");

  function prefillVerify() {
    if (state.hash) verifyHashIn.value = state.hash;
  }

  document.getElementById("btn-verify").addEventListener("click", async () => {
    verifyResult.className = "status";
    const grid = parseGrid(verifyRevealIn.value);
    const claimedHash = verifyHashIn.value.trim().toLowerCase();

    if (!claimedHash || !/^[0-9a-f]{64}$/i.test(claimedHash)) {
      verifyResult.textContent = "✘ That doesn't look like a SHA-256 hash (64 hex characters).";
      verifyResult.classList.add("error");
      return;
    }
    if (!grid) {
      verifyResult.textContent = "✘ Reveal code invalid: it must be 25 unique numbers from 1–25.";
      verifyResult.classList.add("error");
      return;
    }

    const actual = await sha256Hex(canonical(grid));
    if (actual === claimedHash) {
      verifyResult.textContent = `✔ Verified! The revealed grid matches the shared hash. Grid was: ${canonical(grid)}`;
      verifyResult.classList.add("ok");
    } else {
      verifyResult.textContent = "✘ Mismatch — the revealed grid does NOT match the shared hash. Invalid win claim!";
      verifyResult.classList.add("error");
    }
  });

  document.getElementById("btn-back").addEventListener("click", () => show(lastScreen));

  /* ---------- copy buttons ---------- */

  function wireCopy(btnId, sourceEl) {
    document.getElementById(btnId).addEventListener("click", async () => {
      const text = sourceEl.textContent.trim();
      const btn = document.getElementById(btnId);
      let ok = false;
      try {
        await navigator.clipboard.writeText(text);
        ok = true;
      } catch (e) {
        try {
          const ta = document.createElement("textarea");
          ta.value = text;
          ta.style.position = "fixed";
          ta.style.opacity = "0";
          document.body.appendChild(ta);
          ta.select();
          ok = document.execCommand("copy");
          ta.remove();
        } catch (e2) { /* ignore */ }
      }
      const old = btn.textContent;
      btn.textContent = ok ? "Copied ✓" : "Copy failed — select manually";
      setTimeout(() => { btn.textContent = old; }, 1500);
    });
  }

  wireCopy("btn-copy-hash", document.getElementById("hash-out"));
  wireCopy("btn-copy-reveal", document.getElementById("reveal-code"));

  /* ---------- init ---------- */

  prefillSetup();
  refreshSetup();
  refreshPlay();
  show(isValidGrid(state.grid) ? "screen-play" : "screen-setup");
}
