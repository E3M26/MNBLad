// MNBLad simülatörü (paket 9): firmware V2.13 yorumlayıcısının tarayıcı kopyası.
// Kartla aynı metin komutlarını alır, aynı JSON yanıtlarını verir; panel onu sahte bir seri port gibi kullanır.
// Firmware'deki execProgram / parseIns değişirse burası da güncellenmeli (MNBLad.ino ile birlikte).
// Kapsam dışı: Modbus (MB kutusu durum −3 yazar), kalıcı hafıza, giriş filtresi, RS485.
"use strict";
(function () {
  const N_M = 256, N_T = 32, N_C = 32, N_D = 64, N_EDGE = 128, N_ROWS = 8, N_S = 9, N_RT = 9, MAX_INS = 2048;
  const SCAN_MS = 10, AI_MAX = 3000, PWM_MAX = 1000;
  const ALL_PINS = [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 38, 39, 40, 41, 42, 47];
  const MODES = ["OFF", "DI", "DIPU", "DIPD", "DO", "AI", "PWM"];
  const OPS = ["L", "L0", "A", "AN", "AP", "AF", "CMP", "O", "OUT", "OUTN", "SET", "RST",
    "TON", "TOF", "TP", "CTU", "CTD", "MOV", "ADD", "SUB", "MUL", "DIV",
    "MOD", "MIN", "MAX", "ABS", "LIMIT", "SCALE", "MB", "TW",
    "TONR", "CTUD", "AND", "OR", "XOR", "NOT", "SHL", "SHR",
    "LBL", "SBR", "JMP", "CALL", "RET", "PID"];
  const N_F = 64, N_PID = 16;
  const f32 = Math.fround;
  const lround = (v) => v < 0 ? -Math.round(-v) : Math.round(v);   // C lroundf: yarım sıfırdan uzağa
  const N_LBL = 64, CALL_DEPTH = 8;
  const CMPS = ["EQ", "NE", "GT", "LT", "GE", "LE"];
  const STORE = "mnblad.sim.state";
  const isAdc = (p) => p >= 1 && p <= 18 && p !== 3;
  const isInOnly = (p) => p === 0;
  const isDi = (m) => m === "DI" || m === "DIPU" || m === "DIPD";
  const i32 = (v) => v | 0;

  function crc32(str) {
    let c = 0xFFFFFFFF;
    for (const b of new TextEncoder().encode(str)) { c ^= b; for (let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xEDB88320 & -(c & 1)); }
    return (c ^ 0xFFFFFFFF) >>> 0;
  }

  function create({ onMsg, pinModes }) {
    // ---- Kalıcı simülasyon durumu (tarayıcıda): pin modları, program, kaynak, ad ----
    let saved = {};
    try { saved = JSON.parse(localStorage.getItem(STORE) || "{}"); } catch {}
    const modes = {};
    for (const p of ALL_PINS) modes[p] = (saved.modes && saved.modes[p]) || (pinModes && pinModes[p]) || (p === 0 ? "DIPU" : "OFF");
    let progLines = Array.isArray(saved.prog) ? saved.prog : [];
    let prog = [];
    let pcrc = saved.pcrc || "", pt = saved.pt || 0, pn = saved.pn || "", src = saved.src || null;  // src: base64
    let pwmf = saved.pwmf || 1000;
    let runSt = saved.runst ? 1 : 0;
    const save = () => { try { localStorage.setItem(STORE, JSON.stringify({ modes, prog: progLines, pcrc, pt, pn, src, pwmf, runst: runSt })); } catch {} };

    // ---- Proses imajı ----
    const inImg = {}, qImg = {}, aiImg = {}, pwImg = {}, doState = {}, simIn = {}, simAi = {};
    const mBits = new Uint8Array(N_M), dWords = new Int32Array(N_D), edges = new Uint8Array(N_EDGE);
    const fRegs = new Float32Array(64);
    let pidSt = [];
    const tim = [], cnt = [];
    const force = {};   // "I4" -> 0/1, "Q1" -> 0/1, "AI2" -> mV
    for (const p of ALL_PINS) { inImg[p] = qImg[p] = aiImg[p] = pwImg[p] = doState[p] = simAi[p] = 0; simIn[p] = modes[p] === "DIPU" ? 1 : 0; }
    function clearMemory() {
      mBits.fill(0); dWords.fill(0); edges.fill(0); fRegs.fill(0);
      pidSt = Array.from({ length: 16 }, () => ({ i: 0, prevPv: 0, init: 0 }));
      for (let i = 0; i < N_T; i++) tim[i] = { acc: 0, q: 0, run: 0, prev: 0 };
      for (let i = 0; i < N_C; i++) cnt[i] = { cv: 0, pv: 0, q: 0, prev: 0, down: 0, init: 0, prevd: 0 };
      for (const p of ALL_PINS) qImg[p] = 0;
    }
    clearMemory();

    let running = false, firstScan = false, loading = false, stage = [], stageText = "";
    let scanUs = 0, lastScan = performance.now();
    const t0 = performance.now();
    const millis = () => Math.floor(performance.now() - t0);
    let tzMin = -new Date().getTimezoneOffset();

    // ---- Saat (PC saati) ----
    const rtW = new Int32Array(N_RT);
    let rtLocal = 0;
    function rtUpdate() {
      const now = Math.floor(Date.now() / 1000);
      rtLocal = now + tzMin * 60;
      const d = new Date(rtLocal * 1000);
      rtW[0] = d.getUTCFullYear(); rtW[1] = d.getUTCMonth() + 1; rtW[2] = d.getUTCDate();
      rtW[3] = d.getUTCHours(); rtW[4] = d.getUTCMinutes(); rtW[5] = d.getUTCSeconds();
      rtW[6] = d.getUTCDay() || 7; rtW[7] = rtW[3] * 60 + rtW[4]; rtW[8] = 1;
    }
    const hhmmOk = (v) => v >= 0 && v <= 2359 && v % 100 < 60;
    function twActive(on, off, days) {
      if (!hhmmOk(on) || !hhmmOk(off)) return false;
      const now = rtW[7], a = Math.floor(on / 100) * 60 + on % 100, b = Math.floor(off / 100) * 60 + off % 100, wd = rtW[6] - 1;
      if (a === b) return false;
      if (a < b) return !!((days >> wd) & 1) && now >= a && now < b;
      if (now >= a) return !!((days >> wd) & 1);
      return now < b && !!((days >> ((wd + 6) % 7)) & 1);
    }

    // ---- Adresler ----
    function parseOpd(s) {
      if (s == null || s === "") return null;
      s = String(s).toUpperCase();
      if (/^-?\d+$/.test(s)) return { area: "K", v: i32(parseInt(s, 10)) };
      if (/^-?\d+\.\d*$/.test(s)) { const v = f32(parseFloat(s)); return isFinite(v) ? { area: "KF", v } : null; }
      let m = /^(AI|PW|RT|HC|HF)(\d+)$/.exec(s) || /^([IQMTCDSF])(\d+)$/.exec(s);
      return m ? { area: m[1], v: +m[2] } : null;
    }
    const isIo = (p) => ALL_PINS.includes(p);
    function opdValid(o) {
      if (!o) return false;
      switch (o.area) {
        case "K": return true;
        case "I": case "Q": return isIo(o.v);
        case "AI": return isIo(o.v) && isAdc(o.v);
        case "PW": return isIo(o.v) && !isInOnly(o.v);
        case "M": return o.v < N_M; case "T": return o.v < N_T; case "C": return o.v < N_C;
        case "D": return o.v < N_D; case "S": return o.v < N_S; case "RT": return o.v < N_RT;
        case "F": return o.v < N_F; case "KF": return true;
        case "HC": case "HF": return o.v < 4;
      }
      return false;
    }
    const isBitArea = (a) => ["I", "Q", "M", "T", "C", "S", "K"].includes(a);
    const isDst = (o) => o && (o.area === "D" || o.area === "PW" || o.area === "F" || o.area === "HC") && opdValid(o);   // HC: simülasyonda sayıcı yok

    function rdBit(o) {
      switch (o.area) {
        case "I": return !!inImg[o.v];
        case "Q": return !!qImg[o.v];
        case "M": return !!mBits[o.v];
        case "T": return !!tim[o.v].q;
        case "C": return !!cnt[o.v].q;
        case "K": return o.v !== 0;
        case "S": {
          const ms = millis();
          switch (o.v) {
            case 0: return firstScan;
            case 1: return !!(Math.floor(ms / 500) & 1);
            case 2: return true;
            case 3: return false;
            case 4: return !!(Math.floor(ms / 50) & 1);
            case 5: return !!(Math.floor(ms / 250) & 1);
            case 6: return !!(Math.floor(ms / 1000) & 1);
            case 7: return !!(Math.floor(ms / 30000) & 1);
            default: return true;    // S8: saat ayarlı (PC saati)
          }
        }
        default: return rdWord(o) !== 0;
      }
    }
    function rdWord(o) {
      switch (o.area) {
        case "K": return o.v;
        case "D": return dWords[o.v];
        case "AI": return aiImg[o.v];
        case "PW": return pwImg[o.v];
        case "RT": return rtW[o.v];
        case "F": return isFinite(fRegs[o.v]) ? lround(fRegs[o.v]) : 0;
        case "KF": return lround(o.v);
        case "HC": case "HF": return 0;   // simülasyonda hızlı sayıcı donanımı yok
        case "T": return tim[o.v].acc;
        case "C": return cnt[o.v].cv;
        default: return rdBit(o) ? 1 : 0;
      }
    }
    function wrBit(o, v) { if (o.area === "Q") qImg[o.v] = v ? 1 : 0; else if (o.area === "M") mBits[o.v] = v ? 1 : 0; }
    function wrWord(o, v) {
      if (o.area === "D") dWords[o.v] = i32(v);
      else if (o.area === "PW") pwImg[o.v] = Math.max(0, Math.min(PWM_MAX, i32(v)));
    }
    const isFlt = (o) => o && (o.area === "F" || o.area === "KF");
    const rdF = (o) => o.area === "F" ? fRegs[o.v] : o.area === "KF" ? o.v : rdWord(o);
    function wrF(o, v) {
      if (o.area === "F") { fRegs[o.v] = isFinite(v) ? v : 0; return; }
      if (!isFinite(v)) v = 0;
      wrWord(o, Math.max(-2147483648, Math.min(2147483520, lround(v))));
    }
    function doCmp(c, a, b) { return [a === b, a !== b, a > b, a < b, a >= b, a <= b][c]; }
    function resetCounter(c) { c.cv = c.down ? c.pv : 0; c.q = c.down ? (c.cv <= 0 ? 1 : 0) : (c.cv >= c.pv ? 1 : 0); }

    // ---- Komut ayrıştırma (firmware parseIns + insValid) ----
    function parseIns(line) {
      const tok = line.trim().split(/\s+/);
      const op = OPS.indexOf(String(tok[0]).toUpperCase());
      if (op < 0) return "bilinmeyen komut";
      const name = OPS[op], n = tok.length;
      const ins = { op: name, r: 0, x: 0, e: 0 };
      const P = (k, i) => { ins[k] = parseOpd(tok[i]); return !!ins[k]; };
      if (name === "LBL" || name === "SBR") {
        if (n !== 2) return "kullanim: LBL n / SBR n";
        ins.x = parseInt(tok[1], 10); return ins.x >= 0 && ins.x < N_LBL ? ins : "etiket/alt program 0..63";
      }
      if (name === "JMP" || name === "CALL") {
        if (n !== 3) return "kullanim: JMP r n / CALL r n";
        ins.r = parseInt(tok[1], 10); ins.x = parseInt(tok[2], 10);
        if (!(ins.r >= 0 && ins.r < N_ROWS)) return "satir 0..7";
        return ins.x >= 0 && ins.x < N_LBL ? ins : "hedef 0..63";
      }
      if (name === "RET") { if (n !== 2) return "kullanim: RET r"; ins.r = parseInt(tok[1], 10); return ins.r >= 0 && ins.r < N_ROWS ? ins : "satir 0..7"; }
      if (name === "O") { if (n !== 2) return "kullanim: O mask"; ins.x = parseInt(tok[1], 10) || 0; return ins.x ? ins : "bos maske"; }
      if (n < 2) return "eksik arguman";
      ins.r = parseInt(tok[1], 10);
      if (!(ins.r >= 0 && ins.r < N_ROWS)) return "satir 0..7";
      const bad = (m) => m;
      switch (name) {
        case "L": case "L0": if (n !== 2) return "fazla arguman"; return ins;
        case "A": case "AN":
          if (n !== 3 || !P("a", 2) || !opdValid(ins.a) || !isBitArea(ins.a.area)) return "gecersiz bit adresi"; return ins;
        case "AP": case "AF":
          if (n !== 4 || !P("a", 2) || !opdValid(ins.a) || !isBitArea(ins.a.area)) return "gecersiz bit adresi";
          ins.e = parseInt(tok[3], 10); return ins.e >= 0 && ins.e < N_EDGE ? ins : "kenar hafizasi 0..127";
        case "OUT": case "OUTN": case "SET":
          if (n !== 3 || !P("a", 2) || !opdValid(ins.a) || !["Q", "M"].includes(ins.a.area)) return "cikis Q veya M olmali"; return ins;
        case "RST":
          if (n !== 3 || !P("a", 2) || !opdValid(ins.a) || !["Q", "M", "T", "C", "HC"].includes(ins.a.area)) return "RST hedefi Q, M, T, C veya HC olmali"; return ins;
        case "CMP":
          if (n !== 5) return "kullanim: CMP r op A B";
          ins.x = CMPS.indexOf(String(tok[2]).toUpperCase()); if (ins.x < 0) return "gecersiz karsilastirma";
          return P("a", 3) && P("b", 4) && opdValid(ins.a) && opdValid(ins.b) ? ins : "gecersiz adres";
        case "TON": case "TOF": case "TP": case "TONR":
          return n === 4 && P("a", 2) && P("b", 3) && ins.a.area === "T" && opdValid(ins.a) && opdValid(ins.b) ? ins : "zamanlayici T0..31, PT gecersiz";
        case "CTU": case "CTD":
          return n === 4 && P("a", 2) && P("b", 3) && ins.a.area === "C" && opdValid(ins.a) && opdValid(ins.b) ? ins : "sayici C0..31, PV gecersiz";
        case "CTUD":
          if (!(n === 5 && P("a", 2) && P("b", 3) && P("d", 4) && ins.a.area === "C" && opdValid(ins.a) && opdValid(ins.b))) return "kullanim: CTUD r Cn PV GERI_BIT";
          return opdValid(ins.d) && isBitArea(ins.d.area) ? ins : "CTUD: geri sayma girisi bit adresi olmali";
        case "MOV": case "ABS": case "NOT":
          return n === 4 && P("a", 2) && P("c", 3) && opdValid(ins.a) && isDst(ins.c) ? ins : "hedef D veya PW olmali";
        case "LIMIT":
          return n === 6 && P("a", 2) && P("b", 3) && P("d", 4) && P("c", 5) && [ins.a, ins.b, ins.d].every(opdValid) && isDst(ins.c) ? ins : "kullanim: LIMIT r IN MIN MAX DST";
        case "SCALE":
          return n === 8 && P("a", 2) && P("b", 3) && P("d", 4) && P("f", 5) && P("g", 6) && P("c", 7) &&
            [ins.a, ins.b, ins.d, ins.f, ins.g].every(opdValid) && isDst(ins.c) ? ins : "kullanim: SCALE r IN INMIN INMAX OUTMIN OUTMAX DST";
        case "TW":
          if (!(n === 5 && P("a", 2) && P("b", 3))) return "kullanim: TW r ACILIS KAPANIS GUNLER";
          ins.x = parseInt(tok[4], 10) || 0;
          if (!ins.x || ins.x > 127) return "TW: en az bir gun";
          if (!opdValid(ins.a) || !opdValid(ins.b)) return "TW: adres hatali";
          for (const o of [ins.a, ins.b]) if (o.area === "K" && !hhmmOk(o.v)) return "TW: saat SSDD (0..2359)";
          return ins;
        case "PID":
          if (!(n === 9 && P("a", 2) && P("b", 3) && P("c", 4) && P("d", 5) && P("f", 6) && P("g", 7))) return "kullanim: PID r PV SP CIKIS KP TI TD n";
          ins.e = parseInt(tok[8], 10);
          if (!(ins.e >= 0 && ins.e < N_PID)) return "PID: en cok 16 PID";
          if (![ins.a, ins.b, ins.d, ins.f, ins.g].every(opdValid)) return "PID: adres hatali";
          return isDst(ins.c) ? ins : "PID: cikis D, F veya PW olmali";
        case "MB":
          if (!((n === 9 || n === 10) && P("a", 3) && P("b", 4) && P("d", 5) && P("c", 6) && P("g", 7))) return "kullanim: MB r FC SLAVE REG ADET YEREL DURUM IS";
          ins.x = parseInt(tok[2], 10); ins.e = parseInt(tok[8], 10);
          return ins.e >= 0 && ins.e < 32 ? ins : "MB: en cok 32 Modbus kutusu";
        default:   // ADD SUB MUL DIV MOD MIN MAX AND OR XOR SHL SHR
          return n === 5 && P("a", 2) && P("b", 3) && P("c", 4) && opdValid(ins.a) && opdValid(ins.b) && isDst(ins.c) ? ins : bad("hedef D veya PW olmali");
      }
    }

    // ---- Yorumlayıcı (firmware execProgram) ----
    // Program akışı (firmware progIndex): etiket/alt program tabloları ve denetim
    let lblPos = [], sbrPos = [];
    function progIndex(pg) {
      const L = Array(N_LBL).fill(-1), S = Array(N_LBL).fill(-1), blk = [];
      let b = 0;
      for (let i = 0; i < pg.length; i++) {
        const x = pg[i];
        if (x.op === "SBR") { if (S[x.x] >= 0) return "SBR numarasi iki kez"; S[x.x] = i; b++; }
        if (x.op === "LBL") { if (L[x.x] >= 0) return "LBL numarasi iki kez"; L[x.x] = i; }
        blk[i] = b;
      }
      for (let i = 0; i < pg.length; i++) {
        const x = pg[i];
        if (x.op === "JMP") {
          const t = L[x.x];
          if (t < 0) return "JMP hedefi LBL yok";
          if (t <= i) return "JMP yalniz ileri atlar";
          if (blk[t] !== blk[i]) return "JMP ayni bolumde (ana program / alt program) olmali";
        }
        if (x.op === "CALL" && S[x.x] < 0) return "CALL hedefi SBR yok";
      }
      lblPos = L; sbrPos = S;
      return null;
    }
    const FL3 = (ins) => isFlt(ins.a) || isFlt(ins.b) || isFlt(ins.c);
    function execProgram(dt) {
      let R = new Uint8Array(N_ROWS);
      const stk = [];
      let i = 0;
      while (true) {
        if (i >= prog.length) { if (!stk.length) break; const f = stk.pop(); R = f.R; i = f.ret; continue; }
        const ins = prog[i];
        const r = ins.r;
        let p = R[r];
        let next = i + 1;
        if (ins.op === "LBL") { i = next; continue; }
        if (ins.op === "SBR" || (ins.op === "RET" && p)) {
          if (stk.length) { const f = stk.pop(); R = f.R; i = f.ret; } else i = prog.length;
          continue;
        }
        if (ins.op === "RET") { i = next; continue; }
        if (ins.op === "JMP") { i = p ? lblPos[ins.x] : next; continue; }
        if (ins.op === "CALL") {
          if (p && stk.length < CALL_DEPTH) { stk.push({ ret: next, R: R.slice() }); i = sbrPos[ins.x] + 1; } else i = next;
          continue;
        }
        switch (ins.op) {
          case "L": p = 1; break;
          case "L0": p = 0; break;
          case "A": p = p && rdBit(ins.a) ? 1 : 0; break;
          case "AN": p = p && !rdBit(ins.a) ? 1 : 0; break;
          case "AP": { const cur = rdBit(ins.a); const ed = cur && !edges[ins.e]; edges[ins.e] = cur ? 1 : 0; p = p && ed ? 1 : 0; } break;
          case "AF": { const cur = rdBit(ins.a); const ed = !cur && edges[ins.e]; edges[ins.e] = cur ? 1 : 0; p = p && ed ? 1 : 0; } break;
          case "CMP":
            if (isFlt(ins.a) || isFlt(ins.b)) { const a = f32(rdF(ins.a)), b = f32(rdF(ins.b)); p = p && doCmp(ins.x, a > b ? 1 : a < b ? -1 : 0, 0) ? 1 : 0; }
            else p = p && doCmp(ins.x, rdWord(ins.a), rdWord(ins.b)) ? 1 : 0;
            break;
          case "O": {
            let v = 0;
            for (let k = 0; k < N_ROWS; k++) if ((ins.x >> k) & 1) v |= R[k];
            for (let k = 0; k < N_ROWS; k++) if ((ins.x >> k) & 1) R[k] = v;
            i = next;
            continue;
          }
          case "OUT": wrBit(ins.a, p); break;
          case "OUTN": wrBit(ins.a, !p); break;
          case "SET": if (p) wrBit(ins.a, true); break;
          case "RST":
            if (!p) break;
            if (ins.a.area === "T") Object.assign(tim[ins.a.v], { acc: 0, q: 0, run: 0 });
            else if (ins.a.area === "C") resetCounter(cnt[ins.a.v]);
            else wrBit(ins.a, false);
            break;
          case "TON": { const t = tim[ins.a.v], pt = rdWord(ins.b);
            if (p) { if (t.acc < pt) { t.acc += dt; if (t.acc > pt) t.acc = pt; } t.q = t.acc >= pt ? 1 : 0; } else { t.acc = 0; t.q = 0; }
            p = t.q; } break;
          case "TOF": { const t = tim[ins.a.v], pt = rdWord(ins.b);
            if (p) { t.q = 1; t.acc = 0; } else if (t.q) { t.acc += dt; if (t.acc >= pt) { t.acc = pt; t.q = 0; } }
            p = t.q; } break;
          case "TP": { const t = tim[ins.a.v], pt = rdWord(ins.b);
            if (p && !t.prev && !t.run) { t.run = 1; t.acc = 0; }
            if (t.run) { t.acc += dt; if (t.acc >= pt) { t.acc = pt; t.run = 0; } }
            if (!p && !t.run) t.acc = 0;
            t.q = t.run; t.prev = p; p = t.q; } break;
          case "PID": {
            const st = pidSt[ins.e];
            if (!p) { st.i = 0; st.init = 0; break; }
            const pv = rdF(ins.a), sp = rdF(ins.b), kp = rdF(ins.d), ti = rdF(ins.f), td = rdF(ins.g), dts = dt / 1000;
            if (!st.init) { st.init = 1; st.i = 0; st.prevPv = pv; }
            const e = sp - pv;
            const d = td > 0 && dts > 0 ? -td * (pv - st.prevPv) / dts : 0;
            const ni = st.i + (ti > 0 ? e * dts / ti : 0);
            let u = kp * (e + ni + d);
            if (!((u > PWM_MAX && kp * e > 0) || (u < 0 && kp * e < 0))) st.i = ni;
            u = kp * (e + st.i + d);
            if (!isFinite(u)) u = 0;
            u = Math.max(0, Math.min(PWM_MAX, u));
            st.prevPv = pv;
            wrF(ins.c, f32(u));
          } break;
          case "TONR": { const t = tim[ins.a.v], pt = rdWord(ins.b);
            if (p && t.acc < pt) { t.acc += dt; if (t.acc > pt) t.acc = pt; }
            t.q = t.acc >= pt ? 1 : 0; p = t.q; } break;
          case "CTU": case "CTD": { const c = cnt[ins.a.v];
            c.pv = rdWord(ins.b); c.down = ins.op === "CTD" ? 1 : 0;
            if (!c.init) { c.init = 1; c.cv = c.down ? c.pv : 0; }
            if (p && !c.prev) { if (c.down) { if (c.cv > 0) c.cv--; } else if (c.cv < 2147483647) c.cv++; }
            c.prev = p; c.q = (c.down ? c.cv <= 0 : c.cv >= c.pv) ? 1 : 0; p = c.q; } break;
          case "CTUD": { const c = cnt[ins.a.v];
            c.pv = rdWord(ins.b); c.down = 0;
            const dn = rdBit(ins.d) ? 1 : 0;
            if (!c.init) { c.init = 1; c.cv = 0; c.prevd = dn; }
            if (p && !c.prev && c.cv < 2147483647) c.cv++;
            if (dn && !c.prevd && c.cv > -2147483648) c.cv--;
            c.prev = p; c.prevd = dn; c.q = c.cv >= c.pv ? 1 : 0; p = c.q; } break;
          // Ondalıklı: işlenenlerden biri F veya ondalıklı sabitse (firmware ile aynı, float32)
          case "MOV": if (p) { if (isFlt(ins.a) || isFlt(ins.c)) wrF(ins.c, f32(rdF(ins.a))); else wrWord(ins.c, rdWord(ins.a)); } break;
          case "ADD": if (p) { if (FL3(ins)) wrF(ins.c, f32(rdF(ins.a) + rdF(ins.b))); else wrWord(ins.c, rdWord(ins.a) + rdWord(ins.b)); } break;
          case "SUB": if (p) { if (FL3(ins)) wrF(ins.c, f32(rdF(ins.a) - rdF(ins.b))); else wrWord(ins.c, rdWord(ins.a) - rdWord(ins.b)); } break;
          case "MUL": if (p) { if (FL3(ins)) wrF(ins.c, f32(rdF(ins.a) * rdF(ins.b))); else wrWord(ins.c, Math.imul(rdWord(ins.a), rdWord(ins.b))); } break;
          case "DIV": if (p) {
            if (FL3(ins)) { const b = rdF(ins.b); if (b !== 0) wrF(ins.c, f32(rdF(ins.a) / b)); }
            else { const b = rdWord(ins.b); if (b !== 0) wrWord(ins.c, Math.trunc(rdWord(ins.a) / b)); }
          } break;
          case "MOD": if (p) { const b = rdWord(ins.b); if (b !== 0) wrWord(ins.c, rdWord(ins.a) % b); } break;
          case "MIN": if (p) { if (FL3(ins)) wrF(ins.c, Math.min(rdF(ins.a), rdF(ins.b))); else wrWord(ins.c, Math.min(rdWord(ins.a), rdWord(ins.b))); } break;
          case "MAX": if (p) { if (FL3(ins)) wrF(ins.c, Math.max(rdF(ins.a), rdF(ins.b))); else wrWord(ins.c, Math.max(rdWord(ins.a), rdWord(ins.b))); } break;
          case "ABS": if (p) { if (isFlt(ins.a) || isFlt(ins.c)) wrF(ins.c, Math.abs(rdF(ins.a))); else { const a = rdWord(ins.a); wrWord(ins.c, a < 0 ? -a : a); } } break;
          case "LIMIT": if (p) {
            if (FL3(ins) || isFlt(ins.d)) { const v = rdF(ins.a), mn = rdF(ins.b), mx = rdF(ins.d); wrF(ins.c, v < mn ? mn : v > mx ? mx : v); }
            else { const v = rdWord(ins.a), mn = rdWord(ins.b), mx = rdWord(ins.d); wrWord(ins.c, v < mn ? mn : v > mx ? mx : v); }
          } break;
          case "SCALE": if (p && (FL3(ins) || isFlt(ins.d) || isFlt(ins.f) || isFlt(ins.g))) {
            const v = rdF(ins.a), i0 = rdF(ins.b), i1 = rdF(ins.d), o0 = rdF(ins.f), o1 = rdF(ins.g);
            if (i1 === i0) break;
            const r = f32(o0 + (v - i0) * (o1 - o0) / (i1 - i0)), lo = Math.min(o0, o1), hi = Math.max(o0, o1);
            wrF(ins.c, r < lo ? lo : r > hi ? hi : r);
          } else if (p) {
            const v = BigInt(rdWord(ins.a)), i0 = BigInt(rdWord(ins.b)), i1 = BigInt(rdWord(ins.d)), o0 = BigInt(rdWord(ins.f)), o1 = BigInt(rdWord(ins.g));
            if (i1 === i0) break;
            let r = o0 + (v - i0) * (o1 - o0) / (i1 - i0);
            const lo = o0 < o1 ? o0 : o1, hi = o0 < o1 ? o1 : o0;
            if (r < lo) r = lo; if (r > hi) r = hi;
            wrWord(ins.c, Number(r));
          } break;
          case "AND": if (p) wrWord(ins.c, rdWord(ins.a) & rdWord(ins.b)); break;
          case "OR": if (p) wrWord(ins.c, rdWord(ins.a) | rdWord(ins.b)); break;
          case "XOR": if (p) wrWord(ins.c, rdWord(ins.a) ^ rdWord(ins.b)); break;
          case "NOT": if (p) wrWord(ins.c, ~rdWord(ins.a)); break;
          case "SHL": if (p) wrWord(ins.c, rdWord(ins.a) << (rdWord(ins.b) & 31)); break;
          case "SHR": if (p) wrWord(ins.c, rdWord(ins.a) >>> (rdWord(ins.b) & 31)); break;
          case "TW": p = p && twActive(rdWord(ins.a), rdWord(ins.b), ins.x) ? 1 : 0; break;
          case "MB": if (p && ins.g.area === "D") dWords[ins.g.v] = -3; p = 0; break;   // simülasyonda Modbus yok: "master kapalı"
        }
        R[r] = p ? 1 : 0;
        i = next;
      }
    }

    // ---- G/Ç ----
    function readInputs() {
      for (const p of ALL_PINS) {
        const m = modes[p];
        if (isDi(m)) inImg[p] = force["I" + p] != null ? force["I" + p] : simIn[p];
        else inImg[p] = 0;
        if (m === "AI") aiImg[p] = force["AI" + p] != null ? force["AI" + p] : simAi[p];
        else aiImg[p] = 0;
      }
    }
    function writeOutputs() {
      for (const p of ALL_PINS) if (modes[p] === "DO") doState[p] = force["Q" + p] != null ? force["Q" + p] : qImg[p];
    }
    function allOutputsLow() {
      for (const p of ALL_PINS) { qImg[p] = 0; doState[p] = 0; pwImg[p] = 0; }
    }
    const ioBit = (p) => isDi(modes[p]) ? inImg[p] : modes[p] === "DO" ? doState[p] : 0;

    // Değişim yakalama (firmware trackChanges / flipReported): tek scan'lık darbeler de MON'da görünür
    const rep = { io: {}, m: new Uint8Array(N_M), t: new Uint8Array(N_T), c: new Uint8Array(N_C) };
    const dif = { io: {}, m: new Uint8Array(N_M), t: new Uint8Array(N_T), c: new Uint8Array(N_C) };
    for (const p of ALL_PINS) { rep.io[p] = 0; dif.io[p] = 0; }
    function trackChanges() {
      for (const p of ALL_PINS) dif.io[p] |= ioBit(p) !== rep.io[p] ? 1 : 0;
      for (let i = 0; i < N_M; i++) dif.m[i] |= mBits[i] !== rep.m[i] ? 1 : 0;
      for (let i = 0; i < N_T; i++) dif.t[i] |= tim[i].q !== rep.t[i] ? 1 : 0;
      for (let i = 0; i < N_C; i++) dif.c[i] |= cnt[i].q !== rep.c[i] ? 1 : 0;
    }
    function flipReported() {
      trackChanges();
      for (const p of ALL_PINS) { if (dif.io[p]) rep.io[p] ^= 1; dif.io[p] = 0; }
      for (const k of ["m", "t", "c"]) for (let i = 0; i < rep[k].length; i++) { if (dif[k][i]) rep[k][i] ^= 1; dif[k][i] = 0; }
    }
    function bitsHex(bits) {
      let s = "";
      for (let i = 0; i < bits.length; i += 4) {
        let v = 0;
        for (let k = 0; k < 4 && i + k < bits.length; k++) if (bits[i + k]) v |= 1 << k;
        s += v.toString(16);
      }
      return s;
    }

    let st = { cnt: 0, sum: 0, min: 1e9, max: 0, ovr: 0, dt: 0 };
    function scanCycle() {
      const now = performance.now();
      const dt = Math.round(now - lastScan);
      if (dt < SCAN_MS) return;
      lastScan = now;
      rtUpdate();
      readInputs();
      if (running) {
        const a = performance.now();
        execProgram(dt);
        writeOutputs();
        firstScan = false;
        scanUs = Math.round((performance.now() - a) * 1000);
        st.cnt++; st.sum += scanUs; st.min = Math.min(st.min, scanUs); st.max = Math.max(st.max, scanUs);
        if (st.cnt > 1) st.dt = Math.max(st.dt, dt);
        if (scanUs > SCAN_MS * 1000) st.ovr++;
      }
      trackChanges();
    }

    function goStop() { running = false; allOutputsLow(); }
    function goRun() {
      if (!prog.length || loading) return false;
      clearMemory();
      firstScan = true; running = true; lastScan = performance.now();
      return true;
    }
    function setMode(run) {
      if (run) { if (!goRun()) return false; } else goStop();
      runSt = run ? 1 : 0; save();
      return true;
    }
    // Kayıtlı programı yükle
    function loadSaved() {
      const out = [];
      for (const l of progLines) { const r = parseIns(l); if (typeof r === "string") { progLines = []; return; } out.push(r); }
      if (progIndex(out)) { progLines = []; return; }
      prog = out;
    }
    loadSaved();
    rtUpdate();
    if (runSt && prog.length) goRun();

    // ---- Mesajlar ----
    const ioPins = () => ALL_PINS;
    function info() {
      return {
        t: "info", fw: "MNBLad Simülasyon", board: "Tarayıcı simülasyonu", sim: 1, led: 48,
        run: running ? 1 : 0, prog: prog.length, autorun: 1, runst: runSt, err: 0,
        pcrc: prog.length ? pcrc : "", pt: prog.length ? pt : 0, pn: prog.length ? pn : "",
        src: src ? atob(src).length : 0, filt: 0, pwmf, tm: rtLocal, tz: tzMin,
        heap: 0, psram: 0, flash: 0, fs: 0, scan: SCAN_MS, aimax: AI_MAX,
        cap: { m: N_M, t: N_T, c: N_C, d: N_D, e: N_EDGE, r: N_ROWS, ins: MAX_INS, s: N_S },
        pins: ioPins().map(g => ({ g, adc: isAdc(g), ...(isInOnly(g) ? { in: true, name: "BOOT" } : {}) })),
        modes: MODES,
      };
    }
    function mon() {
      flipReported();
      const fo = Object.entries(force).map(([k, v]) => `${k}=${v}`);
      return {
        t: "mon", ms: millis(), run: running ? 1 : 0, sc: scanUs, fo,
        v: ioPins().map(p => isDi(modes[p]) || modes[p] === "DO" ? rep.io[p] : modes[p] === "AI" ? aiImg[p] : modes[p] === "PWM" ? pwImg[p] : -1),
        m: bitsHex(rep.m), tq: bitsHex(rep.t), cq: bitsHex(rep.c),
        ta: tim.map(t => t.acc), ca: cnt.map(c => c.cv), d: Array.from(dWords), f: Array.from(fRegs, v => Math.round(v * 1000) / 1000), tm: rtLocal,
      };
    }

    let monTimer = null;
    const scanTimer = setInterval(scanCycle, SCAN_MS);
    const emit = (o) => setTimeout(() => onMsg(o), 0);
    const ok = () => emit({ t: "ok" });
    const err = (m) => emit({ t: "err", msg: m });
    const requireStop = () => { if (running) { err("once STOP yapin"); return false; } return true; };

    function handle(line) {
      line = line.trim();
      if (!line) return;
      // Program satırı: "P <komut>"; kaynak parçası: "S <base64>"
      if (/^P\s/i.test(line)) {
        if (!loading) return err("PBEGIN bekleniyor");
        if (stage.length >= MAX_INS) { loading = false; return err("program cok uzun"); }
        const body = line.slice(2);
        const r = parseIns(body);
        if (typeof r === "string") { loading = false; return err(`satir ${stage.length + 1}: ${r}`); }
        stage.push(r); stageText += body + "\n"; return ok();
      }
      if (/^S\s/i.test(line)) {
        if (srcStage == null) return err("SBEGIN bekleniyor");
        srcStage += atob(line.slice(2).trim()); return ok();
      }
      const a = line.split(/\s+/), cmd = a[0].toUpperCase();
      switch (cmd) {
        case "INFO": return emit(info());
        case "CFG": return emit({ t: "cfg", mon: monPeriod, m: ioPins().map(p => modes[p]) });
        case "MON": {
          const ms = parseInt(a[1] || "0", 10);
          if (ms !== 0 && (ms < 50 || ms > 5000)) return err("periyot 0 veya 50..5000 ms");
          monPeriod = ms; clearInterval(monTimer); monTimer = ms ? setInterval(() => onMsg(mon()), ms) : null;
          return ok();
        }
        case "RUN": if (!prog.length) return err("program yok"); setMode(true); st = { cnt: 0, sum: 0, min: 1e9, max: 0, ovr: 0, dt: 0 }; return ok();
        case "STOP": setMode(false); return ok();
        case "PBEGIN": if (!requireStop()) return; loading = true; stage = []; stageText = ""; return ok();
        case "PEND": {
          if (!loading) return err("PBEGIN bekleniyor");
          loading = false;
          if (parseInt(a[1], 10) !== stage.length) return err("komut sayisi tutmuyor");
          if (parseInt(a[2], 16) !== crc32(stageText)) return err("CRC tutmuyor");
          { const fe = progIndex(stage); if (fe) { progIndex(prog); return err(fe); } }
          prog = stage; progLines = stageText.split("\n").filter(Boolean);
          pcrc = crc32(stageText).toString(16); pt = 0; pn = ""; src = null; save();
          return ok();
        }
        case "PMETA": pt = parseInt(a[1], 10) || 0; pn = a.slice(2).join(" ").slice(0, 40); save(); return ok();
        case "SBEGIN": srcStage = ""; srcSize = parseInt(a[1], 10) || 0; return ok();
        case "SEND":
          if (srcStage == null) return err("SBEGIN bekleniyor");
          if (srcStage.length !== srcSize) { srcStage = null; return err("kaynak boyutu/CRC tutmuyor"); }
          src = btoa(srcStage); srcStage = null; save(); return ok();
        case "SGET": {
          if (!src) return err("kartta kaynak yok");
          const raw = atob(src), off = parseInt(a[1] || "0", 10);
          return emit({ t: "src", o: off, n: raw.length, d: btoa(raw.slice(off, off + 144)) });
        }
        case "PIN": {
          if (!requireStop()) return;
          const p = parseInt(a[1], 10), m = String(a[2] || "").toUpperCase();
          if (!isIo(p)) return err("gecersiz pin");
          if (!MODES.includes(m)) return err("gecersiz mod");
          if (m === "AI" && !isAdc(p)) return err("pin analog desteklemiyor");
          if ((m === "DO" || m === "PWM") && isInOnly(p)) return err("pin yalniz giris olabilir");
          if (m === "PWM" && modes[p] !== "PWM" && ALL_PINS.filter(x => modes[x] === "PWM").length >= 8) return err("en cok 8 PWM pini");
          modes[p] = m; pwImg[p] = 0; doState[p] = 0; simIn[p] = m === "DIPU" ? 1 : 0;
          for (const k of ["I", "Q", "AI"]) delete force[k + p];
          save(); return ok();
        }
        case "SET": {
          if (!requireStop()) return;
          const p = parseInt(a[1], 10), v = parseInt(a[2], 10);
          if (isIo(p) && modes[p] === "PWM") { if (!(v >= 0 && v <= PWM_MAX)) return err("PWM 0..1000"); pwImg[p] = v; return ok(); }
          if (!isIo(p) || modes[p] !== "DO") return err("pin DO degil");
          doState[p] = v ? 1 : 0; return ok();
        }
        case "RESET": if (!requireStop()) return; for (const p of ALL_PINS) modes[p] = "OFF"; save(); return ok();
        case "WR": {
          const o = parseOpd(a[1]);
          if (o && o.area === "F" && opdValid(o)) { const v = parseFloat(a[2]); if (!isFinite(v)) return err("gecersiz deger"); fRegs[o.v] = v; return ok(); }
          if (!o || !opdValid(o) || (o.area !== "D" && o.area !== "M") || !/^-?\d+$/.test(a[2] || "")) return err("kullanim: WR <Dn|Mn|Fn> <deger>");
          if (o.area === "D") dWords[o.v] = i32(parseInt(a[2], 10)); else mBits[o.v] = parseInt(a[2], 10) ? 1 : 0;
          return ok();
        }
        case "FORCE": {
          const o = parseOpd(a[1]), v = parseInt(a[2], 10);
          if (!o || !opdValid(o) || isNaN(v)) return err("kullanim: FORCE <I|Q|AI><gpio> <deger>");
          if (o.area === "I") { if (!isDi(modes[o.v])) return err("pin dijital giris degil"); force["I" + o.v] = v ? 1 : 0; }
          else if (o.area === "Q") { if (modes[o.v] !== "DO") return err("pin dijital cikis degil"); force["Q" + o.v] = v ? 1 : 0; }
          else if (o.area === "AI") { if (modes[o.v] !== "AI") return err("pin analog giris degil"); if (v < 0 || v > AI_MAX) return err("analog 0..3000 mV"); force["AI" + o.v] = v; }
          else return err("yalniz I, Q, AI zorlanabilir");
          return ok();
        }
        case "UNFORCE": {
          if (String(a[1]).toUpperCase() === "ALL") { for (const k in force) delete force[k]; return ok(); }
          const o = parseOpd(a[1]);
          if (!o || !["I", "Q", "AI"].includes(o.area)) return err("yalniz I, Q, AI");
          delete force[o.area + o.v]; return ok();
        }
        // Simülasyona özel: giriş değeri ver
        case "SIMIN": { const p = parseInt(a[1], 10); if (!isIo(p) || !isDi(modes[p])) return err("pin dijital giris degil"); simIn[p] = parseInt(a[2], 10) ? 1 : 0; return ok(); }
        case "SIMAI": { const p = parseInt(a[1], 10), v = parseInt(a[2], 10); if (!isIo(p) || modes[p] !== "AI") return err("pin analog giris degil"); if (!(v >= 0 && v <= AI_MAX)) return err("analog 0..3000 mV"); simAi[p] = v; return ok(); }
        case "PWMF": { if (!requireStop()) return; const hz = parseInt(a[1], 10); if (!(hz >= 100 && hz <= 20000)) return err("PWM frekansi 100..20000 Hz"); pwmf = hz; save(); return ok(); }
        case "DIAG": return emit({ t: "diag", sim: 1, sc: [scanUs, st.cnt ? st.min : 0, st.cnt ? Math.round(st.sum / st.cnt) : 0, st.max, st.ovr, st.dt, st.cnt],
          rr: 0, boots: 0, heap: 0, heapMin: 0, up: Math.floor(millis() / 1000), callOvf: 0, now: millis(), ev: [] });
        case "DIAGCLR": st = { cnt: 0, sum: 0, min: 1e9, max: 0, ovr: 0, dt: 0 }; return ok();
        case "TIME": if (a[2] != null) tzMin = parseInt(a[2], 10) || 0; rtUpdate(); return ok();
        case "FILTER": case "LED": case "AUTORUN": case "REBOOT": case "MBCLR": return ok();
        case "BOOTLOADER": return err("simulasyonda firmware yuklenmez");
        default: return err("simulasyonda yok: " + cmd);
      }
    }
    let monPeriod = 0, srcStage = null, srcSize = 0;

    return {
      handle,
      stop() { clearInterval(scanTimer); clearInterval(monTimer); },
      // Panel ve testler için
      state: () => ({ running, prog: prog.length, modes: { ...modes } }),
    };
  }

  window.MNBSim = { create, crc32 };
})();
