// mend: the CLI SPEC.md specifies, implemented in full (sections 1-10).
// Parsers cover unified diffs, SEARCH/REPLACE, V4A and JSON edits; line matching uses
// the three whitespace-tolerance tiers of section 5, with strict mode limiting it to tier 0.
// Node 22, standard library alone. Run as `node main.ts [options] [PATCH]`.
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';
const rtrim = (s: string): string => s.replace(/[ \t]+$/, '');
const trim = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const lead = (s: string): string => { const m = /^[ \t]*/.exec(s); return m ? m[0] : ''; };

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; new: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/* ---------- section 3: files, lines, breaks ---------- */
interface Parts { lines: string[]; br: string; final: boolean; }
function fileParts(text: string): Parts {
  if (text === '') return { lines: [], br: '\n', final: false };
  const firstLf = text.indexOf('\n');
  const br = firstLf > 0 && text[firstLf - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const lines = final ? text.slice(0, -br.length).split(br) : text.split(br);
  return { lines, br, final };
}
function writeLines(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}

/* ---------- section 5: matching lines ---------- */
type Tier = 0 | 1 | 2;
function key(s: string, t: Tier): string { return t === 0 ? s : t === 1 ? rtrim(s) : trim(s); }
function maxTier(strict: boolean): Tier { return strict ? 0 : 2; }

interface BodyLine { p: ' ' | '-' | '+' | '\\'; t: string; fromBlank?: boolean; }
function oldOf(body: BodyLine[]): string[] { return body.filter((b) => b.p === ' ' || b.p === '-').map((b) => b.t); }
function newOf(body: BodyLine[]): string[] { return body.filter((b) => b.p === ' ' || b.p === '+').map((b) => b.t); }

function findOcc(F: string[], O: string[], strict: boolean): { tier: Tier; positions: number[] } | null {
  for (let t = 0; t <= maxTier(strict); t++) {
    const ok = O.map((l) => key(l, t as Tier));
    const fk = F.map((l) => key(l, t as Tier));
    const pos: number[] = [];
    for (let i = 0; i + ok.length <= fk.length; i++) {
      let m = true;
      for (let j = 0; j < ok.length; j++) { if (fk[i + j] !== ok[j]) { m = false; break; } }
      if (m) pos.push(i);
    }
    if (pos.length > 0) return { tier: t as Tier, positions: pos };
  }
  return null;
}

function replacement(body: BodyLine[], F: string[], start: number, tier: Tier, reindent: boolean): string[] {
  const oldLen = body.filter((b) => b.p === ' ' || b.p === '-').length;
  const P = reindent && oldLen > 0 ? lead(oldOf(body)[0] ?? '') : '';
  const FF = reindent && oldLen > 0 ? lead(F[start] ?? '') : '';
  const out: string[] = [];
  let j = start;
  for (const b of body) {
    if (b.p === ' ') { out.push(F[j] !== undefined ? F[j] : b.t); j++; }
    else if (b.p === '-') { j++; }
    else if (b.p === '+') {
      let t = b.t;
      if (reindent && oldLen > 0 && tier === 2 && t.trim() !== '' && t.startsWith(P)) t = FF + t.slice(P.length);
      out.push(t);
    }
  }
  return out;
}
function hasBackslashAfterLast(body: BodyLine[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i++) if (body[i].p === ' ' || body[i].p === '+') last = i;
  if (last < 0) return false;
  return body.slice(last + 1).some((b) => b.p === '\\');
}
function trailingBlanksTrim(body: BodyLine[], contextToo = false): void {
  while (body.length > 0 && (body[body.length - 1].fromBlank || (contextToo && body[body.length - 1].p === ' ' && body[body.length - 1].t.trim() === ''))) body.pop();
}

/* ---------- section 6: unified diffs ---------- */
interface Hunk { A: number; body: BodyLine[]; }
interface Section { oldPath: string | null; newPath: string | null; create: boolean; del: boolean; hunks: Hunk[]; }

function parseDiffGit(s: string): { old: string; new: string } | null {
  const m = /^diff --git a\/(.+) b\/(.+)$/.exec(s);
  return m ? { old: m[1]!, new: m[2]! } : null;
}
function headerPath(s: string): string | null {
  let t = s;
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  return t;
}

function applyHunk(cur: string[], final: boolean, h: Hunk, strict: boolean, path: string, d: number): { lines: string[]; final: boolean; d: number } {
  const O = oldOf(h.body);
  const N = newOf(h.body);
  if (O.length > 0) {
    const found = findOcc(cur, O, strict);
    if (!found) throw new Fail('no-match', path);
    const target = h.A - 1 + d;
    let pos = found.positions[0]!;
    let best = Math.abs(pos - target);
    for (const p of found.positions) { const dist = Math.abs(p - target); if (dist < best) { best = dist; pos = p; } }
    const rep = replacement(h.body, cur, pos, found.tier, true);
    const out = [...cur.slice(0, pos), ...rep, ...cur.slice(pos + O.length)];
    const ranToEnd = pos + O.length === cur.length;
    const nf = ranToEnd ? !hasBackslashAfterLast(h.body) : final;
    return { lines: out, final: nf, d: d + rep.length - O.length };
  }
  const at = Math.min(h.A + d, cur.length);
  const out = [...cur.slice(0, at), ...N, ...cur.slice(at)];
  const nf = at === cur.length ? !hasBackslashAfterLast(h.body) : final;
  return { lines: out, final: nf, d: d + N.length };
}

function unifiedSectionEdit(sec: Section, strict: boolean): Edit {
  const op = sec.oldPath;
  const np = sec.newPath;
  return (tree) => {
    for (const p of [op, np]) if (p !== null && !safe(p)) throw new Fail('unsafe', p);
    const isCreate = sec.create || op === null;
    const isDelete = sec.del || np === null;
    if (isCreate) {
      if (np === null) throw new Fail('missing', '');
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const out: string[] = [];
      let noFinal = false;
      for (const h of sec.hunks) {
        const plus = h.body.filter((b) => b.p === '+');
        out.push(...plus.map((b) => b.t));
        if (plus.length > 0 && hasBackslashAfterLast(h.body)) noFinal = true;
      }
      tree.now.set(np, out.length ? out.join('\n') + (noFinal ? '' : '\n') : '');
      return;
    }
    if (isDelete) {
      if (op === null) throw new Fail('missing', '');
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    if (op !== null && np !== null && op !== np) {
      const oldText = tree.get(op);
      if (oldText === null) throw new Fail('missing', op);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const parts = fileParts(oldText);
      let cur = parts.lines, fin = parts.final, d = 0;
      for (const h of sec.hunks) { const r = applyHunk(cur, fin, h, strict, op, d); cur = r.lines; fin = r.final; d = r.d; }
      tree.now.set(op, null);
      tree.now.set(np, writeLines(cur, parts.br, fin));
      tree.moves.push({ old: op, new: np });
      return;
    }
    const p = op ?? np;
    if (p === null) throw new Fail('missing', '');
    const oldText = tree.get(p);
    if (oldText === null) throw new Fail('missing', p);
    const parts = fileParts(oldText);
    let cur = parts.lines, fin = parts.final, d = 0;
    for (const h of sec.hunks) { const r = applyHunk(cur, fin, h, strict, p, d); cur = r.lines; fin = r.final; d = r.d; }
    tree.now.set(p, writeLines(cur, parts.br, fin));
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const L = lines[i]!;
    if (cur === null) {
      if (L.startsWith('diff --git ')) {
        const m = parseDiffGit(L);
        if (!m) throw new Exit2(`error: parse ${i + 1}`);
        cur = { oldPath: m.old, newPath: m.new, create: false, del: false, hunks: [] };
        i++; continue;
      }
      if (L.startsWith('--- ') && i + 1 < n && lines[i + 1]!.startsWith('+++ ')) {
        cur = { oldPath: null, newPath: null, create: false, del: false, hunks: [] };
        continue;
      }
      i++; continue;
    }
    if (L.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(L);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const A = parseInt(m[1]!, 10);
      const body: BodyLine[] = [];
      i++;
      while (i < n) {
        const B = lines[i]!;
        if (B.startsWith('diff --git ')) break;
        if (B.startsWith('--- ') && i + 1 < n && lines[i + 1]!.startsWith('+++ ')) break;
        if (B.startsWith(' ') || B.startsWith('-') || B.startsWith('+') || B.startsWith('\\')) {
          body.push({ p: B[0] as BodyLine['p'], t: B.slice(1) }); i++; continue;
        }
        if (B === '') { body.push({ p: ' ', t: '', fromBlank: true }); i++; continue; }
        break;
      }
      trailingBlanksTrim(body);
      cur.hunks.push({ A, body });
      continue;
    }
    if (L.startsWith('--- ')) {
      if (cur.hunks.length > 0) { sections.push(cur); cur = { oldPath: null, newPath: null, create: false, del: false, hunks: [] }; }
      if (i + 1 >= n || !lines[i + 1]!.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
      cur.oldPath = headerPath(L.slice(4));
      cur.newPath = headerPath(lines[i + 1]!.slice(4));
      i += 2; continue;
    }
    if (L.startsWith('diff --git ')) {
      sections.push(cur);
      const m = parseDiffGit(L);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: m.old, newPath: m.new, create: false, del: false, hunks: [] };
      i++; continue;
    }
    if (L.startsWith('new file mode')) { cur.create = true; i++; continue; }
    if (L.startsWith('deleted file mode')) { cur.del = true; i++; continue; }
    if (L.startsWith('rename from ')) { cur.oldPath = L.slice(12).trim(); i++; continue; }
    if (L.startsWith('rename to ')) { cur.newPath = L.slice(10).trim(); i++; continue; }
    i++;
  }
  if (cur !== null) sections.push(cur);
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

/* ---------- section 7: SEARCH/REPLACE ---------- */
function searchReplaceEdit(path: string, body: BodyLine[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    const O = oldOf(body);
    const N = newOf(body);
    if (O.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, N.length ? N.join('\n') + '\n' : '');
      return;
    }
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    const parts = fileParts(text);
    const found = findOcc(parts.lines, O, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const rep = replacement(body, parts.lines, pos, found.tier, true);
    const out = [...parts.lines.slice(0, pos), ...rep, ...parts.lines.slice(pos + O.length)];
    tree.now.set(path, writeLines(out, parts.br, parts.final));
  };
}
function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let lower = 0;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (rtrim(lines[i]!) !== '<<<<<<< SEARCH') { i++; continue; }
    const searchLine = i + 1;
    let eq = -1;
    for (let j = i + 1; j < n; j++) { if (rtrim(lines[j]!) === '=======') { eq = j; break; } }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine}`);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) { if (rtrim(lines[j]!) === '>>>>>>> REPLACE') { rep = j; break; } }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine}`);
    let path: string | null = null;
    for (let j = i - 1; j >= lower; j--) {
      const L = lines[j]!;
      if (blank(L)) continue;
      const t = L.trim();
      if (t.startsWith('```')) continue;
      path = t; break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine}`);
      path = prevPath;
    }
    prevPath = path;
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const body: BodyLine[] = [
      ...oldLines.map((t) => ({ p: '-' as const, t })),
      ...newLines.map((t) => ({ p: '+' as const, t })),
    ];
    edits.push(searchReplaceEdit(path, body, strict));
    lower = rep + 1;
    i = rep + 1;
  }
  return edits;
}

/* ---------- section 8: V4A ---------- */
interface V4AChunk { anchor: string | null; body: BodyLine[]; eof: boolean; }
interface V4ASection { type: 'add' | 'delete' | 'update'; path: string; addBody: BodyLine[]; move: string | null; chunks: V4AChunk[]; updateLine: number; }

function v4aSectionEdit(s: V4ASection, strict: boolean): Edit {
  return (tree) => {
    const paths: string[] = [s.path];
    if (s.move !== null) paths.push(s.move);
    for (const p of paths) if (!safe(p)) throw new Fail('unsafe', p);
    if (s.type === 'add') {
      if (tree.get(s.path) !== null) throw new Fail('exists', s.path);
      const ls = s.addBody.map((b) => b.t);
      tree.now.set(s.path, ls.length ? ls.join('\n') + '\n' : '');
      return;
    }
    if (s.type === 'delete') {
      if (tree.get(s.path) === null) throw new Fail('missing', s.path);
      tree.now.set(s.path, null);
      return;
    }
    const oldText = tree.get(s.path);
    if (oldText === null) throw new Fail('missing', s.path);
    if (s.move !== null && tree.get(s.move) !== null) throw new Fail('exists', s.move);
    const parts = fileParts(oldText);
    let cur = parts.lines.slice();
    let cursor = 0;
    for (const ch of s.chunks) {
      let start = cursor;
      if (ch.anchor !== null) {
        let ap = -1;
        for (let t = 0; t <= maxTier(strict); t++) {
          const ak = key(ch.anchor!, t as Tier);
          for (let i = cursor; i < cur.length; i++) { if (key(cur[i]!, t as Tier) === ak) { ap = i; break; } }
          if (ap >= 0) break;
        }
        if (ap < 0) throw new Fail('no-match', s.path);
        start = ap + 1;
      }
      const O = oldOf(ch.body);
      if (O.length > 0) {
        let pos = -1; let tier: Tier = 0;
        for (let t = 0; t <= maxTier(strict); t++) {
          const ok = O.map((l) => key(l, t as Tier));
          for (let i = start; i + ok.length <= cur.length; i++) {
            let m = true;
            for (let j = 0; j < ok.length; j++) { if (key(cur[i + j]!, t as Tier) !== ok[j]) { m = false; break; } }
            if (m) { pos = i; tier = t as Tier; break; }
          }
          if (pos >= 0) break;
        }
        if (pos < 0) throw new Fail('no-match', s.path);
        if (ch.eof && pos + O.length !== cur.length) throw new Fail('no-match', s.path);
        const rep = replacement(ch.body, cur, pos, tier, true);
        cur = [...cur.slice(0, pos), ...rep, ...cur.slice(pos + O.length)];
        cursor = pos + rep.length;
      } else {
        const at = ch.eof ? cur.length : start;
        const rep = ch.body.filter((b) => b.p === '+').map((b) => b.t);
        cur = [...cur.slice(0, at), ...rep, ...cur.slice(at)];
        cursor = at + rep.length;
      }
    }
    const result = writeLines(cur, parts.br, parts.final);
    if (s.move !== null) {
      tree.now.set(s.path, null);
      tree.now.set(s.move, result);
      tree.moves.push({ old: s.path, new: s.move });
    } else tree.now.set(s.path, result);
  };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  let first = -1;
  for (let i = 0; i < n; i++) { if (!blank(lines[i]!)) { first = i; break; } }
  if (first < 0 || lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first < 0 ? 1 : first + 1}`);
  let last = -1;
  for (let i = n - 1; i >= 0; i--) { if (!blank(lines[i]!)) { last = i; break; } }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${n + 1}`);
  const sections: V4ASection[] = [];
  let cur: V4ASection | null = null;
  let chunkClosed = false;
  let i = first + 1;
  while (i < last) {
    const L = lines[i]!;
    if (L === '') {
      if (cur === null || cur.type === 'delete') { i++; continue; }
      if (cur.type === 'add') { cur.addBody.push({ p: '+', t: '', fromBlank: true }); i++; continue; }
      if (cur.chunks.length === 0) { i++; continue; }
      cur.chunks[cur.chunks.length - 1]!.body.push({ p: ' ', t: '', fromBlank: true });
      i++; continue;
    }
    if (L.startsWith('*** Add File: ')) {
      if (cur) sections.push(cur);
      cur = { type: 'add', path: L.slice(14).trim(), addBody: [], move: null, chunks: [], updateLine: i + 1 };
      chunkClosed = false; i++; continue;
    }
    if (L.startsWith('*** Delete File: ')) {
      if (cur) sections.push(cur);
      cur = { type: 'delete', path: L.slice(17).trim(), addBody: [], move: null, chunks: [], updateLine: i + 1 };
      chunkClosed = false; i++; continue;
    }
    if (L.startsWith('*** Update File: ')) {
      if (cur) sections.push(cur);
      cur = { type: 'update', path: L.slice(17).trim(), addBody: [], move: null, chunks: [], updateLine: i + 1 };
      chunkClosed = false; i++; continue;
    }
    if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
    if (cur.type === 'add') {
      if (L.startsWith('+')) { cur.addBody.push({ p: '+', t: L.slice(1) }); i++; continue; }
      throw new Exit2(`error: parse ${i + 1}`);
    }
    if (cur.type === 'delete') throw new Exit2(`error: parse ${i + 1}`);
    if (cur.move === null && cur.chunks.length === 0 && L.startsWith('*** Move to: ')) { cur.move = L.slice(13).trim(); i++; continue; }
    if (L.startsWith('*** End of File')) {
      if (cur.chunks.length === 0) throw new Exit2(`error: parse ${i + 1}`);
      cur.chunks[cur.chunks.length - 1]!.eof = true; chunkClosed = true; i++; continue;
    }
    if (L.startsWith('@@')) {
      const anchor = L.slice(2).trim();
      cur.chunks.push({ anchor: anchor === '' ? null : anchor, body: [], eof: false });
      chunkClosed = false; i++; continue;
    }
    if (L.startsWith(' ') || L.startsWith('-') || L.startsWith('+')) {
      if (cur.chunks.length === 0 || chunkClosed) { cur.chunks.push({ anchor: null, body: [], eof: false }); chunkClosed = false; }
      cur.chunks[cur.chunks.length - 1]!.body.push({ p: L[0] as BodyLine['p'], t: L.slice(1) });
      i++; continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  if (cur) sections.push(cur);
  for (const s of sections) {
    trailingBlanksTrim(s.addBody);
    for (const c of s.chunks) trailingBlanksTrim(c.body, true);
  }
  for (const s of sections) if (s.type === 'update' && s.chunks.length === 0 && s.move === null) throw new Exit2(`error: parse ${s.updateLine}`);
  return sections.map((s) => v4aSectionEdit(s, strict));
}

/* ---------- section 9: JSON edits ---------- */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}
function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---------- section 4: detection ---------- */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => rtrim(l) === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/* ---------- driver ---------- */
function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try { text = readFileSync(file ?? 0, 'utf8'); }
  catch { if (file !== null) return { code: 2, out: ['error: no-patch'] }; }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines)
      : kind === 'unified' ? unifiedEdits(lines, strict)
      : kind === 'search-replace' ? searchReplaceEdits(lines, strict)
      : kind === 'v4a' ? v4aEdits(lines, strict)
      : [];
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try { edit(tree); }
    catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const moveFor = new Map<string, string>();
  for (const mv of tree.moves) {
    if (tree.original(mv.old) !== null && tree.get(mv.old) === null && tree.original(mv.new) === null && tree.get(mv.new) !== null) moveFor.set(mv.new, mv.old);
  }
  if (!check) {
    for (const p of tree.now.keys()) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else { mkdirSync(dirname(p), { recursive: true }); writeFileSync(p, now); }
    }
  }
  const movedOld = new Set(moveFor.values());
  const rows: string[] = [];
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (movedOld.has(p)) continue;
    if (moveFor.has(p)) { rows.push(`R ${moveFor.get(p)} -> ${p}`); continue; }
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push(`${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
