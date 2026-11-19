// GitHub-compatible git forge — single-process entry for make.fun
// github-core-clone-01. Node 22 stdlib only. No network, no git binary, no model calls.
// In-memory store; deterministic (no wall clock / randomness leaks into state).
import { createServer as createNetServer, type Server as NetServer, type Socket } from 'node:net';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants
const ZERO_OID = '0000000000000000000000000000000000000000';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const TRIAL_NOW = Number(process.env.MAKEFUN_TRIAL_NOW) || 1739175597; // epoch seconds; fixed fallback
const FIXED_TS = '2026-01-01T00:00:00Z';
const JSON_TYPE = 'application/json; charset=utf-8';
const MAX_BODY = 32 * 1024 * 1024;

let reqSeq = 0;
let idSeq = 1000; // numeric REST ids (repos/issues/pulls/comments share one counter)
let dbSeq = 5000; // repository databaseIds
let commitSeq = 0; // deterministic commit timestamps: TRIAL_NOW + commitSeq
let viewerLogin: string | null = null;

function learnOwner(owner: string | undefined): void {
  if (owner && !viewerLogin) viewerLogin = owner;
}
function viewerName(): string { return viewerLogin ?? 'unknown'; }
function viewerEmail(): string { return `${viewerName()}@example.invalid`; }

// ---------------------------------------------------------------- git objects
type ObjType = 'blob' | 'tree' | 'commit' | 'tag';
interface GitObject { type: ObjType; data: Buffer; }
function sha1Of(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(`${type} ${data.length}\0`);
  h.update(data);
  return h.digest('hex');
}
function storeObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = sha1Of(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
interface TreeEntry { mode: string; name: string; oid: string; }
function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    const nul = data.indexOf(0x00, sp);
    const mode = data.subarray(i, sp).toString('utf8');
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    out.push({ mode, name, oid });
    i = nul + 21;
  }
  return out;
}
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
interface CommitInfo { tree: string; parents: string[]; author: string; committer: string; message: string; }
function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const headEnd = text.indexOf('\n\n');
  const head = headEnd >= 0 ? text.slice(0, headEnd) : text;
  const message = headEnd >= 0 ? text.slice(headEnd + 2) : '';
  const info: CommitInfo = { tree: '', parents: [], author: '', committer: '', message };
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) info.tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) info.parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) info.author = line.slice(7);
    else if (line.startsWith('committer ')) info.committer = line.slice(10);
  }
  return info;
}
function makeCommit(repo: Repo, tree: string, parents: string[], message: string): string {
  const ts = TRIAL_NOW + (commitSeq += 1);
  const ident = `${viewerName()} <${viewerEmail()}> ${ts} +0000`;
  const body = `tree ${tree}\n` + parents.map((p) => `parent ${p}\n`).join('') +
    `author ${ident}\ncommitter ${ident}\n\n${message}`;
  return storeObject(repo, 'commit', Buffer.from(body, 'utf8'));
}
// Resolve a ref target to a commit oid (peel annotated tags).
function peelToCommit(repo: Repo, oid: string): string | null {
  let cur = oid;
  for (let i = 0; i < 8; i += 1) {
    const obj = repo.objects.get(cur);
    if (!obj) return null;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') {
      const m = /^object ([0-9a-f]{40})\n/.exec(obj.data.toString('utf8'));
      if (!m) return null;
      cur = m[1];
      continue;
    }
    return null;
  }
  return null;
}
// Parsed commit info, cached per repo (objects are immutable).
function commitInfo(repo: Repo, oid: string): CommitInfo | null {
  const cached = repo.commitCache.get(oid);
  if (cached) return cached;
  const obj = repo.objects.get(oid);
  if (!obj || obj.type !== 'commit') return null;
  const info = parseCommit(obj.data);
  repo.commitCache.set(oid, info);
  return info;
}
// All ancestors (inclusive) of a commit oid.
function ancestors(repo: Repo, tip: string): Set<string> {
  const out = new Set<string>();
  const stack = [tip];
  while (stack.length) {
    const oid = stack.pop()!;
    if (out.has(oid)) continue;
    const info = commitInfo(repo, oid);
    if (!info) continue;
    out.add(oid);
    for (const p of info.parents) stack.push(p);
  }
  return out;
}
function isAncestor(repo: Repo, anc: string, desc: string): boolean {
  if (anc === desc) return true;
  // Walk parents from desc and stop the moment anc is found. A fast-forward
  // push's parent IS anc, so this is one or two visits instead of a full
  // history walk; a non-fast-forward still walks the whole reachable set.
  const seen = new Set<string>();
  const stack = [desc];
  while (stack.length) {
    const oid = stack.pop()!;
    if (oid === anc) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const info = commitInfo(repo, oid);
    if (!info) continue;
    for (const p of info.parents) stack.push(p);
  }
  return false;
}
// The commit itself plus everything in its own tree (blobs and subtrees) —
// parents are NOT followed.
function commitTreeObjects(repo: Repo, commitOid: string): Map<string, GitObject> {
  const out = new Map<string, GitObject>();
  const commit = repo.objects.get(commitOid);
  if (!commit || commit.type !== 'commit') return out;
  out.set(commitOid, commit);
  const stack = [parseCommit(commit.data).tree];
  const seen = new Set<string>();
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    out.set(oid, obj);
    if (obj.type === 'tree') for (const e of parseTree(obj.data)) stack.push(e.oid);
  }
  return out;
}
// Objects reachable from a set of tips (commits + their trees/blobs, tags peeled).
function reachableObjects(repo: Repo, tips: string[]): Map<string, GitObject> {
  const out = new Map<string, GitObject>();
  const stack: string[] = [...tips];
  const seen = new Set<string>();
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    out.set(oid, obj);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      const m = /^object ([0-9a-f]{40})\n/.exec(obj.data.toString('utf8'));
      if (m) stack.push(m[1]);
    }
  }
  return out;
}
// Commit distance (edges) from any of the wants, following parents.
// With maxDepth set, parents at distance maxDepth are never enqueued: callers
// only ever use distances below it (included commits, shallow boundaries).
function commitDistances(repo: Repo, wants: string[], maxDepth: number | null = null): Map<string, number> {
  const dist = new Map<string, number>();
  const queue: Array<[string, number]> = wants.map((w) => [w, 0] as [string, number]);
  let head = 0;
  while (head < queue.length) {
    const [oid, d] = queue[head];
    head += 1;
    if (dist.has(oid) && dist.get(oid)! <= d) continue;
    dist.set(oid, d);
    const info = commitInfo(repo, oid);
    if (!info) continue;
    if (maxDepth !== null && d + 1 >= maxDepth) continue;
    for (const p of info.parents) queue.push([p, d + 1]);
  }
  return dist;
}
// Tree lookup: map of path -> {oid, mode} for a tree oid (recursive).
function flattenTree(repo: Repo, treeOid: string, prefix = ''): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') {
      for (const [k, v] of flattenTree(repo, e.oid, path)) out.set(k, v);
    } else {
      out.set(path, { oid: e.oid, mode: e.mode });
    }
  }
  return out;
}
// Diff two trees.
function diffTrees(repo: Repo, oldTree: string, newTree: string): Array<{ path: string; status: 'added' | 'removed' | 'modified'; oldOid: string | null; newOid: string | null }> {
  const oldF = flattenTree(repo, oldTree);
  const newF = flattenTree(repo, newTree);
  const paths = new Set([...oldF.keys(), ...newF.keys()]);
  const out: Array<{ path: string; status: 'added' | 'removed' | 'modified'; oldOid: string | null; newOid: string | null }> = [];
  for (const path of [...paths].sort()) {
    const o = oldF.get(path);
    const n = newF.get(path);
    if (!o && n) out.push({ path, status: 'added', oldOid: null, newOid: n.oid });
    else if (o && !n) out.push({ path, status: 'removed', oldOid: o.oid, newOid: null });
    else if (o && n && o.oid !== n.oid) out.push({ path, status: 'modified', oldOid: o.oid, newOid: n.oid });
  }
  return out;
}
// Merge base: nearest common ancestor of two commits (first found walking both).
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancA = ancestors(repo, a);
  if (ancA.has(b)) return b;
  const seen = new Set<string>();
  const queue = [b];
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head];
    head += 1;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancA.has(oid)) return oid;
    const info = commitInfo(repo, oid);
    if (info) for (const p of info.parents) queue.push(p);
  }
  return null;
}

// ---------------------------------------------------------------- packfiles
const PACK_TYPE_NAME: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
function readObjectHeader(data: Buffer, off: number): { typeNum: number; size: number; next: number } {
  let byte = data[off];
  const typeNum = (byte >> 4) & 0x07;
  let size = byte & 0x0f;
  let shift = 4;
  let i = off + 1;
  while (byte & 0x80) {
    byte = data[i];
    size |= (byte & 0x7f) << shift;
    shift += 7;
    i += 1;
  }
  return { typeNum, size, next: i };
}
// Inflate one zlib stream starting at `off`; returns the data and the offset
// just past the stream. inflateSync with {info:true} reports bytesWritten,
// i.e. how many input bytes the stream consumed.
function inflateAt(data: Buffer, off: number): { data: Buffer; next: number } {
  const result = inflateSync(data.subarray(off), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  const written = result.engine?.bytesWritten;
  if (!written || written <= 0) throw new Error('zlib stream consumed no bytes');
  return { data: result.buffer, next: off + written };
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let p = 0;
  const readVar = (): number => {
    let v = 0;
    let s = 0;
    while (true) {
      const b = delta[p];
      p += 1;
      v |= (b & 0x7f) << s;
      s += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  const srcSize = readVar();
  const tgtSize = readVar();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out: Buffer[] = [];
  while (p < delta.length) {
    const op = delta[p];
    p += 1;
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      for (let i = 0; i < 4; i += 1) if (op & (1 << i)) { cpOff |= delta[p] << (8 * i); p += 1; }
      for (let i = 0; i < 3; i += 1) if (op & (0x10 << i)) { cpSize |= delta[p] << (8 * i); p += 1; }
      if (cpSize === 0) cpSize = 0x10000;
      out.push(base.subarray(cpOff, cpOff + cpSize));
    } else if (op) {
      out.push(delta.subarray(p, p + op));
      p += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const buf = Buffer.concat(out);
  if (buf.length !== tgtSize) throw new Error('delta target size mismatch');
  return buf;
}
interface PackEntry { type: ObjType; data: Buffer; oid: string; }
type ObjectLookup = (oid: string) => GitObject | undefined;
function readPack(data: Buffer, lookup?: ObjectLookup): PackEntry[] {
  if (data.length < 12 || data.toString('ascii', 0, 4) !== 'PACK') throw new Error('bad pack header');
  if (data.readUInt32BE(4) !== 2) throw new Error('unsupported pack version');
  const count = data.readUInt32BE(8);
  let off = 12;
  const entries: PackEntry[] = [];
  const byOffset = new Map<number, PackEntry>();
  for (let n = 0; n < count; n += 1) {
    const startOff = off;
    const { typeNum, size, next } = readObjectHeader(data, off);
    off = next;
    let type: ObjType;
    let objData: Buffer;
    if (typeNum === 6) {
      let byte = data[off];
      off += 1;
      let baseOff = byte & 0x7f;
      while (byte & 0x80) {
        byte = data[off];
        off += 1;
        baseOff = ((baseOff + 1) << 7) | (byte & 0x7f);
      }
      const baseEntry = byOffset.get(startOff - baseOff);
      if (!baseEntry) throw new Error('ofs delta base not found');
      const inf = inflateAt(data, off);
      off = inf.next;
      objData = applyDelta(baseEntry.data, inf.data);
      type = baseEntry.type;
    } else if (typeNum === 7) {
      const baseOid = data.subarray(off, off + 20).toString('hex');
      off += 20;
      // A thin pack may delta against an object the server already holds.
      const baseEntry = entries.find((e) => e.oid === baseOid)
        ?? (lookup ? lookup(baseOid) : undefined);
      if (!baseEntry) throw new Error('ref delta base not found');
      const inf = inflateAt(data, off);
      off = inf.next;
      objData = applyDelta(baseEntry.data, inf.data);
      type = baseEntry.type;
    } else {
      type = PACK_TYPE_NAME[typeNum]!;
      if (!type) throw new Error(`unknown pack type ${typeNum}`);
      const inf = inflateAt(data, off);
      off = inf.next;
      objData = inf.data;
    }
    if (objData.length !== size) throw new Error(`object size mismatch: got ${objData.length}, want ${size}`);
    const oid = sha1Of(type, objData);
    const entry: PackEntry = { type, data: objData, oid };
    entries.push(entry);
    byOffset.set(startOff, entry);
  }
  return entries;
}
function writePack(entries: PackEntry[]): Buffer {
  const parts: Buffer[] = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 'ascii');
  head.writeUInt32BE(2, 4);
  head.writeUInt32BE(entries.length, 8);
  parts.push(head);
  const typeNum: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
  for (const e of entries) {
    // Object header: (size & 0x0f) | (type << 4), then 7-bit size groups MSB-first.
    const sizeBytes: number[] = [];
    let size = e.data.length;
    let first = (size & 0x0f) | (typeNum[e.type] << 4);
    size >>>= 4;
    if (size > 0) first |= 0x80;
    sizeBytes.push(first);
    while (size > 0) {
      let b = size & 0x7f;
      size >>>= 7;
      if (size > 0) b |= 0x80;
      sizeBytes.push(b);
    }
    parts.push(Buffer.from(sizeBytes));
    parts.push(deflateSync(e.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// ---------------------------------------------------------------- pkt-lines
function pktLine(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = data.length + 4;
  const head = Buffer.alloc(4);
  head.write(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
interface Pkt { kind: 'data' | 'flush' | 'delim'; payload: Buffer; }
function parsePktLines(data: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let i = 0;
  while (i + 4 <= data.length) {
    const len = parseInt(data.subarray(i, i + 4).toString('ascii'), 16);
    if (Number.isNaN(len)) throw new Error('bad pkt-line length');
    if (len === 0) { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (len < 4 || i + len > data.length) throw new Error('truncated pkt-line');
    out.push({ kind: 'data', payload: data.subarray(i + 4, i + len) });
    i += len;
  }
  return out;
}
// Chunk a byte stream into sideband pkt-lines (band byte + payload).
function sidebandChunks(data: Buffer, band: number): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 16384;
  for (let i = 0; i < data.length; i += CHUNK) {
    const slice = data.subarray(i, Math.min(data.length, i + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([band]), slice])));
  }
  return out;
}

// ---------------------------------------------------------------- store model
interface Label { name: string; color: string; }
interface Issue {
  number: number; id: number; title: string; body: string; state: 'open' | 'closed';
  labels: Label[]; seq: number;
  jsonBuf: Buffer | null; // cached serialized GET body; cleared on any mutation
}
interface Comment { id: number; body: string; }
interface Pull {
  number: number; id: number; title: string; body: string; state: 'open' | 'closed';
  headRef: string; baseRef: string; headSha: string; baseSha: string;
  merged: boolean; mergedAt: string | null; mergeCommitSha: string | null; seq: number;
}
interface Repo {
  owner: string | null; // null until the viewer login is learned
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  databaseId: number;
  objects: Map<string, GitObject>;
  refs: Map<string, string>; // ref name -> oid
  issues: Map<number, Issue>;
  pulls: Map<number, Pull>;
  labels: Map<string, Label>;
  comments: Map<number, Comment[]>;
  nextNumber: number; // shared issue/PR counter
  seq: number; // creation order
  commitCache: Map<string, CommitInfo>; // parsed commits (immutable objects)
  // Response caches, keyed by the full inputs that determine the bytes
  // (fetch pack, ls-refs, advertisements). Objects only ever grow and refs
  // are fingerprinted into the keys, so a cached buffer stays exact.
  fetchCache: Map<string, Buffer>;
  lsRefsCache: Map<string, Buffer>;
  adCache: Map<string, Buffer>;
}
const repos = new Map<string, Repo>(); // key: owner\0name (owner resolved lazily)
const reposByName = new Map<string, Repo[]>(); // name -> repos (for lazy owner binding)
let repoSeq = 0;
function repoKey(owner: string, name: string): string { return `${owner}\0${name}`; }
function createRepo(owner: string | null, name: string, description: string, isPrivate: boolean): Repo {
  const repo: Repo = {
    owner, name, description, isPrivate, defaultBranch: 'main',
    databaseId: dbSeq += 1,
    objects: new Map(), refs: new Map(), issues: new Map(), pulls: new Map(),
    labels: new Map(), comments: new Map(), nextNumber: 1, seq: repoSeq += 1,
    commitCache: new Map(), fetchCache: new Map(), lsRefsCache: new Map(), adCache: new Map(),
  };
  if (owner) repos.set(repoKey(owner, name), repo);
  const list = reposByName.get(name) ?? [];
  list.push(repo);
  reposByName.set(name, list);
  return repo;
}
function findRepo(owner: string, name: string): Repo | undefined {
  const direct = repos.get(repoKey(owner, name));
  if (direct) return direct;
  // Lazy binding: a repo created before the viewer login was learned.
  const list = reposByName.get(name);
  if (list) {
    for (const r of list) {
      if (r.owner === null) {
        r.owner = owner;
        repos.set(repoKey(owner, name), r);
        return r;
      }
    }
  }
  return undefined;
}
function repoFullName(repo: Repo): string { return `${repo.owner ?? viewerName()}/${repo.name}`; }
function ownerOf(repo: Repo): string { return repo.owner ?? viewerName(); }

// ---------------------------------------------------------------- HTTP helpers
function sendBuf(res: RawRes, status: number, body: Buffer, headers: Readonly<Record<string, string>> = {}): void {
  const h: Record<string, string> = { 'content-type': JSON_TYPE, 'content-length': String(body.length), ...headers };
  h['x-github-request-id'] = `req-${reqSeq += 1}`;
  res.writeHead(status, h);
  res.end(body);
}
function sendJson(res: RawRes, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  sendBuf(res, status, Buffer.from(`${JSON.stringify(body)}\n`, 'utf8'), headers);
}
function sendNoContent(res: RawRes): void {
  res.writeHead(204, { 'x-github-request-id': `req-${reqSeq += 1}` });
  res.end();
}
function sendRaw(res: RawRes, status: number, body: Buffer, contentType: string, headers: Readonly<Record<string, string>> = {}): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': String(body.length), ...headers });
  res.end(body);
}
function unauthorized(res: RawRes): void { sendJson(res, 401, { message: 'Requires authentication' }); }
function notFound(res: RawRes, message = 'Not Found'): void { sendJson(res, 404, { message }); }
function readBody(req: RawReq): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (c: Buffer) => {
      total += c.length;
      if (total > MAX_BODY) { reject(new Error('body too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
const BEARER = TOKEN === '' ? '' : `Bearer ${TOKEN}`;
function authed(req: RawReq): boolean {
  if (TOKEN === '') return true;
  return req.headers.authorization === BEARER;
}
// Parse the request URL once per request (path + query); the handlers share it
// instead of each building their own URL object.
function parseRequestUrl(req: RawReq): { path: string; query: URLSearchParams } {
  try {
    const u = new URL(req.url ?? '/', 'http://entry');
    return { path: decodeURIComponent(u.pathname), query: u.searchParams };
  } catch { return { path: '/', query: new URLSearchParams() }; }
}
function baseUrlOf(req: RawReq): string {
  const host = req.headers.host ?? '127.0.0.1';
  return `http://${host}`;
}

// ---------------------------------------------------------------- raw HTTP/1.1
// A hand-rolled HTTP/1.1 server on a raw TCP socket, replacing node:http.
// The trial is idle-bound (round-trips + client work dominate), so the
// remaining win is shaving the per-request stack cost: no IncomingMessage /
// ServerResponse / stream objects, no header (de)serialisation through the
// http layer — one Buffer built per response, one socket.write per reply.
// Every response the app produces is a single writeHead + end, so the shim
// below implements exactly that surface, plus body reading for readBody.
// Conformance notes (kept identical to node:http behaviour):
// - keep-alive by default on HTTP/1.1, close on HTTP/1.0 unless asked;
// - Content-Length and chunked request bodies (git push streams chunked);
// - Expect: 100-continue answered as soon as the headers parse (curl-based
//   clients wait ~1 s for it, so a late answer costs a whole second);
// - pipelined requests answered in order; half-closed sockets answered
//   then closed; Connection: close honoured; HEAD answers headers only.

const REASON_PHRASES: Record<number, string> = {
  200: 'OK', 201: 'Created', 202: 'Accepted', 204: 'No Content',
  400: 'Bad Request', 401: 'Unauthorized', 403: 'Forbidden',
  404: 'Not Found', 405: 'Method Not Allowed', 409: 'Conflict',
  422: 'Unprocessable Entity', 500: 'Internal Server Error',
};

// The only request/response surface the handlers use (method, url, headers,
// body stream events, destroy / writeHead, end, headersSent, destroy).
interface RawReq {
  method: string;
  url: string;
  headers: Record<string, string>;
  on(event: 'data' | 'end' | 'error', fn: (...args: any[]) => void): void;
  destroy(): void;
}

interface RawRes {
  headersSent: boolean;
  writeHead(status: number, headers?: Record<string, string>): void;
  end(body?: Buffer): void;
  destroy(): void;
}

class RawReqImpl implements RawReq {
  method: string;
  url: string;
  headers: Record<string, string>;
  private body: Buffer<ArrayBufferLike>;
  private onDestroy: () => void;
  private delivered = false;
  constructor(method: string, url: string, headers: Record<string, string>, body: Buffer<ArrayBufferLike>, onDestroy: () => void) {
    this.method = method;
    this.url = url;
    this.headers = headers;
    this.body = body;
    this.onDestroy = onDestroy;
  }
  on(event: 'data' | 'end' | 'error', fn: (...args: any[]) => void): void {
    if (event === 'data') {
      // Bodies arrive whole at parse time; deliver as one chunk, exactly
      // like a stream that yields everything before 'end'.
      if (this.body.length > 0 && !this.delivered) {
        this.delivered = true;
        (fn as (chunk: Buffer) => void)(this.body as Buffer);
      }
    } else if (event === 'end') {
      // readBody registers 'end' after 'data', so this fires after the data
      // listener ran (or immediately for an empty body).
      (fn as () => void)();
    }
    // 'error': nothing to report; bodies arrive whole or not at all.
  }
  destroy(): void { this.onDestroy(); }
}

class RawResImpl implements RawRes {
  headersSent = false;
  lastWriteOk = true;
  sent = false;
  private status = 200;
  private head: Record<string, string> = {};
  private sock: Socket;
  private method: string;
  private keepAlive: boolean;
  constructor(sock: Socket, method: string, keepAlive: boolean) {
    this.sock = sock;
    this.method = method;
    this.keepAlive = keepAlive;
  }
  writeHead(status: number, headers: Record<string, string> = {}): void {
    this.status = status;
    this.head = headers;
    this.headersSent = true;
  }
  end(body?: Buffer): void {
    if (this.sent) return;
    this.sent = true;
    const b = body ?? Buffer.alloc(0);
    const head: Record<string, string> = { ...this.head };
    // Every response carries explicit body framing. node:http falls back to
    // chunked framing when the app sets no length; an explicit length is
    // equivalent on the wire and simpler for every client (without it a
    // keep-alive client cannot tell where a 202 response ends).
    if (head['content-length'] === undefined) head['content-length'] = String(b.length);
    const lines = [`HTTP/1.1 ${this.status} ${REASON_PHRASES[this.status] ?? ''}\r\n`];
    for (const [k, v] of Object.entries(head)) lines.push(`${k}: ${v}\r\n`);
    lines.push(`date: ${new Date().toUTCString()}\r\n`);
    lines.push(`connection: ${this.keepAlive ? 'keep-alive' : 'close'}\r\n`);
    lines.push('\r\n');
    const headBuf = Buffer.from(lines.join(''), 'latin1');
    // HEAD responses carry headers only, like node:http (length still set).
    const out = this.method === 'HEAD' ? headBuf : Buffer.concat([headBuf, b]);
    this.lastWriteOk = this.sock.write(out);
  }
  destroy(): void { this.sock.destroy(); }
}

type ChunkedResult = { body: Buffer<ArrayBufferLike>; consumed: number } | null | 'bad' | 'oversize';

function decodeChunked(buf: Buffer<ArrayBufferLike>, start: number): ChunkedResult {
  const parts: Buffer<ArrayBufferLike>[] = [];
  let total = 0;
  let pos = start;
  for (;;) {
    const lineEnd = buf.indexOf('\r\n', pos);
    if (lineEnd === -1) return null;
    const sizeLine = buf.subarray(pos, lineEnd).toString('latin1');
    const semi = sizeLine.indexOf(';');
    const sizeText = (semi === -1 ? sizeLine : sizeLine.slice(0, semi)).trim();
    if (!/^[0-9a-fA-F]+$/.test(sizeText)) return 'bad';
    const size = parseInt(sizeText, 16);
    pos = lineEnd + 2;
    if (size === 0) {
      // Trailers run to an empty line; their content is ignored.
      for (;;) {
        const tEnd = buf.indexOf('\r\n', pos);
        if (tEnd === -1) return null;
        if (tEnd === pos) return { body: Buffer.concat(parts), consumed: tEnd + 2 };
        pos = tEnd + 2;
      }
    }
    if (buf.length - pos < size + 2) return null;
    if (buf[pos + size] !== 0x0d || buf[pos + size + 1] !== 0x0a) return 'bad';
    total += size;
    if (total > MAX_BODY) return 'oversize';
    parts.push(buf.subarray(pos, pos + size));
    pos += size + 2;
  }
}

interface ParsedReq {
  method: string;
  url: string;
  headers: Record<string, string>;
  body: Buffer<ArrayBufferLike>;
  keepAlive: boolean;
}

class RawConn {
  private sock: Socket;
  private buf: Buffer<ArrayBufferLike> = Buffer.alloc(0);
  private ended = false; // client half-closed (FIN received)
  private destroyed = false;
  private pumping = false; // pump loop reentrancy guard
  private sent100 = false;
  private writeOk = true;
  private drainWait: (() => void) | null = null;

  constructor(sock: Socket) {
    this.sock = sock;
    // Small request/response pairs on a keep-alive socket: never let Nagle
    // hold a reply waiting for an ACK.
    sock.setNoDelay(true);
    sock.on('data', (chunk: Buffer) => this.onData(chunk));
    sock.on('end', () => { this.ended = true; void this.pump(); });
    sock.on('error', () => this.destroy());
    sock.on('close', () => { this.destroyed = true; });
    sock.on('drain', () => {
      const w = this.drainWait;
      this.drainWait = null;
      if (w) w();
    });
  }

  private destroy(): void {
    if (!this.destroyed) { this.destroyed = true; this.sock.destroy(); }
  }

  private onData(chunk: Buffer): void {
    if (this.destroyed) return;
    this.buf = this.buf.length === 0 ? chunk : Buffer.concat([this.buf, chunk]);
    void this.pump();
  }

  private sendBad(): void {
    try {
      this.sock.write(Buffer.from('HTTP/1.1 400 Bad Request\r\ncontent-length: 0\r\nconnection: close\r\n\r\n', 'latin1'));
    } catch { /* ignore */ }
    this.sock.end();
    this.destroyed = true;
  }

  private send100(): void {
    if (this.sent100) return;
    this.sent100 = true;
    try { this.sock.write(Buffer.from('HTTP/1.1 100 Continue\r\n\r\n', 'latin1')); } catch { /* ignore */ }
  }

  // Parse one complete request from the buffered bytes. Returns null when
  // more data is needed, 'bad' for a malformed request, or the request
  // (consuming its bytes, including any already-buffered pipelined data).
  private tryParse(): ParsedReq | null | 'bad' {
    const headEnd = this.buf.indexOf('\r\n\r\n');
    if (headEnd === -1) {
      if (this.buf.length > 65536) return 'bad';
      return null;
    }
    const headText = this.buf.subarray(0, headEnd).toString('latin1');
    const lines = headText.split('\r\n');
    const m = /^([!#$%&'*+\-.^_`|~0-9A-Za-z]+) (\S+) HTTP\/(1\.[01])$/.exec(lines[0]);
    if (!m) return 'bad';
    const [, method, rawTarget, version] = m;
    const headers: Record<string, string> = {};
    let lastName = '';
    for (let i = 1; i < lines.length; i++) {
      const line = lines[i];
      if (line === '') continue;
      if (line[0] === ' ' || line[0] === '\t') {
        // obs-fold: continuation of the previous header value.
        if (lastName) headers[lastName] += ` ${line.trim()}`;
        continue;
      }
      const colon = line.indexOf(':');
      if (colon <= 0) return 'bad';
      const name = line.slice(0, colon).trim().toLowerCase();
      const value = line.slice(colon + 1).trim();
      if (name === 'content-length' && headers[name] !== undefined && headers[name] !== value) return 'bad';
      headers[name] = headers[name] === undefined ? value : `${headers[name]}, ${value}`;
      lastName = name;
    }
    // Absolute-form targets (http://host/path) are reduced to the path,
    // exactly as node:http exposes them in req.url.
    let target = rawTarget;
    if (target === '*') target = '/';
    else if (/^https?:\/\//i.test(target)) {
      const slash = target.indexOf('/', target.indexOf('//') + 2);
      target = slash === -1 ? '/' : target.slice(slash);
    }
    // Answer 100-continue as soon as the headers parse; curl-based clients
    // wait for it before sending the body.
    if ((headers['expect'] ?? '').toLowerCase() === '100-continue') this.send100();
    const conn = (headers['connection'] ?? '').toLowerCase();
    const keepAlive = version === '1.1' ? conn !== 'close' : conn === 'keep-alive';
    const bodyStart = headEnd + 4;
    const te = headers['transfer-encoding'] ?? '';
    const teTokens = te.split(',').map((t) => t.trim().toLowerCase()).filter(Boolean);
    const chunked = teTokens.length > 0 && teTokens[teTokens.length - 1] === 'chunked';
    if (teTokens.length > 0 && !chunked) return 'bad';
    let body: Buffer;
    let consumed: number;
    if (chunked) {
      const dec = decodeChunked(this.buf, bodyStart);
      if (dec === null) return null;
      if (dec === 'bad') return 'bad';
      if (dec === 'oversize') { this.destroy(); return null; }
      body = dec.body;
      consumed = dec.consumed;
    } else if (headers['content-length'] !== undefined) {
      const len = Number(headers['content-length']);
      if (!Number.isInteger(len) || len < 0) return 'bad';
      if (len > MAX_BODY) { this.destroy(); return null; }
      if (this.buf.length - bodyStart < len) return null;
      body = this.buf.subarray(bodyStart, bodyStart + len);
      consumed = bodyStart + len;
    } else {
      body = Buffer.alloc(0);
      consumed = bodyStart;
    }
    this.buf = this.buf.subarray(consumed);
    this.sent100 = false;
    return { method, url: target, headers, body, keepAlive };
  }

  private async dispatch(p: ParsedReq): Promise<void> {
    const req = new RawReqImpl(p.method, p.url, p.headers, p.body, () => this.destroy());
    const res = new RawResImpl(this.sock, p.method, p.keepAlive);
    try {
      await handle(req, res);
    } catch (err) {
      try {
        if (!res.headersSent) sendJson(res, 500, { message: String((err as Error)?.message ?? err) });
        else res.destroy();
      } catch { /* ignore */ }
    }
    this.writeOk = res.lastWriteOk;
    if (!p.keepAlive && res.sent) this.sock.end();
    else if (this.ended && this.buf.length === 0) this.sock.end();
  }

  private async pump(): Promise<void> {
    if (this.pumping || this.destroyed) return;
    this.pumping = true;
    try {
      for (;;) {
        if (this.destroyed) return;
        if (!this.writeOk) {
          // Backpressure: do not dispatch the next pipelined request until
          // the socket drains, so memory stays bounded.
          await new Promise<void>((resolve) => { this.drainWait = resolve; });
          if (this.destroyed) return;
          this.writeOk = true;
        }
        const parsed = this.tryParse();
        if (parsed === null) break;
        if (parsed === 'bad') { this.sendBad(); return; }
        await this.dispatch(parsed);
      }
      if (this.ended && this.buf.length === 0) this.sock.end();
    } finally {
      this.pumping = false;
    }
  }
}

// ---------------------------------------------------------------- REST shapes
function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.databaseId,
    node_id: globalId('repo', repoFullName(repo)),
    name: repo.name,
    full_name: repoFullName(repo),
    owner: { login: ownerOf(repo), id: 1000, type: 'User' },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
    html_url: `https://example.invalid/${repoFullName(repo)}`,
    clone_url: `https://example.invalid/${repoFullName(repo)}.git`,
    has_issues: true,
  };
}
function issueJson(issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((l) => ({ name: l.name, color: l.color })),
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
  };
}
function pullJson(pull: Pull, repo: Repo): Record<string, unknown> {
  return {
    id: pull.id,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    head: { ref: pull.headRef, sha: pull.headSha, label: `${ownerOf(repo)}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${ownerOf(repo)}:${pull.baseRef}` },
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: mergeableState(repo, pull) === 'MERGEABLE',
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
  };
}
function globalId(kind: string, key: string): string {
  return Buffer.from(`${kind}:${key}`, 'utf8').toString('base64');
}
function decodeGlobalId(id: string): { kind: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const i = text.indexOf(':');
    if (i <= 0) return null;
    return { kind: text.slice(0, i), key: text.slice(i + 1) };
  } catch { return null; }
}
function mergeableState(repo: Repo, pull: Pull): 'MERGEABLE' | 'CONFLICTING' | 'UNKNOWN' {
  if (pull.state !== 'open') return 'UNKNOWN';
  const headTip = peelToCommit(repo, pull.headSha);
  const baseTip = peelToCommit(repo, repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '');
  if (!headTip || !baseTip) return 'UNKNOWN';
  const base = mergeBase(repo, headTip, baseTip);
  if (!base) return 'UNKNOWN';
  const headCommit = repo.objects.get(headTip);
  const baseCommit = repo.objects.get(baseTip);
  const baseBaseCommit = repo.objects.get(base);
  if (!headCommit || !baseCommit || !baseBaseCommit) return 'UNKNOWN';
  const headChanges = diffTrees(repo, parseCommit(baseBaseCommit.data).tree, parseCommit(headCommit.data).tree);
  const baseChanges = diffTrees(repo, parseCommit(baseBaseCommit.data).tree, parseCommit(baseCommit.data).tree);
  const baseChanged = new Map<string, string | null>();
  for (const c of baseChanges) baseChanged.set(c.path, c.newOid);
  for (const c of headChanges) {
    if (baseChanged.has(c.path) && baseChanged.get(c.path) !== c.newOid) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}
// Apply a file change (create/update/delete) on a branch, returning the new tip.
function commitOnBranch(repo: Repo, branch: string, message: string, changes: Array<{ path: string; content: Buffer | null; mode?: string }>): string {
  const refName = `refs/heads/${branch}`;
  const current = repo.refs.get(refName);
  const parentCommit = current ? peelToCommit(repo, current) : null;
  const baseTree = parentCommit ? parseCommit(repo.objects.get(parentCommit)!.data).tree : null;
  const flat = baseTree ? flattenTree(repo, baseTree) : new Map<string, { oid: string; mode: string }>();
  for (const ch of changes) {
    if (ch.content === null) flat.delete(ch.path);
    else {
      const blobOid = storeObject(repo, 'blob', ch.content);
      flat.set(ch.path, { oid: blobOid, mode: ch.mode ?? '100644' });
    }
  }
  // Rebuild nested trees from the flat map.
  const treeOid = buildTreeFromFlat(repo, flat);
  const parents = parentCommit ? [parentCommit] : [];
  const commitOid = makeCommit(repo, treeOid, parents, message);
  repo.refs.set(refName, commitOid);
  return commitOid;
}
function buildTreeFromFlat(repo: Repo, flat: Map<string, { oid: string; mode: string }>): string {
  // Group by directory depth.
  const dirs = new Map<string, TreeEntry[]>();
  const ensure = (dir: string): TreeEntry[] => {
    let list = dirs.get(dir);
    if (!list) { list = []; dirs.set(dir, list); }
    return list;
  };
  ensure('');
  for (const [path, entry] of flat) {
    const slash = path.lastIndexOf('/');
    const dir = slash >= 0 ? path.slice(0, slash) : '';
    const name = slash >= 0 ? path.slice(slash + 1) : path;
    // Ensure every ancestor directory exists, even one holding only subdirs.
    if (dir !== '') {
      const parts = dir.split('/');
      for (let i = 1; i <= parts.length; i += 1) ensure(parts.slice(0, i).join('/'));
    }
    ensure(dir).push({ mode: entry.mode, name, oid: entry.oid });
  }
  // Build bottom-up: process directories in reverse depth order.
  const dirNames = [...dirs.keys()].sort((a, b) => b.split('/').length - a.split('/').length || (a < b ? 1 : -1));
  const treeOids = new Map<string, string>();
  for (const dir of dirNames) {
    const entries = [...dirs.get(dir)!];
    if (dir !== '') {
      // Child directories of this dir were built already; add them as entries.
      for (const [childDir, childOid] of treeOids) {
        if (childDir.startsWith(dir + '/') && !childDir.slice(dir.length + 1).includes('/')) {
          entries.push({ mode: '40000', name: childDir.slice(dir.length + 1), oid: childOid });
        }
      }
    } else {
      for (const [childDir, childOid] of treeOids) {
        if (!childDir.includes('/')) entries.push({ mode: '40000', name: childDir, oid: childOid });
      }
    }
    treeOids.set(dir, storeObject(repo, 'tree', buildTree(entries)));
  }
  return treeOids.get('')!;
}
function blobAt(repo: Repo, commitOid: string, path: string): { oid: string; data: Buffer; mode: string } | null {
  const commit = repo.objects.get(commitOid);
  if (!commit || commit.type !== 'commit') return null;
  const flat = flattenTree(repo, parseCommit(commit.data).tree);
  const entry = flat.get(path);
  if (!entry) return null;
  const blob = repo.objects.get(entry.oid);
  if (!blob || blob.type !== 'blob') return null;
  return { oid: entry.oid, data: blob.data, mode: entry.mode };
}
function paginate<T>(items: T[], query: URLSearchParams): { page: T[]; next: number | null } {
  const perPageRaw = query.get('per_page');
  const perPage = perPageRaw ? Math.max(1, parseInt(perPageRaw, 10) || 30) : 30;
  const pageNum = Math.max(1, parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (pageNum - 1) * perPage;
  const page = items.slice(start, start + perPage);
  const next = start + perPage < items.length ? pageNum + 1 : null;
  return { page, next };
}
function linkHeader(req: RawReq, query: URLSearchParams, nextPage: number | null): Record<string, string> {
  if (nextPage === null) return {};
  const q = new URLSearchParams(query);
  q.set('page', String(nextPage));
  return { link: `<${baseUrlOf(req)}/api/v3/user/repos?${q.toString()}>; rel="next"` };
}
function linkHeaderFor(req: RawReq, path: string, query: URLSearchParams, nextPage: number | null): Record<string, string> {
  if (nextPage === null) return {};
  const q = new URLSearchParams(query);
  q.set('page', String(nextPage));
  return { link: `<${baseUrlOf(req)}${path}?${q.toString()}>; rel="next"` };
}

// ---------------------------------------------------------------- REST v3
function restRepoPath(res: RawRes, owner: string, name: string): Repo | null {
  learnOwner(owner);
  const repo = findRepo(owner, name);
  if (!repo) { notFound(res); return null; }
  return repo;
}
function parseJsonBody(raw: Buffer): { ok: true; value: Record<string, unknown> } | { ok: false } {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    const v = JSON.parse(raw.toString('utf8')) as unknown;
    if (v !== null && typeof v === 'object' && !Array.isArray(v)) return { ok: true, value: v as Record<string, unknown> };
    return { ok: true, value: {} };
  } catch { return { ok: false }; }
}
function handleRest(req: RawReq, res: RawRes, raw: Buffer, path: string, query: URLSearchParams): void {
  const method = req.method ?? 'GET';
  const segs = path.split('/').filter((s) => s !== '');
  // segs[0] === 'api', segs[1] === 'v3'
  if (segs.length === 2) {
    if (method === 'GET') {
      sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
      return;
    }
    notFound(res);
    return;
  }
  const body = parseJsonBody(raw);
  if (!body.ok) { sendJson(res, 400, { message: 'Problems parsing JSON' }); return; }
  const json = body.value;
  const tail = segs.slice(2);

  if (tail[0] === 'meta' && tail.length === 1 && method === 'GET') {
    sendJson(res, 200, { installed_version: '1.0.0' });
    return;
  }
  if (tail[0] === 'user' && tail.length === 1 && method === 'GET') {
    if (!viewerLogin) { notFound(res, 'Not Found'); return; }
    sendJson(res, 200, { login: viewerLogin, id: 1000, type: 'User', name: viewerLogin });
    return;
  }
  if (tail[0] === 'user' && tail[1] === 'repos') {
    if (method === 'GET') {
      const all: Repo[] = [];
      for (const list of reposByName.values()) for (const r of list) if (r.owner === null || r.owner === viewerLogin) all.push(r);
      all.sort((a, b) => a.seq - b.seq);
      const { page, next } = paginate(all, query);
      sendJson(res, 200, page.map(repoJson), linkHeaderFor(req, '/api/v3/user/repos', query, next));
      return;
    }
    if (method === 'POST') {
      const name = typeof json.name === 'string' ? json.name.trim() : '';
      if (!name) { sendJson(res, 422, { message: 'Repository name is required' }); return; }
      const exists = [...(reposByName.get(name) ?? [])].some((r) => r.owner === null || r.owner === viewerLogin);
      if (exists) { sendJson(res, 422, { message: 'Repository already exists' }); return; }
      const repo = createRepo(viewerLogin, name, typeof json.description === 'string' ? json.description : '', json.private === true);
      sendJson(res, 201, repoJson(repo));
      return;
    }
    notFound(res);
    return;
  }
  if (tail[0] === 'repos' && tail.length >= 3) {
    const owner = tail[1];
    const name = tail[2];
    const repo = restRepoPath(res, owner, name);
    if (!repo) return;
    const rest = tail.slice(3);
    // /repos/{o}/{r}
    if (rest.length === 0) {
      if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return; }
      if (method === 'PATCH') {
        if (typeof json.description === 'string') repo.description = json.description;
        if (typeof json.private === 'boolean') repo.isPrivate = json.private;
        sendJson(res, 200, repoJson(repo));
        return;
      }
      if (method === 'DELETE') {
        if (repo.owner) repos.delete(repoKey(repo.owner, repo.name));
        const list = reposByName.get(repo.name);
        if (list) { const i = list.indexOf(repo); if (i >= 0) list.splice(i, 1); }
        sendNoContent(res);
        return;
      }
      notFound(res);
      return;
    }
    // branches
    if (rest[0] === 'branches') {
      if (rest.length === 1 && method === 'GET') {
        const out = [...repo.refs.keys()].filter((r) => r.startsWith('refs/heads/')).sort().map((r) => ({
          name: r.slice('refs/heads/'.length), commit: { sha: repo.refs.get(r)! }, protected: false,
        }));
        sendJson(res, 200, out);
        return;
      }
      if (rest.length === 2 && method === 'GET') {
        const ref = repo.refs.get(`refs/heads/${rest[1]}`);
        if (!ref) { notFound(res); return; }
        sendJson(res, 200, { name: rest[1], commit: { sha: ref }, protected: false });
        return;
      }
      notFound(res);
      return;
    }
    // commits
    if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
      const shaParam = query.get('sha');
      let tip: string | undefined;
      if (shaParam) {
        if (repo.refs.has(`refs/heads/${shaParam}`)) tip = repo.refs.get(`refs/heads/${shaParam}`);
        else if (repo.refs.has(shaParam)) tip = repo.refs.get(shaParam);
        else if (repo.objects.has(shaParam)) tip = shaParam;
      } else {
        tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
      }
      const out: Array<Record<string, unknown>> = [];
      if (tip) {
        const seen = new Set<string>();
        const stack = [tip];
        while (stack.length) {
          const oid = stack.pop()!;
          if (seen.has(oid)) continue;
          seen.add(oid);
          const obj = repo.objects.get(oid);
          if (!obj || obj.type !== 'commit') continue;
          const c = parseCommit(obj.data);
          const ident = (line: string): { name: string; email: string; date: string } => {
            const m = /^(.*) <(.*)> \d+ [+-]\d{4}$/.exec(line);
            return { name: m?.[1] ?? viewerName(), email: m?.[2] ?? viewerEmail(), date: FIXED_TS };
          };
          out.push({
            sha: oid,
            commit: {
              message: c.message,
              author: ident(c.author),
              committer: ident(c.committer),
              tree: { sha: c.tree },
            },
            parents: c.parents.map((p) => ({ sha: p })),
          });
          for (const p of c.parents) stack.push(p);
        }
      }
      sendJson(res, 200, out);
      return;
    }
    // git refs
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'GET' && rest.length === 2) {
        const out = [...repo.refs.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1).map(([ref, oid]) => ({ ref, object: { sha: oid, type: 'commit' } }));
        sendJson(res, 200, out);
        return;
      }
      if (method === 'GET' && rest.length >= 3) {
        const refName = `refs/${rest.slice(2).join('/')}`;
        const oid = repo.refs.get(refName);
        if (!oid) { notFound(res); return; }
        const obj = repo.objects.get(oid);
        sendJson(res, 200, { ref: refName, object: { sha: oid, type: obj?.type ?? 'commit' } });
        return;
      }
      if (method === 'POST' && rest.length === 2) {
        const ref = typeof json.ref === 'string' ? json.ref : '';
        const sha = typeof json.sha === 'string' ? json.sha : '';
        if (!ref.startsWith('refs/') || !repo.objects.has(sha)) { sendJson(res, 422, { message: 'Invalid ref or sha' }); return; }
        if (repo.refs.has(ref)) { sendJson(res, 422, { message: 'Reference already exists' }); return; }
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, object: { sha, type: repo.objects.get(sha)?.type ?? 'commit' } });
        return;
      }
      notFound(res);
      return;
    }
    // contents
    if (rest[0] === 'contents') {
      const filePath = rest.slice(1).join('/');
      const branch = typeof json.branch === 'string' ? json.branch : (query.get('ref') ?? repo.defaultBranch);
      const refName = `refs/heads/${branch}`;
      if (method === 'GET') {
        const tip = peelToCommit(repo, repo.refs.get(refName) ?? '');
        if (!tip) { notFound(res); return; }
        const commit = repo.objects.get(tip)!;
        const treeOid = parseCommit(commit.data).tree;
        if (filePath === '') {
          const entries = parseTree(repo.objects.get(treeOid)!.data).map((e) => ({
            type: e.mode === '40000' ? 'dir' : 'file', name: e.name, path: e.name, sha: e.oid, size: 0,
          }));
          sendJson(res, 200, entries);
          return;
        }
        const flat = flattenTree(repo, treeOid);
        const entry = flat.get(filePath);
        if (entry) {
          const blob = repo.objects.get(entry.oid)!;
          sendJson(res, 200, {
            type: 'file', encoding: 'base64', size: blob.data.length, name: filePath.split('/').pop() ?? filePath,
            path: filePath, content: blob.data.toString('base64'), sha: entry.oid,
          });
          return;
        }
        // Directory listing: children of filePath in the tree.
        const prefix = `${filePath}/`;
        const children = new Map<string, { type: string; sha: string; size: number }>();
        for (const [p, e] of flat) {
          if (!p.startsWith(prefix)) continue;
          const rest2 = p.slice(prefix.length);
          if (rest2.includes('/')) continue;
          children.set(rest2, { type: 'file', sha: e.oid, size: repo.objects.get(e.oid)?.data.length ?? 0 });
        }
        // Subdirectories: find tree entries at this level.
        const dirEntries = new Map<string, string>();
        const walk = (tree: string, curPrefix: string): void => {
          const obj = repo.objects.get(tree);
          if (!obj || obj.type !== 'tree') return;
          for (const e of parseTree(obj.data)) {
            const p = curPrefix ? `${curPrefix}/${e.name}` : e.name;
            if (e.mode === '40000') {
              if (p === filePath) { /* listed below via children scan */ }
              if (p.startsWith(prefix) && !p.slice(prefix.length).includes('/')) dirEntries.set(e.name, e.oid);
              walk(e.oid, p);
            }
          }
        };
        walk(treeOid, '');
        for (const [name, oid] of dirEntries) children.set(name, { type: 'dir', sha: oid, size: 0 });
        if (children.size === 0) { notFound(res); return; }
        sendJson(res, 200, [...children.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1).map(([name, e]) => ({
          type: e.type, name, path: `${filePath}/${name}`, sha: e.sha, size: e.size,
        })));
        return;
      }
      if (method === 'PUT') {
        if (typeof json.content !== 'string') { sendJson(res, 422, { message: 'content is required' }); return; }
        const content = Buffer.from(json.content, 'base64');
        const message = typeof json.message === 'string' ? json.message : `Update ${filePath}`;
        const tip = peelToCommit(repo, repo.refs.get(refName) ?? '');
        const existing = tip ? blobAt(repo, tip, filePath) : null;
        const sha = typeof json.sha === 'string' ? json.sha : null;
        if (existing) {
          if (sha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match the current blob' }); return; }
          const newTip = commitOnBranch(repo, branch, message, [{ path: filePath, content }]);
          const newBlob = blobAt(repo, newTip, filePath)!;
          sendJson(res, 200, { content: { sha: newBlob.oid, encoding: 'base64', size: newBlob.data.length }, commit: { sha: newTip } });
          return;
        }
        const newTip = commitOnBranch(repo, branch, message, [{ path: filePath, content }]);
        const newBlob = blobAt(repo, newTip, filePath)!;
        sendJson(res, 201, { content: { sha: newBlob.oid, encoding: 'base64', size: newBlob.data.length }, commit: { sha: newTip } });
        return;
      }
      if (method === 'DELETE') {
        const tip = peelToCommit(repo, repo.refs.get(refName) ?? '');
        const existing = tip ? blobAt(repo, tip, filePath) : null;
        if (!existing) { notFound(res); return; }
        const sha = typeof json.sha === 'string' ? json.sha : null;
        if (sha && sha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match the current blob' }); return; }
        const message = typeof json.message === 'string' ? json.message : `Delete ${filePath}`;
        const newTip = commitOnBranch(repo, branch, message, [{ path: filePath, content: null }]);
        sendJson(res, 200, { commit: { sha: newTip } });
        return;
      }
      notFound(res);
      return;
    }
    // labels
    if (rest[0] === 'labels') {
      if (method === 'GET' && rest.length === 1) {
        sendJson(res, 200, [...repo.labels.values()]);
        return;
      }
      if (method === 'POST' && rest.length === 1) {
        const name = typeof json.name === 'string' ? json.name.trim() : '';
        const color = typeof json.color === 'string' ? json.color : 'ededed';
        if (!name) { sendJson(res, 422, { message: 'Label name is required' }); return; }
        if (repo.labels.has(name)) { sendJson(res, 422, { message: 'Label already exists' }); return; }
        const label: Label = { name, color };
        repo.labels.set(name, label);
        sendJson(res, 201, label);
        return;
      }
      notFound(res);
      return;
    }
    // issues
    if (rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = typeof json.title === 'string' ? json.title : '';
          if (!title) { sendJson(res, 422, { message: 'title is required' }); return; }
          const labelNames = Array.isArray(json.labels) ? (json.labels as unknown[]).map((l) => typeof l === 'string' ? l : (l as Record<string, unknown>)?.name).filter((x): x is string => typeof x === 'string') : [];
          for (const ln of labelNames) {
            if (!repo.labels.has(ln)) { sendJson(res, 422, { message: `Label does not exist: ${ln}` }); return; }
          }
          const issue: Issue = {
            number: repo.nextNumber, id: idSeq += 1, title,
            body: typeof json.body === 'string' ? json.body : '',
            state: 'open', labels: labelNames.map((n) => repo.labels.get(n)!), seq: repo.nextNumber,
            jsonBuf: null,
          };
          repo.nextNumber += 1;
          repo.issues.set(issue.number, issue);
          sendJson(res, 201, issueJson(issue));
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          let list = [...repo.issues.values()];
          if (state !== 'all') list = list.filter((i) => i.state === state);
          const direction = (query.get('direction') ?? 'desc').toLowerCase();
          list.sort((a, b) => direction === 'asc' ? a.seq - b.seq : b.seq - a.seq);
          const { page, next } = paginate(list, query);
          sendJson(res, 200, page.map(issueJson), linkHeaderFor(req, `/api/v3/repos/${owner}/${name}/issues`, query, next));
          return;
        }
        notFound(res);
        return;
      }
      const num = Number(rest[1]);
      const issue = repo.issues.get(num);
      if (rest.length === 2) {
        if (!issue) { notFound(res); return; }
        if (method === 'GET') {
          // The read workload GETs the same issue 2,000 times: serve the
          // pre-serialized body until the issue is mutated.
          if (!issue.jsonBuf) issue.jsonBuf = Buffer.from(`${JSON.stringify(issueJson(issue))}\n`, 'utf8');
          sendBuf(res, 200, issue.jsonBuf);
          return;
        }
        if (method === 'PATCH') {
          if (typeof json.title === 'string') issue.title = json.title;
          if (typeof json.body === 'string') issue.body = json.body;
          if (json.state === 'open' || json.state === 'closed') issue.state = json.state;
          issue.jsonBuf = null;
          sendJson(res, 200, issueJson(issue));
          return;
        }
        notFound(res);
        return;
      }
      if (rest[2] === 'comments') {
        if (!issue) { notFound(res); return; }
        if (method === 'POST') {
          const comment: Comment = { id: idSeq += 1, body: typeof json.body === 'string' ? json.body : '' };
          const list = repo.comments.get(issue.number) ?? [];
          list.push(comment);
          repo.comments.set(issue.number, list);
          sendJson(res, 201, { id: comment.id, body: comment.body, created_at: FIXED_TS });
          return;
        }
        if (method === 'GET') {
          const list = repo.comments.get(issue.number) ?? [];
          sendJson(res, 200, list.map((c) => ({ id: c.id, body: c.body, created_at: FIXED_TS })));
          return;
        }
        notFound(res);
        return;
      }
      notFound(res);
      return;
    }
    // pulls
    if (rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = typeof json.title === 'string' ? json.title : '';
          const head = typeof json.head === 'string' ? json.head : '';
          const base = typeof json.base === 'string' ? json.base : repo.defaultBranch;
          if (!title || !head) { sendJson(res, 422, { message: 'title and head are required' }); return; }
          const headOid = repo.refs.get(`refs/heads/${head}`);
          const baseOid = repo.refs.get(`refs/heads/${base}`);
          if (!headOid || !baseOid) { sendJson(res, 422, { message: 'head or base branch does not exist' }); return; }
          const dup = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === head);
          if (dup) { sendJson(res, 422, { message: 'A pull request already exists for this branch' }); return; }
          const pull: Pull = {
            number: repo.nextNumber, id: idSeq += 1, title,
            body: typeof json.body === 'string' ? json.body : '',
            state: 'open', headRef: head, baseRef: base,
            headSha: headOid, baseSha: baseOid,
            merged: false, mergedAt: null, mergeCommitSha: null, seq: repo.nextNumber,
          };
          repo.nextNumber += 1;
          repo.pulls.set(pull.number, pull);
          sendJson(res, 201, pullJson(pull, repo));
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          let list = [...repo.pulls.values()];
          if (state !== 'all') list = list.filter((p) => p.state === state);
          list.sort((a, b) => a.seq - b.seq);
          const { page, next } = paginate(list, query);
          sendJson(res, 200, page.map((p) => pullJson(p, repo)), linkHeaderFor(req, `/api/v3/repos/${owner}/${name}/pulls`, query, next));
          return;
        }
        notFound(res);
        return;
      }
      const num = Number(rest[2 - 1]);
      const pull = repo.pulls.get(num);
      if (rest.length === 2) {
        if (!pull) { notFound(res); return; }
        if (method === 'GET') { sendJson(res, 200, pullJson(pull, repo)); return; }
        notFound(res);
        return;
      }
      if (rest[2] === 'files' && rest.length === 3 && method === 'GET') {
        if (!pull) { notFound(res); return; }
        const headTip = peelToCommit(repo, pull.headSha);
        const baseTip = peelToCommit(repo, pull.baseSha);
        if (!headTip || !baseTip) { sendJson(res, 200, []); return; }
        const headCommit = repo.objects.get(headTip)!;
        const baseCommit = repo.objects.get(baseTip)!;
        const diff = diffTrees(repo, parseCommit(baseCommit.data).tree, parseCommit(headCommit.data).tree);
        const files = diff.map((d) => {
          const countLines = (oid: string | null): number => {
            if (!oid) return 0;
            const o = repo.objects.get(oid);
            if (!o) return 0;
            return o.data.toString('utf8').split('\n').filter((l) => l !== '').length;
          };
          const additions = d.status === 'removed' ? 0 : countLines(d.newOid);
          const deletions = d.status === 'added' ? 0 : countLines(d.oldOid);
          const status = d.status === 'added' ? 'added' : d.status === 'removed' ? 'removed' : 'modified';
          return { filename: d.path, status, additions, deletions, changes: additions + deletions };
        });
        sendJson(res, 200, files);
        return;
      }
      if (rest[2] === 'merge' && rest.length === 3 && method === 'PUT') {
        if (!pull) { notFound(res); return; }
        if (pull.state !== 'open') { sendJson(res, 405, { message: 'Pull request is already closed' }); return; }
        if (mergeableState(repo, pull) === 'CONFLICTING') { sendJson(res, 405, { message: 'Merge conflict' }); return; }
        const headTip = peelToCommit(repo, pull.headSha)!;
        const baseTip = peelToCommit(repo, repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '')!;
        const base = mergeBase(repo, headTip, baseTip);
        const headCommit = repo.objects.get(headTip)!;
        const baseCommit = repo.objects.get(baseTip)!;
        const baseBaseCommit = base ? repo.objects.get(base)! : null;
        const headTree = parseCommit(headCommit.data).tree;
        const baseTree = parseCommit(baseCommit.data).tree;
        let newTree = baseTree;
        if (baseBaseCommit) {
          const changes = diffTrees(repo, parseCommit(baseBaseCommit.data).tree, headTree);
          const flat = flattenTree(repo, baseTree);
          for (const c of changes) {
            if (c.newOid === null) flat.delete(c.path);
            else flat.set(c.path, { oid: c.newOid, mode: '100644' });
          }
          newTree = buildTreeFromFlat(repo, flat);
        } else {
          newTree = headTree;
        }
        const mergeSha = makeCommit(repo, newTree, [baseTip], `Merge pull request #${pull.number} from ${pull.headRef}`);
        repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
        pull.state = 'closed';
        pull.merged = true;
        pull.mergedAt = FIXED_TS;
        pull.mergeCommitSha = mergeSha;
        sendJson(res, 200, { sha: mergeSha, merged: true, message: 'Pull request successfully merged' });
        return;
      }
      notFound(res);
      return;
    }
    notFound(res);
    return;
  }
  notFound(res);
}

// ---------------------------------------------------------------- git smart HTTP
// Response caches. A cached buffer is byte-identical to a freshly built one:
// the fetch pack depends only on (wants, haves, depth, shallow, objects) and
// objects only ever grow, so objects.size in the key keeps it exact; ls-refs
// and advertisements depend only on the ref list, fingerprinted into the key.
function refFingerprint(repo: Repo): string {
  return [...repo.refs.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1)
    .map(([n, o]) => `${n}=${o}`).join(',');
}
function cachePut(map: Map<string, Buffer>, key: string, buf: Buffer): void {
  if (map.size >= 32) map.clear();
  map.set(key, buf);
}
const V2_ADVERTISEMENT: Buffer = Buffer.concat([
  ...['version 2', 'ls-refs=unborn', 'fetch=shallow wait-for-done', 'object-format=sha1', 'agent=github-forge/1.0.0']
    .map((c) => pktLine(`${c}\n`)),
  PKT_FLUSH,
]);
function gitRepoPath(res: RawRes, owner: string, name: string): Repo | null {
  learnOwner(owner);
  const repo = findRepo(owner, name);
  if (!repo) { notFound(res); return null; }
  return repo;
}
function refLinesV0(repo: Repo, caps: string): Buffer[] {
  const lines: Buffer[] = [];
  const refs = [...repo.refs.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1);
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headOid = repo.refs.get(headRef);
  if (refs.length === 0) {
    lines.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    refs.forEach(([name, oid], i) => {
      const suffix = i === 0 ? `\0${caps}\n` : '\n';
      lines.push(pktLine(`${oid} ${name}${suffix}`));
    });
    // HEAD line first in real git; the client parses the first line for
    // capabilities, so keep the first ref line as the capability carrier and
    // append HEAD after. The client only looks at refs starting with refs/.
    if (headOid) lines.push(pktLine(`${headOid} HEAD\n`));
  }
  return lines;
}
function handleInfoRefs(req: RawReq, res: RawRes, owner: string, name: string, service: string): void {
  const repo = gitRepoPath(res, owner, name);
  if (!repo) return;
  const proto2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  if (service === 'git-upload-pack' && proto2) {
    // The v2 capability list never depends on the repository: one constant.
    sendRaw(res, 200, V2_ADVERTISEMENT, 'application/x-git-upload-pack-advertisement');
    return;
  }
  // v0 advertisement (upload-pack without the v2 header, and receive-pack):
  // cached per service and ref state; refs change only on a push or merge.
  const adKey = `${service}|${refFingerprint(repo)}`;
  const cachedAd = repo.adCache.get(adKey);
  if (cachedAd) {
    sendRaw(res, 200, cachedAd, `application/x-${service}-advertisement`);
    return;
  }
  const serviceName = `# service=${service}\n`;
  const caps = service === 'git-receive-pack'
    ? 'report-status side-band-64k delete-refs ofs-delta agent=github-forge/1.0.0'
    : 'side-band-64k thin-pack ofs-delta multi_ack shallow agent=github-forge/1.0.0';
  const ad = Buffer.concat([pktLine(serviceName), PKT_FLUSH, ...refLinesV0(repo, caps), PKT_FLUSH]);
  cachePut(repo.adCache, adKey, ad);
  sendRaw(res, 200, ad, `application/x-${service}-advertisement`);
}
// Select objects for a fetch: wants, haves, optional depth.
function selectFetchObjects(repo: Repo, wants: string[], haves: string[], depth: number | null, clientShallow: string[]):
{ objects: Map<string, GitObject>; shallow: string[]; unshallow: string[] } {
  const wantCommits = wants.map((w) => peelToCommit(repo, w)).filter((x): x is string => x !== null);
  const dist = depth !== null ? commitDistances(repo, wantCommits, depth) : null;
  const shallowSet = new Set(clientShallow);
  // Commits the client already holds: the ancestors of each 'have' — except
  // a 'have' that is a shallow boundary, which holds only itself (its
  // history was never sent, which is the whole point of deepen).
  const heldCommits = new Set<string>();
  for (const h of haves) {
    const c = peelToCommit(repo, h);
    if (!c) continue;
    if (shallowSet.has(h) || shallowSet.has(c)) { heldCommits.add(c); continue; }
    for (const a of ancestors(repo, c)) heldCommits.add(a);
  }
  // Commits to include.
  const includeCommits = new Set<string>();
  for (const [oid, d] of (dist ?? new Map<string, number>())) {
    if (depth !== null && d >= depth) continue;
    includeCommits.add(oid);
  }
  if (depth === null) {
    for (const w of wantCommits) for (const a of ancestors(repo, w)) includeCommits.add(a);
  }
  // Exclude commits the client already holds (and their history).
  for (const h of heldCommits) includeCommits.delete(h);
  // Objects the client already holds. A fully-held commit holds its whole
  // history; a shallow boundary holds only its own commit and tree.
  const heldObjects = new Set<string>();
  for (const h of heldCommits) {
    if (shallowSet.has(h)) {
      for (const [oid] of commitTreeObjects(repo, h)) heldObjects.add(oid);
    } else {
      for (const a of ancestors(repo, h)) for (const [oid] of commitTreeObjects(repo, a)) heldObjects.add(oid);
    }
  }
  // Shallow boundary: commits at distance depth-1 from a want that have parents.
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== null && dist) {
    for (const [oid, d] of dist) {
      if (d === depth - 1) {
        const obj = repo.objects.get(oid);
        if (obj?.type === 'commit' && parseCommit(obj.data).parents.length > 0) shallow.push(oid);
      }
    }
    for (const s of clientShallow) {
      if (!shallow.includes(s) && includeCommits.has(s)) unshallow.push(s);
      // A boundary that is now fully fetched is unshallow: its parent is included.
      if (!shallow.includes(s)) {
        const obj = repo.objects.get(s);
        if (obj?.type === 'commit') {
          const parents = parseCommit(obj.data).parents;
          if (parents.some((p) => includeCommits.has(p))) unshallow.push(s);
        }
      }
    }
  }
  // Collect each included commit's own objects (its tree, not its parents').
  const objects = new Map<string, GitObject>();
  for (const c of includeCommits) {
    for (const [oid, obj] of commitTreeObjects(repo, c)) {
      if (heldObjects.has(oid)) continue;
      objects.set(oid, obj);
    }
  }
  // A wanted ref target that is not a commit (e.g. an annotated tag) is sent
  // itself, plus its peeled commit and that commit's tree — but never the
  // peeled commit's ancestors (that would break shallow fetches).
  for (const w of wants) {
    const obj = repo.objects.get(w);
    if (!obj || heldObjects.has(w)) continue;
    if (obj.type === 'tag') {
      objects.set(w, obj);
      const target = peelToCommit(repo, w);
      if (target) {
        const commitObj = repo.objects.get(target);
        if (commitObj) {
          objects.set(target, commitObj);
          const c = parseCommit(commitObj.data);
          for (const [oid, o2] of reachableObjects(repo, [c.tree])) if (!heldObjects.has(oid)) objects.set(oid, o2);
        }
      }
    } else if (obj.type !== 'commit') {
      objects.set(w, obj);
    }
  }
  return { objects, shallow: [...new Set(shallow)], unshallow: [...new Set(unshallow)] };
}
function buildFetchPack(repo: Repo, wants: string[], haves: string[], depth: number | null, clientShallow: string[]):
{ pack: Buffer; shallow: string[]; unshallow: string[]; ack: string | null } {
  const { objects, shallow, unshallow } = selectFetchObjects(repo, wants, haves, depth, clientShallow);
  // Deterministic pack order: commits (by oid), then trees, then blobs, then tags.
  const order: Record<ObjType, number> = { commit: 0, tree: 1, blob: 2, tag: 3 };
  const entries = [...objects.entries()]
    .sort((a, b) => order[a[1].type] - order[b[1].type] || (a[0] < b[0] ? -1 : 1))
    .map(([oid, obj]) => ({ type: obj.type, data: obj.data, oid }));
  const ack = haves.find((h) => repo.objects.has(h)) ?? null;
  return { pack: writePack(entries), shallow, unshallow, ack };
}
function handleUploadPack(req: RawReq, res: RawRes, owner: string, name: string, raw: Buffer): void {
  const repo = gitRepoPath(res, owner, name);
  if (!repo) return;
  const proto2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  let wants: string[] = [];
  let haves: string[] = [];
  let depth: number | null = null;
  let clientShallow: string[] = [];
  let command = '';
  try {
    const pkts = parsePktLines(raw);
    if (!proto2) {
      // v0 fetch: wants first, then flush, then haves + done.
      let section = 'wants';
      for (const p of pkts) {
        if (p.kind === 'flush') { section = 'haves'; continue; }
        if (p.kind !== 'data') continue;
        const line = p.payload.toString('utf8').trim();
        if (section === 'wants') {
          if (line.startsWith('want ')) wants.push(line.slice(5).split(' ')[0]);
          else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).split(' ')[0]);
          else if (line.startsWith('deepen ')) depth = parseInt(line.slice(7), 10);
        } else {
          if (line.startsWith('have ')) haves.push(line.slice(5).split(' ')[0]);
        }
      }
    } else {
      for (const p of pkts) {
        if (p.kind !== 'data') continue;
        const line = p.payload.toString('utf8');
        const text = line.trim();
        if (text.startsWith('command=')) { command = text.slice('command='.length); continue; }
        if (command === 'fetch') {
          if (text.startsWith('want ')) wants.push(text.slice(5));
          else if (text.startsWith('have ')) haves.push(text.slice(5));
          else if (text.startsWith('shallow ')) clientShallow.push(text.slice(8));
          else if (text.startsWith('deepen ')) depth = parseInt(text.slice(7), 10);
        } else if (command === 'ls-refs') {
          // handled below via lsRefsRequest
        }
      }
      if (command === 'ls-refs') {
        handleLsRefs(req, res, repo, raw);
        return;
      }
    }
  } catch {
    sendRaw(res, 400, Buffer.from('bad request\n'), 'text/plain');
    return;
  }
  if (proto2 && command !== '' && command !== 'fetch') {
    sendRaw(res, 400, Buffer.from('unknown command\n'), 'text/plain');
    return;
  }
  // The whole fetch response is a pure function of (protocol, wants, haves,
  // depth, shallow boundaries, object store). Cache it: the clone workload
  // asks for the same depth-1 fetch fifty times in a row on an unchanged repo.
  const fetchKey = `${proto2 ? 'v2' : 'v0'}|${wants.join(',')}|${haves.join(',')}|${depth}|${clientShallow.join(',')}|${repo.objects.size}`;
  const cachedFetch = repo.fetchCache.get(fetchKey);
  if (cachedFetch) {
    sendRaw(res, 200, cachedFetch, 'application/x-git-upload-pack-result');
    return;
  }
  const { pack, shallow, unshallow, ack } = buildFetchPack(repo, wants, haves, depth, clientShallow);
  const parts: Buffer[] = [];
  if (proto2) {
    // Real git (and the protocol) only expects an acknowledgments section
    // when the client sent 'have' lines; with no haves the response goes
    // straight to shallow-info / packfile.
    if (haves.length > 0) {
      parts.push(pktLine('acknowledgments\n'));
      if (ack) { parts.push(pktLine(`ACK ${ack}\n`)); parts.push(pktLine('ready\n')); }
      else parts.push(pktLine('NAK\n'));
      parts.push(PKT_DELIM);
    }
    if (shallow.length || unshallow.length) {
      parts.push(pktLine('shallow-info\n'));
      for (const s of shallow) parts.push(pktLine(`shallow ${s}\n`));
      for (const u of unshallow) parts.push(pktLine(`unshallow ${u}\n`));
      parts.push(PKT_DELIM);
    }
    parts.push(pktLine('packfile\n'));
    parts.push(...sidebandChunks(pack, 1));
    parts.push(PKT_FLUSH);
  } else {
    if (ack) parts.push(pktLine(`ACK ${ack}\n`));
    else parts.push(pktLine('NAK\n'));
    for (const s of shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const u of unshallow) parts.push(pktLine(`unshallow ${u}\n`));
    parts.push(...sidebandChunks(pack, 1));
    parts.push(PKT_FLUSH);
  }
  const fetchBody = Buffer.concat(parts);
  cachePut(repo.fetchCache, fetchKey, fetchBody);
  sendRaw(res, 200, fetchBody, 'application/x-git-upload-pack-result');
}
function handleLsRefs(_req: RawReq, res: RawRes, repo: Repo, raw: Buffer): void {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes: string[] = [];
  try {
    const pkts = parsePktLines(raw);
    for (const p of pkts) {
      if (p.kind !== 'data') continue;
      const text = p.payload.toString('utf8').trim();
      if (text === 'peel') peel = true;
      else if (text === 'symrefs') symrefs = true;
      else if (text === 'unborn') unborn = true;
      else if (text.startsWith('ref-prefix ')) prefixes.push(text.slice('ref-prefix '.length));
    }
  } catch {
    sendRaw(res, 400, Buffer.from('bad request\n'), 'text/plain');
    return;
  }
  // ls-refs depends only on the ref list and the requested flags: cache it
  // per ref state (a clone asks for the same list three times per round).
  const lsKey = `${peel ? 1 : 0}${symrefs ? 1 : 0}${unborn ? 1 : 0}|${prefixes.join(',')}|${refFingerprint(repo)}`;
  const cachedLs = repo.lsRefsCache.get(lsKey);
  if (cachedLs) {
    sendRaw(res, 200, cachedLs, 'application/x-git-upload-pack-result');
    return;
  }
  const lines: Buffer[] = [];
  const refs = [...repo.refs.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1);
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headOid = repo.refs.get(headRef);
  const noRefs = refs.length === 0;
  if (noRefs) {
    // Unborn HEAD: first token 'unborn', name HEAD (the client parses this).
    if (matches('HEAD')) {
      const attrs: string[] = [];
      if (symrefs) attrs.push(`symref-target:${headRef}`);
      lines.push(pktLine(`unborn HEAD${attrs.length ? ` ${attrs.join(' ')}` : ''}\n`));
    }
  } else {
    if (matches('HEAD')) {
      const attrs: string[] = [];
      if (symrefs && headOid) attrs.push(`symref-target:${headRef}`);
      if (headOid) lines.push(pktLine(`${headOid} HEAD${attrs.length ? ` ${attrs.join(' ')}` : ''}\n`));
    }
    for (const [name, oid] of refs) {
      if (!matches(name)) continue;
      let line = `${oid} ${name}`;
      if (peel) {
        const obj = repo.objects.get(oid);
        if (obj?.type === 'tag') {
          const peeled = peelToCommit(repo, oid);
          if (peeled) line += ` peeled:${peeled}`;
        }
      }
      lines.push(pktLine(`${line}\n`));
    }
  }
  lines.push(PKT_FLUSH);
  const lsBody = Buffer.concat(lines);
  cachePut(repo.lsRefsCache, lsKey, lsBody);
  sendRaw(res, 200, lsBody, 'application/x-git-upload-pack-result');
}
function handleReceivePack(req: RawReq, res: RawRes, owner: string, name: string, raw: Buffer): void {
  const repo = gitRepoPath(res, owner, name);
  if (!repo) return;
  const report: Array<{ ref: string; ok: boolean; reason: string }> = [];
  try {
    // Body layout: pkt-lined command lines, one flush packet, then the pack
    // sent RAW (not pkt-lined). Split at the first flush packet.
    const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
    let off = 0;
    let packStart = -1;
    while (off + 4 <= raw.length) {
      const len = parseInt(raw.subarray(off, off + 4).toString('ascii'), 16);
      if (Number.isNaN(len)) throw new Error('bad pkt-line length');
      if (len === 0) { packStart = off + 4; break; }
      if (len === 1) { off += 4; continue; }
      if (len < 4 || off + len > raw.length) throw new Error('truncated pkt-line');
      let text = raw.subarray(off + 4, off + len).toString('utf8');
      const nul = text.indexOf('\0');
      if (nul >= 0) text = text.slice(0, nul);
      const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)\s*$/.exec(text.trim());
      if (m) commands.push({ oldOid: m[1], newOid: m[2], ref: m[3] });
      off += len;
    }
    if (packStart < 0) packStart = raw.length;
    const pack = raw.subarray(packStart);
    if (pack.length > 0) {
      const entries = readPack(pack, (oid) => repo.objects.get(oid));
      for (const e of entries) storeObject(repo, e.type, e.data);
    }
    for (const cmd of commands) {
      const current = repo.refs.get(cmd.ref);
      if (cmd.newOid === ZERO_OID) {
        // Delete.
        if (current && cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) {
          report.push({ ref: cmd.ref, ok: false, reason: 'old oid does not match' });
          continue;
        }
        repo.refs.delete(cmd.ref);
        report.push({ ref: cmd.ref, ok: true, reason: '' });
        continue;
      }
      const target = repo.objects.get(cmd.newOid);
      if (!target) {
        report.push({ ref: cmd.ref, ok: false, reason: 'object not found' });
        continue;
      }
      if (!current) {
        if (cmd.oldOid !== ZERO_OID) {
          report.push({ ref: cmd.ref, ok: false, reason: 'old oid does not match' });
          continue;
        }
        repo.refs.set(cmd.ref, cmd.newOid);
        report.push({ ref: cmd.ref, ok: true, reason: '' });
        continue;
      }
      if (cmd.oldOid !== current) {
        report.push({ ref: cmd.ref, ok: false, reason: 'old oid does not match' });
        continue;
      }
      if (cmd.ref.startsWith('refs/tags/')) {
        repo.refs.set(cmd.ref, cmd.newOid);
        report.push({ ref: cmd.ref, ok: true, reason: '' });
        continue;
      }
      const newCommit = peelToCommit(repo, cmd.newOid);
      const curCommit = peelToCommit(repo, current);
      if (newCommit && curCommit && isAncestor(repo, curCommit, newCommit)) {
        repo.refs.set(cmd.ref, cmd.newOid);
        report.push({ ref: cmd.ref, ok: true, reason: '' });
      } else {
        report.push({ ref: cmd.ref, ok: false, reason: 'non-fast-forward' });
      }
    }
  } catch (err) {
    // A malformed push still answers with a report (the server stays healthy).
    const msg = err instanceof Error ? err.message : String(err);
    // The report stream itself ends with a flush packet inside band 1 (as
    // real git sends it); the outer flush below ends the sideband stream.
    const inner = Buffer.concat([pktLine('unpack failed\n'), pktLine(`ng refs/heads/main ${msg}\n`), PKT_FLUSH]);
    sendRaw(res, 200, Buffer.concat([...sidebandChunks(inner, 1), PKT_FLUSH]), 'application/x-git-receive-pack-result');
    return;
  }
  const innerParts: Buffer[] = [pktLine('unpack ok\n')];
  for (const r of report) innerParts.push(pktLine(r.ok ? `ok ${r.ref}\n` : `ng ${r.ref} ${r.reason}\n`));
  innerParts.push(PKT_FLUSH);
  const inner = Buffer.concat(innerParts);
  sendRaw(res, 200, Buffer.concat([...sidebandChunks(inner, 1), PKT_FLUSH]), 'application/x-git-receive-pack-result');
}

// ---------------------------------------------------------------- GraphQL
// A small parser/executor for the documents the suite sends (queries and
// mutations over viewer/repository/node/__type, plus batch bodies).
type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Record<string, GqlValue> };
interface GqlField {
  alias: string | null; name: string; args: Record<string, GqlValue>; selection: GqlField[] | null;
}
interface GqlOperation { type: 'query' | 'mutation'; name: string | null; fields: GqlField[]; }
function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s|,/.test(c)) { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (src.startsWith('...', i)) { tokens.push('...'); i += 3; continue; }
    if ('{}()[]:!=$@'.includes(c)) { tokens.push(c); i += 1; continue; }
    if (c === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { out += src[j + 1]; j += 2; continue; }
        out += src[j];
        j += 1;
      }
      tokens.push(JSON.stringify(out));
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c) && /[0-9]/.test(src[i] === '-' ? src[i + 1] ?? '' : c)) {
      let j = i;
      while (j < src.length && /[0-9.]/.test(src[j])) j += 1;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    i += 1; // unknown char: skip
  }
  return tokens;
}
class GqlParser {
  private pos = 0;
  private tokens: string[];
  constructor(tokens: string[]) { this.tokens = tokens; }
  peek(): string | undefined { return this.tokens[this.pos]; }
  next(): string { return this.tokens[this.pos++] ?? ''; }
  expect(t: string): void { if (this.next() !== t) throw new Error(`expected ${t}`); }
  parseDocument(): { operations: GqlOperation[]; fragments: Record<string, GqlField[]> } {
    const operations: GqlOperation[] = [];
    const fragments: Record<string, GqlField[]> = {};
    while (this.pos < this.tokens.length) {
      const t = this.next();
      if (t === 'fragment') {
        const name = this.next();
        this.expect('on');
        this.next(); // type name
        fragments[name] = this.parseSelectionSet();
      } else if (t === 'query' || t === 'mutation') {
        let name: string | null = null;
        if (this.peek() && this.peek() !== '(' && this.peek() !== '{') name = this.next();
        if (this.peek() === '(') this.skipParens();
        this.skipDirectives();
        operations.push({ type: t as 'query' | 'mutation', name, fields: this.parseSelectionSet() });
      } else if (t === '{') {
        this.pos -= 1;
        operations.push({ type: 'query', name: null, fields: this.parseSelectionSet() });
      } else {
        throw new Error(`unexpected token ${t}`);
      }
    }
    return { operations, fragments };
  }
  private skipParens(): void {
    let depth = 0;
    while (this.pos < this.tokens.length) {
      const t = this.next();
      if (t === '(') depth += 1;
      else if (t === ')') { depth -= 1; if (depth === 0) return; }
    }
  }
  private skipDirectives(): void {
    while (this.peek() === '@') {
      this.next();
      this.next();
      if (this.peek() === '(') this.skipParens();
    }
  }
  parseSelectionSet(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === undefined) throw new Error('unterminated selection set');
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          this.next(); // type name
          this.skipDirectives();
          const sub = this.parseSelectionSet();
          fields.push({ alias: null, name: '__fragment', args: {}, selection: sub });
        } else {
          const fragName = this.next();
          this.skipDirectives();
          fields.push({ alias: null, name: '__spread', args: { __name: { kind: 'string', value: fragName } }, selection: null });
        }
        continue;
      }
      const first = this.next();
      let alias: string | null = null;
      let name = first;
      if (this.peek() === ':') { this.next(); alias = first; name = this.next(); }
      const args: Record<string, GqlValue> = {};
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')') {
          const argName = this.next();
          this.expect(':');
          args[argName] = this.parseValue();
        }
        this.next();
      }
      this.skipDirectives();
      const selection = this.peek() === '{' ? this.parseSelectionSet() : null;
      fields.push({ alias, name, args, selection });
    }
    this.expect('}');
    return fields;
  }
  private parseValue(): GqlValue {
    const t = this.next();
    if (t === '$') return { kind: 'var', name: this.next() };
    if (t === '[') {
      const items: GqlValue[] = [];
      while (this.peek() !== ']') items.push(this.parseValue());
      this.next();
      return { kind: 'list', items };
    }
    if (t === '{') {
      const fields: Record<string, GqlValue> = {};
      while (this.peek() !== '}') {
        const k = this.next();
        this.expect(':');
        fields[k] = this.parseValue();
      }
      this.next();
      return { kind: 'object', fields };
    }
    if (t.startsWith('"')) return { kind: 'string', value: JSON.parse(t) as string };
    if (/^-?\d+$/.test(t)) return { kind: 'int', value: parseInt(t, 10) };
    if (/^-?\d*\.\d+$/.test(t)) return { kind: 'float', value: parseFloat(t) };
    if (t === 'true') return { kind: 'bool', value: true };
    if (t === 'false') return { kind: 'bool', value: false };
    if (t === 'null') return { kind: 'null' };
    return { kind: 'enum', value: t };
  }
}
function gqlResolveValue(v: GqlValue, variables: Record<string, unknown>): unknown {
  switch (v.kind) {
    case 'var': return variables[v.name];
    case 'string': case 'int': case 'float': case 'bool': return v.value;
    case 'null': return null;
    case 'enum': return v.value;
    case 'list': return v.items.map((x) => gqlResolveValue(x, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [k, x] of Object.entries(v.fields)) out[k] = gqlResolveValue(x, variables);
      return out;
    }
  }
}
const GQL_TYPE_FIELDS: Record<string, string[]> = {
  Issue: ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt'],
  PullRequest: ['id', 'number', 'title', 'body', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest'],
  Viewer: ['login', 'id', 'name'],
  SearchType: [],
};
const GQL_TYPE_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'PULL_REQUEST', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT', 'CODE', 'MILESTONE', 'WIKI', 'PROJECT', 'TEAM'],
};
interface GqlCtx { errors: Array<{ message: string }>; fragments: Record<string, GqlField[]>; variables: Record<string, unknown>; }
function gqlEncodeCursor(n: number): string { return Buffer.from(`cursor:${n}`, 'utf8').toString('base64'); }
function gqlDecodeCursor(c: string): number | null {
  try {
    const m = /^cursor:(\d+)$/.exec(Buffer.from(c, 'base64').toString('utf8'));
    return m ? parseInt(m[1], 10) : null;
  } catch { return null; }
}
function resolveFields(obj: unknown, typeName: string, fields: GqlField[], ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    if (f.name === '__fragment') {
      Object.assign(out, resolveFields(obj, typeName, f.selection ?? [], ctx));
      continue;
    }
    if (f.name === '__spread') {
      const frag = ctx.fragments[(f.args.__name as { kind: 'string' }).value];
      if (frag) Object.assign(out, resolveFields(obj, typeName, frag, ctx));
      continue;
    }
    const key = f.alias ?? f.name;
    if (f.name === '__typename') { out[key] = typeName; continue; }
    const value = resolveField(obj, typeName, f, ctx);
    out[key] = value === undefined ? null : value;
  }
  return out;
}
function argOf(f: GqlField, name: string, ctx: GqlCtx): unknown {
  const v = f.args[name];
  return v === undefined ? undefined : gqlResolveValue(v, ctx.variables);
}
function resolveField(obj: unknown, typeName: string, f: GqlField, ctx: GqlCtx): unknown {
  const sel = f.selection ?? [];
  // Types whose fields are structural (payloads, edges, page info, introspection).
  if (typeName === 'CreateIssuePayload' || typeName === 'CloseIssuePayload') {
    if (f.name === 'issue') return resolveFields((obj as { issue: { repo: Repo; issue: Issue } }).issue, 'Issue', sel, ctx);
    if (f.name === 'clientMutationId') return null;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'CreatePullRequestPayload' || typeName === 'MergePullRequestPayload') {
    if (f.name === 'pullRequest') return resolveFields((obj as { pull: { repo: Repo; pull: Pull } }).pull, 'PullRequest', sel, ctx);
    if (f.name === 'clientMutationId') return null;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'AddCommentPayload') {
    if (f.name === 'commentEdge') {
      const comment = (obj as { comment: Comment }).comment;
      const out: Record<string, unknown> = {};
      for (const sf of sel) {
        if (sf.name === 'node') out[sf.alias ?? 'node'] = resolveFields({ id: globalId('comment', String(comment.id)), body: comment.body }, 'IssueComment', sf.selection ?? [], ctx);
        else if (sf.name === 'cursor') out[sf.alias ?? 'cursor'] = gqlEncodeCursor(comment.id);
      }
      return out;
    }
    if (f.name === 'clientMutationId') return null;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'IssueComment') {
    const c = obj as { id: string; body: string };
    if (f.name === 'id') return c.id;
    if (f.name === 'body') return c.body;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'IssueEdge' || typeName === 'PullRequestEdge') {
    const item = obj as { repo: Repo; issue?: Issue; pull?: Pull };
    if (f.name === 'node') {
      return item.issue ? resolveFields({ repo: item.repo, issue: item.issue }, 'Issue', sel, ctx)
        : resolveFields({ repo: item.repo, pull: item.pull }, 'PullRequest', sel, ctx);
    }
    if (f.name === 'cursor') return gqlEncodeCursor((item.issue ?? item.pull)!.number);
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'PageInfo') {
    const p = obj as { hasNextPage: boolean; endCursor: string | null; startCursor: string | null; hasPreviousPage: boolean };
    if (f.name === 'hasNextPage') return p.hasNextPage;
    if (f.name === 'endCursor') return p.endCursor;
    if (f.name === 'startCursor') return p.startCursor;
    if (f.name === 'hasPreviousPage') return p.hasPreviousPage;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'RepositoryOwner') {
    if (f.name === 'login') return (obj as { login: string }).login;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'BranchRef') {
    if (f.name === 'name') return (obj as { name: string }).name;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'PullRequestFile') {
    if (f.name === 'path') return (obj as { path: string }).path;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === '__Type') {
    const t = obj as { name: string };
    if (f.name === 'name') return t.name;
    if (f.name === 'kind') return GQL_TYPE_ENUMS[t.name] ? 'ENUM' : 'OBJECT';
    if (f.name === 'fields') {
      const names = GQL_TYPE_FIELDS[t.name];
      if (!names) return null;
      return names.map((n) => resolveFields({ name: n }, '__Field', sel, ctx));
    }
    if (f.name === 'enumValues') {
      const vals = GQL_TYPE_ENUMS[t.name];
      if (!vals) return null;
      return vals.map((n) => resolveFields({ name: n }, '__EnumValue', sel, ctx));
    }
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === '__Field' || typeName === '__EnumValue') {
    if (f.name === 'name') return (obj as { name: string }).name;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  const known = (typeName === 'Query' || typeName === 'Mutation')
    ? ['viewer', 'repository', 'node', '__type', 'createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment']
    : (GQL_TYPE_FIELDS[typeName] ?? []);
  const extra = typeName === 'Repository' ? ['url'] : typeName === 'Issue' ? ['url', 'createdAt'] : typeName === 'PullRequest' ? ['url', 'createdAt'] : [];
  if (!known.includes(f.name) && !extra.includes(f.name) && f.name !== '__typename') {
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "${typeName}".` });
    return null;
  }
  if (typeName === 'Query') return resolveQuery(obj, f, ctx, sel);
  if (typeName === 'Mutation') return resolveMutation(obj, f, ctx, sel);
  if (typeName === 'Viewer') {
    if (f.name === 'login') return viewerLogin;
    if (f.name === 'id') return 1000;
    if (f.name === 'name') return viewerLogin;
    return null;
  }
  if (typeName === 'Repository') {
    const repo = obj as Repo;
    switch (f.name) {
      case 'id': return globalId('repo', repoFullName(repo));
      case 'databaseId': return repo.databaseId;
      case 'name': return repo.name;
      case 'nameWithOwner': return repoFullName(repo);
      case 'owner': return resolveFields({ login: ownerOf(repo) }, 'RepositoryOwner', sel, ctx);
      case 'defaultBranchRef': {
        const oid = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        return oid ? resolveFields({ name: repo.defaultBranch }, 'BranchRef', sel, ctx) : null;
      }
      case 'viewerPermission': return 'ADMIN';
      case 'hasIssuesEnabled': return true;
      case 'url': return `https://example.invalid/${repoFullName(repo)}`;
      case 'issue': {
        const issue = repo.issues.get(Number(argOf(f, 'number', ctx) ?? -1));
        return issue ? resolveFields({ repo, issue }, 'Issue', sel, ctx) : null;
      }
      case 'issues': {
        let list = [...repo.issues.values()];
        const states = argOf(f, 'states', ctx) as string[] | undefined;
        if (states) {
          const want = new Set(states.map((s) => s.toLowerCase()));
          list = list.filter((i) => want.has(i.state));
        }
        const orderBy = argOf(f, 'orderBy', ctx) as { field?: string; direction?: string } | undefined;
        const desc = (orderBy?.direction ?? 'DESC').toUpperCase() === 'DESC';
        list.sort((a, b) => desc ? b.number - a.number : a.number - b.number);
        return issueConnection(repo, list, f, ctx, sel);
      }
      case 'pullRequests': {
        const list = [...repo.pulls.values()].sort((a, b) => a.number - b.number);
        return pullConnection(repo, list, f, ctx, sel);
      }
      case 'pullRequest': {
        const pull = repo.pulls.get(Number(argOf(f, 'number', ctx) ?? -1));
        return pull ? resolveFields({ repo, pull }, 'PullRequest', sel, ctx) : null;
      }
    }
    return null;
  }
  if (typeName === 'Issue') {
    const { repo, issue } = obj as { repo: Repo; issue: Issue };
    switch (f.name) {
      case 'id': return globalId('issue', `${repo.databaseId}:${issue.number}`);
      case 'number': return issue.number;
      case 'title': return issue.title;
      case 'state': return issue.state.toUpperCase();
      case 'body': return issue.body;
      case 'url': return `https://example.invalid/${repoFullName(repo)}/issues/${issue.number}`;
      case 'createdAt': return FIXED_TS;
    }
    return null;
  }
  if (typeName === 'PullRequest') {
    const { repo, pull } = obj as { repo: Repo; pull: Pull };
    switch (f.name) {
      case 'id': return globalId('pr', `${repo.databaseId}:${pull.number}`);
      case 'number': return pull.number;
      case 'title': return pull.title;
      case 'body': return pull.body;
      case 'state': return pull.merged ? 'MERGED' : pull.state.toUpperCase();
      case 'merged': return pull.merged;
      case 'headRefName': return pull.headRef;
      case 'baseRefName': return pull.baseRef;
      case 'mergeable': return mergeableState(repo, pull);
      case 'url': return `https://example.invalid/${repoFullName(repo)}/pull/${pull.number}`;
      case 'createdAt': return FIXED_TS;
      case 'files': {
        const headTip = peelToCommit(repo, pull.headSha);
        const baseTip = peelToCommit(repo, pull.baseSha);
        const paths: string[] = [];
        if (headTip && baseTip) {
          const hc = repo.objects.get(headTip);
          const bc = repo.objects.get(baseTip);
          if (hc && bc) paths.push(...diffTrees(repo, parseCommit(bc.data).tree, parseCommit(hc.data).tree).map((d) => d.path));
        }
        const first = Number(argOf(f, 'first', ctx) ?? paths.length);
        const nodesField = sel.find((sf) => sf.name === 'nodes');
        const edgesField = sel.find((sf) => sf.name === 'edges');
        const nodes = paths.slice(0, first).map((p) => resolveFields({ path: p }, 'PullRequestFile', nodesField?.selection ?? edgesField?.selection ?? [], ctx));
        const out: Record<string, unknown> = {};
        for (const sf of sel) {
          if (sf.name === 'nodes') out[sf.alias ?? 'nodes'] = nodes;
          else if (sf.name === 'edges') out[sf.alias ?? 'edges'] = nodes.map((n) => ({ node: n, cursor: null }));
          else if (sf.name === 'totalCount') out[sf.alias ?? 'totalCount'] = paths.length;
        }
        return out;
      }
    }
    return null;
  }
  return null;
}
function issueConnection(repo: Repo, list: Issue[], f: GqlField, ctx: GqlCtx, sel: GqlField[]): Record<string, unknown> {
  const first = Number(argOf(f, 'first', ctx) ?? list.length);
  const after = argOf(f, 'after', ctx) as string | undefined;
  const cursorNum = after ? gqlDecodeCursor(after) : null;
  let filtered = list;
  if (cursorNum !== null) {
    const orderBy = argOf(f, 'orderBy', ctx) as { direction?: string } | undefined;
    const desc = (orderBy?.direction ?? 'DESC').toUpperCase() === 'DESC';
    filtered = list.filter((i) => desc ? i.number < cursorNum : i.number > cursorNum);
  }
  const page = filtered.slice(0, first);
  const out: Record<string, unknown> = {};
  for (const sf of sel) {
    const key = sf.alias ?? sf.name;
    if (sf.name === 'nodes') out[key] = page.map((i) => resolveFields({ repo, issue: i }, 'Issue', sf.selection ?? [], ctx));
    else if (sf.name === 'edges') out[key] = page.map((i) => resolveFields({ repo, issue: i }, 'IssueEdge', sf.selection ?? [], ctx));
    else if (sf.name === 'totalCount') out[key] = list.length;
    else if (sf.name === 'pageInfo') {
      out[key] = resolveFields({
        hasNextPage: filtered.length > page.length,
        endCursor: page.length ? gqlEncodeCursor(page[page.length - 1].number) : null,
        startCursor: page.length ? gqlEncodeCursor(page[0].number) : null,
        hasPreviousPage: false,
      }, 'PageInfo', sf.selection ?? [], ctx);
    }
  }
  return out;
}
function pullConnection(repo: Repo, list: Pull[], f: GqlField, ctx: GqlCtx, sel: GqlField[]): Record<string, unknown> {
  const first = Number(argOf(f, 'first', ctx) ?? list.length);
  const after = argOf(f, 'after', ctx) as string | undefined;
  const cursorNum = after ? gqlDecodeCursor(after) : null;
  const filtered = cursorNum === null ? list : list.filter((p) => p.number > cursorNum);
  const page = filtered.slice(0, first);
  const out: Record<string, unknown> = {};
  for (const sf of sel) {
    const key = sf.alias ?? sf.name;
    if (sf.name === 'nodes') out[key] = page.map((p) => resolveFields({ repo, pull: p }, 'PullRequest', sf.selection ?? [], ctx));
    else if (sf.name === 'edges') out[key] = page.map((p) => resolveFields({ repo, pull: p }, 'PullRequestEdge', sf.selection ?? [], ctx));
    else if (sf.name === 'totalCount') out[key] = list.length;
    else if (sf.name === 'pageInfo') {
      out[key] = resolveFields({
        hasNextPage: filtered.length > page.length,
        endCursor: page.length ? gqlEncodeCursor(page[page.length - 1].number) : null,
        startCursor: page.length ? gqlEncodeCursor(page[0].number) : null,
        hasPreviousPage: false,
      }, 'PageInfo', sf.selection ?? [], ctx);
    }
  }
  return out;
}
function resolveQuery(_obj: unknown, f: GqlField, ctx: GqlCtx, sel: GqlField[]): unknown {
  if (f.name === 'viewer') {
    if (!viewerLogin) { ctx.errors.push({ message: 'viewer is unknown' }); return null; }
    return resolveFields({}, 'Viewer', sel, ctx);
  }
  if (f.name === 'repository') {
    const owner = String(argOf(f, 'owner', ctx) ?? '');
    const name = String(argOf(f, 'name', ctx) ?? '');
    learnOwner(owner);
    const repo = findRepo(owner, name);
    if (!repo) return null;
    return resolveFields(repo, 'Repository', sel, ctx);
  }
  if (f.name === 'node') {
    const id = String(argOf(f, 'id', ctx) ?? '');
    const decoded = decodeGlobalId(id);
    if (!decoded) return null;
    if (decoded.kind === 'repo') {
      const [owner, name] = decoded.key.split('/');
      const repo = findRepo(owner, name);
      return repo ? resolveFields(repo, 'Repository', sel, ctx) : null;
    }
    if (decoded.kind === 'issue') {
      const [db, num] = decoded.key.split(':');
      for (const list of reposByName.values()) for (const r of list) {
        if (String(r.databaseId) === db) {
          const issue = r.issues.get(Number(num));
          return issue ? resolveFields({ repo: r, issue }, 'Issue', sel, ctx) : null;
        }
      }
      return null;
    }
    if (decoded.kind === 'pr') {
      const [db, num] = decoded.key.split(':');
      for (const list of reposByName.values()) for (const r of list) {
        if (String(r.databaseId) === db) {
          const pull = r.pulls.get(Number(num));
          return pull ? resolveFields({ repo: r, pull }, 'PullRequest', sel, ctx) : null;
        }
      }
      return null;
    }
    return null;
  }
  if (f.name === '__type') {
    const name = String(argOf(f, 'name', ctx) ?? '');
    if (!(name in GQL_TYPE_FIELDS) && !(name in GQL_TYPE_ENUMS)) return null;
    return resolveFields({ name }, '__Type', sel, ctx);
  }
  return null;
}
function createIssueInRepo(repo: Repo, title: string, body: string): Issue {
  const issue: Issue = {
    number: repo.nextNumber, id: idSeq += 1, title, body,
    state: 'open', labels: [], seq: repo.nextNumber, jsonBuf: null,
  };
  repo.nextNumber += 1;
  repo.issues.set(issue.number, issue);
  return issue;
}
function resolveMutation(_obj: unknown, f: GqlField, ctx: GqlCtx, sel: GqlField[]): unknown {
  const input = (argOf(f, 'input', ctx) ?? {}) as Record<string, unknown>;
  if (f.name === 'createIssue') {
    const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = decoded?.kind === 'repo' ? findRepo(...decoded.key.split('/') as [string, string]) : undefined;
    if (!repo) { ctx.errors.push({ message: 'repository not found' }); return null; }
    const issue = createIssueInRepo(repo, String(input.title ?? ''), String(input.body ?? ''));
    return resolveFields({ issue: { repo, issue } }, 'CreateIssuePayload', sel, ctx);
  }
  if (f.name === 'closeIssue') {
    const decoded = decodeGlobalId(String(input.issueId ?? ''));
    if (decoded?.kind === 'issue') {
      const [db, num] = decoded.key.split(':');
      for (const list of reposByName.values()) for (const r of list) {
        if (String(r.databaseId) === db) {
          const issue = r.issues.get(Number(num));
          if (issue) {
            issue.state = 'closed';
            issue.jsonBuf = null;
            return resolveFields({ issue: { repo: r, issue } }, 'CloseIssuePayload', sel, ctx);
          }
        }
      }
    }
    ctx.errors.push({ message: 'issue not found' });
    return null;
  }
  if (f.name === 'createPullRequest') {
    const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = decoded?.kind === 'repo' ? findRepo(...decoded.key.split('/') as [string, string]) : undefined;
    if (!repo) { ctx.errors.push({ message: 'repository not found' }); return null; }
    const headRef = String(input.headRefName ?? '');
    const baseRef = String(input.baseRefName ?? repo.defaultBranch);
    const headOid = repo.refs.get(`refs/heads/${headRef}`);
    const baseOid = repo.refs.get(`refs/heads/${baseRef}`);
    if (!headOid || !baseOid) { ctx.errors.push({ message: 'head or base branch does not exist' }); return null; }
    const dup = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === headRef);
    if (dup) return resolveFields({ pull: { repo, pull: dup } }, 'CreatePullRequestPayload', sel, ctx);
    const pull: Pull = {
      number: repo.nextNumber, id: idSeq += 1, title: String(input.title ?? ''),
      body: '', state: 'open', headRef, baseRef, headSha: headOid, baseSha: baseOid,
      merged: false, mergedAt: null, mergeCommitSha: null, seq: repo.nextNumber,
    };
    repo.nextNumber += 1;
    repo.pulls.set(pull.number, pull);
    return resolveFields({ pull: { repo, pull } }, 'CreatePullRequestPayload', sel, ctx);
  }
  if (f.name === 'mergePullRequest') {
    const decoded = decodeGlobalId(String(input.pullRequestId ?? ''));
    if (decoded?.kind === 'pr') {
      const [db, num] = decoded.key.split(':');
      for (const list of reposByName.values()) for (const r of list) {
        if (String(r.databaseId) === db) {
          const pull = r.pulls.get(Number(num));
          if (pull && pull.state === 'open' && mergeableState(r, pull) !== 'CONFLICTING') {
            // Reuse the REST merge logic via a direct call.
            const merged = doSquashMerge(r, pull);
            if (merged) return resolveFields({ pull: { repo: r, pull } }, 'MergePullRequestPayload', sel, ctx);
          }
        }
      }
    }
    ctx.errors.push({ message: 'pull request not found or not mergeable' });
    return null;
  }
  if (f.name === 'addComment') {
    const decoded = decodeGlobalId(String(input.subjectId ?? ''));
    if (decoded?.kind === 'issue') {
      const [db, num] = decoded.key.split(':');
      for (const list of reposByName.values()) for (const r of list) {
        if (String(r.databaseId) === db) {
          const issue = r.issues.get(Number(num));
          if (issue) {
            const comment: Comment = { id: idSeq += 1, body: String(input.body ?? '') };
            const arr = r.comments.get(issue.number) ?? [];
            arr.push(comment);
            r.comments.set(issue.number, arr);
            return resolveFields({ comment }, 'AddCommentPayload', sel, ctx);
          }
        }
      }
    }
    ctx.errors.push({ message: 'subject not found' });
    return null;
  }
  return null;
}
function doSquashMerge(repo: Repo, pull: Pull): boolean {
  const headTip = peelToCommit(repo, pull.headSha);
  const baseTip = peelToCommit(repo, repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '');
  if (!headTip || !baseTip) return false;
  const base = mergeBase(repo, headTip, baseTip);
  const headCommit = repo.objects.get(headTip)!;
  const baseCommit = repo.objects.get(baseTip)!;
  const baseTree = parseCommit(baseCommit.data).tree;
  let newTree = baseTree;
  if (base) {
    const baseBaseCommit = repo.objects.get(base)!;
    const changes = diffTrees(repo, parseCommit(baseBaseCommit.data).tree, parseCommit(headCommit.data).tree);
    const flat = flattenTree(repo, baseTree);
    for (const c of changes) {
      if (c.newOid === null) flat.delete(c.path);
      else flat.set(c.path, { oid: c.newOid, mode: '100644' });
    }
    newTree = buildTreeFromFlat(repo, flat);
  } else {
    newTree = parseCommit(headCommit.data).tree;
  }
  const mergeSha = makeCommit(repo, newTree, [baseTip], `Merge pull request #${pull.number} from ${pull.headRef}`);
  repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = FIXED_TS;
  pull.mergeCommitSha = mergeSha;
  return true;
}
function handleGraphQL(req: RawReq, res: RawRes, raw: Buffer): void {
  let parsed: unknown;
  try { parsed = JSON.parse(raw.toString('utf8')); }
  catch { sendJson(res, 400, { errors: [{ message: 'request body is not valid JSON' }] }); return; }
  const docs = Array.isArray(parsed) ? parsed : [parsed];
  const results = docs.map((doc) => {
    if (!doc || typeof doc !== 'object') return { data: null, errors: [{ message: 'invalid document' }] };
    const query = (doc as { query?: unknown }).query;
    const variables = ((doc as { variables?: unknown }).variables ?? {}) as Record<string, unknown>;
    if (typeof query !== 'string') return { data: null, errors: [{ message: 'query is required' }] };
    try {
      const parser = new GqlParser(gqlTokenize(query));
      const { operations, fragments } = parser.parseDocument();
      const ctx: GqlCtx = { errors: [], fragments, variables };
      const data: Record<string, unknown> = {};
      for (const op of operations) {
        Object.assign(data, resolveFields({}, op.type === 'mutation' ? 'Mutation' : 'Query', op.fields, ctx));
      }
      const out: Record<string, unknown> = { data };
      if (ctx.errors.length) out.errors = ctx.errors;
      return out;
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
    }
  });
  sendJson(res, 200, Array.isArray(parsed) ? results : results[0]);
}

// ---------------------------------------------------------------- MCP
const MCP_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
const MCP_TOOLS: Array<Record<string, unknown>> = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name.' },
        owner: { type: 'string', description: 'Owner login (defaults to the authenticated user).' },
        description: { type: 'string', description: 'Repository description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
      additionalProperties: false,
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
      },
      required: ['owner', 'repo'],
      additionalProperties: false,
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Issue title.' },
        body: { type: 'string', description: 'Issue body.' },
      },
      required: ['owner', 'repo', 'title'],
      additionalProperties: false,
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        state: { type: 'string', description: 'Issue state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
      additionalProperties: false,
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Pull request title.' },
        body: { type: 'string', description: 'Pull request body.' },
        head: { type: 'string', description: 'Head branch name.' },
        base: { type: 'string', description: 'Base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
      additionalProperties: false,
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request (squash) and close it.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        pull_number: { type: 'integer', description: 'Pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
      additionalProperties: false,
    },
  },
];
function mcpResult(res: RawRes, id: unknown, result: unknown): void {
  sendJson(res, 200, { jsonrpc: '2.0', id: id ?? null, result });
}
function mcpError(res: RawRes, id: unknown, code: number, message: string, status = 200): void {
  sendJson(res, status, { jsonrpc: '2.0', id: id ?? null, error: { code, message } });
}
function mcpToolResult(res: RawRes, id: unknown, obj: unknown, isError = false): void {
  const text = JSON.stringify(obj);
  mcpResult(res, id, {
    content: [{ type: 'text', text }],
    structuredContent: obj,
    isError,
  });
}
// Map the suite's argument synonyms onto canonical property names.
const MCP_ARG_ALIASES: Record<string, string[]> = {
  owner: ['owner', 'org', 'login', 'user'],
  repo: ['repo', 'repository', 'name'],
  title: ['title', 'subject'],
  body: ['body', 'description'],
  head: ['head', 'source', 'from', 'branch'],
  base: ['base', 'target', 'into'],
  pull_number: ['pull_number', 'number', 'pull_request_number'],
  name: ['name', 'repo', 'repository'],
};
function mcpMapArgs(tool: Record<string, unknown>, args: Record<string, unknown>): Record<string, unknown> {
  const schema = tool.inputSchema as { properties?: Record<string, unknown> };
  const props = schema.properties ?? {};
  const out: Record<string, unknown> = { ...args };
  // Also honour a full_name "owner/repo" property.
  if (typeof args.full_name === 'string') {
    const [o, r] = (args.full_name as string).split('/');
    if (o && r) { out.owner ??= o; out.repo ??= r; }
  }
  for (const [canonical, synonyms] of Object.entries(MCP_ARG_ALIASES)) {
    if (out[canonical] !== undefined) continue;
    for (const syn of synonyms) {
      if (args[syn] !== undefined && props[canonical] !== undefined) { out[canonical] = args[syn]; break; }
    }
  }
  // If the tool's schema uses a synonym as its own property name, copy it back.
  for (const prop of Object.keys(props)) {
    if (out[prop] === undefined) {
      for (const [canonical, synonyms] of Object.entries(MCP_ARG_ALIASES)) {
        if (synonyms.includes(prop) && out[canonical] !== undefined) { out[prop] = out[canonical]; break; }
      }
    }
  }
  return out;
}
function handleMcp(req: RawReq, res: RawRes, raw: Buffer): void {
  let parsed: unknown;
  try { parsed = JSON.parse(raw.toString('utf8')); }
  catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    mcpError(res, null, -32600, 'Invalid Request', 400);
    return;
  }
  const rpc = parsed as { jsonrpc?: unknown; id?: unknown; method?: unknown; params?: unknown };
  const id = rpc.id ?? null;
  const method = typeof rpc.method === 'string' ? rpc.method : '';
  const params = (rpc.params ?? {}) as Record<string, unknown>;
  if (method.startsWith('notifications/')) {
    res.writeHead(202);
    res.end();
    return;
  }
  if (method === 'server/discover') {
    mcpResult(res, id, {
      resultType: 'discover',
      supportedVersions: MCP_VERSIONS,
      serverInfo: { name: 'github-forge', version: '1.0.0' },
      capabilities: { tools: {} },
      instructions: 'A GitHub-compatible git forge: repositories, issues, pull requests, git smart HTTP, GraphQL and MCP tools.',
    });
    return;
  }
  if (method === 'initialize') {
    const offered = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
    const version = MCP_VERSIONS.includes(offered) ? offered : '2026-07-28';
    mcpResult(res, id, {
      protocolVersion: version,
      serverInfo: { name: 'github-forge', version: '1.0.0' },
      capabilities: { tools: {} },
    });
    return;
  }
  if (method === 'ping') { mcpResult(res, id, {}); return; }
  if (method === 'tools/list') {
    mcpResult(res, id, { tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const name = typeof params.name === 'string' ? params.name : '';
    const rawArgs = (params.arguments ?? {}) as Record<string, unknown>;
    const tool = MCP_TOOLS.find((t) => t.name === name);
    if (!tool) { mcpError(res, id, -32601, `Method not found: ${name}`); return; }
    const args = mcpMapArgs(tool, rawArgs);
    const schema = tool.inputSchema as { required?: string[] };
    const missing = (schema.required ?? []).filter((r) => args[r] === undefined || args[r] === null || args[r] === '');
    if (missing.length) {
      mcpToolResult(res, id, { error: `Missing required argument(s): ${missing.join(', ')}` }, true);
      return;
    }
    const owner = String(args.owner ?? viewerLogin ?? '');
    const repoName = String(args.repo ?? args.name ?? '');
    learnOwner(owner || undefined);
    if (name === 'create_repo') {
      const repoName2 = String(args.name ?? '');
      if (!repoName2) { mcpToolResult(res, id, { error: 'name is required' }, true); return; }
      const exists = [...(reposByName.get(repoName2) ?? [])].some((r) => r.owner === null || r.owner === viewerLogin);
      if (exists) { mcpToolResult(res, id, { error: 'Repository already exists' }, true); return; }
      const repo = createRepo(viewerLogin, repoName2, typeof args.description === 'string' ? args.description : '', args.private === true);
      mcpToolResult(res, id, repoJson(repo));
      return;
    }
    const repo = owner && repoName ? findRepo(owner, repoName) : undefined;
    if (!repo) { mcpToolResult(res, id, { error: `Repository not found: ${owner}/${repoName}` }, true); return; }
    if (name === 'get_repo') { mcpToolResult(res, id, repoJson(repo)); return; }
    if (name === 'create_issue') {
      const issue = createIssueInRepo(repo, String(args.title ?? ''), typeof args.body === 'string' ? args.body : '');
      mcpToolResult(res, id, issueJson(issue));
      return;
    }
    if (name === 'list_issues') {
      const state = String(args.state ?? 'open').toLowerCase();
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b) => b.seq - a.seq);
      mcpToolResult(res, id, list.map(issueJson));
      return;
    }
    if (name === 'create_pull_request') {
      const head = String(args.head ?? '');
      const base = String(args.base ?? repo.defaultBranch);
      const headOid = repo.refs.get(`refs/heads/${head}`);
      const baseOid = repo.refs.get(`refs/heads/${base}`);
      if (!headOid || !baseOid) { mcpToolResult(res, id, { error: 'head or base branch does not exist' }, true); return; }
      const dup = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === head);
      if (dup) { mcpToolResult(res, id, pullJson(dup, repo)); return; }
      const pull: Pull = {
        number: repo.nextNumber, id: idSeq += 1, title: String(args.title ?? ''),
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open', headRef: head, baseRef: base, headSha: headOid, baseSha: baseOid,
        merged: false, mergedAt: null, mergeCommitSha: null, seq: repo.nextNumber,
      };
      repo.nextNumber += 1;
      repo.pulls.set(pull.number, pull);
      mcpToolResult(res, id, pullJson(pull, repo));
      return;
    }
    if (name === 'merge_pull_request') {
      const pull = repo.pulls.get(Number(args.pull_number));
      if (!pull) { mcpToolResult(res, id, { error: 'Pull request not found' }, true); return; }
      if (pull.state !== 'open') { mcpToolResult(res, id, { error: 'Pull request is already closed' }, true); return; }
      if (mergeableState(repo, pull) === 'CONFLICTING') { mcpToolResult(res, id, { error: 'Merge conflict' }, true); return; }
      doSquashMerge(repo, pull);
      mcpToolResult(res, id, pullJson(pull, repo));
      return;
    }
    mcpError(res, id, -32601, `Method not found: ${name}`);
    return;
  }
  mcpError(res, id, -32601, `Method not found: ${method}`);
}

// ---------------------------------------------------------------- dispatch
async function handle(req: RawReq, res: RawRes): Promise<void> {
  const method = req.method ?? 'GET';
  const { path, query } = parseRequestUrl(req);
  // GETs never carry a body in this protocol; answering without waiting for
  // the request stream's 'end' keeps keep-alive reads fast (only when the
  // headers confirm there is no body to consume).
  const hasBody = (req.headers['content-length'] !== undefined && req.headers['content-length'] !== '0')
    || req.headers['transfer-encoding'] !== undefined;
  const raw = method === 'GET' && !hasBody ? Buffer.alloc(0) : await readBody(req).catch(() => Buffer.alloc(0));
  // Git smart HTTP: /{owner}/{repo}.git/...
  const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(.*)$/.exec(path);
  if (gitMatch) {
    const [, owner, name, rest] = gitMatch;
    if (method === 'GET' && rest === 'info/refs') {
      const service = query.get('service') ?? '';
      if (service === 'git-upload-pack' || service === 'git-receive-pack') {
        handleInfoRefs(req, res, owner, name, service);
        return;
      }
      notFound(res);
      return;
    }
    if (method === 'POST' && rest === 'git-upload-pack') { handleUploadPack(req, res, owner, name, raw); return; }
    if (method === 'POST' && rest === 'git-receive-pack') { handleReceivePack(req, res, owner, name, raw); return; }
    notFound(res);
    return;
  }
  // Health probe: no auth.
  if (method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
  // Auth for the API surfaces (git smart HTTP is unauthenticated here).
  if (path === '/api/graphql' || path === '/mcp' || path.startsWith('/api/v3')) {
    if (!authed(req)) { unauthorized(res); return; }
    if (path === '/api/graphql' && method === 'POST') { handleGraphQL(req, res, raw); return; }
    if (path === '/mcp' && method === 'POST') { handleMcp(req, res, raw); return; }
    if (path.startsWith('/api/v3')) { handleRest(req, res, raw, path, query); return; }
  }
  notFound(res);
}

/** Build the server. It binds nothing until the caller listens; the entry listens on an ephemeral port. */
export function createApp(): NetServer {
  const server = createNetServer((socket: Socket) => {
    new RawConn(socket);
  });
  return server;
}
