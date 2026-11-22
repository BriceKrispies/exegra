// A specification kept as a manifest and part files (WG-5386), resolved to the one text Exegra reads.
//
// A project's specification file may be a manifest: {"specParts": ["intent.jsonc", "boundary.jsonc", ...]}
// listing part files beside it, each a JSONC object holding some top-level sections. Resolving it gives
// the document a single file holding every section would have:
//
//   * array sections are concatenated in manifest order (`claims` may be in two parts);
//   * a section that is not an array (system, vocabulary, exegra, ...) may be in one part only;
//   * an entity id that two parts give one array section is refused;
//   * a missing part, a part that is itself a manifest, and a manifest with sections of its own are refused.
//
// Every refusal is a SpecManifestError that names the files. Strata's specc (crates/spec-parts),
// Concordance (concordance-exegra/src/parts.rs) and Strata's scripts/spec-parts.mjs apply the same rule.
//
// The assembled text is canonical, so each implementation produces the same bytes: `{`, one member per
// line at two spaces in the order a key first appears, an array as `[`, its items one per line at four
// spaces (each item's own text unchanged, comments between items dropped), then `]`, any other value
// unchanged after `"key": `, and `}` with a final newline. A file that is not a manifest is the text as it is.
//
// `planWrite` is the way back: given the assembled text after an edit, it says which part files change.
// An entity stays in the part that holds it; a new one goes where the manifest's optional
// `specSections` table puts its section (a string, or {"by": "<field>", "values": {<value>: <part>},
// "default": <part>} to choose by a field of the entity), else beside the entities of its section that
// already exist, else in the first part. Only the items that changed are replaced in the part's own
// text, so the comments and layout of everything else stay.
//
// Node-only, like tools/workspace.js.

import { readFileSync } from 'node:fs';
import path from 'node:path';
import { parse as parseJsonc } from 'jsonc-parser';

export const MANIFEST_KEY = 'specParts';
export const PLACEMENT_KEY = 'specSections';

/** A manifest that cannot be resolved, with a stable `code` and a message that names the files. */
export class SpecManifestError extends Error {
  /** @param {string} code @param {string} message */
  constructor(code, message) {
    super(message);
    this.name = 'SpecManifestError';
    this.code = code;
  }
}

/**
 * @typedef {{key: string, keyStart: number, start: number, end: number, items: {start: number, end: number}[] | null}} Member
 */

/**
 * The top-level members of a JSONC object text with the offsets of each value and, for an array, of each item.
 * @param {string} text @param {string} [what]
 * @returns {{src: string, members: Member[]}}
 */
export function scanTopLevel(text, what = 'the file') {
  const src = text.charCodeAt(0) === 0xfeff ? ` ${text.slice(1)}` : text;
  let i = 0;
  /** @param {string} message @returns {never} */
  const fail = (message) => {
    throw new SpecManifestError('syntax', `${what}: ${message} (line ${src.slice(0, i).split('\n').length})`);
  };
  const skip = () => {
    for (;;) {
      while (i < src.length && /\s/.test(src[i])) i += 1;
      if (src[i] === '/' && src[i + 1] === '/') {
        while (i < src.length && src[i] !== '\n') i += 1;
      } else if (src[i] === '/' && src[i + 1] === '*') {
        const end = src.indexOf('*/', i + 2);
        if (end < 0) fail('unterminated block comment');
        i = end + 2;
      } else return;
    }
  };
  const string = () => {
    const start = i;
    i += 1;
    while (i < src.length && src[i] !== '"') i += src[i] === '\\' ? 2 : 1;
    if (i >= src.length) fail('unterminated string');
    i += 1;
    return src.slice(start, i);
  };
  const value = () => {
    const c = src[i];
    if (c === '"') {
      string();
    } else if (c === '{' || c === '[') {
      let depth = 0;
      do {
        const d = src[i];
        if (d === '"') {
          string();
          continue;
        }
        if (d === '/' && (src[i + 1] === '/' || src[i + 1] === '*')) {
          skip();
          continue;
        }
        if (d === '{' || d === '[') depth += 1;
        else if (d === '}' || d === ']') depth -= 1;
        i += 1;
      } while (depth > 0 && i < src.length);
      if (depth > 0) fail('unterminated value');
    } else {
      const start = i;
      while (i < src.length && !/[\s,}\]]/.test(src[i]) && !(src[i] === '/' && (src[i + 1] === '/' || src[i + 1] === '*'))) i += 1;
      if (i === start) fail('a value was expected');
    }
  };
  skip();
  if (src[i] !== '{') fail('the top level is not an object');
  i += 1;
  /** @type {Member[]} */
  const members = [];
  for (;;) {
    skip();
    if (src[i] === '}') break;
    if (src[i] !== '"') fail('a member name was expected');
    const keyStart = i;
    const key = JSON.parse(string());
    skip();
    if (src[i] !== ':') fail('a colon was expected');
    i += 1;
    skip();
    const start = i;
    /** @type {{start: number, end: number}[] | null} */
    let items = null;
    if (src[i] === '[') {
      items = [];
      i += 1;
      for (;;) {
        skip();
        if (src[i] === ']') {
          i += 1;
          break;
        }
        const s = i;
        value();
        items.push({ start: s, end: i });
        skip();
        if (src[i] === ',') i += 1;
      }
    } else {
      value();
    }
    members.push({ key, keyStart, start, end: i, items });
    skip();
    if (src[i] === ',') i += 1;
    else if (src[i] !== '}') fail('a comma or the closing brace was expected');
  }
  return { src, members };
}

/** Whether a text is a manifest: its top level has the `specParts` key. @param {string} text */
export function isManifest(text) {
  if (!text.includes(MANIFEST_KEY)) return false;
  try {
    return scanTopLevel(text).members.some((m) => m.key === MANIFEST_KEY);
  } catch {
    return false;
  }
}

/**
 * The part file names a manifest lists, in order, and its placement table.
 * @param {string} text @param {string} [what]
 * @returns {{parts: string[], placement: Record<string, any>}}
 */
export function readManifest(text, what = 'the manifest') {
  const top = scanTopLevel(text, what);
  const others = top.members.filter((m) => m.key !== MANIFEST_KEY && m.key !== PLACEMENT_KEY).map((m) => `"${m.key}"`);
  if (others.length) {
    throw new SpecManifestError('manifest-sections', `${what} is a manifest and lists parts, so it holds no section of its own; found ${others.join(', ')}`);
  }
  const own = top.members.filter((m) => m.key === MANIFEST_KEY);
  if (own.length !== 1) throw new SpecManifestError('manifest-shape', `${what}: "${MANIFEST_KEY}" appears ${own.length} times`);
  const list = parseJsonc(top.src.slice(own[0].start, own[0].end));
  if (!Array.isArray(list) || list.length === 0 || !list.every((p) => typeof p === 'string' && p !== '')) {
    throw new SpecManifestError('manifest-shape', `${what}: "${MANIFEST_KEY}" must be a non-empty list of part file names`);
  }
  list.forEach((p, i) => {
    if (list.indexOf(p) !== i) throw new SpecManifestError('manifest-shape', `${what} lists the part ${p} twice`);
  });
  const table = top.members.find((m) => m.key === PLACEMENT_KEY);
  const placement = table ? parseJsonc(top.src.slice(table.start, table.end)) : {};
  if (placement === null || typeof placement !== 'object' || Array.isArray(placement)) {
    throw new SpecManifestError('manifest-shape', `${what}: "${PLACEMENT_KEY}" must be an object mapping a section to a part`);
  }
  const named = (/** @type {any} */ v) => (typeof v === 'string' ? [v] : v && typeof v === 'object' ? [...Object.values(v.values ?? {}), v.default].filter((x) => x !== undefined) : [null]);
  for (const [section, to] of Object.entries(placement)) {
    for (const part of named(to)) {
      if (typeof part !== 'string' || !list.includes(part)) throw new SpecManifestError('manifest-shape', `${what}: "${PLACEMENT_KEY}" puts the section "${section}" in ${JSON.stringify(part)}, which "${MANIFEST_KEY}" does not list`);
    }
  }
  return { parts: list, placement };
}

/** @param {string} src @param {{start: number, end: number}} item @returns {string|null} */
function idOf(src, item) {
  try {
    const id = parseJsonc(src.slice(item.start, item.end))?.id;
    return typeof id === 'string' ? id : null;
  } catch {
    return null;
  }
}

/**
 * Assembles parts given in manifest order as {file, text}.
 * @param {{file: string, text: string}[]} parts
 * @returns {{text: string}}
 */
export function assembleParts(parts) {
  /** @type {Map<string, {array: boolean, items: string[], files: string[]}>} */
  const sections = new Map();
  const tops = new Map();
  for (const part of parts) {
    const top = scanTopLevel(part.text, part.file);
    tops.set(part, top);
    const seen = new Set();
    for (const m of top.members) {
      if (m.key === MANIFEST_KEY) throw new SpecManifestError('nested-manifest', `${part.file} is a manifest; a part holds sections, not a list of parts`);
      if (seen.has(m.key)) throw new SpecManifestError('duplicate-section', `${part.file} names the section "${m.key}" twice`);
      seen.add(m.key);
      const array = m.items !== null;
      let s = sections.get(m.key);
      if (s && (!array || !s.array)) {
        throw new SpecManifestError('duplicate-section', `the section "${m.key}" is in both ${s.files[0]} and ${part.file}; only an array section may be in more than one part`);
      }
      if (!s) {
        s = { array, items: [], files: [] };
        sections.set(m.key, s);
      }
      s.files.push(part.file);
      if (m.items === null) s.items.push(top.src.slice(m.start, m.end));
      else for (const item of m.items) s.items.push(top.src.slice(item.start, item.end));
    }
  }
  for (const [key, s] of sections) {
    if (!s.array || s.files.length < 2) continue;
    /** @type {Map<string, string>} */
    const owner = new Map();
    for (const part of parts) {
      const top = tops.get(part);
      const m = top.members.find((/** @type {Member} */ x) => x.key === key);
      if (!m) continue;
      for (const item of m.items ?? []) {
        const id = idOf(top.src, item);
        if (id === null) continue;
        const first = owner.get(id);
        if (first !== undefined && first !== part.file) throw new SpecManifestError('duplicate-id', `the id "${id}" of section "${key}" is in both ${first} and ${part.file}`);
        owner.set(id, part.file);
      }
    }
  }
  const out = [];
  for (const [key, s] of sections) {
    const q = JSON.stringify(key);
    if (s.array) out.push(s.items.length ? `  ${q}: [\n${s.items.map((t) => `    ${t}`).join(',\n')}\n  ]` : `  ${q}: []`);
    else out.push(`  ${q}: ${s.items[0]}`);
  }
  return { text: `{\n${out.join(',\n')}\n}\n` };
}

/**
 * @typedef {Object} ResolvedSpec
 * @property {boolean} manifest   whether the file is a manifest
 * @property {string} text        the specification text: assembled, or the file's own
 * @property {string} file        the absolute path of the file
 * @property {{file: string, text: string}[]} parts  the part files as read (none when not a manifest)
 * @property {Record<string, any>} placement  the manifest's placement table
 */

/**
 * Resolves the specification text read from `file`.
 * @param {string} file absolute path @param {string} text @param {(p: string) => string} [read]
 * @returns {ResolvedSpec}
 */
export function resolveSpecText(file, text, read = (p) => readFileSync(p, 'utf8')) {
  if (!isManifest(text)) return { manifest: false, text, file, parts: [], placement: {} };
  const { parts: names, placement } = readManifest(text, file);
  const dir = path.dirname(file);
  const parts = names.map((name) => {
    const abs = path.resolve(dir, name);
    try {
      return { file: abs, text: read(abs) };
    } catch (err) {
      const code = /** @type {NodeJS.ErrnoException} */ (err).code;
      if (code === 'ENOENT' || code === 'ENOTDIR') throw new SpecManifestError('missing-part', `${file} lists the part ${name}, which does not exist (${abs})`);
      throw err;
    }
  });
  return { manifest: true, text: assembleParts(parts).text, file, parts, placement };
}

/**
 * The part for an entity or a section that no part holds yet.
 * @param {Record<string, any>} placement @param {string[]} names @param {string} section @param {any} item the entity, or undefined for a whole section
 * @returns {string|null} a part name from the manifest, or null when the table says nothing
 */
function placedBy(placement, names, section, item) {
  const rule = placement[section];
  if (typeof rule === 'string') return rule;
  if (rule && typeof rule === 'object') {
    const v = item && typeof item === 'object' ? item[rule.by] : undefined;
    return (typeof v === 'string' && rule.values?.[v]) || rule.default || names[0] || null;
  }
  return null;
}

/**
 * The part files that change when the assembled text of `resolved` becomes `newText`.
 * @param {ResolvedSpec} resolved @param {string} newText
 * @returns {{file: string, text: string}[]} only the files whose text changes
 */
export function planWrite(resolved, newText) {
  if (!resolved.manifest) throw new Error('planWrite needs a manifest');
  const partOf = new Map(resolved.parts.map((p) => [p.file, p]));
  const names = resolved.parts.map((p) => p.file);
  const byName = (/** @type {string} */ rel) => path.resolve(path.dirname(resolved.file), rel);
  const placement = Object.fromEntries(Object.entries(resolved.placement).map(([k, v]) => [k, typeof v === 'string' ? byName(v) : { ...v, values: Object.fromEntries(Object.entries(v.values ?? {}).map(([a, b]) => [a, byName(/** @type {string} */ (b))])), default: v.default === undefined ? undefined : byName(v.default) }]));

  // What each part holds now.
  const tops = new Map(resolved.parts.map((p) => [p.file, scanTopLevel(p.text, p.file)]));
  /** @type {Map<string, string>} */
  const holder = new Map();
  /** @type {Map<string, string>} section\0id -> part */
  const owner = new Map();
  /** @type {Map<string, string[]>} section -> parts holding it, in order */
  const holders = new Map();
  for (const [file, top] of tops) {
    for (const m of top.members) {
      if (!holders.has(m.key)) holders.set(m.key, []);
      /** @type {string[]} */ (holders.get(m.key)).push(file);
      if (m.items === null) holder.set(m.key, file);
      else for (const item of m.items) {
        const id = idOf(top.src, item);
        if (id !== null) owner.set(`${m.key}\0${id}`, file);
      }
    }
  }

  // Where each member of the new text goes.
  const next = scanTopLevel(newText, 'the edited specification');
  /** @type {Map<string, Map<string, {array: boolean, items: string[], ids: (string|null)[]}>>} part -> section -> desired */
  const want = new Map(names.map((n) => [n, new Map()]));
  const slot = (/** @type {string} */ file, /** @type {string} */ key, /** @type {boolean} */ array) => {
    const sections = /** @type {Map<string, any>} */ (want.get(file));
    if (!sections.has(key)) sections.set(key, { array, items: [], ids: [] });
    return sections.get(key);
  };
  for (const m of next.members) {
    if (m.items === null) {
      const file = holder.get(m.key) ?? placedBy(placement, names, m.key, undefined) ?? holders.get(m.key)?.[0] ?? names[0];
      slot(file, m.key, false).items.push(next.src.slice(m.start, m.end));
      continue;
    }
    for (const item of m.items) {
      const text = next.src.slice(item.start, item.end);
      const id = idOf(next.src, item);
      let file = id === null ? undefined : owner.get(`${m.key}\0${id}`);
      if (file === undefined) {
        let entity;
        try { entity = parseJsonc(text); } catch { entity = undefined; }
        file = placedBy(placement, names, m.key, entity) ?? holders.get(m.key)?.[0] ?? names[0];
        if (!placement[m.key] && (holders.get(m.key)?.length ?? 0) > 1 && entity && typeof entity.kind === 'string') {
          // No table: beside the entities of this section that have the same kind.
          const same = (holders.get(m.key) ?? []).find((f) => {
            const top = /** @type {any} */ (tops.get(f));
            const mm = top.members.find((/** @type {Member} */ x) => x.key === m.key);
            return (mm?.items ?? []).some((/** @type {{start: number, end: number}} */ it) => { try { return parseJsonc(top.src.slice(it.start, it.end))?.kind === entity.kind; } catch { return false; } });
          });
          if (same) file = same;
        }
      }
      const s = slot(file, m.key, true);
      s.items.push(text);
      s.ids.push(id);
    }
  }

  // Each part's new text: the original with only what changed replaced.
  /** @type {{file: string, text: string}[]} */
  const changed = [];
  for (const [file, top] of tops) {
    const part = /** @type {{file: string, text: string}} */ (partOf.get(file));
    const desired = /** @type {Map<string, any>} */ (want.get(file));
    const src = top.src;
    /** @type {{start: number, end: number, text: string}[]} */
    const edits = [];
    let rebuild = false;
    for (const m of top.members) {
      const d = desired.get(m.key);
      if (!d) { rebuild = true; break; }
      if (m.items === null) {
        if (src.slice(m.start, m.end) !== d.items[0]) edits.push({ start: m.start, end: m.end, text: d.items[0] });
        continue;
      }
      const ids = m.items.map((i) => idOf(src, i));
      const sameIds = ids.length === d.ids.length && ids.every((id, i) => id !== null && id === d.ids[i]);
      if (sameIds) {
        m.items.forEach((item, i) => {
          if (src.slice(item.start, item.end) !== d.items[i]) edits.push({ start: item.start, end: item.end, text: d.items[i] });
        });
      } else {
        const original = m.items.map((i) => src.slice(i.start, i.end));
        if (original.length === d.items.length && original.every((t, i) => t === d.items[i])) continue;
        edits.push({ start: m.start, end: m.end, text: d.items.length ? `[\n${d.items.map((/** @type {string} */ t) => `    ${t}`).join(',\n')}\n  ]` : '[]' });
      }
    }
    const added = [...desired.keys()].filter((k) => !top.members.some((m) => m.key === k));
    let text;
    if (rebuild) {
      // A section left this part: write the part again, keeping the comments that open it.
      const header = src.slice(0, src.indexOf('{')).replace(/^ /, '');
      const body = [...desired.entries()].map(([k, d]) => (d.array ? `  ${JSON.stringify(k)}: ${d.items.length ? `[\n${d.items.map((/** @type {string} */ t) => `    ${t}`).join(',\n')}\n  ]` : '[]'}` : `  ${JSON.stringify(k)}: ${d.items[0]}`));
      text = `${header}{\n${body.join(',\n')}\n}\n`;
    } else {
      text = src;
      for (const e of edits.sort((a, b) => b.start - a.start)) text = text.slice(0, e.start) + e.text + text.slice(e.end);
      if (added.length) {
        const render = added.map((k) => {
          const d = /** @type {any} */ (desired.get(k));
          return d.array ? `  ${JSON.stringify(k)}: ${d.items.length ? `[\n${d.items.map((/** @type {string} */ t) => `    ${t}`).join(',\n')}\n  ]` : '[]'}` : `  ${JSON.stringify(k)}: ${d.items[0]}`;
        });
        const close = text.lastIndexOf('}');
        const before = text.slice(0, close).replace(/\s+$/, '');
        const comma = before.endsWith('{') ? '\n' : ',\n';
        text = `${before}${comma}${render.join(',\n')}\n}${text.slice(close + 1)}`;
      }
    }
    const original = part.text;
    if (text !== original) changed.push({ file, text });
  }
  return changed;
}
