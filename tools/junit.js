// Reading JUnit XML reports into flat test cases. Node-free and dependency-free;
// handles the subset test runners write (elements, attributes, text, CDATA,
// comments, the five named entities and numeric character references).

/**
 * One test case of a report.
 * `suites` are the enclosing describe blocks, outermost first. A testsuite that
 * stands for a file (its name equals its file attribute, as bun writes it) is not
 * part of that path.
 * @typedef {{file: string, suites: string[], name: string, status: 'pass'|'fail'|'error'|'skipped', message: string}} JUnitCase
 */

/** @param {string} text */
function decode(text) {
  return text.replace(/&(#x[0-9a-fA-F]+|#\d+|amp|lt|gt|quot|apos);/g, (_m, e) => {
    if (e[0] === '#') return String.fromCodePoint(e[1] === 'x' ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10));
    return /** @type {Record<string, string>} */ ({ amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" })[e];
  });
}

/** @param {string} src @returns {Record<string, string>} */
function attributes(src) {
  /** @type {Record<string, string>} */
  const out = {};
  for (const m of src.matchAll(/([A-Za-z_:][\w:.-]*)\s*=\s*("([^"]*)"|'([^']*)')/g)) out[m[1]] = decode(m[3] ?? m[4] ?? '');
  return out;
}

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/').replace(/^\.\//, '');

/**
 * Parse a JUnit XML report.
 * @param {string} xml
 * @returns {JUnitCase[]}
 */
export function parseJUnit(xml) {
  /** @type {JUnitCase[]} */
  const cases = [];
  /** @type {{name: string, file: string, isFile: boolean}[]} */
  const suites = [];
  /** @type {(JUnitCase & {text: string})|null} */
  let current = null;
  /** @type {string|null} the child element of a case whose text is being collected */
  let collecting = null;

  const tokens = /<!--[\s\S]*?-->|<!\[CDATA\[([\s\S]*?)\]\]>|<\?[\s\S]*?\?>|<!DOCTYPE[^>]*>|<(\/?)([A-Za-z_][\w:.-]*)((?:\s+[^\s=/>]+\s*=\s*(?:"[^"]*"|'[^']*'))*)\s*(\/?)>|([^<]+)/g;
  for (const m of xml.matchAll(tokens)) {
    const [, cdata, closing, tag, attrSrc, selfClosing, text] = m;
    if (cdata !== undefined || text !== undefined) {
      if (current && collecting) current.text += cdata ?? decode(text ?? '');
      continue;
    }
    if (!tag) continue;
    const local = tag.replace(/^.*:/, '');
    if (closing) {
      if (local === 'testsuite') suites.pop();
      else if (local === 'testcase' && current) {
        cases.push(finish(current));
        current = null;
      } else if (local === collecting) collecting = null;
      continue;
    }
    const attrs = attributes(attrSrc ?? '');
    if (local === 'testsuite') {
      const file = slash(attrs.file ?? attrs.filepath ?? '');
      const name = attrs.name ?? '';
      const parentFile = suites.length ? suites[suites.length - 1].file : '';
      const entry = { name, file: file || parentFile, isFile: file !== '' && slash(name) === file };
      if (!selfClosing) suites.push(entry);
    } else if (local === 'testcase') {
      const enclosing = suites.length ? suites[suites.length - 1].file : '';
      current = {
        file: slash(attrs.file ?? attrs.filepath ?? enclosing),
        suites: suites.filter((s) => !s.isFile).map((s) => s.name),
        name: attrs.name ?? '',
        status: 'pass',
        message: '',
        text: '',
      };
      if (selfClosing) {
        cases.push(finish(current));
        current = null;
      }
    } else if (current && (local === 'failure' || local === 'error' || local === 'skipped')) {
      // A failure outranks a skip; an error outranks both.
      const rank = { pass: 0, skipped: 1, fail: 2, error: 3 };
      const status = local === 'failure' ? 'fail' : local;
      if (rank[status] > rank[current.status]) current.status = /** @type {JUnitCase['status']} */ (status);
      if (attrs.message) current.message += (current.message ? '\n' : '') + attrs.message;
      if (!selfClosing) collecting = local;
    }
  }
  return cases;
}

/** @param {JUnitCase & {text: string}} c @returns {JUnitCase} */
function finish(c) {
  const message = [c.message, c.text.trim()].filter(Boolean).join('\n');
  return { file: c.file, suites: c.suites, name: c.name, status: c.status, message };
}
