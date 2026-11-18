// The shape of a test evidence reference, `<test file>` or `<test file>#<title pattern>`.
// `exegra verify` runs only references of this shape, and the validator reports every other one
// as an error, so an author learns of an unusable reference from `validate`, not from `verify`.
// Both call these functions; neither keeps its own copy of the rule.
// Pure: no Node-only APIs. Whether the file lies inside the repository and exists is checked by
// the verify command, which owns the file system.

const ALLOWED = /^[A-Za-z0-9_./\- #:]$/;
// A reference into a realisation root ("<alias>:<file>#<describe> > <name>") is matched against
// that root's JUnit report and never handed to a command, so its title may hold any printable character.
export const ROOT_REF = /^([a-z][a-z0-9_-]*):(.+)$/;
const PRINTABLE = /^[^\u0000-\u001f\u007f]$/;

/** The allowed characters, in words, for messages. */
export const TEST_REF_CHARACTERS = 'letters, digits, underscore, dot, slash, hyphen, space, hash and colon';

/**
 * Why a test evidence reference cannot be run, or null when it can.
 * `characters` lists each disallowed character once, in order of first appearance; `position` is
 * the 1-based index of the first one. A reference with no file part before `#` has reason
 * `no-file`.
 * @param {string} ref
 * @returns {null | {reason: 'characters', characters: string[], position: number} | {reason: 'no-file'}}
 */
export function testRefProblem(ref) {
  const text = String(ref);
  const hash = text.indexOf('#');
  const titleFrom = hash >= 0 && ROOT_REF.test(text.slice(0, hash)) ? hash : text.length;
  /** @type {string[]} */
  const characters = [];
  let position = 0;
  for (let i = 0; i < text.length; i++) {
    const ch = text.charAt(i);
    if (ALLOWED.test(ch) || (i > titleFrom && PRINTABLE.test(ch))) continue;
    if (position === 0) position = i + 1;
    if (!characters.includes(ch)) characters.push(ch);
  }
  if (characters.length) return { reason: 'characters', characters, position };
  const hashAt = text.indexOf('#');
  const file = (hashAt < 0 ? text : text.slice(0, hashAt)).trim();
  if (file === '') return { reason: 'no-file' };
  return null;
}

/**
 * The sentence that says why a reference is unusable. Used by the validator's diagnostic and by
 * verify's recorded detail, so both report the same words.
 * @param {string} ref
 * @param {NonNullable<ReturnType<typeof testRefProblem>>} problem
 * @returns {string}
 */
export function describeTestRefProblem(ref, problem) {
  if (problem.reason === 'no-file') return `The test reference "${ref}" names no test file before "#".`;
  const shown = problem.characters.map((c) => (c === ' ' ? 'a space' : `"${c}"`)).join(', ');
  return `The test reference "${ref}" contains ${shown}, which a test reference may not contain (first at character ${problem.position}). A test reference may contain only ${TEST_REF_CHARACTERS}.`;
}
