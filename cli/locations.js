// Source locations for a specification kept as a manifest of part files (WG-5704).
//
// The model is parsed from the one assembled text, so a `loc` carries a line of text that no file holds. loadProject
// registers the project's locator here (`workspace.read` gives it for a manifest); every command that reports a source
// location asks `locate` for the part file and the line in it. For a one-file specification, and for a product file of a
// layered project, the loc is reported as it is.

/** @type {((offset: number) => {file: string, line: number, column: number} | null) | null} */
let locator = null;

/** @param {((offset: number) => {file: string, line: number, column: number} | null) | null | undefined} fn */
export function setLocator(fn) {
  locator = typeof fn === 'function' ? fn : null;
}

/**
 * @param {{offset?: number, line?: number, column?: number, file?: string} | undefined} loc
 * @param {string} [defaultFile] the file a loc without its own is in
 * @returns {{file?: string, line: number|null, column: number|null}}
 */
export function locate(loc, defaultFile) {
  if (loc && loc.file === undefined && locator && typeof loc.offset === 'number') {
    const at = locator(loc.offset);
    if (at) return { file: at.file, line: at.line, column: at.column };
  }
  const file = loc?.file ?? defaultFile;
  return { ...(file !== undefined ? { file } : {}), line: loc?.line ?? null, column: loc?.column ?? null };
}
