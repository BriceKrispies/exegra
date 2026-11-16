// Formatting-preserving text edits on JSONC arrays.

/**
 * Insert a value into an array node without reformatting its neighbours.
 * @param {string} text @param {import('jsonc-parser').Node} array @param {number} index @param {any} value
 * @returns {string}
 */
export function insertInArray(text, array, index, value) {
  const eol = text.includes('\r\n') ? '\r\n' : '\n';
  const items = array.children ?? [];
  /** Whitespace between the start of the line and `offset`, when only whitespace precedes it. @param {number} offset */
  const indentOf = (offset) => {
    const ls = text.lastIndexOf('\n', offset - 1) + 1;
    const lead = text.slice(ls, offset);
    return /^[ \t]*$/.test(lead) ? lead : null;
  };
  /** Indentation of the line containing `offset`. @param {number} offset */
  const lineIndentOf = (offset) => {
    const ls = text.lastIndexOf('\n', offset - 1) + 1;
    return /^[ \t]*/.exec(text.slice(ls))?.[0] ?? '';
  };
  const indent = (items.length ? indentOf(items[0].offset) : null) ?? lineIndentOf(array.offset) + '  ';
  const body = JSON.stringify(value, null, 2).split('\n').join(eol + indent);
  if (!items.length) {
    const closing = array.offset + array.length - 1;
    return text.slice(0, array.offset + 1) + eol + indent + body + eol + lineIndentOf(array.offset) + text.slice(closing);
  }
  if (index >= items.length) {
    const lastItem = items[items.length - 1];
    const at = lastItem.offset + lastItem.length;
    return text.slice(0, at) + ',' + eol + indent + body + text.slice(at);
  }
  const at = items[index].offset;
  return text.slice(0, at) + body + ',' + eol + indent + text.slice(at);
}
