// Text for a log entry's `detail`: a string as is; a rejected transaction's
// {code, diagnostics} as the code plus the first diagnostic messages; anything
// else renders nothing (never "[object Object]").

/**
 * @param {any} detail
 * @returns {string}
 */
export function detailText(detail) {
  if (typeof detail === 'string') return detail;
  if (detail && typeof detail === 'object' && Array.isArray(detail.diagnostics)) {
    const msgs = detail.diagnostics.map((/** @type {any} */ d) => String(d?.message ?? '')).filter(Boolean);
    const parts = [...msgs.slice(0, 3)];
    if (msgs.length > 3) parts.push(`+${msgs.length - 3} more`);
    return [typeof detail.code === 'string' ? detail.code : '', ...parts].filter(Boolean).join(' ');
  }
  return '';
}
