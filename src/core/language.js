// The language construct (WG-4929, NC-2): an expression language that tenants of the specified system write,
// such as Strata's rule language, described as data so that a generator can produce its parser, printer, checker
// and evaluator. It is not Exegra's guard language (src/core/expr.js) and is not mirrored in Lean; claims about it
// are checked, not proved. docs/model-and-format.md, "Languages".
//
// What a language may mean is fixed here, in the primitive catalogue: each operator of a language names one
// primitive, and the generator owns that primitive's evaluation, null handling, static check and printing. The
// catalogue is pinned to the Strata kernel (crates/kernel/src/expr.rs and crates/substrate/src/syntax.rs).
//
// Consistency rules (errors, always on):
//   language.operator-duplicate  operator names are unique within a language
//   language.token-clash         no word or symbol is claimed by two operators, literal forms or scopes
//   language.syntax              each form has the token it needs, in the lexical class it needs, and the primitive
//                                can be written in that form
//   language.precedence          binary and prefix operators state a precedence (and binary ones an associativity,
//                                one per level); primaries state neither
//   language.primitive-unknown   a primitive names an entry of the catalogue
//   language.arity               operands, the primitive's arity and the AST variant's expression fields agree
//   language.shape-unknown       every shape named is one of the language's shapes
//   language.nulls               an operator's stated null handling is its primitive's
//   language.variant             ast and values are unions; an operator names a variant of ast (and a case of it);
//                                no variant or case has two operators
//   language.scope               scopes are well formed and fit the operators that read them
// Readiness (errors when system.generation is set, listed by the readiness command otherwise):
//   ready.language-variant-uncovered  every AST variant (every case of a split variant) has an operator
//   ready.language-primitive-missing  every operator names a primitive

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** How an operator is written. */
export const SYNTAX_FORMS = Object.freeze(['infix', 'keyword-infix', 'prefix-word', 'call', 'literal', 'scope']);
/** How a binary operator groups with itself. `n-ary` collects a run of the operator into one list operand. */
export const ASSOCIATIVITY = Object.freeze(['left', 'right', 'none', 'n-ary']);
/** What an operator does with null operands. */
export const NULL_RULES = Object.freeze(['propagate', 'kleene-and', 'kleene-or', 'kleene-not', 'total', 'null-is-false']);
/** The kinds of scope a name can be read through. */
export const SCOPE_KINDS = Object.freeze(['record-scope', 'param', 'constant', 'role-test']);
/**
 * The lexical forms of literals and the words each reserves. `int` is an optional `-` and decimal digits (i64);
 * `string` is single-quoted with the escapes \' \\ \n; `time` and `ref` are `time(<int>)` and `ref(<int ≥ 0>)`;
 * `list` is `[` literals separated by `,` `]`.
 * @type {Readonly<Record<string, readonly string[]>>}
 */
export const LITERAL_FORMS = Object.freeze({ null: ['null'], bool: ['true', 'false'], int: [], string: [], time: ['time'], ref: ['ref'], list: [] });
/**
 * The kernel's name of each literal form's kind of value (crates/kernel/src/value.rs Value::kind), which evaluation
 * errors print: "len does not apply to a timestamp".
 * @type {Readonly<Record<string, string>>}
 */
export const LITERAL_KINDS = Object.freeze({ null: 'null', bool: 'bool', int: 'int', string: 'string', time: 'timestamp', ref: 'reference', list: 'list' });
/** Punctuation the generated parser keeps for itself: grouping, lists, argument separators and scope access. */
export const RESERVED_SYMBOLS = Object.freeze(['(', ')', '[', ']', ',', '.']);

const WORD_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;
const SYMBOL_RE = /^[=!<>+\-*/%&|^~?:]+$/;
const ATTRIBUTE_RE = /^\$[A-Za-z_][A-Za-z0-9_]*$/;
const OPERAND_REF_RE = /^operand:([1-9][0-9]*)$/;

/**
 * @typedef {Object} Primitive
 * @property {number|'n'} arity   expression operands; 'n' is a list of operands (an n-ary operator)
 * @property {string[]} forms     the syntax forms the generator can write it in
 * @property {string} nulls       its null handling (NULL_RULES)
 * @property {string} [scope]     for the scope form: the kind of scope it reads ('record-scope' reads them all)
 * @property {string} [literal]   for the literal form: the literal forms it may take
 * @property {string} kernel      the kernel code it mirrors
 * @property {string} semantics   evaluation, including null handling and errors
 * @property {string} check       the static check
 */

const CMP = (/** @type {string} */ op, /** @type {string} */ sym, /** @type {string} */ test) => /** @type {Primitive} */ ({
  arity: 2, forms: ['infix'], nulls: 'propagate',
  kernel: `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::${op}) -> compare`,
  semantics: `null if either operand is null (so null ${sym} null is null); an error if the two values are of different kinds; otherwise ${test}.`,
  check: op === 'Eq' || op === 'Ne'
    ? 'check, Expr::Cmp: the two shapes agree unless one is the any shape.'
    : 'check, Expr::Cmp: the two shapes agree unless one is the any shape, and each is Int, Time or Str.',
});

/** The largest magnitude an integer of checked arithmetic may have: 2^53-1 (Strata D-6540, D-5004). */
export const SAFE_INT = 9007199254740991;
/** The longest string concat may build, in bytes of UTF-8 (Strata D-6542). */
export const MAX_TEXT_BYTES = 4096;
/** The error of a checked integer outside ±SAFE_INT, and of a string longer than MAX_TEXT_BYTES. */
export const INTEGER_OVERFLOW = 'integer-overflow';
export const STRING_TOO_LONG = 'string-too-long';
const RANGE = 'an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow.';

const ARITH = (/** @type {string} */ op, /** @type {string} */ sym, /** @type {string} */ what) => /** @type {Primitive} */ ({
  arity: 2, forms: ['infix'], nulls: 'propagate',
  kernel: `crates/kernel/src/expr.rs: eval, Expr::Arith(ArithOp::${op === 'add' ? 'Add' : 'Sub'}) -> checked`,
  semantics: `null if either operand is null; ${what}; a left operand that is neither an int nor a timestamp, then a right operand that is not an int, is an error (so int ${sym} timestamp is an error); ${RANGE}`,
  check: 'check, Expr::Arith: the left has the Int, Time or any shape and the right the Int or any shape; the result is the shape of the left.',
});

const DURATION = (/** @type {string} */ unit, /** @type {number} */ ms) => /** @type {Primitive} */ ({
  arity: 1, forms: ['call'], nulls: 'propagate',
  kernel: `crates/kernel/src/expr.rs: eval, Expr::Duration(DurationUnit::${unit[0].toUpperCase()}${unit.slice(1)}) -> checked`,
  semantics: `null gives null; an int n gives n times ${ms} (milliseconds in ${unit}); anything else is an error; ${RANGE}`,
  check: 'check, Expr::Duration: the operand has the Int or any shape; the result is Int.',
});

/**
 * The primitive catalogue. Every operator of every language names one of these; nothing else can be expressed.
 * @type {Readonly<Record<string, Primitive>>}
 */
export const LANGUAGE_PRIMITIVES = Object.freeze({
  eq: CMP('Eq', '==', 'whether the values are equal (structural equality of Value)'),
  ne: CMP('Ne', '!=', 'whether they differ'),
  lt: CMP('Lt', '<', 'true when the left orders before the right; ordering applies to Int (numeric), Time (numeric) and Str (by Unicode scalar values, Rust str::cmp), and is an error on other kinds'),
  le: CMP('Le', '<=', 'true unless the left orders after the right (orderable kinds as for lt)'),
  gt: CMP('Gt', '>', 'true when the left orders after the right (orderable kinds as for lt)'),
  ge: CMP('Ge', '>=', 'true unless the left orders before the right (orderable kinds as for lt)'),
  and3: {
    arity: 'n', forms: ['keyword-infix'], nulls: 'kleene-and',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::And -> tri_and',
    semantics: 'operands left to right: the first false gives false without evaluating the rest; a non-boolean, non-null operand is an error; otherwise null if any operand was null, else true. The empty list is true and is printed as the literal true.',
    check: 'check, Expr::And: every operand has the Bool or any shape; the result is Bool.',
  },
  or3: {
    arity: 'n', forms: ['keyword-infix'], nulls: 'kleene-or',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Or -> tri_or',
    semantics: 'operands left to right: the first true gives true without evaluating the rest; a non-boolean, non-null operand is an error; otherwise null if any operand was null, else false. The empty list is false and is printed as the literal false.',
    check: 'check, Expr::Or: every operand has the Bool or any shape; the result is Bool.',
  },
  not3: {
    arity: 1, forms: ['prefix-word'], nulls: 'kleene-not',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Not',
    semantics: 'true gives false, false gives true, null gives null; any other value is an error.',
    check: 'check, Expr::Not: the operand has the Bool or any shape; the result is Bool.',
  },
  'in-list': {
    arity: 2, forms: ['keyword-infix', 'infix'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::In',
    semantics: 'null if either operand is null; an error if the right is not a list; otherwise whether the list holds an element equal to the left (structural equality, no kind check).',
    check: 'check, Expr::In: the left is checked; the right has the List or any shape; the result is Bool.',
  },
  'is-null': {
    arity: 1, forms: ['call'], nulls: 'total',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::IsNull',
    semantics: 'whether the operand is null; never null, never an error of its own.',
    check: 'check, Expr::IsNull: the operand is checked; the result is Bool.',
  },
  len: {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Len',
    semantics: 'null gives null; a string gives its count of Unicode scalar values (chars, not bytes); a list gives its element count; anything else is an error.',
    check: 'check, Expr::Len: the operand has the Str, List or any shape; the result is Int.',
  },
  lower: {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Lower',
    semantics: 'null gives null; a string gives its full Unicode lower case (Rust str::to_lowercase); anything else is an error.',
    check: 'check, Expr::Lower: the operand has the Str or any shape; the result is Str.',
  },
  contains: {
    arity: 2, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Contains',
    semantics: 'null if either operand is null; two strings: whether the second is a substring of the first; a list and any value: whether the list holds an element equal to it; a first operand that is neither, or a string with a non-string second, is an error.',
    check: 'check, Expr::Contains: the first has the Str, List or any shape; when it is Str the second has the Str or any shape; the result is Bool.',
  },
  'starts-with': {
    arity: 2, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::StartsWith',
    semantics: 'null if either operand is null; two strings: whether the first begins with the second; anything else is an error.',
    check: 'check, Expr::StartsWith: both have the Str or any shape; the result is Bool.',
  },
  'is-slug': {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::IsSlug -> is_slug',
    semantics: 'null gives null; a string gives whether it matches [a-z0-9]+(-[a-z0-9]+)* in ASCII (non-empty, single hyphens, no hyphen at either end); anything else is an error.',
    check: 'check, Expr::IsSlug: the operand has the Str or any shape; the result is Bool.',
  },
  // Grapheme and emoji functions (Strata WG-5597): what a reader sees as one character, UAX #29 extended clusters.
  graphemes: {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Graphemes -> graphemes',
    semantics: 'null gives null; a string gives its count of extended grapheme clusters (UAX #29: a combining sequence, a ZWJ emoji sequence, a flag or a keycap is one); anything else is an error.',
    check: 'check, Expr::Graphemes: the operand has the Str or any shape; the result is Int.',
  },
  'is-emoji': {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::IsEmoji -> is_emoji',
    semantics: 'null gives null; a string gives whether it is exactly one grapheme that is an emoji: a keycap, a flag, a subdivision tag sequence, or ZWJ-joined parts each an emoji presentation or a text-default emoji followed by VS16 or a skin tone (a VS15 makes it not an emoji); anything else is an error.',
    check: 'check, Expr::IsEmoji: the operand has the Str or any shape; the result is Bool.',
  },
  // Bounded reference ancestry (Strata WG-5510): is x the record y or one of its ancestors through a self-reference.
  'ancestor-of': {
    arity: 4, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::AncestorOf',
    semantics: 'the first two operands are references (null gives null); the third and fourth are string literals naming an object type and a field of it that is a single reference to that type. Walking from y through the field, the answer is true when a record equals x (y itself counts), false when the walk ends at a record whose field is null or whose target is absent, and an error when the walk would take more than 32 hops, when it returns to a record it already visited (a cycle), or when the lookup does not cover a record it reads. Every operand is evaluated, left to right, before the nulls are read; a non-reference operand is an error.',
    check: 'check, Expr::AncestorOf: the first two operands have the Ref or any shape, the last two are string literals (the field a valid field identifier, the object type non-empty); the result is Bool. That the object type exists and the field is a single reference to it is checked by the kernel against the schema, where the object is known.',
  },
  // Checked integer and time arithmetic, durations and text (Strata D-6540 to D-6543, CMS-1540 to CMS-1546). Every
  // integer an operand holds or a result would be lies in -(2^53-1) to 2^53-1, the range Rust's i64 and JavaScript's
  // numbers both hold exactly; anything outside it is the error integer-overflow, never a wrapped or rounded value.
  'add-checked': ARITH('add', '+', 'the left plus the right: an int and an int give an int, a timestamp and an int give the timestamp that many milliseconds later'),
  'sub-checked': ARITH('sub', '-', 'the left minus the right: an int and an int give an int, a timestamp and an int give the timestamp that many milliseconds earlier'),
  'mul-checked': {
    arity: 2, forms: ['infix'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Arith(ArithOp::Mul) -> checked',
    semantics: `null if either operand is null; two ints give their product; a left operand that is not an int, then a right operand that is not an int, is an error; ${RANGE}`,
    check: 'check, Expr::Arith: both operands have the Int or any shape; the result is Int.',
  },
  'time-difference': {
    arity: 2, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::MsBetween -> checked',
    semantics: `null if either operand is null; two timestamps a and b give b minus a in milliseconds, as an int; a first operand that is not a timestamp, then a second that is not, is an error; ${RANGE}`,
    check: 'check, Expr::MsBetween: both operands have the Time or any shape; the result is Int.',
  },
  'days-ms': DURATION('days', 86400000),
  'hours-ms': DURATION('hours', 3600000),
  'minutes-ms': DURATION('minutes', 60000),
  'concat-checked': {
    arity: 2, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Concat',
    semantics: `null if either operand is null; two strings give the first followed by the second; a first operand that is not a string, then a second that is not, is an error; a result longer than ${MAX_TEXT_BYTES} bytes of UTF-8 is the error string-too-long.`,
    check: 'check, Expr::Concat: both operands have the Str or any shape; the result is Str.',
  },
  'to-text': {
    arity: 1, forms: ['call'], nulls: 'propagate',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Text',
    semantics: 'null gives null; an int, a timestamp or a reference gives its decimal digits (a leading - when negative); a bool gives true or false; a string gives itself; a list is an error.',
    check: 'check, Expr::Text: the operand has the Int, Time, Ref, Bool, Str or any shape; the result is Str.',
  },
  if: {
    arity: 3, forms: ['call'], nulls: 'null-is-false',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::If',
    semantics: 'the condition is evaluated first; true evaluates and gives the second operand; false or null evaluates and gives the third; any other condition is an error. Only the chosen branch is evaluated.',
    check: 'check, Expr::If: the condition has the Bool or any shape; the branch shapes agree unless one is the any shape; the result is the then shape, or the else shape when the then shape is the any shape.',
  },
  'has-role': {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'role-test',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::HasRole; crates/substrate/src/syntax.rs: primary, "has_role"',
    semantics: 'whether the acting principal holds the named role in the context; never null. Written `<token>(<role id>)`, the role a name, not an expression.',
    check: 'check, Expr::HasRole: the role is declared at the definition site; the result is Bool.',
  },
  now: {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'constant',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Now',
    semantics: 'the context timestamp, as a Time value; never null.',
    check: 'check, Expr::Now: the result is Time.',
  },
  principal: {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'constant',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Principal',
    semantics: "the acting principal's id as a string for a user; null for an anonymous or system principal.",
    check: 'check, Expr::Principal: the result is Str.',
  },
  param: {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'param',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Param',
    semantics: 'the named parameter of the context; null when it is not supplied. Written `<scope>.<name>`.',
    check: 'check, Expr::Param: the parameter is declared at the definition site; the result is the any shape.',
  },
  var: {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'record-scope',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Var -> attribute',
    semantics: "the record of the scope (null when the scope has no record, such as old on a create); a system attribute ($id a Ref, $version an Int, $created_at and $updated_at Times, $created_by the creator's id as a string or null); otherwise the field's value, null when unset; a name that is not a valid field id is an error. Written `<scope>.<name>`.",
    check: 'check, Expr::Var -> attribute_shape: a system attribute has its declared shape; a field is declared on the record at the definition site and has the shape of its field type.',
  },
  through: {
    arity: 0, forms: ['scope'], nulls: 'total', scope: 'record-scope',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Through',
    semantics: "one reference hop: null when the scope has no record or the reference field is null; an error when the field holds something other than a Ref, when the field is not a single reference of the record's object type, or when no lookup is available or the lookup does not cover the target; null when the target record does not exist; otherwise the target's attribute, as var reads it. Written `<scope>.<field>.<name>`.",
    check: 'check, Expr::Through: the field is declared and is a single reference; the target object type exists; the result is the shape of the attribute on the target type.',
  },
  literal: {
    arity: 0, forms: ['literal'], nulls: 'total', literal: 'null bool int string time ref',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Lit; write_value; crates/substrate/src/syntax.rs: tokenize, primary',
    semantics: 'the value written. null is the null value; printed as written in the literal forms (strings single-quoted with \\\' \\\\ and \\n escaped).',
    check: 'check, Expr::Lit -> shape_of_value: the shape of the value; null has the any shape.',
  },
  'list-literal': {
    arity: 0, forms: ['literal'], nulls: 'total', literal: 'list',
    kernel: 'crates/kernel/src/expr.rs: eval, Expr::Lit(Value::List); crates/substrate/src/syntax.rs: primary, "["',
    semantics: 'the list of the literal values written; an item that is not a literal is a parse error. Printed [a, b].',
    check: 'check, Expr::Lit: the result is List.',
  },
});

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const show = (v) => (typeof v === 'string' ? `"${v}"` : JSON.stringify(v));

/**
 * The union type an id names, or undefined.
 * @param {Model} model @param {any} id
 */
function unionType(model, id) {
  const t = typeof id === 'string' ? model.entities.get(id) : undefined;
  return t?.kind === 'type' && t.data.kind === 'union' ? t : undefined;
}

/**
 * How many expression operands an AST variant holds: its fields typed as the AST union itself (or option of it)
 * count one each; a field typed list<ast> makes it n-ary.
 * @param {any} variant @param {string} astId @returns {number|'n'}
 */
export function variantOperandCount(variant, astId) {
  let n = 0;
  for (const f of list(variant?.fields)) {
    const t = isObj(f) && typeof f.type === 'string' ? f.type.replace(/\s+/g, '') : '';
    if (t === `list<${astId}>`) return 'n';
    if (t === astId || t === `option<${astId}>`) n++;
  }
  return n;
}

/**
 * The values a case may take on a field of a variant: an enum's values or a union's variant names.
 * @param {Model} model @param {any} variant @param {any} field
 * @returns {string[]|undefined} undefined when the field is not there or is not an enum or a union
 */
function caseValues(model, variant, field) {
  const f = list(variant?.fields).find((x) => isObj(x) && x.name === field);
  if (!f) return undefined;
  const t = typeof f.type === 'string' ? model.entities.get(f.type.trim()) : undefined;
  if (t?.kind !== 'type') return undefined;
  if (t.data.kind === 'enum') return list(t.data.values).filter((v) => typeof v === 'string');
  if (t.data.kind === 'union') return list(t.data.variants).filter(isObj).map((v) => v.name);
  return undefined;
}

/**
 * The consistency rules of languages.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkLanguages(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const lang of model.byKind.language ?? []) {
    /** @param {string} code @param {string} message @param {(string|number)[]} [sub] */
    const err = (code, message, sub = []) => out.push({ code, severity: 'error', message, entityId: lang.id, loc: lang.loc, path: [...lang.path, ...sub] });
    checkLanguage(model, lang, err);
  }
  return out;
}

/**
 * @param {Model} model @param {Entity} lang
 * @param {(code: string, message: string, sub?: (string|number)[]) => void} err
 */
function checkLanguage(model, lang, err) {
  const d = lang.data;
  const L = `language "${lang.id}"`;

  // Shapes.
  const shapes = new Set();
  list(d.shapes).forEach((s, i) => {
    if (typeof s !== 'string' || !s) err('language.shape-unknown', `Shape ${i + 1} of ${L} needs a name.`, ['shapes', i]);
    else if (shapes.has(s)) err('language.shape-unknown', `${L} names the shape "${s}" twice.`, ['shapes', i]);
    else shapes.add(s);
  });
  if (!shapes.size) err('language.shape-unknown', `${L} declares no "shapes".`, ['shapes']);
  if (d.anyShape !== undefined && !shapes.has(d.anyShape)) err('language.shape-unknown', `The anyShape ${show(d.anyShape)} of ${L} is not one of its shapes.`, ['anyShape']);
  /** @param {any} s @param {(string|number)[]} at @param {string} what */
  const shape = (s, at, what) => {
    if (typeof s !== 'string' || !shapes.has(s)) err('language.shape-unknown', `${what} names the shape ${show(s)}, which is not one of the shapes of ${L} (${[...shapes].join(', ')}).`, at);
  };

  // AST and values.
  const ast = unionType(model, d.ast);
  if (!ast && typeof d.ast === 'string' && model.entities.get(d.ast)?.kind === 'type') err('language.variant', `The ast of ${L}, "${d.ast}", is not a union type; the AST is the union of the expression forms.`, ['ast']);
  if (!unionType(model, d.values) && typeof d.values === 'string' && model.entities.get(d.values)?.kind === 'type') err('language.variant', `The values of ${L}, "${d.values}", is not a union type; the values are the union of what an expression evaluates to.`, ['values']);
  const astVariants = new Map(list(ast?.data.variants).filter(isObj).map((v) => [v.name, v]));

  // Scopes.
  /** @type {Map<string, any>} */
  const scopes = new Map();
  /** @type {Map<string, string>} */
  const scopeValues = new Map();
  list(d.scopes).forEach((s, i) => {
    const at = ['scopes', i];
    if (!isObj(s)) return;
    if (typeof s.name !== 'string' || !WORD_RE.test(s.name)) { err('language.scope', `Scope ${i + 1} of ${L} needs a name that is a word (${show(s.name)}).`, [...at, 'name']); return; }
    if (scopes.has(s.name)) err('language.scope', `${L} declares the scope "${s.name}" twice.`, [...at, 'name']);
    scopes.set(s.name, s);
    if (s.kind !== 'record-scope' && s.attributes !== undefined) err('language.scope', `Scope "${s.name}" of ${L} is a ${s.kind} and has "attributes"; only a record-scope has system attributes.`, [...at, 'attributes']);
    if (s.kind !== 'record-scope' && s.value !== undefined) err('language.scope', `Scope "${s.name}" of ${L} is a ${s.kind} and has a "value"; only a record-scope stands for a value of the AST's scope field.`, [...at, 'value']);
    if (s.kind === 'record-scope' && typeof s.value === 'string') {
      const first = scopeValues.get(s.value);
      if (first !== undefined) err('language.scope', `Scopes "${first}" and "${s.name}" of ${L} both stand for "${s.value}".`, [...at, 'value']);
      else scopeValues.set(s.value, s.name);
    }
    const attrs = new Set();
    list(s.attributes).forEach((a, j) => {
      const aat = [...at, 'attributes', j];
      if (!isObj(a) || typeof a.name !== 'string' || !ATTRIBUTE_RE.test(a.name)) { err('language.scope', `Attribute ${j + 1} of scope "${s.name}" of ${L} needs a name that starts with $ (${show(a?.name)}).`, aat); return; }
      if (attrs.has(a.name)) err('language.scope', `Scope "${s.name}" of ${L} has the attribute "${a.name}" twice.`, [...aat, 'name']);
      attrs.add(a.name);
      shape(a.shape, [...aat, 'shape'], `Attribute "${a.name}" of scope "${s.name}"`);
    });
  });
  const recordScopes = [...scopes.values()].filter((s) => s.kind === 'record-scope');
  if (recordScopes.some((s) => s.value !== undefined) && recordScopes.some((s) => s.value === undefined)) {
    err('language.scope', `Some record scopes of ${L} state a "value" and some do not; state it on all of them or none.`, ['scopes']);
  }
  /** @type {Set<string>} */
  const readScopes = new Set();

  // Operators.
  const names = new Set();
  /** @type {Map<string, string>} */
  const claimedBy = new Map();
  /** @param {string} w @param {string} who @param {(string|number)[]} at */
  const claim = (w, who, at) => {
    const first = claimedBy.get(w);
    if (first !== undefined) err('language.token-clash', `${who} of ${L} claims "${w}", which ${first} already claims.`, at);
    else claimedBy.set(w, who.replace(/^Operator/, 'operator'));
  };
  for (const s of scopes.values()) claimedBy.set(s.name, `scope "${s.name}"`);
  /** @type {Map<number, {assoc: any, name: string}>} */
  const levels = new Map();
  /** @type {Map<string, {cased: boolean, field?: any, values: Map<string, string>, plain?: string}>} */
  const covered = new Map();

  list(d.operators).forEach((op, i) => {
    const at = ['operators', i];
    if (!isObj(op)) return;
    const who = `Operator "${op.name}"`;
    if (names.has(op.name)) err('language.operator-duplicate', `${L} has the operator "${op.name}" twice.`, [...at, 'name']);
    names.add(op.name);
    const syn = isObj(op.syntax) ? op.syntax : {};
    const form = syn.form;
    const prim = typeof op.primitive === 'string' ? LANGUAGE_PRIMITIVES[op.primitive] : undefined;
    if (op.primitive !== undefined && !(typeof op.primitive === 'string' && Object.hasOwn(LANGUAGE_PRIMITIVES, op.primitive))) {
      err('language.primitive-unknown', `${who} of ${L} names the primitive ${show(op.primitive)}, which is not in the catalogue (${Object.keys(LANGUAGE_PRIMITIVES).join(', ')}).`, [...at, 'primitive']);
    }

    // Syntax: tokens and lexical classes.
    const binary = form === 'infix' || form === 'keyword-infix';
    const sat = [...at, 'syntax'];
    if (form === 'infix') {
      if (typeof syn.token !== 'string' || !SYMBOL_RE.test(syn.token) || RESERVED_SYMBOLS.includes(syn.token)) err('language.syntax', `${who} of ${L} is infix and needs a symbol token made of = ! < > + - * / % & | ^ ~ ? : (found ${show(syn.token)}).`, [...sat, 'token']);
      else claim(syn.token, who, [...sat, 'token']);
    } else if (form === 'keyword-infix' || form === 'prefix-word' || form === 'call') {
      if (typeof syn.token !== 'string' || !WORD_RE.test(syn.token)) err('language.syntax', `${who} of ${L} is ${form} and needs a word token (found ${show(syn.token)}).`, [...sat, 'token']);
      else claim(syn.token, who, [...sat, 'token']);
    } else if (form === 'literal') {
      if (typeof syn.token !== 'string' || !Object.hasOwn(LITERAL_FORMS, syn.token)) err('language.syntax', `${who} of ${L} is a literal and its token names a literal form (${Object.keys(LITERAL_FORMS).join(', ')}); found ${show(syn.token)}.`, [...sat, 'token']);
      else {
        claim(`literal:${syn.token}`, who, [...sat, 'token']);
        for (const w of LITERAL_FORMS[syn.token]) claim(w, who, [...sat, 'token']);
        if (prim?.literal !== undefined && !prim.literal.split(' ').includes(syn.token)) err('language.syntax', `${who} of ${L} is the ${syn.token} literal form, which primitive "${op.primitive}" does not write (it writes ${prim.literal.split(' ').join(', ')}).`, [...sat, 'token']);
      }
    }
    if (prim && typeof form === 'string' && !prim.forms.includes(form)) err('language.syntax', `${who} of ${L} is written in the ${form} form, but primitive "${op.primitive}" is written ${prim.forms.join(' or ')} only.`, [...sat, 'form']);

    // Scope-form operators read scopes.
    if (form === 'scope' && prim?.scope !== undefined) {
      if (prim.scope === 'record-scope') {
        if (syn.token !== undefined) err('language.scope', `${who} of ${L} reads every record scope and takes no token.`, [...sat, 'token']);
        if (!recordScopes.length) err('language.scope', `${who} of ${L} reads record scopes, but the language declares none.`, [...at, 'primitive']);
        for (const s of recordScopes) readScopes.add(s.name);
      } else {
        const s = typeof syn.token === 'string' ? scopes.get(syn.token) : undefined;
        if (!s || s.kind !== prim.scope) err('language.scope', `${who} of ${L} reads a ${prim.scope} scope and its token names one; found ${show(syn.token)}${s ? `, a ${s.kind}` : ''}.`, [...sat, 'token']);
        else readScopes.add(s.name);
      }
    }

    // Precedence and associativity.
    const prefix = form === 'prefix-word';
    if (binary || prefix) {
      if (!Number.isInteger(syn.precedence) || syn.precedence < 1) err('language.precedence', `${who} of ${L} is ${form} and needs a "precedence", a positive integer (higher binds tighter).`, [...sat, 'precedence']);
    } else if (syn.precedence !== undefined) err('language.precedence', `${who} of ${L} is ${form === undefined ? 'of no form' : `a ${form}`}, a primary, and takes no precedence.`, [...sat, 'precedence']);
    if (binary) {
      if (syn.assoc === undefined) err('language.precedence', `${who} of ${L} is ${form} and needs an "assoc" (${ASSOCIATIVITY.join(', ')}).`, [...sat, 'assoc']);
      else if (Number.isInteger(syn.precedence)) {
        const lv = levels.get(syn.precedence);
        if (lv && lv.assoc !== syn.assoc) err('language.precedence', `${who} of ${L} groups ${syn.assoc} at precedence ${syn.precedence}, where operator "${lv.name}" groups ${lv.assoc}; one level has one associativity.`, [...sat, 'assoc']);
        else if (!lv) levels.set(syn.precedence, { assoc: syn.assoc, name: op.name });
      }
    } else if (syn.assoc !== undefined) err('language.precedence', `${who} of ${L} is not binary and takes no "assoc".`, [...sat, 'assoc']);

    // Nulls.
    if (prim && op.nulls !== undefined && op.nulls !== prim.nulls) err('language.nulls', `${who} of ${L} says its null handling is "${op.nulls}", but primitive "${op.primitive}" is "${prim.nulls}".`, [...at, 'nulls']);

    // Operands and result.
    const operands = list(op.operands);
    operands.forEach((o, j) => {
      const what = `Operand ${j + 1} of operator "${op.name}"`;
      if (Array.isArray(o)) {
        if (!o.length) err('language.shape-unknown', `${what} lists no shapes.`, [...at, 'operands', j]);
        o.forEach((s, k) => shape(s, [...at, 'operands', j, k], what));
      } else shape(o, [...at, 'operands', j], what);
    });
    // One arity finding per operator: the later comparisons would only restate the first.
    let arityFound = false;
    /** @param {string} message @param {(string|number)[]} sub */
    const arityErr = (message, sub) => { if (!arityFound) err('language.arity', message, sub); arityFound = true; };
    const nary = syn.assoc === 'n-ary';
    const count = nary ? 'n' : operands.length;
    if (nary && operands.length !== 1) arityErr(`${who} of ${L} is n-ary and states one operand shape, which every item has; it states ${operands.length}.`, [...at, 'operands']);
    if (nary && form !== 'keyword-infix' && form !== 'infix') arityErr(`${who} of ${L} is n-ary, which only a binary form can be.`, [...sat, 'assoc']);
    if (prim) {
      if (prim.arity !== count) arityErr(`${who} of ${L} has ${count === 'n' ? 'a list of' : count} operand${count === 1 ? '' : 's'}, but primitive "${op.primitive}" takes ${prim.arity === 'n' ? 'a list (an n-ary operator)' : prim.arity}.`, [...at, 'operands']);
    } else {
      const need = binary ? (nary ? 'n' : 2) : prefix ? 1 : form === 'literal' || form === 'scope' ? 0 : undefined;
      if (need !== undefined && need !== count) arityErr(`${who} of ${L} is ${form} and has ${count === 'n' ? 'a list of operands' : count} operand${count === 1 ? '' : 's'}; the form takes ${need === 'n' ? 'a list' : need}.`, [...at, 'operands']);
    }
    if (op.result !== undefined) {
      const m = typeof op.result === 'string' ? OPERAND_REF_RE.exec(op.result) : null;
      if (m) {
        if (count === 'n' ? Number(m[1]) !== 1 : Number(m[1]) > count) arityErr(`${who} of ${L} gives the shape of ${op.result}, but it has ${count === 'n' ? 'one operand shape' : `${count} operand${count === 1 ? '' : 's'}`}.`, [...at, 'result']);
      } else shape(op.result, [...at, 'result'], `The result of operator "${op.name}"`);
    }

    // The AST variant, its case, and its expression fields.
    if (!ast || typeof op.variant !== 'string') return;
    const v = astVariants.get(op.variant);
    if (!v) { err('language.variant', `${who} of ${L} names the variant "${op.variant}", which the AST "${ast.id}" does not have.`, [...at, 'variant']); return; }
    const fields = variantOperandCount(v, ast.id);
    if (fields !== count) arityErr(`${who} of ${L} has ${count === 'n' ? 'a list of operands' : `${count} operand${count === 1 ? '' : 's'}`}, but AST variant "${v.name}" holds ${fields === 'n' ? `a list<${ast.id}>` : `${fields} ${ast.id} field${fields === 1 ? '' : 's'}`}.`, [...at, 'operands']);
    /** @type {{cased: boolean, field?: any, values: Map<string, string>, plain?: string}} */
    const entry = covered.get(v.name) ?? { cased: op.case !== undefined, values: new Map() };
    covered.set(v.name, entry);
    if (op.case === undefined) {
      if (entry.cased || entry.plain !== undefined) err('language.variant', `${who} of ${L} is a second operator for AST variant "${v.name}" (with "${entry.plain ?? [...entry.values.values()][0]}"); a variant has one operator, or one per case.`, [...at, 'variant']);
      else entry.plain = op.name;
      return;
    }
    const c = isObj(op.case) ? op.case : {};
    const allowed = caseValues(model, v, c.field);
    if (!allowed) { err('language.variant', `${who} of ${L} splits AST variant "${v.name}" on ${show(c.field)}, which is not a field of the variant typed as an enum or a union.`, [...at, 'case', 'field']); return; }
    if (!allowed.includes(c.value)) { err('language.variant', `${who} of ${L} is the case ${show(c.value)} of field "${c.field}" of AST variant "${v.name}", which is not one of ${allowed.join(', ')}.`, [...at, 'case', 'value']); return; }
    if (!entry.cased || (entry.field !== undefined && entry.field !== c.field)) { err('language.variant', `${who} of ${L} splits AST variant "${v.name}" differently from the other operators of that variant; a variant has one operator, or one per case of one field.`, [...at, 'case']); return; }
    entry.field = c.field;
    const first = entry.values.get(c.value);
    if (first !== undefined) err('language.variant', `${who} of ${L} is a second operator for case "${c.value}" of AST variant "${v.name}" (with "${first}").`, [...at, 'case', 'value']);
    else entry.values.set(c.value, op.name);
  });

  for (const s of scopes.values()) {
    if (!readScopes.has(s.name)) err('language.scope', `Scope "${s.name}" of ${L} is read by no operator.`, ['scopes', list(d.scopes).indexOf(s)]);
  }
}

/**
 * Readiness of languages: complete enough to generate a parser, printer, checker and evaluator from.
 * @param {Model} model @returns {Gap[]}
 */
export function languageReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const lang of model.byKind.language ?? []) {
    const gap = (/** @type {string} */ code, /** @type {string} */ message) => out.push({ code, severity: 'error', message, entityId: lang.id });
    const ops = list(lang.data.operators).filter(isObj);
    for (const op of ops) {
      if (op.primitive === undefined) gap('ready.language-primitive-missing', `Operator "${op.name}" of language "${lang.id}" names no primitive, so nothing says what it means.`);
    }
    const ast = unionType(model, lang.data.ast);
    for (const v of list(ast?.data.variants).filter(isObj)) {
      const mine = ops.filter((op) => op.variant === v.name);
      if (!mine.length) { gap('ready.language-variant-uncovered', `AST variant "${v.name}" of language "${lang.id}" has no operator, so it can be neither parsed nor printed.`); continue; }
      const cased = mine.filter((op) => isObj(op.case));
      if (!cased.length) continue;
      const field = cased[0].case.field;
      const allowed = caseValues(model, v, field) ?? [];
      const have = new Set(cased.map((op) => op.case.value));
      for (const value of allowed) if (!have.has(value)) gap('ready.language-variant-uncovered', `Case "${value}" of field "${field}" of AST variant "${v.name}" of language "${lang.id}" has no operator.`);
    }
  }
  return out;
}
