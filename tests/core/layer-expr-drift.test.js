// The product-expression parser (src/core/layer-expr.js, WG-5120) against the language a specification declares.
//
// layer-expr.js keeps its own parser of the tenant rule language, because language.js and language-eval.js work on an
// AST value, never on text. The two were once written in parallel and drifted: nine operators the language gained
// were refused as layer.expr-syntax in product files. So two tests hold them together.
//
//   drift   for each operator a language entity declares (the fixture language, and Strata's platform language when
//           its specification is at the path below), a probe is built from the declared form, token and operand
//           shapes: an accepted text per accepted operand shape, a refused one per shape the operand does not accept,
//           and the associativity and precedence. An operator layer-expr.js does not parse and type as declared fails.
//   corpus  the checked cases of the shared table (tests/fixtures/language/kernel-cases.json), each given as the
//           authoring text and the AST value: layer-expr.js on the text and language-eval.js on the value must agree
//           on accept or refuse, on the shape of the result, and on the message of a type error.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { checkLanguage, printLanguage } from '../../src/core/language-eval.js';
import { decodeValue } from '../../src/core/function-value.js';
import { typeStructure } from '../../src/core/codegen-model.js';
import { typeExpressionText } from '../../src/core/layer-expr.js';
import { spec } from '../fixtures/language/fixtures.js';
import { spec as functionsSpec } from '../fixtures/functions/fixtures.js';

const STRATA_SPEC = 'C:/dev/strata-int3-kernel/specifications/spec.jsonc';
const TABLE = JSON.parse(fs.readFileSync(new URL('../fixtures/language/kernel-cases.json', import.meta.url), 'utf8'));

/** The environment of a text: no fields, no params, no roles. */
const bare = () => ({ fields: new Map(), params: new Set(), roles: new Set(), objects: new Map() });

/** A shape as the kernel prints it in a message. @param {string} s */
const pascal = (s) => s[0].toUpperCase() + s.slice(1);

/** The languages a specification declares. @param {any} model @returns {any[]} */
const languagesOf = (model) => [...model.entities.values()].filter((e) => e.kind === 'language');

/** One literal text per shape. */
const SAMPLE = { bool: 'true', int: '1', str: "'a'", time: 'time(1)', ref: 'ref(1)', list: '[1]' };
/** @param {string} shape */
const sample = (shape) => SAMPLE[/** @type {keyof typeof SAMPLE} */ (shape)];

/**
 * The probes of one operator. An operand is a shape or a list of the shapes it accepts; `any` accepts every shape.
 * Each probe puts one shape at one operand; the other operands take their first accepted shape (an operand that takes
 * any follows the operand before it, so contains and if stay well typed).
 * @param {any} lang @param {any} op
 * @returns {{text: string, accept: boolean, result?: string, shape?: string}[]}
 */
function probesOf(lang, op) {
  const any = lang.data.anyShape;
  const all = /** @type {string[]} */ (lang.data.shapes).filter((s) => s !== any);
  const form = op.syntax?.form;
  const token = op.syntax?.token;
  /** @type {string[][]} */
  let operands = (op.operands ?? []).map((/** @type {any} */ o) => (Array.isArray(o) ? o : [o]));
  if (op.syntax?.assoc === 'n-ary' && operands.length === 1) operands = [operands[0], operands[0]];
  /** @param {string[]} shapes */
  const text = (shapes) => {
    const parts = shapes.map(sample);
    if (form === 'infix' || form === 'keyword-infix') return parts.join(` ${token} `);
    if (form === 'prefix-word') return `${token} ${parts[0]}`;
    return `${token}(${parts.join(', ')})`;
  };
  /** @param {number} k @param {string[]} chosen */
  const dflt = (k, chosen) => {
    if (!operands[k].includes(any)) return operands[k][0];
    const before = chosen[k - 1];
    return before === undefined || before === 'bool' ? 'int' : before;
  };
  /** @param {string[]} chosen */
  const resultOf = (chosen) => {
    const m = typeof op.result === 'string' ? /^operand:([1-9][0-9]*)$/.exec(op.result) : null;
    return m ? chosen[Number(m[1]) - 1] : op.result;
  };
  /** @type {{text: string, accept: boolean, result?: string, shape?: string}[]} */
  const out = [];
  for (let k = 0; k < operands.length; k++) {
    if (operands[k].includes(any)) continue;
    for (const shape of all) {
      /** @type {string[]} */
      const chosen = [];
      for (let j = 0; j < operands.length; j++) chosen.push(j === k ? shape : dflt(j, chosen));
      // A comparison needs both sides of one shape.
      if (/^(eq|ne|lt|le|gt|ge)$/.test(op.primitive)) for (let j = 0; j < operands.length; j++) if (j !== k) chosen[j] = shape;
      if (operands[k].includes(shape)) out.push({ text: text(chosen), accept: true, result: resultOf(chosen) });
      else out.push({ text: text(chosen), accept: false, shape });
    }
  }
  if (operands.every((o) => o.includes(any))) {
    /** @type {string[]} */
    const chosen = [];
    for (let j = 0; j < operands.length; j++) chosen.push(dflt(j, chosen));
    out.push({ text: text(chosen), accept: true, result: resultOf(chosen) });
  }
  return out;
}

/**
 * The probes of the way operators bind, from their declared precedence and associativity.
 * @param {any} lang
 * @returns {{text: string, accept: boolean, syntax?: boolean}[]}
 */
function bindingProbes(lang) {
  const any = lang.data.anyShape;
  /** @type {{text: string, accept: boolean, syntax?: boolean}[]} */
  const out = [];
  const infix = lang.data.operators.filter((/** @type {any} */ o) => o.syntax?.form === 'infix' && Array.isArray(o.operands) && o.operands.length === 2);
  /** @param {any} o @returns {string[][]} */
  const sets = (o) => o.operands.map((/** @type {any} */ x) => (Array.isArray(x) ? x : [x]));
  for (const op of infix) {
    const [l, r] = sets(op);
    const token = op.syntax.token;
    if (op.syntax.assoc === 'none') {
      const a = sample(l.find((s) => s !== any) ?? 'int');
      out.push({ text: `${a} ${token} ${a} ${token} ${a}`, accept: false, syntax: true });
    }
    if (op.syntax.assoc === 'left' && l.includes('int') && r.includes('int') && op.result !== 'bool') out.push({ text: `1 ${token} 1 ${token} 1`, accept: true });
  }
  // Of two infix operators of different precedence the tighter binds first. With a time in front, a sum can only be
  // read as time + (1 * 2); (time + 1) * 2 and (time * 1) + 2 are type errors.
  for (const lo of infix) for (const hi of infix) {
    const [l1, r1] = sets(lo), [l2, r2] = sets(hi);
    if (lo.syntax.precedence >= hi.syntax.precedence || lo.result === 'bool' || hi.result === 'bool') continue;
    if (!(l1.includes('time') && r1.includes('int') && l2.length === 1 && l2[0] === 'int' && r2.length === 1 && r2[0] === 'int')) continue;
    out.push({ text: `time(1) ${lo.syntax.token} 1 ${hi.syntax.token} 2`, accept: true });
    out.push({ text: `time(1) ${hi.syntax.token} 1 ${lo.syntax.token} 2`, accept: false });
  }
  return out;
}

/** The literal and scope tokens layer-expr.js reads, with a text for each. */
const LITERALS = { null: 'null', bool: 'true', int: '1', string: "'a'", time: 'time(1)', ref: 'ref(1)', list: '[1, 2]' };
const SCOPES = { param: 'param.p', now: 'now', principal: 'principal', has_role: 'has_role(r)' };

/** Probe every operator of a language; throws on the first one layer-expr.js does not parse and type as declared. @param {any} lang @param {string} where */
function holdsLanguage(lang, where) {
  const ops = /** @type {any[]} */ (lang.data.operators);
  assert.ok(ops.length > 0, `${where}: operators declared`);
  const scoped = { ...bare(), params: new Set(['p']), roles: new Set(['r']) };
  for (const op of ops) {
    const form = op.syntax?.form;
    if (form === 'scope' && op.syntax.token === undefined) continue; // var and through: the record scopes
    if (form === 'literal' || form === 'scope') {
      const table = /** @type {Record<string, string>} */ (form === 'literal' ? LITERALS : SCOPES);
      const text = table[op.syntax.token];
      assert.ok(text !== undefined, `${where}: ${op.name}: the ${form} ${op.syntax.token} is not one layer-expr.js knows`);
      const r = typeExpressionText(text, scoped);
      assert.equal(r.problem, undefined, `${where}: ${op.name}: ${text}: ${r.problem?.message}`);
      assert.equal(r.shape, op.result, `${where}: ${op.name}: ${text}`);
      continue;
    }
    for (const p of probesOf(lang, op)) {
      const r = typeExpressionText(p.text, bare());
      const label = `${where}: ${op.name} (${op.syntax?.token}): ${p.text}`;
      if (p.accept) {
        assert.equal(r.problem, undefined, `${label} is declared accepted, layer-expr.js says: ${r.problem?.message}`);
        assert.equal(r.shape, p.result, `${label}: declared result`);
      } else {
        assert.equal(r.problem?.code, 'layer.expr-type', `${label}: a ${p.shape} operand is declared refused, got ${JSON.stringify(r)}`);
        assert.match(r.problem.message, new RegExp(`(does not accept a ${pascal(String(p.shape))} operand|^cannot compare )`), label);
      }
    }
  }
  for (const p of bindingProbes(lang)) {
    const r = typeExpressionText(p.text, bare());
    assert.equal(r.problem === undefined, p.accept, `${where}: ${p.text}: ${JSON.stringify(r)}`);
    if (p.syntax) assert.equal(r.problem?.code, 'layer.expr-syntax', `${where}: ${p.text}`);
  }
}

// Every operator the fixture language declares is parsed and typed as declared.
// @evidence product-layers-expressions
test('layer-expr.js parses and types every operator the fixture language declares', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const [lang] = languagesOf(model);
  assert.ok(lang);
  holdsLanguage(lang, 'fixture');
});

// The probe fails for an operator layer-expr.js lacks.
// @evidence product-layers-expressions
test('the probe fails for an operator layer-expr.js lacks and for one it types differently', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const lang = structuredClone(languagesOf(model)[0]);
  lang.data.operators.push({ name: 'abs', variant: 'Abs', syntax: { form: 'call', token: 'abs' }, operands: ['int'], result: 'int', nulls: 'propagate', primitive: 'abs' });
  assert.throws(() => holdsLanguage(lang, 'mutant'), /abs/);
  const wrong = structuredClone(languagesOf(model)[0]);
  wrong.data.operators.find((/** @type {any} */ o) => o.name === 'concat').operands = ['str', 'int'];
  assert.throws(() => holdsLanguage(wrong, 'mutant'), /concat/);
  const loose = structuredClone(languagesOf(model)[0]);
  loose.data.operators.find((/** @type {any} */ o) => o.name === 'mul').syntax.precedence = 5;
  assert.doesNotThrow(() => holdsLanguage(loose, 'mutant'), 'equal precedence has no probe');
});

// The same probe over the Strata platform language, when its specification is present.
// @evidence product-layers-expressions
test('layer-expr.js parses and types every operator the Strata platform declares', { skip: !fs.existsSync(STRATA_SPEC) }, () => {
  const model = /** @type {any} */ (analyzeSpec(fs.readFileSync(STRATA_SPEC, 'utf8')).model);
  const langs = languagesOf(model);
  assert.ok(langs.length > 0, 'the platform declares a language');
  for (const lang of langs) {
    // balance, in_segment and setting name a unit, a segment or a setting of the platform: a product expression has no
    // such call (specc's layer_expr.rs refuses them as well), so they are not probed.
    const own = { ...lang, data: { ...lang.data, operators: lang.data.operators.filter((/** @type {any} */ o) => !['balance', 'in-segment', 'setting'].includes(o.name)) } };
    holdsLanguage(own, lang.id);
  }
});

// layer-expr.js and the language checker agree on every checked case.
// @evidence product-layers-expressions
test('layer-expr.js and the language checker agree on every checked case of the shared table', () => {
  const model = /** @type {any} */ (analyzeSpec(functionsSpec()).model);
  const [lang] = languagesOf(model);
  const exprT = typeStructure(model, 'expr');
  const checkEnvT = typeStructure(model, 'check-env');
  assert.ok(TABLE.check.length >= 30);
  for (const c of TABLE.check) {
    const e = decodeValue(exprT, c.expr, 'expr');
    const env = decodeValue(checkEnvT, { fields: {}, params: [], roles: [], ...c.env }, 'env');
    const reference = checkLanguage(model, lang, e, env);
    const fields = new Map(Object.entries(c.env.fields ?? {}).map(([name, shape]) => [name, { shape: String(shape), target: shape === 'ref' ? 'target' : null }]));
    const own = typeExpressionText(printLanguage(model, lang, e), { fields, params: new Set(c.env.params ?? []), roles: new Set(c.env.roles ?? []), objects: new Map([['target', new Map()]]) });
    const label = `${c.name}: ${c.source}`;
    if (reference.variant === 'Ok') {
      assert.equal(own.problem, undefined, `${label}: ${own.problem?.message}`);
      assert.equal(own.shape, reference.fields.value, label);
    } else {
      assert.ok(own.problem, `${label}: language.js refuses with "${reference.fields.error}", layer-expr.js accepts`);
      const typeError = /(does not accept a \w+ operand|^cannot compare|branches differ|is not a single reference)/.test(reference.fields.error);
      assert.equal(own.problem.code === 'layer.expr-type', typeError, `${label}: ${own.problem.code} ${own.problem.message} against ${reference.fields.error}`);
      if (typeError) assert.equal(own.problem.message, reference.fields.error, label);
    }
  }
});
