// Readiness rules for implementation-level state machines (behaviors with `level: "implementation"`).
// A machine at this level is one a code generator could turn into code: every variable has a
// representation, every receiver and delivery guarantee is named, and every (state, event) pair has an
// outcome. The rules are checks over the model; they never change simulation (docs/semantics.md).
// Diagnostic codes start with `ready.`, except machine.initial-unreachable (a shipped machine whose initial
// state the runtime cannot reproduce, WG-4903); see docs/semantics.md, "Implementation-level properties" and
// "Faults the runtime can produce".

import { typeResolves, unsharedText } from './codegen-model.js';
import { parseExpr, exprRefs } from './expr.js';
import { timeReadiness, scenarioIntegerReadiness } from './readiness-time.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

export { typeResolves };

/**
 * A record field's type split into whether it may be unset and the type it holds when set: a field that is
 * `optional` or whose type is `option<T>` is optional with base T.
 * @param {any} field
 * @returns {{optional: boolean, base: string}}
 */
export function fieldBase(field) {
  let base = typeof field?.type === 'string' ? unsharedText(field.type) : '';
  let optional = field?.optional === true;
  const m = /^option<(.+)>$/.exec(base);
  if (m) { optional = true; base = m[1].trim(); }
  return { optional, base };
}

/**
 * Whether a variable of representation `repr` can be held in a record field: the field's type is the repr, or a
 * declared id or scalar type whose repr is the variable's repr, in either case optional or not; a variable of
 * repr option<T> needs an optional field of type T.
 * @param {Model} model @param {string} repr @param {any} field
 * @returns {boolean}
 */
export function reprFitsField(model, repr, field) {
  const r = repr.trim();
  const { optional, base } = fieldBase(field);
  const opt = /^option<(.+)>$/.exec(r);
  if (opt) return optional && base === opt[1].trim();
  if (base === r) return true;
  const e = model.entities.get(base);
  return !!e && e.kind === 'type' && (e.data.kind === 'id' || e.data.kind === 'scalar') && typeof e.data.repr === 'string' && e.data.repr.trim() === r;
}

/**
 * The fields a machine's key names: `storage.key` / `instances.key` is one field name, or, for a record with a
 * composite key, the list of its key fields. Null when it is neither a non-empty string nor a list of strings.
 * @param {any} key @returns {string[] | null}
 */
export function keyFieldsOf(key) {
  if (typeof key === 'string') return [key];
  if (Array.isArray(key) && key.length > 0 && key.every((k) => typeof k === 'string')) return key;
  return null;
}

/**
 * The storage-field rules of one implementation-level machine held in `record`: `storage.fields` (variable to
 * record field, default the field of the same name), `storage.state` (default "state"), `storage.stateValues`
 * and `storage.creates` (default false).
 * @param {Model} model @param {Entity} b @param {Entity} record @param {any} st @param {any} keyField
 * @param {Entity[]} states
 * @param {(code: string, entity: Entity, message: string, sub?: (string|number)[]) => void} report
 */
function checkStorageFields(model, b, record, st, keyField, states, report) {
  const list = (/** @type {any} */ v) => (Array.isArray(v) ? v : []);
  const isMap = (/** @type {any} */ v) => !!v && typeof v === 'object' && !Array.isArray(v);
  /** @type {Map<string, any>} */
  const fields = new Map(list(record.data.fields).filter((f) => f && typeof f.name === 'string').map((f) => [f.name, f]));
  const variables = list(b.data.variables).filter((v) => v && typeof v.name === 'string');
  const varNames = new Set(variables.map((v) => v.name));
  const explicit = isMap(st.fields) ? st.fields : {};

  // What each record field holds: the key, a variable, the state.
  /** @type {Map<string, string>} */
  const owned = new Map();
  for (const k of keyFieldsOf(keyField) ?? []) owned.set(k, 'the key');

  for (const [v, f] of Object.entries(explicit)) {
    if (!varNames.has(v)) report('ready.storage-field-unknown', b, `storage.fields of "${b.id}" maps "${v}", which is not one of its variables.`, ['storage', 'fields', v]);
    else if (typeof f !== 'string' || !fields.has(f)) report('ready.storage-field-unknown', b, `storage.fields of "${b.id}" maps variable "${v}" to ${typeof f === 'string' ? `"${f}"` : 'a non-string'}, which is not a field of record "${record.id}".`, ['storage', 'fields', v]);
  }
  variables.forEach((v) => {
    const i = list(b.data.variables).indexOf(v);
    const mapped = Object.hasOwn(explicit, v.name);
    const f = mapped ? explicit[v.name] : v.name;
    if (mapped && (typeof f !== 'string' || !fields.has(f))) return; // reported above
    if (!fields.has(f)) {
      report('ready.storage-variable-unmapped', b, `Variable "${v.name}" of "${b.id}" is held in no field of record "${record.id}": the record has no field "${v.name}" and storage.fields does not map the variable.`, ['variables', i]);
      return;
    }
    const taken = owned.get(f);
    if (taken) {
      report('ready.storage-field-unknown', b, `Field "${f}" of record "${record.id}" already holds ${taken}, so variable "${v.name}" of "${b.id}" cannot be held there too.`, mapped ? ['storage', 'fields', v.name] : ['variables', i]);
      return;
    }
    owned.set(f, `variable "${v.name}"`);
    if (typeof v.repr === 'string' && typeResolves(model, v.repr) && !reprFitsField(model, v.repr, fields.get(f))) {
      const { optional, base } = fieldBase(fields.get(f));
      report('ready.storage-field-type', b, `Variable "${v.name}" of "${b.id}" has repr "${v.repr}", but field "${f}" of record "${record.id}" holds ${optional ? 'an optional ' : ''}"${base}".`, ['variables', i, 'repr']);
    }
  });

  // The state: stored when the machine says where, or has more than one state, or the record has a free "state" field.
  const stateField = typeof st.state === 'string' ? st.state : 'state';
  const stateValues = isMap(st.stateValues) ? st.stateValues : undefined;
  const storesState = typeof st.state === 'string' || stateValues !== undefined || states.length > 1 || (fields.has('state') && !owned.has('state'));
  if (storesState) {
    const problem = stateFieldProblem(model, b, record, fields, stateField, stateValues, owned, states);
    if (problem) report('ready.storage-state-field', b, problem, ['storage', typeof st.state === 'string' ? 'state' : stateValues ? 'stateValues' : 'record']);
    else owned.set(stateField, 'the state');
  }

  // A creating machine writes whole records; a non-creating one carries over what it does not hold.
  if (st.creates === true) {
    for (const f of fields.values()) {
      if (fieldBase(f).optional || owned.has(f.name) || (storesState && f.name === stateField)) continue;
      report('ready.storage-creates-unfilled', b, `"${b.id}" creates records of "${record.id}" (storage.creates), but required field "${f.name}" is neither its key, its state nor one of its variables, so a new record would leave it unset.`, ['storage', 'creates']);
    }
  }
}

/**
 * Why the state of `b` cannot be held in `stateField` of `record`, or undefined when it can.
 * @param {Model} model @param {Entity} b @param {Entity} record @param {Map<string, any>} fields
 * @param {string} stateField @param {any} stateValues @param {Map<string, string>} owned @param {Entity[]} states
 * @returns {string | undefined}
 */
function stateFieldProblem(model, b, record, fields, stateField, stateValues, owned, states) {
  const f = fields.get(stateField);
  if (!f) return `Record "${record.id}" has no field "${stateField}" to hold the state of "${b.id}" (storage.state names the field; default "state").`;
  const taken = owned.get(stateField);
  if (taken) return `Field "${stateField}" of record "${record.id}" holds ${taken}, so it cannot also hold the state of "${b.id}".`;
  const { optional, base } = fieldBase(f);
  const t = model.entities.get(base);
  const isEnum = !!t && t.kind === 'type' && t.data.kind === 'enum';
  if (optional) return `Field "${stateField}" of record "${record.id}" is optional; the state of "${b.id}" needs a required field.`;
  if (base !== 'string' && !isEnum) return `Field "${stateField}" of record "${record.id}" has type "${base}"; the state of "${b.id}" is held in a string or an enum field.`;
  const ids = states.map((s) => s.id);
  if (stateValues) {
    for (const [k, v] of Object.entries(stateValues)) {
      if (!ids.includes(k)) return `storage.stateValues of "${b.id}" names "${k}", which is not one of its states.`;
      if (typeof v !== 'string') return `storage.stateValues of "${b.id}" gives state "${k}" a value that is not a string.`;
    }
  }
  const stored = ids.map((id) => (stateValues && typeof stateValues[id] === 'string' ? stateValues[id] : id));
  const dup = stored.find((v, i) => stored.indexOf(v) !== i);
  if (dup !== undefined) return `Two states of "${b.id}" would be stored as "${dup}" in field "${stateField}", so the state could not be read back.`;
  if (isEnum) {
    const values = Array.isArray(t.data.values) ? t.data.values : [];
    const missing = ids.filter((_, i) => !values.includes(stored[i]));
    if (missing.length) return `Field "${stateField}" of record "${record.id}" is enum "${base}", whose values do not include ${missing.map((id) => `"${stored[ids.indexOf(id)]}"`).join(', ')} (for state${missing.length > 1 ? 's' : ''} ${missing.map((id) => `"${id}"`).join(', ')} of "${b.id}"); map the states through storage.stateValues.`;
  }
  return undefined;
}

/**
 * Why a machine's key is not the whole key of its record, or undefined when it is (storage.key-whole). Two machines
 * keyed by part of a record's key would share one instance for every record that agrees on that part: a record keyed by
 * object and record id, held by a machine keyed by record id, is one instance for every object with that id. The key
 * names every key field of the record, in the record's order. @param {any} key @param {Entity} record @param {string} what
 */
function keyNotWhole(key, record, what) {
  const names = keyFieldsOf(key);
  const whole = Array.isArray(record.data.key) ? record.data.key : [];
  if (!names || JSON.stringify(names) === JSON.stringify(whole)) return undefined;
  const have = names.length === whole.length && names.every((n) => whole.includes(n)) ? 'the right fields in another order' : `${names.length === 1 ? 'one key field' : `${names.length} fields`}`;
  return `${what} is ${JSON.stringify(names.length === 1 ? names[0] : names)}, which is ${have}, but the key of record "${record.id}" is ${JSON.stringify(whole)}; a machine is keyed by the whole key of its record, every key field in order (write storage.key as the list ${JSON.stringify(whole)}), or two records that share the named field would share one instance.`;
}

/**
 * The readiness diagnostics of every implementation-level behavior of the model.
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function machineReadiness(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  const get = (/** @type {string} */ id) => model.entities.get(id);
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  /** @param {string} code @param {Entity} entity @param {string} message @param {(string|number)[]} [sub] */
  const report = (code, entity, message, sub) => {
    out.push({ code, severity: 'error', message, entityId: entity.id, loc: entity.loc, path: sub ? [...entity.path, ...sub] : entity.path });
  };
  const list = (/** @type {any} */ v) => (Array.isArray(v) ? v : []);

  const behaviors = kind('behavior').filter((b) => b.data.level === 'implementation');
  if (!behaviors.length) return out;

  // Events produced by a timer effect anywhere in the model, and events a scenario routes to a behavior.
  /** @type {Set<string>} */
  const timerEmits = new Set();
  for (const t of kind('transition')) for (const fx of list(t.data.effects)) if (fx && typeof fx === 'object' && 'timer' in fx && typeof fx.emit === 'string') timerEmits.add(fx.emit);
  /** @type {Set<string>} */
  const routedEvents = new Set();
  for (const s of kind('scenario')) for (const r of list(s.data.routes)) if (r && typeof r.event === 'string' && typeof r.behavior === 'string') routedEvents.add(r.event);

  // The behaviors some scenario runs, and whether a machine ships: its subject states an implementation
  // that exists (any status but not-implemented; a machine of an unbuilt component is a target) and does
  // not run in the browser (a client machine starts in its initial state there, generated as JavaScript).
  /** @type {Set<string>} */
  const runByScenario = new Set();
  for (const s of kind('scenario')) for (const id of list(s.data.behaviors)) if (typeof id === 'string') runByScenario.add(id);
  const shipped = (/** @type {Entity} */ b) => {
    const subject = get(b.data.subject);
    if (!subject || subject.kind !== 'component' || subject.data.category === 'client') return false;
    const status = subject.data.implementation?.status;
    return typeof status === 'string' && status !== 'not-implemented';
  };

  /** @type {Set<string>} */
  const eventsChecked = new Set();
  /** @param {Entity} ev */
  const checkEvent = (ev) => {
    if (eventsChecked.has(ev.id)) return;
    eventsChecked.add(ev.id);
    list(ev.data.payload).forEach((/** @type {any} */ f, /** @type {number} */ i) => {
      if (f && !typeResolves(model, f.type)) report('ready.payload-type-unresolved', ev, `Payload field "${f.name}" of event "${ev.id}" has type ${f.type === undefined ? 'none' : `"${f.type}"`}, which is not a built-in type, a declared type, or list<T> / option<T> of one.`, ['payload', i]);
    });
    if (ev.data.elapsed === true && !timerEmits.has(ev.id)) report('ready.elapsed-no-timer', ev, `Event "${ev.id}" represents elapsed time but no timer effect emits it.`, ['elapsed']);
  };

  for (const b of behaviors) {
    const states = kind('state').filter((s) => s.owner === b.id);
    const transitions = kind('transition').filter((t) => t.owner === b.id);

    // Variables: a representation that resolves.
    list(b.data.variables).forEach((/** @type {any} */ v, /** @type {number} */ i) => {
      if (!v || typeof v.name !== 'string') return;
      if (v.repr === undefined) report('ready.repr-missing', b, `Variable "${v.name}" of implementation-level behavior "${b.id}" has no repr.`, ['variables', i]);
      else if (!typeResolves(model, v.repr)) report('ready.repr-unresolved', b, `Variable "${v.name}" has repr "${v.repr}", which is not a built-in type, a declared type, or list<T> / option<T> of one.`, ['variables', i, 'repr']);
    });

    // Instances: stored in a record, keyed by one of its key fields.
    const inst = b.data.instances;
    if (inst && typeof inst === 'object') {
      const rec = typeof inst.storedIn === 'string' ? get(inst.storedIn) : undefined;
      if (typeof inst.key !== 'string' || !rec || rec.kind !== 'record') {
        report('ready.instances-storage', b, `Instances of "${b.id}" must be {key, storedIn} with storedIn naming a record${inst.storedIn === undefined ? '' : ` ("${inst.storedIn}" is not one)`}.`, ['instances']);
      } else if (!list(rec.data.key).includes(inst.key)) {
        report('ready.instances-storage', b, `Instance key "${inst.key}" is not a key field of record "${rec.id}".`, ['instances', 'key']);
      } else {
        const whole = keyNotWhole(inst.key, rec, `instances.key of "${b.id}"`);
        if (whole) report('storage.key-whole', b, whole, ['instances', 'key']);
      }
    }

    // Storage: the record that holds the machine and its key field. `instances.storedIn` says the same for a keyed
    // machine; when both are present they must agree.
    // A machine held in memory (storage.durability "memory") has no record to name; storage.durability reports what it
    // must not declare.
    const inMemory = !!b.data.storage && typeof b.data.storage === 'object' && b.data.storage.durability === 'memory';
    const storage = b.data.storage;
    const viaInstances = inst && typeof inst === 'object' && typeof inst.storedIn === 'string';
    if (inMemory) {
      // nothing to check against a record
    } else if (storage && typeof storage === 'object') {
      const rec = typeof storage.record === 'string' ? get(storage.record) : undefined;
      const storageKey = keyFieldsOf(storage.key);
      if (rec && rec.kind === 'record') {
        const outside = storageKey?.find((k) => !list(rec.data.key).includes(k));
        if (!storageKey || outside !== undefined) {
          report('ready.storage-key', b, `Storage key ${JSON.stringify(storage.key)} of "${b.id}" is not a key field of record "${rec.id}"${outside !== undefined && storageKey && storageKey.length > 1 ? ` ("${outside}" is not)` : ''}.`, ['storage', 'key']);
        } else {
          const whole = keyNotWhole(storage.key, rec, `storage.key of "${b.id}"`);
          if (whole) report('storage.key-whole', b, whole, ['storage', 'key']);
        }
      }
      // A defect of instances itself is ready.instances-storage; a mismatch is reported between two valid declarations.
      const instRec = viaInstances ? get(inst.storedIn) : undefined;
      const instancesValid = !!instRec && instRec.kind === 'record' && list(instRec.data.key).includes(inst.key);
      if (instancesValid && (inst.storedIn !== storage.record || JSON.stringify(keyFieldsOf(inst.key)) !== JSON.stringify(keyFieldsOf(storage.key)))) {
        report('ready.storage-mismatch', b, `"${b.id}" declares storage {record: "${storage.record}", key: ${JSON.stringify(storage.key)}} but instances {storedIn: "${inst.storedIn}", key: "${inst.key}"}; they must name the same record and key.`, ['storage']);
      }
    } else if (!viaInstances && (list(b.data.variables).length > 0 || states.length > 1)) {
      // A machine with no variables keeps nothing between events beyond its state; with one state it is
      // stateless and needs no record. With several states it still has a state to keep.
      report('ready.storage-missing', b, `Implementation-level behavior "${b.id}" does not say which record holds it: declare storage {record, key} (or instances {key, storedIn}).`, ['storage']);
    }

    // Storage fields: which record field holds each variable and the state, and whether the machine creates records.
    // Checked against the one record the machine is held in; a missing or disputed record is reported above.
    const st = storage && typeof storage === 'object' && !inMemory ? storage : undefined;
    const recordId = inMemory ? undefined : st ? st.record : viaInstances ? inst.storedIn : undefined;
    const keyField = st ? st.key : viaInstances ? inst.key : undefined;
    const disputed = !!st && viaInstances && inst.storedIn !== st.record;
    const holder = typeof recordId === 'string' && !disputed ? get(recordId) : undefined;
    if (holder && holder.kind === 'record') checkStorageFields(model, b, holder, st ?? {}, keyField, states, report);

    // Initial state (WG-4903): Exegra starts every instance in its initial state; the runtime does so
    // only for a machine that creates its records (storage.creates), and otherwise refuses its events
    // (RecordMissing) until the contract that creates the record (storage.createdBy) has written it.
    if (holder && holder.kind === 'record' && runByScenario.has(b.id) && shipped(b) && st?.creates !== true) {
      const by = typeof st?.createdBy === 'string' ? get(st.createdBy) : undefined;
      if (!by || by.kind !== 'contract') {
        const scenarios = kind('scenario').filter((s) => list(s.data.behaviors).includes(b.id)).map((s) => s.id);
        report('machine.initial-unreachable', b, `Scenario${scenarios.length > 1 ? 's' : ''} ${scenarios.slice(0, 3).map((s) => `"${s}"`).join(', ')}${scenarios.length > 3 ? ` and ${scenarios.length - 3} more` : ''} ${scenarios.length > 1 ? 'start' : 'starts'} "${b.id}" in its initial state "${b.data.initial}", but the runtime cannot: the machine does not create its records of "${holder.id}" (storage.creates) and names no contract that writes them (storage.createdBy), so the runtime refuses its events (RecordMissing) until someone else writes the record, in whatever state they write it. Set storage.creates when the machine owns the whole record, or name the contract in storage.createdBy.`, ['storage']);
      }
    }

    // Transaction.
    const tx = b.data.transaction;
    if (!inMemory && (!tx || typeof tx !== 'object' || tx.scope !== 'transition' || typeof tx.isolation !== 'string')) {
      report('ready.transaction-missing', b, `Implementation-level behavior "${b.id}" needs transaction {scope: "transition", isolation}.`, ['transaction']);
    }

    // Events the machine reacts to or emits.
    /** @type {Set<string>} */
    const onEvents = new Set();
    for (const t of transitions) {
      const ev = get(t.data.on);
      if (ev && ev.kind === 'event') { onEvents.add(ev.id); checkEvent(ev); }
    }

    for (const t of transitions) {
      if (t.data.faultOnly === true) report('ready.fault-only', t, `Transition "${t.id}" is faultOnly; an implementation-level machine has no fault-activated transitions.`, ['faultOnly']);
      const ev = get(t.data.on);
      const declared = new Set(ev && ev.kind === 'event' ? list(ev.data.payload).map((/** @type {any} */ f) => f?.name) : []);
      /** @param {any} src @param {(string|number)[]} sub */
      const readsOf = (src, sub) => {
        if (typeof src !== 'string') return;
        const p = parseExpr(src);
        if (!p.ok) return;
        for (const path of exprRefs(p.ast)) {
          if (path.length === 2 && path[0] === 'event' && !declared.has(path[1])) {
            report('ready.event-field-undeclared', t, `Expression "${src}" reads event.${path[1]}, which is not a declared payload field of event "${t.data.on}".`, sub);
          }
        }
      };
      readsOf(t.data.guard, ['guard']);
      list(t.data.effects).forEach((/** @type {any} */ fx, /** @type {number} */ i) => {
        if (!fx || typeof fx !== 'object') return;
        const sub = ['effects', i];
        if ('set' in fx) readsOf(fx.to, [...sub, 'to']);
        if (fx.payload && typeof fx.payload === 'object') for (const [k, v] of Object.entries(fx.payload)) readsOf(v, [...sub, 'payload', k]);
        if ('timer' in fx) {
          if (fx.after && typeof fx.after === 'object') readsOf(fx.after.expr, [...sub, 'after', 'expr']);
          const e = get(fx.emit);
          if (e && e.kind === 'event') checkEvent(e);
        } else if ('emit' in fx) {
          const emitted = get(fx.emit);
          if (emitted && emitted.kind === 'event') {
            checkEvent(emitted);
            if (fx.target !== 'reply' && fx.to === undefined && !routedEvents.has(emitted.id)) {
              report('ready.emit-receiver-missing', t, `Effect emits "${emitted.id}" without a receiver: no "target": "reply", no "to", and no scenario route for the event.`, sub);
            }
            if (emitted.data.delivery !== 'at-most-once' && emitted.data.delivery !== 'at-least-once') {
              report('ready.delivery-missing', emitted, `Event "${emitted.id}" is emitted by "${t.id}" but declares no delivery (at-most-once or at-least-once).`, ['delivery']);
            }
          }
        }
      });
    }

    // Ordering: among transitions with the same (from, on), declaration order decides, so it must be explicit.
    /** @type {Map<string, Entity[]>} */
    const groups = new Map();
    for (const t of transitions) {
      if (t.data.faultOnly === true) continue;
      const k = `${t.data.from}^@${t.data.on}`;
      groups.set(k, [...(groups.get(k) ?? []), t]);
    }
    const guarded = (/** @type {Entity} */ t) => typeof t.data.guard === 'string' && t.data.guard.trim() !== '';
    for (const g of groups.values()) {
      g.forEach((t, i) => {
        const last = i === g.length - 1;
        if (t.data.otherwise === true && !last) report('ready.otherwise-misplaced', t, `Transition "${t.id}" is marked otherwise but is not the last of its (from, on) group.`, ['otherwise']);
        else if (!last && !guarded(t)) report('ready.order-ambiguous', t, `Transition "${t.id}" is unguarded but is followed by "${g[i + 1].id}" on the same state and event; only declaration order would decide.`);
        else if (last && !guarded(t) && t.data.otherwise !== true) report('ready.order-ambiguous', t, `Transition "${t.id}" is the last on its state and event but has neither a guard nor "otherwise": true.`);
      });
    }

    // Time and integers (WG-4902): src/core/readiness-time.js.
    timeReadiness(model, b, states, transitions, report);

    // Completeness: every non-terminal state has an outcome for every event the machine reacts to.
    for (const s of states) {
      if (s.data.terminal === true) continue;
      const ignored = new Set(list(s.data.ignores));
      for (const evId of onEvents) {
        if (ignored.has(evId)) continue;
        if (!transitions.some((t) => t.data.from === s.id && t.data.on === evId && t.data.faultOnly !== true)) {
          report('ready.outcome-missing', s, `State "${s.id}" has no transition on event "${evId}" and does not list it in "ignores".`);
        }
      }
    }
  }
  /** @type {Set<string>} */
  const received = new Set();
  for (const b of behaviors) for (const t of kind('transition')) if (t.owner === b.id && typeof t.data.on === 'string') received.add(t.data.on);
  scenarioIntegerReadiness(model, received, report);
  return out;
}
