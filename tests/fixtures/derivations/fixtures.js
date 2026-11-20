// Fixtures of derived and facade contracts (WG-4935, NC-4 and NC-5 of WG-4895): the specification of specc's golden
// fixture crates/spec-compiler/tests/fixtures/derived/spec.jsonc in the Strata repository, a store of named counters
// reached through load-counters and commit-bump, with contracts derived from functions and from those two (pure,
// read, a read with a need loop, and the load-decide-commit loop of a command) and a facade lowered onto the served
// mutate-counter; and for each rule a mutation that breaks exactly that rule. The read with a need loop (peek-copy,
// WG-4939) is not yet in specc's fixture.

const TYPES = [
  {"id": "counter-need", "name": "Counter need", "kind": "struct", "fields": [{"name": "name", "type": "string"}]},
  {"id": "bump", "name": "Bump", "kind": "struct", "fields": [{"name": "name", "type": "string"}, {"name": "value", "type": "u64"}]},
  {"id": "copy-error", "name": "Copy error", "kind": "union", "variants": [{"name": "Missing", "newtype": true, "fields": [{"name": "need", "type": "counter-need"}]}]}
];

const FUNCTIONS = [
  {"id": "larger", "description": "The larger of two counts.", "params": [{"name": "a", "type": "u64"}, {"name": "b", "type": "u64"}], "returns": "u64", "body": "if a > b then a else b", "examples": [{"args": {"a": 3, "b": 5}, "result": 5}, {"args": {"a": 7, "b": 2}, "result": 7}]},
  {"id": "read-needs", "description": "What a read of one counter loads: that counter.", "params": [{"name": "name", "type": "string"}], "returns": "list<counter-need>", "body": "[counter-need{name}]", "examples": [{"args": {"name": "a"}, "result": [{"name": "a"}]}]},
  {"id": "read-value", "description": "The value of a loaded counter.", "params": [{"name": "name", "type": "string"}, {"name": "counters", "type": "map<string, u64>"}], "returns": "u64", "errors": "copy-error", "body": "match get(counters, name) { None => fail(copy-error.Missing(counter-need{name})), Some(v) => v }", "examples": [{"args": {"name": "a", "counters": {"a": 3}}, "result": 3}, {"args": {"name": "b", "counters": {"a": 3}}, "error": {"Missing": {"name": "b"}}}]},
  {"id": "header-needs", "description": "What a read of one counter loads once the header (the counters every load holds) is known: that counter, when the header has it.", "params": [{"name": "name", "type": "string"}, {"name": "counters", "type": "map<string, u64>"}], "returns": "list<counter-need>", "body": "if any(k in keys(counters), k == name) then [counter-need{name}] else []", "examples": [{"args": {"name": "a", "counters": {"a": 1}}, "result": [{"name": "a"}]}, {"args": {"name": "b", "counters": {"a": 1}}, "result": []}]},
  {"id": "copy-needs", "description": "What a copy loads first: the source counter only, so the target is asked for by the decision.", "params": [{"name": "source", "type": "string"}], "returns": "list<counter-need>", "body": "[counter-need{name: source}]", "examples": [{"args": {"source": "a"}, "result": [{"name": "a"}]}]},
  {"id": "decide-copy", "description": "The change a copy makes: the target takes the source's value. A counter that was not loaded is asked for.", "params": [{"name": "source", "type": "string"}, {"name": "target", "type": "string"}, {"name": "counters", "type": "map<string, u64>"}], "returns": "bump", "errors": "copy-error", "body": "match get(counters, source) { None => fail(copy-error.Missing(counter-need{name: source})), Some(v) => match get(counters, target) { None => fail(copy-error.Missing(counter-need{name: target})), Some(_) => bump{name: target, value: v} } }", "examples": [{"args": {"source": "a", "target": "b", "counters": {"a": 3, "b": 1}}, "result": {"name": "b", "value": 3}}, {"args": {"source": "a", "target": "b", "counters": {"a": 3}}, "error": {"Missing": {"name": "b"}}}, {"args": {"source": "a", "target": "b", "counters": {}}, "error": {"Missing": {"name": "a"}}}]}
];

const CONTRACTS = [
  {"id": "load-counters", "name": "Load counters", "ref": "CT-001", "realisation": "generated", "implementedBy": "store", "inputs": [{"name": "needs", "type": "list<counter-need>"}], "outputs": [{"name": "counters", "type": "map<string, u64>"}, {"name": "revision", "type": "u64"}], "postconditions": ["counters holds every counter a need names that exists, and revision is the store's revision they were read at."], "errors": [{"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "commit-bump", "name": "Commit a bump", "ref": "CT-002", "realisation": "generated", "implementedBy": "store", "inputs": [{"name": "bump", "type": "bump"}, {"name": "revision", "type": "u64"}], "outputs": [{"name": "revision", "type": "u64"}], "postconditions": ["The counter of the bump holds its value, and revision is the store's new revision."], "errors": [{"name": "conflict", "condition": "Another commit changed the store since revision."}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "mutate-counter", "name": "Change a counter", "ref": "CT-003", "realisation": "generated", "implementedBy": "store", "bffRoute": "POST /api/counters records", "inputs": [{"name": "op", "type": "string"}, {"name": "name", "type": "string"}, {"name": "value", "type": "u64", "optional": true}], "outputs": [{"name": "revision", "type": "u64"}], "postconditions": ["The generic counter endpoint: op names the change."], "errors": [{"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "pick-larger", "name": "Pick the larger count", "ref": "CT-004", "realisation": "derived", "derivation": {"kind": "pure", "function": "larger"}, "inputs": [{"name": "a", "type": "u64"}, {"name": "b", "type": "u64"}], "outputs": [{"name": "larger", "type": "u64"}], "errors": []},
  {"id": "read-counter", "name": "Read a counter", "ref": "CT-005", "realisation": "derived", "derivation": {"kind": "read", "needs": "read-needs", "load": "load-counters", "decide": "read-value"}, "inputs": [{"name": "name", "type": "string"}], "outputs": [{"name": "value", "type": "u64"}], "errors": [{"name": "missing", "condition": "The counter does not exist.", "type": "counter-need"}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "copy-counter", "name": "Copy a counter", "ref": "CT-006", "realisation": "derived", "derivation": {"kind": "command", "needs": "copy-needs", "load": "load-counters", "decide": "decide-copy", "commit": "commit-bump", "conflict": "conflict", "insufficient": "Missing", "needRounds": 4, "retries": 3}, "inputs": [{"name": "source", "type": "string"}, {"name": "target", "type": "string"}], "outputs": [{"name": "revision", "type": "u64"}, {"name": "value", "type": "u64"}], "errors": [{"name": "missing", "condition": "A counter does not exist, or more were asked for than needRounds allows.", "type": "counter-need"}, {"name": "conflict", "condition": "Every commit lost its race, retries times over."}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "copy-counter-once", "name": "Copy a counter without asking twice", "ref": "CT-007", "realisation": "derived", "derivation": {"kind": "command", "needs": "copy-needs", "load": "load-counters", "decide": "decide-copy", "commit": "commit-bump", "conflict": "conflict", "insufficient": "Missing", "needRounds": 0, "retries": 0}, "inputs": [{"name": "source", "type": "string"}, {"name": "target", "type": "string"}], "outputs": [{"name": "revision", "type": "u64"}, {"name": "value", "type": "u64"}], "errors": [{"name": "missing", "condition": "The decision asked for a counter that was not loaded.", "type": "counter-need"}, {"name": "conflict", "condition": "The commit lost its race."}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "peek-copy", "name": "Preview a copy", "ref": "CT-009", "realisation": "derived", "derivation": {"kind": "read", "needs": "copy-needs", "load": "load-counters", "decide": "decide-copy", "insufficient": "Missing", "needRounds": 2}, "inputs": [{"name": "source", "type": "string"}, {"name": "target", "type": "string"}], "outputs": [{"name": "name", "type": "string"}, {"name": "value", "type": "u64"}], "errors": [{"name": "missing", "condition": "A counter does not exist, or more were asked for than needRounds allows.", "type": "counter-need"}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "read-counter-header", "name": "Read a counter after the header", "ref": "CT-010", "realisation": "derived", "derivation": {"kind": "read", "needs": "header-needs", "load": "load-counters", "decide": "read-value", "header": true}, "inputs": [{"name": "name", "type": "string"}], "outputs": [{"name": "value", "type": "u64"}], "errors": [{"name": "missing", "condition": "The counter does not exist.", "type": "counter-need"}, {"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "archive-counters", "name": "Archive counters", "ref": "CT-011", "realisation": "target", "implementedBy": "store", "bffRoute": "POST /api/archive records", "inputs": [{"name": "before", "type": "u64"}], "outputs": [{"name": "archived", "type": "u64"}], "postconditions": ["Specified, not yet implemented: counters last changed before the revision are archived."], "errors": [{"name": "unavailable", "condition": "The store did not answer."}]},
  {"id": "edit-counter", "name": "Edit a counter", "ref": "CT-008", "realisation": "facade", "bffRoute": "POST /api/counters records update counter", "inputs": [{"name": "name", "type": "string"}, {"name": "value", "type": "u64"}], "outputs": [{"name": "revision", "type": "u64"}], "errors": [{"name": "unavailable", "condition": "The store did not answer."}]}
];

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'derived-fixture', name: 'Derived fixture', ...(generation ? { generation: { target: 'rust' } } : {}) },
    vocabulary: {"properties": [{"entity": "contract", "name": "bffRoute", "type": "string", "label": "BFF route", "doc": "How a client calls the contract: \"<METHOD> <path>\", optionally followed by a shape."}]},
    components: [{"id": "store", "name": "Store", "category": "computational"}],
    types: structuredClone(TYPES),
    functions: structuredClone(FUNCTIONS),
    // Every contract is an in-process call (it needs no route, session or capability to be generated from) and every
    // error states its status.
    contracts: structuredClone(CONTRACTS).map((c) => ({ ...c, exposure: 'local', auth: { scheme: 'in-process' }, errors: c.errors.map((/** @type {any} */ e) => ({ ...e, status: 500 })) })),
  };
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any} d @param {string} id */
const ct = (d, id) => d.contracts.find((/** @type {any} */ c) => c.id === id);
/** @param {any} c @param {string} name */
const dropError = (c, name) => { c.errors = c.errors.filter((/** @type {any} */ e) => e.name !== name); };

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports, with and without system.generation.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['a derived contract without a derivation', 'derivation.kind', (d) => { delete ct(d, 'pick-larger').derivation; }],
  ['a derivation of an unknown kind', 'derivation.kind', (d) => { ct(d, 'pick-larger').derivation.kind = 'query'; }],
  ['a derivation on a generated contract', 'derivation.kind', (d) => { ct(d, 'load-counters').derivation = { kind: 'pure', function: 'larger' }; }],
  ['a read derivation that names a commit contract', 'derivation.kind', (d) => { ct(d, 'read-counter').derivation.commit = 'commit-bump'; }],
  ['a function parameter that is no input of the contract', 'derivation.signature', (d) => { ct(d, 'pick-larger').inputs[1].name = 'c'; }],
  ['a function parameter of another type than the input', 'derivation.signature', (d) => { ct(d, 'pick-larger').inputs[0].type = 'u32'; }],
  ['a function that gives another type than the output', 'derivation.signature', (d) => { ct(d, 'pick-larger').outputs[0].type = 'string'; }],
  ['an error variant of decide that the contract does not have', 'derivation.signature', (d) => { dropError(ct(d, 'read-counter'), 'missing'); }],
  ['an insufficient-state variant decide does not have', 'derivation.signature', (d) => { ct(d, 'copy-counter').derivation.insufficient = 'Absent'; }],
  ['a fault that is not an error of the contract', 'derivation.signature', (d) => { ct(d, 'pick-larger').derivation.fault = 'overflow'; }],
  ['a load contract with an input nothing fills', 'derivation.load', (d) => { ct(d, 'read-counter').derivation.load = 'mutate-counter'; }],
  ['a load contract that is a facade', 'derivation.load', (d) => { ct(d, 'read-counter').derivation.load = 'edit-counter'; }],
  ['a load error the contract does not have', 'derivation.load', (d) => { dropError(ct(d, 'read-counter'), 'unavailable'); }],
  ['a conflict error the commit contract does not have', 'derivation.commit', (d) => { ct(d, 'copy-counter').derivation.conflict = 'clash'; }],
  ['a commit contract with an input nothing fills', 'derivation.commit', (d) => { ct(d, 'copy-counter').derivation.commit = 'mutate-counter'; }],
  ['an output neither committed nor decided', 'derivation.commit', (d) => { ct(d, 'copy-counter').outputs.push({ name: 'count', type: 'u64' }); }],
  ['a commit error the contract does not have', 'derivation.commit', (d) => { dropError(ct(d, 'copy-counter'), 'conflict'); }],
  ['a negative number of need rounds', 'derivation.bounds', (d) => { ct(d, 'copy-counter').derivation.needRounds = -1; }],
  ['a command derivation without retries', 'derivation.bounds', (d) => { delete ct(d, 'copy-counter').derivation.retries; }],
  ['a read need loop without need rounds', 'derivation.bounds', (d) => { delete ct(d, 'peek-copy').derivation.needRounds; }],
  ['a read with need rounds and no insufficient-state variant', 'derivation.kind', (d) => { delete ct(d, 'peek-copy').derivation.insufficient; }],
  ['a read need loop whose insufficient-state variant decide does not have', 'derivation.signature', (d) => { ct(d, 'peek-copy').derivation.insufficient = 'Absent'; }],
  ['a fractional number of need rounds', 'derivation.bounds', (d) => { ct(d, 'copy-counter-once').derivation.needRounds = 1.5; }],
  ['a header that is not a boolean', 'property.type', (d) => { ct(d, 'read-counter-header').derivation.header = 'yes'; }],
  ['a needs function that reads a load output without a header', 'derivation.signature', (d) => { ct(d, 'read-counter-header').derivation.header = false; }],
  ['a pure derivation with a header', 'derivation.kind', (d) => { ct(d, 'pick-larger').derivation.header = true; }],
  ['a header whose load output is named like an input', 'derivation.load', (d) => { ct(d, 'read-counter-header').inputs.push({ name: 'revision', type: 'u64', optional: true }); }],
  ['a target contract with a derivation', 'derivation.kind', (d) => { ct(d, 'archive-counters').derivation = { kind: 'pure', function: 'larger' }; }],
  ['a load contract that is a target', 'derivation.load', (d) => { ct(d, 'read-counter').derivation.load = 'archive-counters'; }],
  ['a commit contract that is a target', 'derivation.commit', (d) => { ct(d, 'copy-counter').derivation.commit = 'archive-counters'; }],
  ['a facade whose route only a target contract states', 'contract.facade-route', (d) => { ct(d, 'edit-counter').bffRoute = 'POST /api/archive records'; }],
  ['a facade with an implementing component', 'contract.facade-route', (d) => { ct(d, 'edit-counter').implementedBy = 'store'; }],
  ['a facade without a bffRoute', 'contract.facade-route', (d) => { delete ct(d, 'edit-counter').bffRoute; }],
  ['a facade whose route no served contract states', 'contract.facade-route', (d) => { ct(d, 'edit-counter').bffRoute = 'POST /api/counters view'; }],
  ['a facade whose route two served contracts state', 'contract.facade-route', (d) => { ct(d, 'load-counters').bffRoute = 'POST /api/counters records'; }],
];

/**
 * Readiness: each mutation leaves a gap that is an error only when system.generation is set.
 * @type {[string, string, (d: any) => void][]}
 */
export const READINESS_FIXTURES = [
  ['a derivation naming a function that is not declared', 'ready.derived-function-missing', (d) => { ct(d, 'pick-larger').derivation.function = 'largest'; }],
  ['a command derivation whose decide function is not declared', 'ready.derived-function-missing', (d) => { ct(d, 'copy-counter-once').derivation.decide = 'decide-once'; }],
];
