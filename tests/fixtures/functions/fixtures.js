// Fixtures of the function construct (WG-4933, NC-3): a specification that states real decisions of the Strata
// kernel (crates/kernel/src/rules.rs: roles_of, may_attempt, authorize; crates/kernel/src/transition.rs:
// check_version) as functions, with examples taken from the kernel's own tests (tests/behaviour.rs and the notes
// schema of src/testkit.rs), and for each rule a mutation that breaks exactly that rule.

import { spec as languageSpec } from '../language/fixtures.js';

// --- Values as examples write them (serde's external form) ---------------------------------------------------
const str = (/** @type {string} */ s) => ({ Str: s });
const lit = (/** @type {any} */ v) => ({ Lit: v });
const varOf = (/** @type {string} */ scope, /** @type {string} */ name) => ({ Var: { scope, name } });
const eq = (/** @type {any} */ left, /** @type {any} */ right) => ({ Cmp: { op: 'Eq', left, right } });
const ALL = ['Read', 'Create', 'Update', 'Delete'];
const policy = (/** @type {string} */ id, /** @type {string} */ role, /** @type {string} */ object, /** @type {string[]} */ actions, /** @type {any} */ condition) => (
  { id, role, resource: { Object: object }, actions, ...(condition ? { condition } : {}) });

/** The policies of notes_schema (crates/kernel/src/testkit.rs), keyed by id as the kernel's BTreeMap is. */
const NOTES_POLICIES = Object.fromEntries([
  policy('public_reads_published', 'public', 'note', ['Read'], eq(varOf('Record', 'status'), lit(str('published')))),
  policy('public_reads_people', 'public', 'person', ['Read']),
  policy('writers_read_notes', 'writer', 'note', ['Read', 'Create']),
  policy('writers_edit_own', 'writer', 'note', ['Update', 'Delete'], eq(varOf('Record', '$created_by'), 'Principal')),
  policy('writers_add_people', 'writer', 'person', ['Create']),
  policy('editors_manage_notes', 'editor', 'note', ALL),
  policy('editors_manage_people', 'editor', 'person', ALL),
].map((p) => [p.id, p]));

/** Tenant alpha of notes_world: an owner, two writers and an editor. */
export const ALPHA = {
  members: { 'alpha:owner': ['owner'], 'alpha:writer1': ['writer'], 'alpha:writer2': ['writer'], 'alpha:editor': ['editor'] },
  policies: NOTES_POLICIES,
};
const user = (/** @type {string} */ who) => ({ User: `alpha:${who}` });
/** Note 1 as writer1 created it: its fields and system attributes. */
const note = (/** @type {Record<string, any>} */ fields = {}) => ({ $id: { Ref: 1 }, $version: { Int: 1 }, $created_by: str('alpha:writer1'), title: str('First'), slug: str('first'), ...fields });
const stored = (/** @type {any} */ record) => ({ old: record, new: record });
const pass = (/** @type {string} */ rule) => ({ rule, passed: true });
const fail = (/** @type {string} */ rule) => ({ rule, passed: false });

const TYPES = [
  { id: 'action', name: 'Action', kind: 'enum', values: ['Read', 'Create', 'Update', 'Delete', 'Manage'] },
  { id: 'object-type-id', name: 'Object type id', kind: 'id', repr: 'string' },
  { id: 'resource', name: 'Resource', kind: 'union', variants: [
    { name: 'Object', newtype: true, fields: [{ name: 'object', type: 'object-type-id' }] },
    { name: 'AnyObject' }, { name: 'Schema' }, { name: 'Members' },
  ] },
  { id: 'principal', name: 'Principal', kind: 'union', variants: [
    { name: 'System' }, { name: 'Anonymous' }, { name: 'User', newtype: true, fields: [{ name: 'id', type: 'string' }] },
  ] },
  { id: 'policy-def', name: 'Policy', kind: 'struct', fields: [
    { name: 'id', type: 'string' }, { name: 'role', type: 'string' }, { name: 'resource', type: 'resource' },
    { name: 'actions', type: 'list<action>' }, { name: 'condition', type: 'option<expr>' },
  ] },
  { id: 'tenant', name: 'Tenant', kind: 'struct', fields: [
    { name: 'members', type: 'map<string, list<string>>' }, { name: 'policies', type: 'map<string, policy-def>' },
  ] },
  { id: 'subject', name: 'Subject', kind: 'struct', fields: [
    { name: 'old', type: 'option<map<string, value>>' }, { name: 'new', type: 'option<map<string, value>>' },
  ] },
  { id: 'rule-env', name: 'Rule environment', kind: 'struct', fields: [
    { name: 'record', type: 'option<map<string, value>>' }, { name: 'old', type: 'option<map<string, value>>' },
    { name: 'new', type: 'option<map<string, value>>' }, { name: 'param', type: 'map<string, value>' },
    { name: 'now', type: 'value' }, { name: 'principal', type: 'value' }, { name: 'has_role', type: 'list<string>' },
  ] },
  { id: 'rule-check', name: 'Check', kind: 'struct', fields: [{ name: 'rule', type: 'string' }, { name: 'passed', type: 'bool' }] },
  { id: 'decision', name: 'Decision', kind: 'struct', fields: [{ name: 'allowed', type: 'bool' }, { name: 'checks', type: 'list<rule-check>' }] },
  { id: 'auth-state', name: 'Authorization state', kind: 'struct', fields: [{ name: 'granted', type: 'option<rule-check>' }, { name: 'checks', type: 'list<rule-check>' }] },
  { id: 'domain-error', name: 'Domain error', kind: 'union', variants: [{ name: 'VersionConflict', fields: [{ name: 'message', type: 'string' }] }] },
  { id: 'check-env', name: 'Check environment', kind: 'struct', fields: [
    { name: 'fields', type: 'map<string, string>' }, { name: 'params', type: 'list<string>' }, { name: 'roles', type: 'list<string>' },
  ] },
  { id: 'error-kind', name: 'Error kind', kind: 'enum', values: ['unknown-record', 'version-conflict', 'evaluation'] },
  // Variants and fields named like keywords of the body language, as Strata's value and expr unions name them.
  { id: 'plain-value', name: 'Plain value', kind: 'union', variants: [
    { name: 'null' },
    { name: 'str', newtype: true, fields: [{ name: 'value', type: 'string' }] },
    { name: 'if', fields: [{ name: 'then', type: 'string' }, { name: 'else', type: 'string' }] },
  ] },
  { id: 'json-node', name: 'JSON node', kind: 'union', variants: [
    { name: 'leaf', newtype: true, fields: [{ name: 'value', type: 'string' }] },
    { name: 'node', newtype: true, fields: [{ name: 'value', type: 'map<string, json-node>' }] },
  ] },
];

const ruleEnv = (/** @type {string} */ roles) => `rule-env{record: null, old: null, new: null, param: {}, now: value.Null, principal: value.Null, has_role: ${roles}}`;
const MENTIONS_FIELD = [
  "match e { Var{name} => !startsWith(name, '$'), Through => true, Lit => false, Param => false, Now => false, Principal => false, HasRole => false",
  'Not(a) => call mentions-field(a), IsNull(a) => call mentions-field(a), Len(a) => call mentions-field(a), Lower(a) => call mentions-field(a), IsSlug(a) => call mentions-field(a)',
  'And(items) => any(i in items, call mentions-field(i)), Or(items) => any(i in items, call mentions-field(i))',
  'Cmp{left, right} => call mentions-field(left) || call mentions-field(right), In{item, list: l} => call mentions-field(item) || call mentions-field(l)',
  'Contains{haystack, needle} => call mentions-field(haystack) || call mentions-field(needle), StartsWith{text, prefix} => call mentions-field(text) || call mentions-field(prefix)',
  'If{cond, then: t, otherwise} => call mentions-field(cond) || call mentions-field(t) || call mentions-field(otherwise)',
  'Arith{left, right} => call mentions-field(left) || call mentions-field(right), MsBetween{from: a, to: b} => call mentions-field(a) || call mentions-field(b)',
  'Duration{amount} => call mentions-field(amount), Concat{left, right} => call mentions-field(left) || call mentions-field(right), Text(a) => call mentions-field(a), AncestorOf{x: p, y: q, object: o, via: v} => call mentions-field(p) || call mentions-field(q) || call mentions-field(o) || call mentions-field(v) }',
].join(', ');
/** References to the fixtures below, as examples write them. */
const TENANT = { fixture: 'tenant-alpha' };
const STORED_NOTE = { fixture: 'note-stored' };

/** Values the examples share (WG-4963). */
const EXAMPLE_FIXTURES = [
  { id: 'tenant-alpha', type: 'tenant', description: 'Tenant alpha of notes_world: an owner, two writers and an editor, with the policies of notes_schema.', value: ALPHA },
  { id: 'note-stored', type: 'subject', description: 'Note 1 as writer1 created it, unchanged by the request.', value: stored(note()) },
];

const FUNCTIONS = [
  {
    id: 'set-of',
    description: 'A BTreeSet<String> as a list: sorted by Unicode scalar values, each item once.',
    params: [{ name: 'items', type: 'list<string>' }],
    returns: 'list<string>',
    body: 'fold(r in sortBy(r in items, r), acc = [], if any(a in acc, a == r) then acc else concat(acc, [r]))',
    examples: [
      { args: { items: ['writer', 'public', 'writer'] }, result: ['public', 'writer'] },
      { args: { items: [] }, result: [] },
    ],
  },
  {
    id: 'roles-of',
    description: 'rules.rs roles_of: the roles a principal holds in a tenant; everyone but the system holds public.',
    params: [{ name: 'tenant', type: 'tenant' }, { name: 'principal', type: 'principal' }],
    returns: 'list<string>',
    body: "match principal { System => [], Anonymous => ['public'], User(id) => call set-of(concat(match get(tenant.members, id) { None => [], Some(roles) => roles }, ['public'])) }",
    examples: [
      { args: { tenant: TENANT, principal: 'System' }, result: [] },
      { args: { tenant: TENANT, principal: 'Anonymous' }, result: ['public'] },
      { args: { tenant: TENANT, principal: user('writer1') }, result: ['public', 'writer'] },
      { args: { tenant: TENANT, principal: user('stranger') }, result: ['public'] },
    ],
  },
  {
    id: 'policy-applies',
    description: 'Whether a policy names a role held, the action and the resource (AnyObject covers every object), its condition aside.',
    params: [{ name: 'policy', type: 'policy-def' }, { name: 'roles', type: 'list<string>' }, { name: 'action', type: 'action' }, { name: 'resource', type: 'resource' }],
    returns: 'bool',
    body: 'any(r in roles, r == policy.role) && any(a in policy.actions, a == action) && match policy.resource { AnyObject => match resource { Object(_) => true, _ => policy.resource == resource }, _ => policy.resource == resource }',
    examples: [
      { args: { policy: NOTES_POLICIES.writers_edit_own, roles: ['public', 'writer'], action: 'Update', resource: { Object: 'note' } }, result: true },
      { args: { policy: NOTES_POLICIES.writers_edit_own, roles: ['public', 'writer'], action: 'Read', resource: { Object: 'note' } }, result: false },
      { args: { policy: { ...NOTES_POLICIES.writers_read_notes, resource: 'AnyObject' }, roles: ['writer'], action: 'Read', resource: { Object: 'person' } }, result: true },
      { args: { policy: { ...NOTES_POLICIES.writers_read_notes, resource: 'AnyObject' }, roles: ['writer'], action: 'Read', resource: 'Schema' }, result: false },
    ],
  },
  {
    id: 'may-attempt',
    description: 'rules.rs may_attempt: whether some policy could grant the action, conditions aside; the owner may do anything.',
    params: [{ name: 'tenant', type: 'tenant' }, { name: 'principal', type: 'principal' }, { name: 'action', type: 'action' }, { name: 'resource', type: 'resource' }],
    returns: 'bool',
    let: [{ name: 'roles', expr: 'call roles-of(tenant, principal)' }],
    body: "any(r in roles, r == 'owner') || any(p in values(tenant.policies), call policy-applies(p, roles, action, resource))",
    examples: [
      { args: { tenant: TENANT, principal: user('owner'), action: 'Manage', resource: 'Schema' }, result: true },
      { args: { tenant: TENANT, principal: user('writer2'), action: 'Update', resource: { Object: 'note' } }, result: true },
      { args: { tenant: TENANT, principal: user('writer1'), action: 'Manage', resource: 'Schema' }, result: false },
      { args: { tenant: TENANT, principal: 'Anonymous', action: 'Create', resource: { Object: 'note' } }, result: false },
      { args: { tenant: TENANT, principal: 'Anonymous', action: 'Read', resource: { Object: 'note' } }, result: true },
      { args: { tenant: TENANT, principal: 'System', action: 'Read', resource: { Object: 'person' } }, result: false },
    ],
  },
  {
    id: 'deny',
    description: 'A failed check of a policy whose condition did not hold.',
    params: [{ name: 'acc', type: 'auth-state' }, { name: 'rule', type: 'string' }],
    returns: 'auth-state',
    body: 'auth-state{granted: acc.granted, checks: concat(acc.checks, [rule-check{rule, passed: false}])}',
    examples: [{ args: { acc: { checks: [] }, rule: 'policy:p' }, result: { checks: [fail('policy:p')] } }],
  },
  {
    id: 'policy-step',
    description: 'One applicable policy in authorize: no condition grants; a condition grants only when it evaluates to true; false, null or an evaluation error is a failed check.',
    params: [{ name: 'policy', type: 'policy-def' }, { name: 'env', type: 'rule-env' }, { name: 'acc', type: 'auth-state' }],
    returns: 'auth-state',
    let: [{ name: 'rule', expr: 'format("policy:{}", policy.id)' }],
    body: 'match policy.condition { None => auth-state{granted: rule-check{rule, passed: true}, checks: acc.checks}, Some(c) => match eval(rule-language, c, env) { Ok(v) => match v { Bool(b) => if b then auth-state{granted: rule-check{rule, passed: true}, checks: acc.checks} else call deny(acc, rule), _ => call deny(acc, rule) }, Err(e) => call deny(acc, rule) } }',
    examples: [
      {
        args: { policy: NOTES_POLICIES.writers_read_notes, env: { param: {}, now: { Time: 5000 }, principal: str('alpha:writer1'), has_role: ['public', 'writer'] }, acc: { checks: [] } },
        result: { granted: pass('policy:writers_read_notes'), checks: [] },
      },
      {
        description: 'Comparing a string with an int is an evaluation error, which fails the check.',
        args: { policy: { ...NOTES_POLICIES.writers_read_notes, condition: eq(lit(str('a')), lit({ Int: 1 })) }, env: { param: {}, now: { Time: 5000 }, principal: 'Null', has_role: [] }, acc: { checks: [] } },
        result: { checks: [fail('policy:writers_read_notes')] },
      },
      {
        description: 'A condition that holds grants.',
        args: { policy: { ...NOTES_POLICIES.writers_read_notes, condition: eq(lit(str('a')), lit(str('a'))) }, env: { param: {}, now: { Time: 5000 }, principal: 'Null', has_role: [] }, acc: { checks: [] } },
        result: { granted: pass('policy:writers_read_notes'), checks: [] },
      },
      {
        description: 'A condition that is false fails the check.',
        args: { policy: { ...NOTES_POLICIES.writers_read_notes, condition: eq(lit({ Int: 1 }), lit({ Int: 2 })) }, env: { param: {}, now: { Time: 5000 }, principal: 'Null', has_role: [] }, acc: { checks: [] } },
        result: { checks: [fail('policy:writers_read_notes')] },
      },
      {
        description: 'A condition that is not a boolean fails the check.',
        args: { policy: { ...NOTES_POLICIES.writers_read_notes, condition: lit('Null') }, env: { param: {}, now: { Time: 5000 }, principal: 'Null', has_role: [] }, acc: { checks: [] } },
        result: { checks: [fail('policy:writers_read_notes')] },
      },
    ],
  },
  {
    id: 'authorize',
    description: 'rules.rs authorize: default deny; the owner is allowed everything; otherwise the first applicable policy (in id order) without a condition, or whose condition is true, grants; a condition that is false, null or fails to evaluate denies; with no applicable policy the check is policy:none. Check details are not stated (see the report of WG-4933).',
    params: [
      { name: 'tenant', type: 'tenant' }, { name: 'principal', type: 'principal' }, { name: 'now', type: 'i64' },
      { name: 'action', type: 'action' }, { name: 'resource', type: 'resource' }, { name: 'subject', type: 'subject' },
    ],
    returns: 'decision',
    let: [
      { name: 'roles', expr: 'call roles-of(tenant, principal)' },
      { name: 'env', expr: 'rule-env{record: if subject.old == null then subject.new else subject.old, old: subject.old, new: subject.new, param: {}, now: value.Time(now), principal: match principal { User(id) => value.Str(id), _ => value.Null }, has_role: roles}' },
      { name: 'state', expr: 'fold(p in values(tenant.policies), acc = auth-state{granted: null, checks: []}, if acc.granted != null || !call policy-applies(p, roles, action, resource) then acc else call policy-step(p, env, acc))' },
    ],
    body: "if any(r in roles, r == 'owner') then decision{allowed: true, checks: [rule-check{rule: 'policy:builtin_owner', passed: true}]} else match state.granted { Some(c) => decision{allowed: true, checks: [c]}, None => decision{allowed: false, checks: if state.checks == [] then [rule-check{rule: 'policy:none', passed: false}] else state.checks} }",
    examples: [
      {
        description: 'The owner role bypasses the policies.',
        args: { tenant: TENANT, principal: user('owner'), now: 5000, action: 'Delete', resource: { Object: 'note' }, subject: STORED_NOTE },
        result: { allowed: true, checks: [pass('policy:builtin_owner')] },
      },
      {
        description: 'behaviour.rs create_applies_defaults_and_allocates_the_next_id: writers_read_notes grants the create.',
        args: { tenant: TENANT, principal: user('writer1'), now: 5000, action: 'Create', resource: { Object: 'note' }, subject: { new: note() } },
        result: { allowed: true, checks: [pass('policy:writers_read_notes')] },
      },
      {
        description: 'behaviour.rs writers_edit_only_their_own_notes: writer2 is refused by writers_edit_own.',
        args: { tenant: TENANT, principal: user('writer2'), now: 5001, action: 'Update', resource: { Object: 'note' }, subject: STORED_NOTE },
        result: { allowed: false, checks: [fail('policy:writers_edit_own')] },
      },
      {
        description: 'behaviour.rs writers_edit_only_their_own_notes: writer1 edits its own note.',
        args: { tenant: TENANT, principal: user('writer1'), now: 5002, action: 'Update', resource: { Object: 'note' }, subject: STORED_NOTE },
        result: { allowed: true, checks: [pass('policy:writers_edit_own')] },
      },
      {
        description: 'No policy grants an anonymous create: policy:none.',
        args: { tenant: TENANT, principal: 'Anonymous', now: 5000, action: 'Create', resource: { Object: 'note' }, subject: { new: note() } },
        result: { allowed: false, checks: [fail('policy:none')] },
      },
      {
        description: 'A condition that is null fails: the note has no status, so record.status == published is null.',
        args: { tenant: TENANT, principal: 'Anonymous', now: 5000, action: 'Read', resource: { Object: 'note' }, subject: STORED_NOTE },
        result: { allowed: false, checks: [fail('policy:public_reads_published')] },
      },
      {
        description: 'A published note is read by anyone.',
        args: { tenant: TENANT, principal: 'Anonymous', now: 5000, action: 'Read', resource: { Object: 'note' }, subject: { fixture: 'note-stored', with: { 'old.status': str('published'), 'new.status': str('published') } } },
        result: { allowed: true, checks: [pass('policy:public_reads_published')] },
      },
    ],
  },
  {
    id: 'check-version',
    description: 'transition.rs check_version: an expected version other than the stored one is a version conflict.',
    params: [{ name: 'version', type: 'u64' }, { name: 'expected', type: 'option<u64>' }],
    returns: 'unit',
    errors: 'domain-error',
    body: 'match expected { Some(v) => if v != version then fail(domain-error.VersionConflict{message: format("record is at version {}, expected {}", version, v)}) else (), None => () }',
    examples: [
      { description: 'behaviour.rs a_stale_expected_version_is_a_conflict', args: { version: 2, expected: 1 }, error: { VersionConflict: { message: 'record is at version 2, expected 1' } } },
      { description: 'behaviour.rs every_rejection_lists_at_least_one_failed_check, stale version', args: { version: 1, expected: 7 }, error: { VersionConflict: { message: 'record is at version 1, expected 7' } } },
      { description: 'Result<(), DomainError>: the unit value is written null.', args: { version: 2, expected: 2 }, result: null },
      { args: { version: 2, expected: null }, result: null },
    ],
  },
  {
    id: 'next-version',
    description: 'The version an update writes: the stored one plus one, after check_version.',
    params: [{ name: 'version', type: 'u64' }, { name: 'expected', type: 'option<u64>' }],
    returns: 'u64',
    errors: 'domain-error',
    let: [{ name: 'checked', expr: 'try call check-version(version, expected)' }],
    body: 'version + 1',
    examples: [
      { args: { version: 1 }, result: 2 },
      { args: { version: 1, expected: 1 }, result: 2 },
      { args: { version: 2, expected: 1 }, error: { VersionConflict: { message: 'record is at version 2, expected 1' } } },
    ],
  },
  {
    id: 'holds-role',
    description: 'expr.rs eval, Expr::HasRole: whether the roles held include the role. Its operand is a role-id, an id over string (WG-4962).',
    params: [{ name: 'role', type: 'role-id' }, { name: 'roles', type: 'list<string>' }],
    returns: 'result<value, string>',
    body: `eval(rule-language, expr.HasRole(role), ${ruleEnv('roles')})`,
    examples: [
      { args: { role: 'editor', roles: ['editor', 'public'] }, result: { Ok: { Bool: true } } },
      { args: { role: 'editor', roles: ['public'] }, result: { Ok: { Bool: false } } },
    ],
  },
  {
    id: 'role-declared',
    description: 'expr.rs check, Expr::HasRole: the role is declared at the definition site.',
    params: [{ name: 'role', type: 'role-id' }, { name: 'roles', type: 'list<string>' }],
    returns: 'result<string, string>',
    body: 'check(rule-language, expr.HasRole(role), check-env{fields: {}, params: [], roles})',
    examples: [
      { args: { role: 'editor', roles: ['editor'] }, result: { Ok: 'bool' } },
      { args: { role: 'editor', roles: ['public'] }, result: { Err: 'unknown role editor' } },
    ],
  },
  {
    id: 'print-rule',
    description: "expr.rs Display: an expression printed in the language's authoring syntax.",
    params: [{ name: 'e', type: 'expr' }],
    returns: 'string',
    body: 'print(rule-language, e)',
    examples: [
      { args: { e: eq(varOf('Record', '$created_by'), 'Principal') }, result: '(record.$created_by == principal)' },
      { description: 'An empty And prints as its identity.', args: { e: { And: [] } }, result: 'true' },
      { args: { e: { Or: [{ HasRole: 'editor' }, { Not: { IsNull: varOf('Old', 'status') } }] } }, result: '(has_role(editor) or not(is_null(old.status)))' },
      { args: { e: { If: { cond: lit({ Bool: true }), then: lit(str("it's\\")), otherwise: lit({ List: [{ Int: -1 }, 'Null', { Time: 5 }, { Ref: 2 }] }) } } }, result: "if(true, 'it\\'s\\\\', [-1, null, time(5), ref(2)])" },
      { args: { e: { Through: { scope: 'New', field: 'author', target: 'principal' } } }, result: 'new.author.principal' },
      { args: { e: { In: { item: { Param: 'tag' }, list: lit({ List: [str('a')] }) } } }, result: "(param.tag in ['a'])" },
      { args: { e: { Contains: { haystack: { Lower: 'Principal' }, needle: lit(str('x')) } } }, result: "contains(lower(principal), 'x')" },
    ],
  },
  {
    id: 'request-text',
    description: 'rules.rs authorize, the request of a check: format!("{action:?} on {resource:?}"), Rust\'s derived Debug.',
    params: [{ name: 'action', type: 'action' }, { name: 'resource', type: 'resource' }],
    returns: 'string',
    body: "format('{:?} on {:?}', action, resource)",
    examples: [
      { args: { action: 'Update', resource: { Object: 'note' } }, result: 'Update on Object(ObjectTypeId("note"))' },
      { args: { action: 'Manage', resource: 'Schema' }, result: 'Manage on Schema' },
    ],
  },
  {
    id: 'debug-texts',
    description: 'Rust Debug of a struct (field names in snake_case), a list of strings and an option.',
    params: [{ name: 'c', type: 'rule-check' }, { name: 'roles', type: 'list<string>' }, { name: 'granted', type: 'option<rule-check>' }],
    returns: 'string',
    body: "format('{:?} {:?} {:?}', c, roles, granted)",
    examples: [
      { args: { c: { rule: 'a"b', passed: true }, roles: ['public', 'x\ny'], granted: null }, result: 'RuleCheck { rule: "a\\"b", passed: true } ["public", "x\\ny"] None' },
      { args: { c: { rule: 'r', passed: false }, roles: [], granted: { rule: 'g', passed: true } }, result: 'RuleCheck { rule: "r", passed: false } [] Some(RuleCheck { rule: "g", passed: true })' },
    ],
  },
  {
    id: 'json-text',
    description: 'serde_json text: strings escaped, an f64 as ryu writes it, an integer in decimal.',
    params: [{ name: 's', type: 'string' }, { name: 'x', type: 'f64' }, { name: 'n', type: 'i64' }],
    returns: 'string',
    body: "format('{:json} {:json} {:json}', s, x, n)",
    examples: [
      { args: { s: 'a"b\\\n', x: 1, n: -3 }, result: '"a\\"b\\\\\\n" 1.0 -3' },
      { args: { s: '\u0001', x: 1e16, n: 0 }, result: '"\\u0001" 1e16 0' },
      { args: { s: '', x: 0.1, n: 2 }, result: '"" 0.1 2' },
    ],
  },
  {
    id: 'mentions-field',
    description: 'schema.rs mentions_field: whether a condition reads a record field (a $-attribute is not a field), by structural recursion over the expression.',
    params: [{ name: 'e', type: 'expr' }],
    returns: 'bool',
    body: MENTIONS_FIELD,
    examples: [
      { args: { e: varOf('Record', 'status') }, result: true },
      { args: { e: varOf('Record', '$created_by') }, result: false },
      { args: { e: eq(varOf('Record', '$created_by'), 'Principal') }, result: false },
      { args: { e: { And: [{ HasRole: 'editor' }, { Not: { IsNull: varOf('New', 'title') } }] } }, result: true },
      { args: { e: { If: { cond: lit({ Bool: true }), then: 'Now', otherwise: { Through: { scope: 'New', field: 'author', target: 'name' } } } } }, result: true },
      { args: { e: { Or: [] } }, result: false },
      { args: { e: { AncestorOf: { x: lit({ Ref: 1 }), y: varOf('Record', 'parent'), object: lit({ Str: 'comment' }), via: lit({ Str: 'parent' }) } } }, result: true },
      { args: { e: { Param: 'tag' } }, result: false },
      { args: { e: { Len: varOf('Record', 'tags') } }, result: true },
      { args: { e: { Lower: varOf('Old', 'title') } }, result: true },
      { args: { e: { IsSlug: lit(str('a-b')) } }, result: false },
      { args: { e: { In: { item: { Param: 'tag' }, list: varOf('Record', 'tags') } } }, result: true },
      { args: { e: { Contains: { haystack: varOf('New', 'body'), needle: lit(str('x')) } } }, result: true },
      { args: { e: { StartsWith: { text: lit(str('abc')), prefix: varOf('Record', 'prefix') } } }, result: true },
      { args: { e: { Arith: { op: 'Sub', left: 'Now', right: { Duration: { unit: 'Days', amount: lit({ Int: 7 }) } } } } }, result: false },
      { args: { e: { MsBetween: { from: varOf('Record', 'starts_at'), to: 'Now' } } }, result: true },
      { args: { e: { Concat: { left: 'Principal', right: { Text: varOf('Record', '$id') } } } }, result: false },
    ],
  },
  {
    id: 'node-text',
    description: 'The text of a tree: a leaf as a JSON string, a node as the list of its children in key order, by structural recursion through the values of a map.',
    params: [{ name: 'n', type: 'json-node' }],
    returns: 'string',
    body: "match n { leaf(s) => format('{:json}', s), node(m) => '[' + fold(v in values(m), acc = '', let t = call node-text(v) in if acc == '' then t else acc + ',' + t) + ']' }",
    examples: [
      { args: { n: { leaf: 'a"b' } }, result: '"a\\"b"' },
      { args: { n: { node: { b: { leaf: 'x' }, a: { node: {} } } } }, result: '[[],"x"]' },
    ],
  },
  {
    id: 'is-field-id',
    description: 'ids.rs is_name, the rule of FieldId::new: an ASCII lower-case letter, then lower-case letters, digits and _, at most 64 bytes.',
    params: [{ name: 's', type: 'string' }],
    returns: 'bool',
    body: "match get(chars(s), 0) { Some(c) => isAsciiLowercase(c) && length(s) <= 64 && all(x in chars(s), isAsciiLowercase(x) || isAsciiDigit(x) || x == '_'), None => false }",
    examples: [
      { args: { s: 'title' }, result: true },
      { args: { s: 'a_1' }, result: true },
      { args: { s: 'Title' }, result: false },
      { args: { s: '' }, result: false },
      { args: { s: '1x' }, result: false },
      { args: { s: 'a-b' }, result: false },
      { args: { s: 'a'.repeat(65) }, result: false },
    ],
  },
  {
    id: 'kind-rule',
    description: 'transition.rs: the rule of a refusal, intent:<snake_case of the ErrorKind Debug name>.',
    params: [{ name: 'kind', type: 'error-kind' }],
    returns: 'string',
    body: "format('intent:{}', snakeCase(format('{:?}', kind)))",
    examples: [
      { args: { kind: 'unknown-record' }, result: 'intent:unknown_record' },
      { args: { kind: 'evaluation' }, result: 'intent:evaluation' },
    ],
  },
  {
    id: 'blank',
    description: "transition.rs create_tenant: a name is blank when str::trim leaves nothing (Rust's White_Space; U+FEFF is not one).",
    params: [{ name: 's', type: 'string' }],
    returns: 'bool',
    body: "trim(s) == ''",
    examples: [
      { args: { s: ' \t\n' }, result: true },
      { args: { s: ' 　' }, result: true },
      { args: { s: ' a ' }, result: false },
      { args: { s: '﻿' }, result: false },
    ],
  },
  {
    id: 'route-ok',
    description: 'A route starts with / and does not end with one (str::starts_with, str::ends_with).',
    params: [{ name: 's', type: 'string' }],
    returns: 'bool',
    body: "startsWith(s, '/') && (s == '/' || !endsWith(s, '/'))",
    examples: [
      { args: { s: '/a' }, result: true },
      { args: { s: '/' }, result: true },
      { args: { s: 'a' }, result: false },
      { args: { s: '/a/' }, result: false },
    ],
  },
  {
    id: 'parse-time',
    description: 'plain.rs parse_time, with the cases of its tests.',
    params: [{ name: 's', type: 'string' }],
    returns: 'result<i64, string>',
    body: 'parseTime(s)',
    examples: [
      { args: { s: '1970-01-01' }, result: { Ok: 0 } },
      { args: { s: '2000-03-01T00:00:00Z' }, result: { Ok: 951868800000 } },
      { args: { s: '2026-11-18T09:30Z' }, result: { Ok: 1794994200000 } },
      { description: 'A time needs its Z.', args: { s: '2026-11-18T09:30' }, result: { Err: 'not a UTC timestamp: "2026-11-18T09:30"' } },
      { args: { s: '18/11/2026' }, result: { Err: 'not a UTC timestamp: "18/11/2026"' } },
    ],
  },
  {
    id: 'plain-null',
    description: 'A variant named like a keyword (null) is written after the dot.',
    params: [],
    returns: 'plain-value',
    body: 'plain-value.null',
    examples: [{ args: {}, result: 'null' }],
  },
  {
    id: 'plain-text',
    description: 'Keyword-named variants and fields matched: null, if{then, else}.',
    params: [{ name: 'x', type: 'plain-value' }],
    returns: 'string',
    body: "match x { null => '', str(s) => s, if{then: t, else: e} => t + e }",
    examples: [
      { args: { x: 'null' }, result: '' },
      { args: { x: { str: 'a' } }, result: 'a' },
      { args: { x: { if: { then: 'a', else: 'b' } } }, result: 'ab' },
    ],
  },
  {
    id: 'plain-choice',
    description: 'A keyword-named variant built with keyword-named fields.',
    params: [{ name: 'c', type: 'bool' }],
    returns: 'plain-value',
    body: "if c then plain-value.if{then: 'yes', else: 'no'} else plain-value.null",
    examples: [
      { args: { c: true }, result: { if: { then: 'yes', else: 'no' } } },
      { args: { c: false }, result: 'null' },
    ],
  },
];

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const d = JSON.parse(languageSpec(undefined, { generation }));
  // Strata's ancestor_of (WG-5510), declared as crates/spec-compiler/tests/fixtures/language/spec.jsonc declares it.
  const ancestorExpr = (/** @type {string} */ name) => ({ name, type: 'expr' });
  d.types.find((/** @type {any} */ t) => t.id === 'expr').variants.push(
    { name: 'AncestorOf', fields: [ancestorExpr('x'), ancestorExpr('y'), ancestorExpr('object'), ancestorExpr('via')] });
  const ifAt = d.languages[0].operators.findIndex((/** @type {any} */ o) => o.name === 'if');
  d.languages[0].operators.splice(ifAt, 0, {
    name: 'ancestor-of', variant: 'AncestorOf', syntax: { form: 'call', token: 'ancestor_of' },
    operands: ['ref', 'ref', 'str', 'str'], result: 'bool', nulls: 'propagate', primitive: 'ancestor-of',
  });
  d.types.push(...structuredClone(TYPES));
  d.functions = structuredClone(FUNCTIONS);
  d.exampleFixtures = structuredClone(EXAMPLE_FIXTURES);
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any} d @param {string} id */
const fn = (d, id) => d.functions.find((/** @type {any} */ f) => f.id === id);

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports, with and without system.generation.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['a body that does not parse', 'function.expr-syntax', (d) => { fn(d, 'deny').body = 'auth-state{granted: acc.granted, checks: concat(acc.checks, ['; }],
  ['a let that does not parse', 'function.expr-syntax', (d) => { fn(d, 'policy-step').let[0].expr = 'format("policy:{}" policy.id)'; }],
  ['a field the struct does not have', 'function.expr-reference', (d) => { fn(d, 'deny').body = fn(d, 'deny').body.replace('acc.granted', 'acc.grant'); }],
  ['a call of a function that is not declared', 'function.expr-reference', (d) => { fn(d, 'may-attempt').let[0].expr = 'call roles(tenant, principal)'; }],
  ['a variant the union does not have', 'function.expr-reference', (d) => { fn(d, 'check-version').body = fn(d, 'check-version').body.replace('VersionConflict{', 'Conflict{'); }],
  ['an operation that does not exist', 'function.expr-reference', (d) => { fn(d, 'set-of').body = 'reverse(items)'; }],
  ['a comparison of an action with a resource', 'function.expr-type', (d) => { fn(d, 'policy-applies').body = fn(d, 'policy-applies').body.replace('a == action', 'a == resource'); }],
  ['a body of another type than the return', 'function.expr-type', (d) => { fn(d, 'next-version').body = "format('{}', version)"; }],
  ['a call with an argument of the wrong type', 'function.expr-type', (d) => { fn(d, 'deny').body = fn(d, 'deny').body.replace('[rule-check{rule, passed: false}]', '[rule-check{rule, passed: 1}]'); }],
  ['a match that leaves out a variant', 'function.match-exhaustive', (d) => { fn(d, 'roles-of').body = fn(d, 'roles-of').body.replace('System => [], ', ''); }],
  ['a match with two arms for one variant', 'function.match-exhaustive', (d) => { fn(d, 'roles-of').body = fn(d, 'roles-of').body.replace('System => [], ', 'System => [], System => [], '); }],
  ['a match arm after _', 'function.match-exhaustive', (d) => { fn(d, 'policy-step').body = fn(d, 'policy-step').body.replace('_ => call deny(acc, rule) }', '_ => call deny(acc, rule), Null => acc }'); }],
  ['a function that calls itself', 'function.recursion', (d) => { fn(d, 'set-of').body = 'if items == [] then [] else call set-of(take(items, 0))'; }],
  ['two functions that call each other', 'function.recursion', (d) => { fn(d, 'deny').body = 'call deny2(acc, rule)'; d.functions.push({ id: 'deny2', params: [{ name: 'acc', type: 'auth-state' }, { name: 'rule', type: 'string' }], returns: 'auth-state', body: 'call deny(acc, rule)', examples: [{ args: { acc: { checks: [] }, rule: 'r' }, result: { checks: [] } }] }); }],
  ['a fail in a function that declares no errors', 'function.error-unknown', (d) => { fn(d, 'deny').body = 'fail(domain-error.VersionConflict{message: rule})'; }],
  ['errors that name a type that is not a union', 'function.error-unknown', (d) => { fn(d, 'deny').errors = 'action'; }],
  ['a try of an error from another union', 'function.error-unknown', (d) => {
    d.types.push({ id: 'other-error', name: 'Other', kind: 'union', variants: [{ name: 'Other' }] });
    fn(d, 'next-version').errors = 'other-error';
    fn(d, 'next-version').examples = fn(d, 'next-version').examples.filter((/** @type {any} */ e) => !e.error);
  }],
  ['two parameters of one name', 'function.param', (d) => { fn(d, 'policy-applies').params[1].name = 'policy'; }],
  ['a parameter whose type does not resolve', 'function.param', (d) => { fn(d, 'deny').params[0].type = 'state'; }],
  ['a return type that does not resolve', 'function.param', (d) => { fn(d, 'deny').returns = 'auth'; }],
  ['a let named like a parameter', 'function.param', (d) => { fn(d, 'policy-step').let[0].name = 'acc'; }],
  ['an example whose result is wrong', 'function.example-failed', (d) => { fn(d, 'authorize').examples[2].result.allowed = true; }],
  ['an example whose error is wrong', 'function.example-failed', (d) => { fn(d, 'check-version').examples[0].error.VersionConflict.message = 'stale'; }],
  ['an example that succeeds where an error is expected', 'function.example-failed', (d) => { fn(d, 'check-version').examples[2].error = { VersionConflict: { message: 'x' } }; delete fn(d, 'check-version').examples[2].result; }],
  ['an example with an argument of the wrong type', 'function.example-failed', (d) => { fn(d, 'roles-of').examples[0].args.principal = 'Root'; }],
  ['an example naming a parameter that is not there', 'function.example-failed', (d) => { fn(d, 'set-of').examples[0].args.list = []; }],
  // WG-4957: each new rule, broken once.
  ['a call of itself on the whole parameter', 'function.recursion', (d) => { fn(d, 'mentions-field').body = MENTIONS_FIELD.replace('Not(a) => call mentions-field(a)', 'Not(a) => call mentions-field(e)'); }],
  ['a call of itself on a value it builds', 'function.recursion', (d) => { fn(d, 'mentions-field').body = MENTIONS_FIELD.replace('Through => true', 'Through => call mentions-field(expr.Now)'); }],
  ['a keyword-named field bound without a name', 'function.expr-syntax', (d) => { fn(d, 'mentions-field').body = MENTIONS_FIELD.replace('then: t', 'then'); }],
  ['a keyword-named variant the union does not have', 'function.expr-reference', (d) => { fn(d, 'plain-null').body = 'plain-value.in'; }],
  ['the unit value where a string is expected', 'function.expr-type', (d) => { fn(d, 'blank').body = "trim(()) == ''"; }],
  ['the unit value in a {} placeholder', 'function.expr-type', (d) => { fn(d, 'request-text').body = "format('{} on {:?}', (), resource)"; }],
  ['an enum value in a {:json} placeholder', 'function.expr-type', (d) => { fn(d, 'request-text').body = "format('{:json} on {:?}', action, resource)"; }],
  ['print of a value that is not an expression', 'function.expr-type', (d) => { fn(d, 'print-rule').body = "print(rule-language, 'x')"; }],
  ['print of something that is not a language', 'function.expr-reference', (d) => { fn(d, 'print-rule').body = 'print(rules, e)'; }],
  ['startsWith given a number', 'function.expr-type', (d) => { fn(d, 'route-ok').body = "startsWith(length(s), '/')"; }],
  ['a character class given a list', 'function.expr-type', (d) => { fn(d, 'is-field-id').body = 'isAsciiLowercase(chars(s))'; }],
  ['parseTime read as a number', 'function.expr-type', (d) => { fn(d, 'parse-time').body = 'parseTime(s) + 1'; }],
  ['a declared type named unit', 'type.shadows-builtin', (d) => { d.types.push({ id: 'unit', name: 'Unit', kind: 'union', variants: [{ name: 'Unit' }] }); }],
  ['an id represented as unit', 'type.repr-not-builtin', (d) => { d.types.push({ id: 'nothing-id', name: 'Nothing', kind: 'id', repr: 'unit' }); }],
  ['an example that refers to a fixture that is not declared', 'example.fixture-unknown', (d) => { fn(d, 'roles-of').examples[0].args.tenant = { fixture: 'tenant-beta' }; }],
  ['a result that refers to a fixture that is not declared', 'example.fixture-unknown', (d) => { fn(d, 'deny').examples[0].result = { fixture: 'denied' }; }],
  ['a fixture whose value is not its type', 'example.fixture-type', (d) => { d.exampleFixtures[0].value.members = 'owner'; }],
  ['a fixture whose type does not resolve', 'example.fixture-type', (d) => { d.exampleFixtures[0].type = 'tenants'; }],
  ['a fixture used for a parameter of another type', 'example.fixture-type', (d) => { fn(d, 'roles-of').examples[0].args.principal = { fixture: 'tenant-alpha' }; }],
  ['an override that makes the value another type', 'example.fixture-type', (d) => { fn(d, 'roles-of').examples[0].args.tenant = { fixture: 'tenant-alpha', with: { 'members.alpha:owner': 'owner' } }; }],
  ['an override of a field the struct does not have', 'example.fixture-override', (d) => { fn(d, 'roles-of').examples[0].args.tenant = { fixture: 'tenant-alpha', with: { member: {} } }; }],
  ['an override that goes into a map key that is not there', 'example.fixture-override', (d) => { fn(d, 'roles-of').examples[0].args.tenant = { fixture: 'tenant-alpha', with: { 'members.nobody.0': 'owner' } }; }],
  ['an override whose path has an empty step', 'example.fixture-override', (d) => { fn(d, 'roles-of').examples[0].args.tenant = { fixture: 'tenant-alpha', with: { 'members..x': [] } }; }],
];

/**
 * Readiness: each mutation leaves a gap that is an error only when system.generation is set.
 * @type {[string, string, (d: any) => void][]}
 */
export const READINESS_FIXTURES = [
  ['a function without a success example', 'ready.function-example-missing', (d) => { fn(d, 'may-attempt').examples = []; }],
  ['an error variant a function fails with but no example shows', 'ready.function-example-missing', (d) => { fn(d, 'check-version').examples = fn(d, 'check-version').examples.filter((/** @type {any} */ e) => !e.error); }],
  ['an error variant passed on by try but no example shows', 'ready.function-example-missing', (d) => { fn(d, 'next-version').examples = fn(d, 'next-version').examples.filter((/** @type {any} */ e) => !e.error); }],
];
