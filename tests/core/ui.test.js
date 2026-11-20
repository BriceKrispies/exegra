import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { checkUiConsistency, routeParams } from '../../src/core/ui.js';

// User interface constructs (WG-4865): screen, form, action, liveBinding and uiScenario; their consistency
// rules (always errors), their readiness rules (errors when system.generation is set), and client-side
// implementation machines held to the machine rules.

/** A specification using every user interface construct, ready to generate from. */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'notes', name: 'Notes', ...(generation ? { generation: { target: 'rust' } } : {}) },
    vocabulary: { verificationMethods: { review: { label: 'Review', description: 'Checked by a person.' } } },
    components: [
      { id: 'bff', name: 'BFF', category: 'computational' },
      { id: 'web', name: 'Web page', category: 'client' },
    ],
    types: [
      { id: 'summary', name: 'Post summary', kind: 'struct', fields: [{ name: 'slug', type: 'string' }, { name: 'title', type: 'string' }] },
      { id: 'series', name: 'Series', kind: 'struct', fields: [{ name: 'key', type: 'string' }, { name: 'title', type: 'string' }, { name: 'count', type: 'u32' }] },
    ],
    records: [
      { id: 'page-state', name: 'Page state', owner: 'web', key: ['id'], schemaVersion: 1, fields: [{ name: 'id', type: 'uuid' }, { name: 'online', type: 'bool' }, { name: 'heartbeatMs', type: 'u32' }, { name: 'state', type: 'string' }] },
    ],
    contracts: [
      { id: 'view-home', name: 'Home view', realisation: 'generated', outputs: [{ name: 'posts', type: 'list<summary>' }, { name: 'featured', type: 'summary' }] },
      { id: 'view-post', name: 'Post view', realisation: 'generated', inputs: [{ name: 'slug', type: 'string' }], outputs: [{ name: 'title', type: 'string' }, { name: 'id', type: 'u64' }, { name: 'series', type: 'list<series>' }, { name: 'accents', type: 'list<string>' }, { name: 'depends', type: 'list<string>' }] },
      { id: 'view-missing', name: 'Missing view', realisation: 'generated', inputs: [{ name: 'missing', type: 'string' }], outputs: [{ name: 'title', type: 'string' }] },
      { id: 'preview-text', name: 'Preview text', realisation: 'generated', inputs: [{ name: 'text', type: 'string' }], outputs: [{ name: 'blocks', type: 'list<summary>' }] },
      { id: 'view-search', name: 'Search view', realisation: 'generated', inputs: [{ name: 'q', type: 'string', optional: true }], outputs: [{ name: 'results', type: 'list<summary>' }] },
      { id: 'sign-in', name: 'Sign in', realisation: 'generated', inputs: [{ name: 'name', type: 'string' }, { name: 'password', type: 'string' }, { name: 'remember', type: 'bool', optional: true }], outputs: [{ name: 'display', type: 'string' }], errors: [{ name: 'wrong' }] },
      { id: 'save-draft', name: 'Save a draft', realisation: 'generated', policyDefault: 'deny', inputs: [{ name: 'title', type: 'string', encode: { trim: true } }, { name: 'body', type: 'string' }, { name: 'topic', type: 'string', optional: true, encode: { empty: 'null' } }, { name: 'after', type: 'u64' }, { name: 'slug', type: 'string', optional: true }, { name: 'accent', type: 'string', optional: true }, { name: 'series', type: 'string', optional: true, encode: { split: ',' } }], outputs: [{ name: 'slug', type: 'string' }] },
      { id: 'view-desk', name: 'Desk view', realisation: 'generated', outputs: [{ name: 'posts', type: 'list<summary>' }, { name: 'featured', type: 'summary' }] },
      { id: 'unpublish', name: 'Unpublish', realisation: 'generated', inputs: [{ name: 'slug', type: 'string' }], outputs: [{ name: 'ok', type: 'bool' }] },
      { id: 'sign-out', name: 'Sign out', realisation: 'generated', outputs: [{ name: 'ok', type: 'bool' }] },
      { id: 'publish', name: 'Publish', realisation: 'generated', policyDefault: 'deny', inputs: [{ name: 'post', type: 'u64' }], outputs: [{ name: 'ok', type: 'bool' }] },
    ],
    events: [
      { id: 'post-published', name: 'Post published', payload: [{ name: 'slug', type: 'string' }] },
      { id: 'went-online', name: 'Went online', payload: [{ name: 'heartbeat', type: 'u32' }] },
      { id: 'heartbeat-due', name: 'Heartbeat due', payload: [] },
    ],
    behaviors: [
      {
        id: 'page-kernel', name: 'Page kernel', subject: 'web', level: 'implementation', initial: 'offline',
        storage: { record: 'page-state', key: 'id' },
        transaction: { scope: 'transition', isolation: 'serializable' },
        variables: [{ name: 'online', type: 'boolean', initial: false, repr: 'bool' }, { name: 'heartbeatMs', type: 'number', initial: 10000, repr: 'u32' }],
        states: [{ id: 'offline', name: 'Offline' }, { id: 'live', name: 'Live', terminal: true }],
        transitions: [{ id: 't-online', from: 'offline', to: 'live', on: 'went-online', otherwise: true, effects: [{ set: 'online', to: true }, { set: 'heartbeatMs', to: 'event.heartbeat' }, { timer: 'heartbeat', after: { expr: 'heartbeatMs', simulate: 10000 }, emit: 'heartbeat-due' }] }],
      },
    ],
    policies: [
      { id: 'p-draft', subject: { principal: 'member', role: 'author' }, contract: 'save-draft', effect: 'allow' },
      { id: 'p-publish', subject: { principal: 'member', role: 'editor' }, contract: 'publish', effect: 'allow' },
    ],
    validations: [
      { id: 'v-title', contract: 'save-draft', input: 'title', rule: 'required', message: 'A title is required.' },
    ],
    screens: [
      { id: 'home', name: 'Front page', route: '/', viewModel: 'view-home', kind: 'home', title: 'Notes', auth: 'none' },
      { id: 'post', name: 'Article', route: '/posts/:slug', viewModel: 'view-post', kind: 'article' },
      { id: 'search', name: 'Search', route: '/search', query: ['q'], viewModel: 'view-search', kind: 'search' },
      { id: 'login', name: 'Sign in', route: '/login', query: ['next'], viewModel: 'view-home', kind: 'login' },
      { id: 'missing', name: 'Not found', route: '*missing', viewModel: 'view-missing', kind: 'missing' },
      { id: 'desk', name: 'Writing desk', route: '/desk', viewModel: 'view-desk', kind: 'desk', auth: 'session' },
      { id: 'editor', name: 'Editor', route: '/desk/edit/:slug', viewModel: 'view-post', kind: 'editor', auth: 'role:author', local: [{ name: 'preview', type: 'list<summary>' }] },
    ],
    forms: [
      {
        id: 'f-login', screen: 'login', contract: 'sign-in', submitLabel: 'Sign in',
        fields: [
          { name: 'name', input: 'name', label: 'Name', control: 'text', normalize: 'trim' },
          { name: 'password', input: 'password', label: 'Password', control: 'password' },
          { name: 'remember', input: 'remember', label: 'Remember me', control: 'checkbox' },
        ],
        onSuccess: { navigate: { path: 'query.next', screen: 'home' }, toast: 'Signed in as ${response.display}.' },
        onError: { show: 'inline', announce: 'Some fields need attention.' },
      },
      {
        id: 'f-draft', screen: 'editor', contract: 'save-draft', submitLabel: 'Save draft',
        fields: [
          { name: 'title', input: 'title', label: 'Title', control: 'text', initial: { path: 'title' } },
          { name: 'body', input: 'body', label: 'Text', control: 'textarea' },
          { name: 'topic', input: 'topic', label: 'Topic', control: 'select', options: [{ value: 'design', label: 'Design' }] },
          { name: 'slug', input: 'slug', label: 'Address', control: 'text', derive: 'form.title', transform: 'slug', until: 'edited' },
          { name: 'accent', input: 'accent', label: 'Accent colour', control: 'radio', optionsFrom: { path: 'accents' } },
          { name: 'series', input: 'series', label: 'Series', control: 'select', optionsFrom: { path: 'series', value: 'key', label: 'title' }, initial: { path: 'series', where: { field: 'title', equals: 'route.slug' }, value: 'key' } },
        ],
        arguments: { after: 'view.id' },
        then: { contract: 'unpublish', arguments: { slug: 'response.slug' } },
        onSuccess: { navigate: { screen: 'editor', params: { slug: 'response.slug' } }, toast: 'Draft "${form.title}" saved at ${response.slug}.', view: { title: 'form.title' } },
        onError: { show: 'inline' },
      },
    ],
    actions: [
      {
        id: 'a-publish', screen: 'editor', label: 'Publish', contract: 'publish', arguments: { post: 'view.id' },
        confirm: 'Publish this article?', confirmAnnounce: 'Publishing makes the article public.', optimistic: false,
        onSuccess: { navigate: { screen: 'post', params: { slug: 'route.slug' } }, toast: 'Published.' }, onError: { show: 'toast', prefix: 'Not done. ' },
      },
      {
        id: 'a-preview', screen: 'editor', label: 'Preview', contract: 'preview-text', form: 'f-draft', arguments: { text: 'form.title' },
        result: { into: 'preview', output: 'blocks' }, onSuccess: {}, onError: { show: 'inline' },
      },
      {
        id: 'a-unpublish', screen: 'desk', forEach: 'posts', label: 'Unpublish ${item.title}', confirm: 'Confirm unpublishing ${item.title}', contract: 'unpublish',
        arguments: { slug: 'item.slug' }, onSuccess: { navigate: { screen: 'post', params: { slug: 'item.slug' } }, toast: 'Moved back to drafts.' }, onError: { show: 'toast' },
      },
      {
        id: 'a-sign-out', screen: 'desk', label: 'Sign out', contract: 'sign-out', arguments: {}, alsoOn: { auth: 'session' },
        onSuccess: { navigate: { screen: 'login' } }, onError: { show: 'toast' },
      },
    ],
    liveBindings: [
      { id: 'lb-home', screen: 'home', event: 'post-published', refresh: 'posts' },
      { id: 'lb-featured', screen: 'post', event: 'post-published', refresh: 'whole', when: { any: ['event.slug == route.slug', { value: 'event.slug', in: 'depends' }] } },
      { id: 'lb-search', screen: 'search', event: 'went-online', refresh: 'results.title' },
    ],
    errorMessages: [
      { id: 'em-default', on: 'error', text: '${error.message}', fallback: 'That did not work.' },
      { id: 'em-check-name', on: 'check', kinds: ['required'], text: '${check.statement}', fallback: 'Check this value.', field: 'name' },
      { id: 'em-wrong', on: 'error', kinds: ['wrong'], text: 'The name or password is wrong.', appliesTo: ['f-login'] },
    ],
    uiScenarios: [
      {
        id: 'j-publish', name: 'An author publishes and a reader sees it live', verifies: ['r-live'], browsers: ['author', 'reader'], viewport: { width: 1280, height: 800 },
        steps: [
          { goto: { screen: 'login' } },
          { fill: { form: 'f-login', field: 'name', value: 'tomasz' } },
          { fill: { role: 'textbox', name: 'Password', value: 'secret' } },
          { submit: { form: 'f-login' } },
          { expectScreen: 'home' },
          { expectStatus: 200 },
          { goto: { screen: 'editor', params: { slug: 'on-sharpening' } } },
          { click: { role: 'button', name: 'Publish' } },
          { expectText: { text: 'Published.', within: { role: 'status', name: 'Notices' } } },
          { switchBrowser: 'reader' },
          { goto: { screen: 'search', params: { q: 'kiln' } } },
          { waitFor: { event: 'post-published' } },
          { expectRole: { role: 'heading', name: 'On Sharpening', state: 'visible' } },
          { goOffline: {} },
          { goOnline: {} },
          { setViewport: { width: 390, height: 844 } },
          { press: 'Escape' },
          { axeScan: {} },
          { logScan: { forbid: ['strata-dev-[a-z]+', 'secret'] } },
        ],
      },
      {
        id: 'j-steps', name: 'Every further step kind', verifies: ['r-live'], browsers: ['owner', 'thief'],
        steps: [
          { emulate: { colorScheme: 'dark', reducedMotion: 'reduce', touch: true, mobile: true } },
          { recordRequests: 'net' },
          { goto: { screen: 'home', host: 'tidewater.localhost:4200' } },
          { mark: 'doc' },
          { expectTitle: { text: 'Notes' } },
          { expectRole: { role: 'heading', level: 1, namePattern: '^Notes$', within: { role: 'main', name: 'Content' }, timeoutMs: 5000 } },
          { expectCount: { role: 'article', within: { role: 'region', name: 'Earlier essays' }, count: 5 } },
          { expectNoText: { text: 'Notes Toward a Workbench' } },
          { expectAttribute: { attribute: 'data-accent', value: 'moss' } },
          { expectAttribute: { role: 'button', name: 'Menu', attribute: 'aria-expanded', pattern: '^(true|false)$' } },
          { click: { role: 'link', name: 'Topics', within: { role: 'navigation', name: 'Sections' } } },
          { focus: { role: 'textbox', name: 'Text' } },
          { expectNoReload: 'doc' },
          { back: {} },
          { reload: true },
          { gotoPath: { path: '/no/such/route' } },
          { expectStatus: 404 },
          { expectScreen: { screen: 'post', params: { slug: 'x' }, timeoutMs: 1000 } },
          { expectRequests: { log: 'net', to: '^http://127\\.0\\.0\\.1:4200/', only: true, atLeast: 2, fromWorker: true } },
          { expectNoRequest: { log: 'net', path: '/api/view' } },
          { apiCall: { method: 'GET', path: '/api/session', expectStatus: 200, capture: { csrf: 'session.csrf_token' } } },
          { apiCall: { method: 'POST', path: '/api/records', headers: { origin: 'http://evil.example', 'x-csrf-token': '${csrf}' }, body: { op: 'update' }, expectStatus: 403, expectJson: { 'failed.0.rule': 'policy:authors_own_posts' }, expectBodyExcludes: ['${csrf}'] } },
          { apiCall: { method: 'POST', path: '/api/records', anonymous: true, expectStatus: 401 } },
          { expectCookie: { name: '__Host-sid', attributes: { secure: true, httpOnly: true, sameSite: 'Strict', path: '/', hostPrefix: true } } },
          { capture: { name: 'sid', from: 'cookie', cookie: '__Host-sid' } },
          { capture: { name: 'accent', from: 'attribute', element: { role: 'main', name: 'Content' }, attribute: 'data-accent' } },
          { capture: { name: 'snapshot', from: 'text', element: { role: 'status', name: 'Snapshot' } } },
          { capture: { name: 'corr', from: 'header', header: 'x-correlation' } },
          { switchBrowser: 'thief' },
          { setCookie: { name: '__Host-sid', value: '${sid}', host: 'tidewater.localhost', attributes: { secure: true, httpOnly: true, sameSite: 'Strict', path: '/' } } },
          { apiCall: { method: 'GET', path: '/api/session', as: 'owner', expectBodyIncludes: ['authenticated'] } },
          { expectNoEvent: { event: 'post-published', forMs: 1200 } },
          { expectNoOverflow: {} },
          { expectBeside: { a: { role: 'complementary', name: 'Notes' }, b: { role: 'article', name: 'Body' }, side: 'left' } },
          { goto: { screen: 'desk' } },
          { clickAction: { action: 'a-unpublish', item: { title: 'On Sharpening' }, confirm: true } },
          { expectText: { pattern: 'Moved back to drafts\\.', timeoutMs: 60000 } },
          { expectText: { text: '${snapshot}' } },
          { waitFor: { event: 'post-published', timeoutMs: 20000 } },
          { logScan: { forbid: ['${sid}', '${csrf}', 'strata-dev-'] } },
          { gotoPath: { path: '/login', host: 'tidewater.localhost:4200', fragment: 'i=ab&t=cd' } },
          { expectUrl: { pattern: '#i=ab&t=cd$', timeoutMs: 1000 } },
          { captureMail: { to: 'owner@tidewater.example', pattern: '#(i=[0-9a-f]{64}&t=[0-9a-f]{64})', name: 'invite', as: 'owner', timeoutMs: 8000 } },
          { gotoPath: { path: '/login', fragment: '${invite}' } },
          { expectUrl: { pattern: '#', absent: true } },
        ],
      },
    ],
    claims: [
      { id: 'r-live', kind: 'requirement', statement: 'Readers see a publication without reloading.', realisation: 'checked', evaluate: { method: 'review' } },
      { id: 'c-struct', kind: 'structural', statement: 'Pages are drawn by renderers.', evaluate: { method: 'review' } },
    ],
  };
  mutate(d);
  // Every contract states its exposure and a structured auth (contract.exposure, contract.auth-structured); a
  // contract whose test leaves them out is a local, in-process one.
  for (const c of /** @type {any[]} */ (d.contracts ?? [])) {
    if (!('exposure' in c)) c.exposure = 'local';
    if (!('auth' in c)) c.auth = { scheme: 'in-process' };
  }
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const entity = (list, id) => list.find((e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
/** @param {any} r */
const explain = (r) => r.diagnostics.map((/** @type {any} */ d) => `${d.severity} ${d.code} ${d.message}`).join('\n');
/** @param {any} d @param {number} i */
const step = (d, i) => entity(d.uiScenarios, 'j-publish').steps[i];
/** @param {any} d @param {number} i */
const st = (d, i) => entity(d.uiScenarios, 'j-steps').steps[i];
/** @param {any} d @param {number} i */
const draft = (d, i) => entity(d.forms, 'f-draft').fields[i];
/** The timer whose delay is read at run time. @param {any} d */
const timer = (d) => entity(d.behaviors, 'page-kernel').transitions[0].effects[2];

test('a specification with every user interface construct validates with no errors, no warnings and no readiness gaps', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.severity !== 'info').map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

test('an implementation machine whose subject is a client component is held to the machine rules like any other', () => {
  assert.equal(analyzeSpec(spec()).errorCount, 0);
  const r = analyzeSpec(spec((/** @type {any} */ d) => { delete entity(d.behaviors, 'page-kernel').transaction; }, { generation: false }));
  assert.deepEqual(codes(errors(r)), ['ready.transaction-missing'], explain(r));
});

test('route patterns: a catch-all route binds the unmatched path to its name', () => {
  assert.deepEqual(routeParams('*'), { params: [], catchAll: true });
  assert.deepEqual(routeParams('*missing'), { params: ['missing'], catchAll: true });
  for (const bad of ['**', '*/x', '*Missing', '/a/*']) assert.ok(routeParams(bad).error, bad);
});

test('a run-time timer delay is allowed only on an implementation-level machine', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    const b = entity(d.behaviors, 'page-kernel');
    b.level = 'model';
    for (const k of ['storage', 'transaction']) delete b[k];
    for (const v of b.variables) delete v.repr;
  }, { generation: false }));
  assert.deepEqual(codes(errors(r)), ['effect.after'], explain(r));
});

test('route patterns: "/" or literal and :param segments, no parameter twice', () => {
  assert.deepEqual(routeParams('/'), { params: [] });
  assert.deepEqual(routeParams('/desk/edit/:slug'), { params: ['slug'] });
  assert.deepEqual(routeParams('/a/:x/b/:y'), { params: ['x', 'y'] });
  for (const bad of ['', 'posts', '/posts/', '/a//b', '/:x/:x', '/a b', '/:X', '/posts?q', 7]) assert.ok(routeParams(bad).error, String(bad));
});

/** Each consistency rule, a mutation that breaks it once, and the code it reports. */
const CONSISTENCY = [
  ['a screen whose view model is not a contract', 'ref.kind', (/** @type {any} */ d) => { entity(d.screens, 'home').viewModel = 'post-published'; }],
  ['a form submitted to a contract that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.forms, 'f-login').contract = 'log-in'; }],
  ['an action on a screen that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').screen = 'nowhere'; }],
  ['a live binding on an event that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-home').event = 'post-pulled'; }],
  ['a navigation to a screen that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onSuccess.navigate.screen = 'nowhere'; }],
  ['a journey verifying a claim that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-publish').verifies = ['r-gone']; }],
  ['a route that is not a path pattern', 'screen.route', (/** @type {any} */ d) => { entity(d.screens, 'post').route = '/posts/:slug/'; }],
  ['a query parameter that repeats a route parameter', 'screen.route', (/** @type {any} */ d) => { entity(d.screens, 'post').query = ['slug']; }],
  ['two screens on one route', 'screen.route-duplicate', (/** @type {any} */ d) => { d.screens.push({ id: 'post-by-id', name: 'Article by id', route: '/posts/:slug', viewModel: 'view-post', kind: 'article' }); }],
  ['two screens whose routes tie', 'route.ambiguous', (/** @type {any} */ d) => { d.screens.push({ id: 'desk-tie', name: 'Tied desk', route: '/desk/:slug/edit', viewModel: 'view-post', kind: 'article' }); }],
  ['an authentication that is not none, session or a role', 'screen.auth', (/** @type {any} */ d) => { entity(d.screens, 'editor').auth = 'authors'; }],
  ['an empty renderer name', 'screen.kind', (/** @type {any} */ d) => { entity(d.screens, 'home').kind = ' '; }],
  ['a view-model input that is not a route parameter', 'screen.view-model-input', (/** @type {any} */ d) => { entity(d.screens, 'login').viewModel = 'view-post'; }],
  ['a form field filling an input the contract does not have', 'form.field-unknown', (/** @type {any} */ d) => { entity(d.forms, 'f-login').fields[2].input = 'stay'; }],
  ['two form fields filling one input', 'form.field-duplicate', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').fields[2] = { name: 'title2', input: 'title', label: 'Title again', control: 'text' }; }],
  ['a required input no field or argument fills', 'form.input-uncovered', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').fields.splice(1, 1); }],
  ['a select without options', 'form.options', (/** @type {any} */ d) => { delete entity(d.forms, 'f-draft').fields[2].options; }],
  ['a checkbox for a string input', 'form.control-type', (/** @type {any} */ d) => { const f = entity(d.forms, 'f-login').fields[0]; f.control = 'checkbox'; delete f.normalize; }],
  ['an empty field label', 'form.label-empty', (/** @type {any} */ d) => { entity(d.forms, 'f-login').fields[0].label = ''; }],
  ['an empty submit label', 'form.label-empty', (/** @type {any} */ d) => { entity(d.forms, 'f-login').submitLabel = '  '; }],
  ['a form argument for an input the contract does not have', 'form.argument-unknown', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').arguments.before = 'view.id'; }],
  ['a form navigation missing a route parameter', 'form.navigate-params', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.navigate.params = {}; }],
  ['a form navigation reading an undeclared output', 'form.expr-reference', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.navigate.params.slug = 'response.address'; }],
  ['a form argument of the wrong class', 'form.expr-type', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').arguments.after = 'view.title'; }],
  ['a form argument that does not parse', 'form.expr-syntax', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').arguments.after = 'view.id +'; }],
  ['an empty action label', 'action.label-empty', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').label = ''; }],
  ['an action argument for an input the contract does not have', 'action.argument-unknown', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments.force = 'true'; }],
  ['an action missing a required argument', 'action.argument-missing', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments = {}; }],
  ['an action argument reading a route parameter the screen does not have', 'action.expr-reference', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments.post = 'route.id'; }],
  ['an action argument of the wrong class', 'action.expr-type', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments.post = 'route.slug'; }],
  ['an action argument that does not parse', 'action.expr-syntax', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments.post = '(view.id'; }],
  ['an action navigation with a parameter the screen does not have', 'action.navigate-params', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onSuccess.navigate.params.page = "'2'"; }],
  ['two live bindings of one event on one screen', 'liveBinding.duplicate', (/** @type {any} */ d) => { d.liveBindings.push({ id: 'lb-home-2', screen: 'home', event: 'post-published', refresh: 'whole' }); }],
  ['a refresh of an output the view model does not have', 'liveBinding.refresh', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-home').refresh = 'drafts'; }],
  ['a refresh of a path into a json output', 'liveBinding.refresh', (/** @type {any} */ d) => { entity(d.contracts, 'view-search').outputs.push({ name: 'params', type: 'json' }); entity(d.liveBindings, 'lb-search').refresh = 'params.page'; }],
  ['an action argument of class json for a number input', 'action.expr-type', (/** @type {any} */ d) => { entity(d.contracts, 'view-post').outputs.push({ name: 'meta', type: 'json' }); entity(d.actions, 'a-publish').arguments.post = 'view.meta'; }],
  ['a refresh of a field the struct does not have', 'liveBinding.refresh', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-search').refresh = 'results.author'; }],
  ['a journey browser named twice', 'uiScenario.browsers', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-publish').browsers.push('reader'); }],
  ['a journey viewport of zero width', 'uiScenario.viewport', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-publish').viewport.width = 0; }],
  ['a journey verifying a claim that is not a requirement', 'uiScenario.verifies-not-requirement', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-publish').verifies.push('c-struct'); }],
  ['a step with two keys', 'uiScenario.step', (/** @type {any} */ d) => { step(d, 7).press = 'Enter'; }],
  ['a step of an unknown kind', 'uiScenario.step', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-publish').steps.push({ hover: { role: 'link', name: 'Topics' } }); }],
  ['a step selecting by CSS', 'uiScenario.step', (/** @type {any} */ d) => { step(d, 7).click.selector = '.toolbar a'; }],
  ['a step going to a screen that does not exist', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 0).goto.screen = 'signin'; }],
  ['a step filling a field the form does not have', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 1).fill.field = 'email'; }],
  ['a step submitting a form that does not exist', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 3).submit.form = 'f-signin'; }],
  ['a step expecting a screen that does not exist', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 4).expectScreen = 'nowhere'; }],
  ['a step switching to a browser the journey does not have', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 9).switchBrowser = 'editor'; }],
  ['a step waiting for an event that does not exist', 'uiScenario.step-reference', (/** @type {any} */ d) => { step(d, 11).waitFor.event = 'post-pulled'; }],
  ['a step going to a screen without its route parameter', 'uiScenario.goto-params', (/** @type {any} */ d) => { step(d, 6).goto.params = {}; }],
  ['a step selecting by a role that is not a WAI-ARIA role', 'uiScenario.role', (/** @type {any} */ d) => { step(d, 7).click.role = 'btn'; }],
  ['a step selecting by an empty accessible name', 'uiScenario.name-empty', (/** @type {any} */ d) => { step(d, 12).expectRole.name = ''; }],
  ['a step expecting a status that is not an HTTP status', 'uiScenario.status', (/** @type {any} */ d) => { step(d, 5).expectStatus = 42; }],
  ['a log scan pattern that is not a regular expression', 'uiScenario.pattern', (/** @type {any} */ d) => { step(d, 18).logScan.forbid.push('(unclosed'); }],
  ['a per-row action over an output that is not a list', 'action.for-each', (/** @type {any} */ d) => { entity(d.actions, 'a-unpublish').forEach = 'featured'; }],
  ['a per-row action over an output the view model does not have', 'action.for-each', (/** @type {any} */ d) => { entity(d.actions, 'a-unpublish').forEach = 'drafts'; }],
  ['a per-row label reading a field the rows do not have', 'action.label-template', (/** @type {any} */ d) => { entity(d.actions, 'a-unpublish').label = 'Unpublish ${item.author}'; st(d, 35).clickAction.item.author = 'Tomasz Wren'; }],
  ['a label reading item fields on an action that is not per-row', 'action.label-template', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').label = 'Publish ${item.title}'; }],
  ['a label placeholder that is not an item field', 'action.label-template', (/** @type {any} */ d) => { entity(d.actions, 'a-unpublish').confirm = 'Sure, ${who}?'; }],
  ['a per-row argument reading a field the rows do not have', 'action.expr-reference', (/** @type {any} */ d) => { entity(d.actions, 'a-unpublish').arguments.slug = 'item.address'; }],
  ['a level on an element that is not a heading', 'uiScenario.level', (/** @type {any} */ d) => { st(d, 10).click.level = 2; }],
  ['a heading level of 7', 'uiScenario.level', (/** @type {any} */ d) => { st(d, 5).expectRole.level = 7; }],
  ['a name pattern that is not a regular expression', 'uiScenario.pattern', (/** @type {any} */ d) => { st(d, 5).expectRole.namePattern = '(Notes'; }],
  ['a request pattern that is not a regular expression', 'uiScenario.pattern', (/** @type {any} */ d) => { st(d, 18).expectRequests.to = '[a-'; }],
  ['an element with both a name and a name pattern', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 5).expectRole.name = 'Notes'; }],
  ['a selector key inside within', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 10).click.within.css = 'nav'; }],
  ['an aria attribute read from the document element', 'uiScenario.attribute', (/** @type {any} */ d) => { st(d, 8).expectAttribute.attribute = 'aria-busy'; }],
  ['a class attribute read from an element', 'uiScenario.attribute', (/** @type {any} */ d) => { st(d, 9).expectAttribute.attribute = 'class'; }],
  ['an attribute expectation with both a value and a pattern', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 9).expectAttribute.value = 'true'; }],
  ['a negative count', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 6).expectCount.count = -1; }],
  ['a no-reload check against a marker never set', 'uiScenario.mark-undefined', (/** @type {any} */ d) => { st(d, 12).expectNoReload = 'page'; }],
  ['a no-reload check in a browser the marker was not set in', 'uiScenario.mark-undefined', (/** @type {any} */ d) => { entity(d.uiScenarios, 'j-steps').steps[31] = { expectNoReload: 'doc' }; }],
  ['a request check on a log never started', 'uiScenario.log-undefined', (/** @type {any} */ d) => { st(d, 19).expectNoRequest.log = 'web'; }],
  ['a timeout of zero', 'uiScenario.timeout', (/** @type {any} */ d) => { st(d, 5).expectRole.timeoutMs = 0; }],
  ['a host with a space', 'uiScenario.host', (/** @type {any} */ d) => { st(d, 2).goto.host = 'tide water'; }],
  ['a gotoPath fragment with a character a fragment may not hold', 'uiScenario.fragment', (/** @type {any} */ d) => { st(d, 40).gotoPath.fragment = 'i=a b'; }],
  ['an empty gotoPath fragment', 'uiScenario.fragment', (/** @type {any} */ d) => { st(d, 40).gotoPath.fragment = ''; }],
  ['a gotoPath fragment using a value never captured', 'uiScenario.capture-undefined', (/** @type {any} */ d) => { st(d, 40).gotoPath.fragment = '${token}'; }],
  ['a path that carries its fragment inline', 'uiScenario.path', (/** @type {any} */ d) => { st(d, 40).gotoPath.path = '/login#i=ab'; }],
  ['an expectUrl pattern that is not a regular expression', 'uiScenario.pattern', (/** @type {any} */ d) => { st(d, 41).expectUrl.pattern = '(#'; }],
  ['a captureMail without the address it reads', 'uiScenario.step', (/** @type {any} */ d) => { delete st(d, 42).captureMail.to; }],
  ['a captureMail as a browser the journey does not have', 'uiScenario.step-reference', (/** @type {any} */ d) => { st(d, 42).captureMail.as = 'editor'; }],
  ['a captureMail binding a name already captured', 'uiScenario.capture-duplicate', (/** @type {any} */ d) => { st(d, 42).captureMail.name = 'sid'; st(d, 43).gotoPath.fragment = '${sid}'; }],
  ['a raw path that is not absolute', 'uiScenario.path', (/** @type {any} */ d) => { st(d, 15).gotoPath.path = 'no/such/route'; }],
  ['an API reply path with brackets', 'uiScenario.json-path', (/** @type {any} */ d) => { st(d, 21).apiCall.expectJson = { 'failed[0].rule': 'x' }; }],
  ['an API call expecting a status that is not an HTTP status', 'uiScenario.status', (/** @type {any} */ d) => { st(d, 22).apiCall.expectStatus = 999; }],
  ['an API call as a browser the journey does not have', 'uiScenario.step-reference', (/** @type {any} */ d) => { st(d, 30).apiCall.as = 'editor'; }],
  ['a value used before it is captured', 'uiScenario.capture-undefined', (/** @type {any} */ d) => { st(d, 20).apiCall.headers = { 'x-csrf-token': '${csrf}' }; }],
  ['a log scan using a value never captured', 'uiScenario.capture-undefined', (/** @type {any} */ d) => { st(d, 39).logScan.forbid.push('${token}'); }],
  ['a value captured twice', 'uiScenario.capture-duplicate', (/** @type {any} */ d) => { st(d, 25).capture.name = 'sid'; }],
  ['a cookie capture that names an element', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 24).capture.element = { role: 'main', name: 'Content' }; }],
  ['an emulation that sets nothing', 'uiScenario.step', (/** @type {any} */ d) => { st(d, 0).emulate = {}; }],
  ['a per-row action clicked without its row', 'uiScenario.action-item', (/** @type {any} */ d) => { delete st(d, 35).clickAction.item; }],
  ['a row item on an action that is not per-row', 'uiScenario.action-item', (/** @type {any} */ d) => { st(d, 35).clickAction = { action: 'a-publish', item: { title: 'x' } }; }],
  ['a click of an action that does not exist', 'uiScenario.step-reference', (/** @type {any} */ d) => { st(d, 35).clickAction.action = 'a-delete'; }],
  ['an event check without its duration', 'uiScenario.step', (/** @type {any} */ d) => { delete st(d, 31).expectNoEvent.forMs; }],
  // Third set (WG-4877): options from the view model, catch-all routes, navigation from query and form values,
  // filtered live refreshes, templated toasts, run-time timer delays, derived fields and screen-local results.
  ['a select with both options and optionsFrom', 'form.options', (/** @type {any} */ d) => { draft(d, 5).options = [{ value: 'a', label: 'A' }]; }],
  ['optionsFrom on a text control', 'form.options', (/** @type {any} */ d) => { draft(d, 3).optionsFrom = { path: 'accents' }; }],
  ['optionsFrom over an output the view model does not have', 'form.options-from', (/** @type {any} */ d) => { draft(d, 4).optionsFrom.path = 'colours'; }],
  ['optionsFrom over an output that is not a list', 'form.options-from', (/** @type {any} */ d) => { draft(d, 4).optionsFrom.path = 'title'; }],
  ['optionsFrom over structs naming a field they do not have', 'form.options-from', (/** @type {any} */ d) => { draft(d, 5).optionsFrom.value = 'slug'; }],
  ['optionsFrom over structs taking values from a number field', 'form.options-from', (/** @type {any} */ d) => { draft(d, 5).optionsFrom.value = 'count'; }],
  ['optionsFrom over structs without a label field', 'form.options-from', (/** @type {any} */ d) => { delete draft(d, 5).optionsFrom.label; }],
  ['optionsFrom over strings naming a label field', 'form.options-from', (/** @type {any} */ d) => { draft(d, 4).optionsFrom.label = 'title'; }],
  ['a radio for a number input', 'form.control-type', (/** @type {any} */ d) => { entity(d.contracts, 'save-draft').inputs.find((/** @type {any} */ i) => i.name === 'accent').type = 'u32'; draft(d, 4).optionsFrom = undefined; draft(d, 4).options = [{ value: '1', label: 'One' }]; }],
  ['a second catch-all screen', 'screen.catch-all-duplicate', (/** @type {any} */ d) => { d.screens.push({ id: 'missing-2', name: 'Not found again', route: '*', viewModel: 'view-home', kind: 'missing' }); }],
  ['a catch-all route that is not "*" or "*name"', 'screen.route', (/** @type {any} */ d) => { entity(d.screens, 'missing').route = '*/x'; }],
  ['a catch-all whose view model needs an input it does not bind', 'screen.view-model-input', (/** @type {any} */ d) => { entity(d.screens, 'missing').route = '*'; }],
  ['a navigation to the catch-all screen', 'form.navigate-params', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onSuccess.navigate.screen = 'missing'; }],
  ['a journey going to the catch-all screen', 'uiScenario.goto-params', (/** @type {any} */ d) => { step(d, 0).goto.screen = 'missing'; }],
  ['a navigation address reading a query parameter the screen does not have', 'form.expr-reference', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onSuccess.navigate.path = 'query.back'; }],
  ['a navigation address that is not a string', 'form.expr-type', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onSuccess.navigate.path = "query.next == '/'"; }],
  ['a navigation parameter reading a field the form does not have', 'form.expr-reference', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.navigate.params.slug = 'form.address'; }],
  ['an action navigation parameter reading a form field', 'action.expr-reference', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onSuccess.navigate.params.slug = 'form.title'; }],
  ['a toast reading an output the contract does not have', 'form.toast-template', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onSuccess.toast = 'Signed in as ${response.name}.'; }],
  ['a toast reading a field the form does not have', 'form.toast-template', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.toast = 'Saved ${form.address}.'; }],
  ['a toast showing a list', 'form.toast-template', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.toast = 'Saved ${view.series}.'; }],
  ['a toast placeholder that is not a scope and a name', 'action.toast-template', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onSuccess.toast = 'Published ${title}.'; }],
  ['an action toast reading a form field', 'action.toast-template', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onSuccess.toast = 'Published ${form.title}.'; }],
  ['a live condition that is not a boolean', 'liveBinding.expr-type', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when.any[0] = 'event.slug'; }],
  ['a live condition reading a payload field the event does not have', 'liveBinding.expr-reference', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when.any[0] = "event.object == 'x'"; }],
  ['a live membership over a view-model value that is not a list', 'liveBinding.when', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when.any[1].in = 'title'; }],
  ['a live membership of a value of the wrong class', 'liveBinding.expr-type', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when.any[1].value = '1'; }],
  ['a live condition of an unknown shape', 'liveBinding.when', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when = { either: [] }; }],
  ['an empty list of live conditions', 'liveBinding.when', (/** @type {any} */ d) => { entity(d.liveBindings, 'lb-featured').when = { all: [] }; }],
  ['a run-time timer delay reading a variable the machine does not have', 'expr.reference', (/** @type {any} */ d) => { timer(d).after.expr = 'pingMs'; }],
  ['a run-time timer delay that is not a number', 'effect.after', (/** @type {any} */ d) => { timer(d).after.expr = 'online'; }],
  ['a run-time timer delay without its simulated delay', 'effect.after', (/** @type {any} */ d) => { delete timer(d).after.simulate; }],
  ['a run-time timer delay with another key', 'effect.after', (/** @type {any} */ d) => { timer(d).after.unit = 'ms'; }],
  ['a derived field reading itself', 'form.expr-reference', (/** @type {any} */ d) => { draft(d, 3).derive = 'form.slug'; }],
  ['a derived field of the wrong class', 'form.expr-type', (/** @type {any} */ d) => { draft(d, 3).derive = 'view.id'; }],
  ['a derivation until something other than edited', 'form.derive', (/** @type {any} */ d) => { draft(d, 3).until = 'saved'; }],
  ['a transform on a field that is not derived', 'form.derive', (/** @type {any} */ d) => { delete draft(d, 3).derive; delete draft(d, 3).until; }],
  ['two fields derived from each other', 'form.derive', (/** @type {any} */ d) => { const f = draft(d, 0); f.derive = 'form.slug'; delete f.initial; }],
  ['an action reading a form of another screen', 'action.form', (/** @type {any} */ d) => { const a = entity(d.actions, 'a-preview'); a.form = 'f-login'; a.arguments.text = 'form.name'; }],
  ['an action reading a form that does not exist', 'ref.unresolved', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').form = 'f-none'; }],
  ['an action reading a field its form does not have', 'action.expr-reference', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').arguments.text = 'form.address'; }],
  ['an action argument of the wrong class from its form', 'action.expr-type', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').arguments.text = "form.title == 'x'"; }],
  ['an action reading a form field without naming the form', 'action.expr-reference', (/** @type {any} */ d) => { delete entity(d.actions, 'a-preview').form; }],
  ['a result kept in a screen-local value the screen does not declare', 'action.result', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').result.into = 'draft'; }],
  ['a result from an output the contract does not have', 'action.result', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').result.output = 'html'; }],
  ['a result of another type than its screen-local value', 'action.result', (/** @type {any} */ d) => { entity(d.screens, 'editor').local[0].type = 'string'; }],
  ['a kept result that also navigates', 'action.result', (/** @type {any} */ d) => { entity(d.actions, 'a-preview').onSuccess = { navigate: { screen: 'home' } }; }],
  ['a screen-local value declared twice', 'screen.local', (/** @type {any} */ d) => { entity(d.screens, 'editor').local.push({ name: 'preview', type: 'string' }); }],
  ['a screen-local value of a type that does not exist', 'screen.local', (/** @type {any} */ d) => { entity(d.screens, 'home').local = [{ name: 'notes', type: 'list<note>' }]; }],
  ['an expression reading a screen-local value the screen does not declare', 'action.expr-reference', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').arguments.post = 'local.id'; }],
  // Fourth set (WG-4882): request encoding, initial values, normalization, a second call, view-model overlays,
  // refusal prefixes and announcements, confirmation announcements, alsoOn, and error messages.
  ['a trim on an input that is a number', 'contract.encode', (/** @type {any} */ d) => { entity(d.contracts, 'save-draft').inputs[3].encode = { trim: true }; }],
  ['an encoding that says nothing', 'contract.encode', (/** @type {any} */ d) => { entity(d.contracts, 'save-draft').inputs[0].encode = {}; }],
  ['an initial value that is a list for a text control', 'form.initial', (/** @type {any} */ d) => { draft(d, 0).initial = { path: 'series' }; }],
  ['an item search over a value that is not a list', 'form.initial-where', (/** @type {any} */ d) => { draft(d, 5).initial.path = 'title'; }],
  ['a trim on a select', 'form.normalize', (/** @type {any} */ d) => { draft(d, 2).normalize = 'trim'; }],
  ['a form success setting a view-model value the target screen does not have', 'form.view-overlay', (/** @type {any} */ d) => { entity(d.forms, 'f-draft').onSuccess.view = { nope: 'form.title' }; }],
  ['an action success setting a view-model value the target screen does not have', 'action.view-overlay', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onSuccess.view = { nope: 'view.id' }; }],
  ['an empty prefix on a form refusal', 'form.on-error', (/** @type {any} */ d) => { entity(d.forms, 'f-login').onError.prefix = ''; }],
  ['a blank announcement of an action refusal', 'action.on-error', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').onError.announce = ' '; }],
  ['an empty announcement of a confirmation', 'action.confirm-announce', (/** @type {any} */ d) => { entity(d.actions, 'a-publish').confirmAnnounce = ' '; }],
  ['an action also offered with an unknown authentication', 'action.also-on', (/** @type {any} */ d) => { entity(d.actions, 'a-sign-out').alsoOn.auth = 'admins'; }],
  ['an error message naming an error no contract answers', 'errorMessage.kinds', (/** @type {any} */ d) => { entity(d.errorMessages, 'em-wrong').kinds = ['gone']; }],
  ['a field on an error message rather than a check', 'errorMessage.field', (/** @type {any} */ d) => { entity(d.errorMessages, 'em-default').field = 'name'; }],
  ['a check message filling in the error message', 'errorMessage.template', (/** @type {any} */ d) => { entity(d.errorMessages, 'em-check-name').text = '${check.statement} ${error.message}'; }],
  ['an error message applying to one form twice', 'errorMessage.applies-to', (/** @type {any} */ d) => { entity(d.errorMessages, 'em-wrong').appliesTo = ['f-login', 'f-login']; }],
  ['a second default error message', 'errorMessage.duplicate', (/** @type {any} */ d) => { d.errorMessages.push({ id: 'em-default-2', on: 'error', text: 'Something went wrong.' }); }],
];

for (const [title, code, mutate] of CONSISTENCY) {
  for (const generation of [false, true]) {
    test(`ui consistency: ${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation }));
      assert.deepEqual(codes(errors(r)), [code], explain(r));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

// Screens whose routes differ in segment count or in literal count do not tie (route.ambiguous is not reported).
test('ui consistency: screens whose routes differ do not tie', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    d.screens.push({ id: 'desk-short', name: 'Desk slug', route: '/desk/:slug', viewModel: 'view-post', kind: 'article' });
    d.screens.push({ id: 'posts-new', name: 'New post', route: '/posts/new', viewModel: 'view-home', kind: 'desk' });
  }));
  assert.deepEqual(codes(errors(r)), [], explain(r));
});

// A second call that is not an object: the metamodel accepts only objects for then, so the rule is checked on the model.
test('ui consistency: a second call that is not an object is reported once as form.then', () => {
  const r = analyzeSpec(spec());
  entity(r.model.byKind.form, 'f-draft').data.then = 'unpublish';
  assert.deepEqual(codes(checkUiConsistency(/** @type {any} */ (r.model))), ['form.then']);
});

/** Each readiness rule, a mutation that breaks it once, and the code it reports. */
const READINESS = [
  ['a screen without a view model', 'ready.screen-view-model-missing', (/** @type {any} */ d) => { delete entity(d.screens, 'login').viewModel; }],
  ['a screen without a renderer', 'ready.screen-kind-missing', (/** @type {any} */ d) => { delete entity(d.screens, 'login').kind; }],
  ['a form field without a label', 'ready.form-field-label-missing', (/** @type {any} */ d) => { delete entity(d.forms, 'f-login').fields[2].label; }],
  ['an action without onSuccess', 'ready.action-on-success-missing', (/** @type {any} */ d) => { delete entity(d.actions, 'a-publish').onSuccess; }],
  ['an action without onError', 'ready.action-on-error-missing', (/** @type {any} */ d) => { delete entity(d.actions, 'a-publish').onError; }],
  ['a contract a form submits to, governed by policies, without a policyDefault', 'ready.policy-default-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'save-draft').policyDefault; }],
  ['a contract an action calls, governed by policies, without a policyDefault', 'ready.policy-default-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'publish').policyDefault; }],
  ['forms and actions with no default error message', 'ready.error-message-default-missing', (/** @type {any} */ d) => { d.errorMessages.splice(0, 1); }],
];

for (const [title, code, mutate] of READINESS) {
  test(`ui readiness: ${title} is exactly one ${code} error when generation is set`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(codes(errors(r)), [code], explain(r));
    assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
  });

  test(`ui readiness: ${title} is no validation diagnostic without the switch and readinessGaps lists ${code}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation: false }));
    assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.code.startsWith('ready.')), []);
    assert.equal(r.errorCount, 0);
    assert.deepEqual(codes(readinessGaps(/** @type {any} */ (r.model))), [code]);
  });
}
