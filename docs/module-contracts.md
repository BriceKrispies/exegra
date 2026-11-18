# Module contracts

The binding interfaces between Exegra's modules. Read the real source for the
semantic core (`src/core/*.js`, all written); this document fixes the interfaces
of the modules around it. If a contract here conflicts with core source, the
core source wins — report the conflict.

## Ground rules (all modules)

- Vanilla JavaScript, native ES modules, JSDoc types. No frameworks, no new
  dependencies (available: `three`, `jsonc-parser`, dev: `vite`, `@playwright/test`, `typescript`).
- `src/core/**` must not import `three`, touch the DOM, or use Node-only APIs.
  It runs unchanged in the browser and in Node 24.
- JSON import syntax: `import x from './file.json' with { type: 'json' }`.
- Determinism: no `Date.now()`, `Math.random()`, or iteration-order dependence
  on anything but declaration order or explicit sorting, in core and generators.
- No hardcoded knowledge of a particular project (no entity ids from a spec in
  code). Categories, relationship kinds, shapes, colors come from `model.meta`.
- Nothing decorative that implies meaning. Nothing that looks functional but is not.
- Never present a claim as verified because it exists. Statuses come only from
  `ClaimResult`s.

## Semantic core (written — read the source)

| File | Exports |
|---|---|
| `src/core/types.js` | JSDoc typedefs: `Model`, `Entity`, `Ref`, `Diagnostic`, `Loc`, `Operation`, `TransactionResult`, `SceneModel`, `SceneNode`, `SceneEdge`, `Placement` |
| `src/core/metamodel.json` | entity kinds and property definitions as data |
| `src/core/parse.js` | `parseSpec(text)`, `SCHEMA_VERSION`, `BASE_METAMODEL` |
| `src/core/validate.js` | `validateModel(model)` |
| `src/core/analyze.js` | `analyzeSpec(text) -> {model, diagnostics, errorCount}` |
| `src/core/expr.js` | `parseExpr`, `evalExpr`, `exprRefs`, `evaluate`, `ExprError` |
| `src/core/hash.js` | `stableStringify`, `normalize`, `semanticHash`, `hashString` |
| `src/core/query.js` | `entityLabel`, `componentOf`, `childrenOf`, `ancestorsOf`, `descendantsOf`, `ownedBy`, `inboundRefs`, `relationshipsOf`, `componentGraph`, `dependencies`, `selectComponents`, `contractsOf`, `declarationSite` |
| `src/core/operations.js` | `OPERATIONS`, `planDelete`, `parseLayout`, `OpError`, `EMPTY_LAYOUT` |
| `src/core/project.js` | `Project` (apply / undo / redo / reload / subscribe / history) |
| `src/core/claim-methods.js` | `CLAIM_METHODS`, `CLAIM_STATUSES` |

Model essentials: `model.entities: Map<id, Entity>`; `model.byKind[kind]: Entity[]`
(declaration order); `Entity = {id, kind, data, owner, path, loc}` where `data` is
the raw JSON declaration (references are id strings). `model.meta.categories[id]
= {label, shape, color, description}`; `model.meta.relationshipKinds[id] = {label,
line, color, dependency, description}`; `model.meta.entities[kind].properties[name]`
are property definitions (`type`: id, string, text, boolean, number, enum, ref, expr,
list, object, map, entities, effect, evaluation, any; plus `label`, `doc`, `required`,
`values`/`valuesFrom`, `ref`, `items`, `fields`, `extension`).

## Simulation — `src/core/engine.js` and the Rust engine (`engine/`)

Discrete-event execution of the state machines (`behavior` entities) named by a
`scenario`. Pure and deterministic. The engine is the Rust crate
`engine/exegra-engine`, compiled to WebAssembly (`engine/exegra-engine-wasm`,
bound into `src/engine/pkg/` by `npm run build:engine`); `src/core/engine.js` is
the only module that loads it. It reads the engine input of `src/core/sim-input.js`
and nothing else ([simulation.md](simulation.md), "Engine input and trace format").

```js
initEngine() -> Promise<void>   // Node: loads synchronously (the promise is already settled); browser/worker: await it
runEngine(input | inputJsonText) -> Trace     // synchronous after initEngine(); a refusal throws Error(message)
runEngineText(inputJsonText) -> string        // the same, JSON text in and out
runScenario(model, scenarioId, opts?) -> Trace
//   opts.faults?: string[]  active fault ids; default = scenario.data.faults ?? []
//   = runEngine(simulationInput(model, scenarioId, opts.faults))
createTraceCursor(trace) -> Simulation        // stepwise view of a finished trace
createSimulation(model, scenarioId, opts?) -> Simulation   // createTraceCursor(runScenario(...))

Simulation = {
  scenarioId, faults: string[],
  initial: Configuration,
  config: Configuration,          // after the last revealed step
  steps: TraceStep[],             // revealed so far
  outcome: 'running'|'quiescent'|'step-limit'|'error',   // 'running' while steps remain hidden
  step(): TraceStep|null,         // reveal the next recorded step; null at the end
  run(): Trace,                   // reveal the rest
  reset(): void,                  // hide every step again
  trace(): Trace,                 // the revealed prefix as a trace
}
Trace = { scenarioId, faults, initial, steps, outcome, final: Configuration }
Configuration = {
  time: number,
  machines: { [behaviorId]: { state: stateId, vars: { [name]: boolean|number|string } } },
  pending: { seq, time, event, payload, source }[]   // queue, in delivery order
}
TraceStep = {
  index: number, time: number,
  kind: 'deliver'|'drop'|'delay',
  event: { id, payload, seq, source },
  //   source: {kind:'scenario', step:number} | {kind:'transition', transition, behavior} | {kind:'fault', fault}
  fired: { behavior, transition, from, to, guard: string|null,
           sets: { variable, before, after }[],
           emitted: { event, time, seq, payload }[] }[],
  ignored: { behavior, reason: 'no-transition'|'guard-false'|'disabled', considered: string[] }[],
  faults: { fault, effect: 'dropped'|'delayed'|'enabled'|'disabled'|'injected' }[],
  responsible: string[],     // ids of every entity that explains this step: event, transitions, behaviors, their subject components, faults
  config: Configuration,     // after the step (deep copy)
  error?: { message: string }
}
```

Semantics (must be implemented exactly; they are documented to users):

1. Logical time is a number starting at 0. The queue is ordered by `(time, seq)`;
   `seq` is assigned in scheduling order starting at 0: scenario `steps` in
   declaration order first, then `inject-event` faults in `faults` order, then
   emitted events as they are produced.
2. One step removes the head of the queue and sets `time` to its time.
3. Faults on delivery, counting occurrences per event id over delivery attempts
   (1-based; a fault with no `occurrence` applies to every occurrence):
   `drop-event` → the step has kind `drop`, nothing fires. `delay-event` → the
   event is re-queued at `time + by` with a fresh `seq`, step kind `delay`; an
   event already delayed by that fault is not delayed again.
4. Otherwise the event is delivered to every behavior of the scenario, in
   `scenario.data.behaviors` order. Guards of all behaviors are evaluated against
   the configuration as it was when the step began (snapshot). Each behavior fires
   at most one transition: the first, in declaration order, whose `from` is the
   behavior's current state, whose `on` is the event, which is enabled, and whose
   guard (if any) is true. A `faultOnly` transition is enabled only while an
   `enable-transition` fault names it; `disable-transition` disables a transition.
5. Effects run in order. `{"set": v, "to": x}`: `x` is a literal or, when a string,
   an expression; evaluated against the behavior's current variables (already
   updated by earlier effects of the same transition) and the step's event.
   `{"emit": e, "after": n, "payload": {...}}`: schedules `e` at `time + (after ?? 0)`;
   string payload values are expressions, others literals.
6. Expression scope: bare name = variable of the transition's behavior, or `time`;
   `event.<field>` = payload of the delivered event; `<behaviorId>.<var>` and
   `<behaviorId>.state` (the current state id) = any behavior of the scenario.
7. The run ends `quiescent` when the queue is empty, `step-limit` after
   `scenario.data.maxSteps ?? 1000` steps, `error` when an expression fails
   (the failing step carries `error`).

## Claims — `src/core/claims.js`

```js
evaluateClaims(model, opts?) -> ClaimResult[]      // every claim, declaration order
evaluateClaim(model, claimId, opts?) -> ClaimResult
checkTrace(model, trace) -> { claimId, holds: boolean, pending?: boolean, stepIndex?: number, explanation: string }[]
//   every invariant/temporal claim that lists the trace's scenario in
//   evaluate.scenarios and whose referenced behaviors are all in that scenario,
//   evaluated against that trace (used live by the simulator UI).
//   pending: the check is undecided on an unfinished or unevaluable trace (for
//   example an eventually still waiting, an absence that may still happen, an
//   implication whose antecedent was never true on a finished trace); it is
//   reported with holds: false but is not a violation.

opts = { recorded?: Recorded }
Recorded = { results: { [evidenceId]: { outcome: 'pass'|'fail', detail?: string, ranAt?: string } } }

ClaimResult = {
  claimId, kind, method: string|null,
  status: 'verified'|'supported'|'model-holds'|'violated'|'inconclusive'|'not-evaluated',
  evaluator: string,         // e.g. "exegra.structural/0.1", "exegra.trace/0.1", "exegra.evidence/0.1", "none"
  semanticHash: string,      // hash of the model the result was computed from
  scope: string,             // one sentence: what exactly was checked and what was not
  explanation: string,       // why this status
  assumptions: string[],     // assumption ids the result rests on
  involved: string[],        // entity ids to highlight: subjects + everything the evaluation touched
  counterexample?: { summary: string, entities: string[], path?: string[], scenario?: string, stepIndex?: number },
  evidence: { id, kind, ref, supports: boolean, recorded: 'pass'|'fail'|'none', detail?: string }[]
}
```

Status rules:

- Unsupported method (not in `CLAIM_METHODS`) → `not-evaluated`.
- `model-holds` is the status of a metric-bound claim over the model, with its stated parameters: it holds
  in the model at the stated confidence over its runs. It is never `verified` or `supported`, and says nothing
  about a system until calibrated (docs/simulation.md, Claims over metrics).
- Structural methods (see `claim-methods.js` for parameters; selectors via
  `selectComponents`; relationship endpoints resolved with `componentOf`):
  holds → `verified`; fails → `violated` with a concrete counterexample
  (relationship ids / path of component ids and relationship ids); a required
  selector that selects nothing → `inconclusive` (vacuous truth is not reported
  as verified).
- `state-invariant`, `precedes`, `eventually`, `never`: run each listed scenario
  with its declared faults via `runScenario`. All hold → `verified`, with scope
  stating it is a check of those traces only, not of all executions. Any
  violation → `violated` with `scenario` and `stepIndex`. A run ending in `error`
  → `inconclusive`. Invariant expressions resolve `<behaviorId>.<var>`,
  `<behaviorId>.state` and `time` against a `Configuration`.
  Matchers: `{event: id}` matches steps of kind `deliver` for that event;
  `{transition: id}` matches steps where that transition fired.
- `external-evidence`: no evidence → `not-evaluated`. Any contradicting evidence
  (`supports: false`) or recorded `fail` → `violated`. Otherwise at least one
  `test` evidence with recorded `pass`, or at least one non-test evidence →
  `supported`; the explanation must say whether Exegra executed anything or the
  evidence is author-entered only. Only `test` evidence with no recorded result →
  `inconclusive`.
- A model-evaluated claim that also has evidence: a recorded `fail` or
  contradicting evidence turns `verified` into `violated`.

## Projections and layout — `src/core/projections.js`, `src/core/layout.js`

```js
listViews(model) -> { id, name, projection, description, declared: boolean }[]
//   declared `view` entities in order, then an implicit view for each projection
//   type that has no declared view (ids 'structural', 'claims', 'behavior', 'references')
project(model, viewId, ctx) -> SceneModel
registerProjection(name, fn)       // fn(model, view, ctx) -> SceneModel

ctx = {
  collapsed?: Set<string>, hidden?: Set<string>, isolate?: string|null,
  focusClaim?: string|null, focusScenario?: string|null,
  focusEntity?: string|null,                   // the references projection's centre: any entity id
  claimResults?: ClaimResult[], trace?: Trace|null, stepIndex?: number   // stepIndex -1 = initial configuration
}

layoutScene(scene, pinned?, opts?) -> Placement
//   pinned: Record<sceneNodeId, [x, z]> absolute ground-plane positions for leaf nodes
//   opts: { method?: 'layered'|'layered-down'|'packed'|'radial'|'auto',   // default 'layered'
//           aspect?: number }                                              // target width/depth, default 1.6
//   An unknown method throws.
chooseLayout(scene, pinned?, opts?) -> { method, placement, scores }
//   runs every method in LAYOUT_METHODS, scores each (layout/score.js) and returns the
//   lowest total; scores: Record<method, { total, aspect, edgeLength, crossings, area }>
LAYOUT_METHODS: { id, label, description }[]      // the four concrete methods, not 'auto'
scorePlacement(scene, placement, { aspect? }) -> Score
```

`structural`: components passing the view filter; subsystems with visible children
are container nodes; a collapsed subsystem is a leaf with a child-count badge;
relationships are edges resolved to components and lifted to the nearest visible
ancestor (`lifted: true`), dropped when both ends lift to the same node. `isolate`
shows only that subsystem's subtree. Node `status: 'violated'` when a violated
claim result involves it. `display.colorBy`: category (default) | implementation | trustZone.

`claims`: with `focusClaim`: the claim (diamond), its assumptions, its evidence,
the involved components and the relationships among them; edges claim→subject,
claim→assumption, evidence→claim; counterexample entities carry `status:
'violated'`. Without focus: every claim with its subjects. Claim node `status` is
the claim result status (or `not-evaluated`).

`references` (`display.depth` 1 to 3, `filter.entityKinds`): with `ctx.focusEntity`, that entity (badge `focus`)
and every entity within `depth` reference hops in either direction, any kind (built-in kinds have a fixed
shape and colour; kinds declared by the specification take them from the meta-model); edges are the
references between drawn entities, labelled by property, and a relationship whose two components are
drawn becomes an edge instead of a node. At most 150 entities are drawn, nearest first, with a note
naming what was left out. Without focus: nothing, with a note, unless `filter.entityKinds` selects at
most 300 entities, which are then all drawn.

`behavior`: with `focusScenario`: one container per behavior of the scenario
(label = behavior name, sublabel = subject component name), states as capsule
nodes, transitions as edges (label `event [guard]`), events as sphere nodes
outside containers with edges state→event (emits) and event→state (triggers).
Without focus: every behavior. With `trace`/`stepIndex`: the current state of each
machine has `status: 'active'`, transitions fired in that step and the delivered
event have `status: 'active'`.

Layout: deterministic layout on the ground plane (x right, z toward the
viewer), recursive over containers, by one of four methods (`layered`, the default;
`layered-down`; `packed`; `radial`) or the lowest-scoring of the four (`auto`); container rect = bounding box of its children
plus padding; pinned leaves sit at their pinned position. Leaf footprint about
2.6 × 1.6 units; gaps about 1.4. Position carries no meaning; containment does.

## Renderer — `src/render/scene-view.js`

```js
createSceneView(host: HTMLElement, callbacks) -> SceneView
callbacks = {
  onSelect(id: string|null),            // click on node or edge (entity id), null on empty space
  onHover(id: string|null),
  onActivate(id: string),               // double click
  onMoveEnd(moves: {id, x, z}[]),       // drag finished; leaf ids with absolute positions
  onConnect(fromId, toId),              // connect mode: two successive node clicks
}
SceneView = {
  setScene(scene: SceneModel, placement: Placement): void,   // incremental diff by node/edge id
  setSelection(ids: string[]): void,
  setHighlight(ids: string[]|null): void,   // emphasise these, dim everything else; null clears
  setMode(mode: 'select'|'connect'): void,
  setCameraMode(mode: 'perspective'|'top'): void,
  fit(ids?: string[]): void,                // animated fit-to-selection / fit-to-system
  getCamera(): object, setCamera(state: object): void,   // JSON-serialisable
  pulse(ids: string[]): void,               // brief emphasis for simulation steps (edges: travelling marker)
  getStats(): { fps, frameMs, drawCalls, triangles, nodes, edges, labels },
  screenPoint(id: string): {x, y}|null,     // client coordinates of a node centre / edge midpoint (for tests and overlays)
  dispose(): void,
}
```

## Persistence — `tools/workspace.js` (Node), `tools/vite-plugin-exegra.js`, `src/persist/client.js`

Project directory: `specs/<name>/` with `spec.jsonc`, `layout.jsonc`, optional
`evidence/results.json` (recorded results), `generated/` (generated artifacts),
`.history/journal.jsonl` (append-only write journal).

```js
// src/persist/client.js (browser)
listProjects() -> Promise<{name, title}[]>
readProject(name) -> Promise<{ spec: {text, hash}, layout: {text, hash}|null, recorded: object|null }>
writeFile(name, file: 'spec'|'layout', text, baseHash: string|null, meta?: {label, origin})
  -> Promise<{ok: true, hash} | {ok: false, conflict: true, current: {text, hash}} | {ok: false, error: string}>
writeGenerated(name, files: Record<string, string>) -> Promise<{ok, written: string[]}>
watchProject(name, onChange: ({file: 'spec'|'layout'|'recorded', hash}) => void) -> () => void   // SSE
exportProject(name) -> Promise<Bundle>
importProject(name, bundle) -> Promise<{ok, error?}>
Bundle = { format: 'exegra-project', version: 1, name, files: { 'spec.jsonc': string, 'layout.jsonc'?: string, 'evidence/results.json'?: string } }
```

## Application session — `src/app/session.js` (written by the coordinator)

The single object UI modules talk to. UI modules never mutate the model except
through `session.apply`, and never keep their own copy of semantic state.

```js
session.projects: {name, title}[]          session.projectName: string
session.refreshProjects(): Promise<void>   // re-read the project list (after an import)
session.project: Project                   session.model: Model|null
session.diagnostics: Diagnostic[]
session.open(name): Promise<void>

session.apply(ops, {label?}) -> TransactionResult     // commits, persists, logs; failures are logged and returned
session.undo(), session.redo()
session.saveState: 'saved'|'saving'|'conflict'|'error'|'readonly'   // readonly: production build, no persistence
session.resolveConflict('reload'|'overwrite')

session.selection: string|null             session.select(id|null, {source?: string})
session.hover: string|null                 session.setHover(id|null)
session.views: listViews() result          session.viewId: string
session.setView(viewId)
session.ui: { collapsed: Set<string>, hidden: Set<string>, isolate: string|null,
              cameraMode: 'perspective'|'top', mode: 'select'|'connect',
              focusClaim: string|null, focusScenario: string|null }
session.toggleCollapsed(id), session.setHidden(id, bool), session.setIsolate(id|null),
session.setCameraMode(m), session.setMode(m), session.focusClaim(id|null), session.focusScenario(id|null)

session.scene: SceneModel                  session.placement: Placement
session.layout: { methods: LAYOUT_METHODS, requested: 'auto'|methodId, used: methodId,
                  scores: Record<methodId, Score>, aspect: number }
session.setLayoutMethod('auto'|methodId)   // per project and view, kept in browser storage; presentation only
session.setViewportAspect(width/height)    // what 'auto' aims at; clamped to 0.5..3.5, small changes ignored
session.claimResults: ClaimResult[]        session.claimResult(id) -> ClaimResult|undefined
session.recorded: Recorded|null

session.sim: { scenarioId: string|null, faults: string[], simulation: Simulation|null,
               stepIndex: number, playing: boolean, checks: checkTrace() result }
session.simLoad(scenarioId, faults?), session.simStep(), session.simBack(), session.simReset(),
session.simRunToEnd(), session.simPlay(bool), session.simSeek(stepIndex), session.simSetFaults(ids)

session.revealSource(id)        // ask the source editor to show an entity's declaration
session.requestFit(ids?)        // ask the scene to fit
session.log: {seq, kind: 'change'|'error'|'info'|'save', message, detail?, diagnostics?}[]
session.note(kind, message, detail?)

session.on(type, fn) -> unsubscribe
//  types: 'project' (opened/switched), 'model' (any commit), 'selection', 'hover', 'view',
//         'ui', 'scene' (scene or placement recomputed), 'claims', 'sim', 'save', 'log',
//         'reveal-source' ({id}), 'fit' ({ids})
```

## HTML/CSS conventions

- `index.html` contains the static semantic skeleton; panels are mounted by
  `mountX(element, session)` functions exported from `src/ui/*.js`.
- CSS in `src/styles/`, one file per layer or component group, imported from
  `src/styles/main.css`, which declares
  `@layer reset, tokens, base, layout, components, states, utilities;`.
  Every rule lives inside a layer. Class names are component-scoped:
  `.explorer`, `.explorer__row`, `.explorer__row--selected` (block__element--modifier).
- Tokens (custom properties on `:root`, defined in `tokens.css`): surfaces
  `--surface-0..3`, text `--text-1..3`, borders `--line-1..2`, accent `--accent`,
  semantic `--ok`, `--ok-external`, `--warn`, `--bad`, `--none`, palette roles
  `--c-slate`, `--c-blue`, `--c-amber`, `--c-teal`, `--c-violet`, `--c-steel`,
  `--c-rose`, `--c-green`, `--c-red`, `--c-neutral`, spacing `--s-1..6`,
  type `--font-ui`, `--font-mono`, `--fs-1..4`, radius `--r-1..2`, elevation `--shadow-1..2`.
- Native elements: `<button>`, `<nav>`, `<section>`, `<header>`, `<dialog>`,
  `<label>`, `<output>`, `<details>`. Every control keyboard reachable with a
  visible `:focus-visible` ring. Every icon-only button has `aria-label`.
- Stable hooks for browser tests: `data-testid` on key controls and
  `data-entity-id` on any element that represents an entity.
