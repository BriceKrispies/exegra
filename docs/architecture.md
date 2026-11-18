# Architecture

Exegra has one semantic core and several things attached to it. Everything the user sees is derived from the core or submits operations to it.

```
 specification text (spec.jsonc)  +  layout text (layout.jsonc)
                 |                          |
                 v                          v
        parse + validate  ->  Model     parseLayout
                 |
   Project (transactions: apply / undo / redo / reload)
                 |
        subscribe(commit)
                 |
      Session (src/app/session.js)
        |        |         |            \
   claims     projections  simulation    persistence (dev only)
   (claims.js) (projections.js,  (engine.js ->   (src/persist/client.js)
                layout.js)       lean.js -> the
                                 Lean core as
                                 WebAssembly; a
                                 Web Worker for
                                 the Simulation tab)
        |
   UI panels, Three.js scene view, CLI
```

## Semantic architecture

**Source is the authority.** `Project` (`src/core/project.js`) holds two texts: the specification and the presentation layout. The model, diagnostics, `errorCount` and the semantic hash are derived from the specification text by `analyzeSpec` (`parse.js` then `validate.js`) and are replaced as a whole on every commit. An operation (`operations.js`) never mutates the model. It computes source-preserving JSONC edits (via `jsonc-parser`, plus `text-edit.js` for array insertion), and `Project` re-derives the model from the edited text.

**The model** (`Model` in `types.js`) is an immutable snapshot: `entities` by id in declaration order, `byKind`, `refs` (every reference with its source location), `exprs` (every expression string), the effective meta-model `meta` and the raw `vocabulary`. Nested entities (ports, states, transitions) are entities with an `owner`.

**Commit.** `Project.apply` checks revision and hash preconditions, applies all operations to a scratch `Tx`, validates the resulting text, and only then commits: text swapped, model re-derived (only when the specification text changed; a presentation-only commit keeps the model), `revision` incremented, a history entry and undo record pushed, listeners notified synchronously. Any failure leaves the project unchanged. Details are in [transactions-and-persistence.md](transactions-and-persistence.md).

**Derived services**, all pure functions of the model (no DOM, no clock, no randomness):

| Module | Derives |
|---|---|
| `hash.js` | normal form and 53-bit hash of the semantic content (excludes comments, whitespace, key order, top-level declaration order, locations and layout) |
| `query.js` | labels, containment, ownership, inbound references, component graph, dependency traversal, selectors |
| `claims.js`, `claim-methods.js` | claim results with status, scope and counterexample ([claims-and-evidence.md](claims-and-evidence.md)) |
| `engine.js`, `sim-input.js` | scenario traces: `sim-input.js` derives the engine input, `engine.js` runs it on the Lean core (`formal/`) compiled to WebAssembly ([simulation.md](simulation.md)) |
| `lean.js` | the call boundary to the Lean core: a JSON request `{fn, args}` to `{ok}` or `{error}` ([module-contracts.md](module-contracts.md)) |
| `projections.js` | a `SceneModel` per view (`structural`, `claims`, `behavior`, `references`, `data`; `reader` draws no scene) |
| `reader.js` | the page of a reader view: text, counts, tables, lists, document sections and an index of kinds, shown by `src/ui/reader.js` in place of the scene |
| `layout.js`, `layout/*` | a `Placement` per `SceneModel`, by one of four methods or an automatic choice among them |
| `generate/` | five artifacts ([self-hosting.md](self-hosting.md)) |

**Session** (`src/app/session.js`) is the one object UI modules talk to. It owns no semantic state. It holds the `Project`, memoised derived values (claim results, scene, placement, simulation) and interaction state that is deliberately not in the specification: selection, hover, active view, collapsed/hidden/isolated sets, camera mode, mode, the chosen layout method per view (`session.layout`) and the shape of the viewport. Interaction state is remembered per project in `localStorage`; the camera per project and view in `sessionStorage`. The Simulation tab's runs go to a Web Worker (`src/app/engine-worker.js`, through `src/app/engine-runner.js`) that loads the same WebAssembly engine, so a long run never blocks the page; the session steps through the finished trace with a cursor.

## Rendering and projection architecture

A **projection** turns the model into a flat `SceneModel` of nodes and edges. Every node and edge is backed by an entity (`entityId`), and each scene carries `notes` stating what the view does and does not show. Four projections are registered: `structural`, `claims`, `behavior` and `references`. A specification declares **views** (name, projection, filter, display); a projection with no declared view gets an implicit one. Projection inputs besides the model are interaction state (collapsed, hidden, isolate, focused claim and scenario), claim results, and the current simulation trace and step.

**Structural** draws components as nodes and relationships as edges. Collapsing a subsystem lifts edges to the collapsed container and drops internal ones; relationships of the same kind between the same two drawn nodes are bundled into one labelled line. Filters (`categories`, `relationshipKinds`, `within`, `tags`) and `display.colorBy` (`category`, `implementation`, `trustZone`) apply here. **Claims** draws a claim with the entities it involves and its status. **Behavior** draws the state machines of a scenario, marking visited and active states and transitions at the current step. **References** draws the selected entity (any kind, built-in or declared by the specification's vocabulary) and its reference neighbourhood: every entity that refers to it or is referred to by it, up to `display.depth` hops (1 to 3, default 1), as nodes whose shape and colour come from the meta-model, with an edge for each reference, labelled by the property that holds it; a relationship between two drawn components is drawn as an edge instead of a node. `filter.entityKinds` restricts the drawn kinds; the focus is always drawn. At most 150 entities are drawn, nearest first, and a note says how many were left out and of which kinds. Without a selection the view draws nothing and says how to start, except that a filter naming at most 300 entities in total draws all of them. The session passes the current selection as `ctx.focusEntity`.

**Layout** (`layout.js`, `layout/*`) is deterministic, on the ground plane, recursive over containers: containers enclose their children, siblings never overlap, and a leaf may be **pinned** to an absolute `[x, z]` from `layout.jsonc` (containers are then re-fitted around their children). There are four methods, `LAYOUT_METHODS`:

| Method | Arrangement of siblings |
|---|---|
| `layered` | Dependency layers flowing left to right at the root, alternating direction per nesting level (front to back one level in); a long run of layers wraps into rows. The default method. |
| `layered-down` | The same layers flowing front to back at the root. |
| `packed` | No flow direction: strongly connected siblings sit next to each other, shelf-packed towards the target aspect. |
| `radial` | The best-connected sibling at the centre, the rest on concentric rings by graph distance, stretched to the target aspect. |

Each takes a target aspect (width over depth; default 1.6), which is the shape of the viewport.

**Automatic choice.** `chooseLayout` runs all four methods, scores each placement and takes the lowest total (a tie goes to the earlier method in the list above). `scorePlacement` in `layout/score.js` computes, over the bounding box of every placed rectangle and the leaf nodes:

```
total = 3 * aspect + 0.3 * edgeLength + 1 * crossings + 0.25 * area
aspect     = | ln( (W / D) / targetAspect ) |
edgeLength = mean centre-to-centre edge length / mean leaf diagonal
crossings  = crossing pairs of straight leaf-to-leaf segments / number of such edges
             (above 400 edges, every k-th edge is sampled)
area       = bounding-box area / total leaf area      (the whitespace factor)
```

Lower is better. The weights are constants in `layout/score.js` (`W_ASPECT`, `W_EDGE_LENGTH`, `W_CROSSINGS`, `W_AREA`). The session chooses automatically unless told otherwise, and aims at the viewport: it reports the viewport's width over height (`setViewportAspect`, clamped to 0.5 to 3.5, small changes ignored).

**The layout method is a viewer preference, not part of the model.** The app bar's layout selector (`auto` or one method) is remembered per project and view in the browser's `localStorage`. A view may declare a default in the specification with `display.layout`; the viewer's own choice, when there is one, wins. Changing it never changes the semantic hash or any file. Pins still apply under every method.

A large model (more than 30 components) opens for the first time as an overview: top-level subsystems collapsed, so relationships between them are bundled into one labelled line per pair and kind. This is a viewing default, remembered once changed.

**Renderer** (`src/render/scene-view.js`) is Three.js with `OrbitControls` (`camera-rig.js`, perspective and top-down orthographic cameras), `CSS2DRenderer` labels and `Line2` fat lines for edges. It draws one mesh plus an outline per node and one line plus an arrowhead per edge. There is no instancing, so draw calls grow with the number of elements. The choice keeps every element individually pickable and styleable. The overlay shows frame rate, frame time, draw calls, triangles and counts from `getStats()`. No frame-rate figure is recorded for any real hardware; the self-specification's claim `benchmark-scene-interactive` is deliberately not evaluated. The renderer holds no domain state and imports nothing from `src/core`; it is a function of scene, placement, selection, highlight and camera, and reports interaction through callbacks (`onSelect`, `onHover`, `onActivate`, `onMoveEnd`, `onConnect`). `src/app/main.js` is the composition root that wires callbacks to session operations (a drag becomes `MovePresentationNode`).

## Interface architecture

The interface is mobile first: the base styles are for a phone, and `min-width` media queries (768 px, 1200 px; the `--bp-*` tokens in `src/styles/tokens.css`) widen it. There is **one DOM for every size**. `index.html` holds the app bar, the navigation, the scene viewport and two panels, the explorer panel and the context panel (one tabpanel per destination: inspector, simulation, verification, changes, diagnostics, source, realisation). No component is built twice for different sizes.

| Size | Navigation | Panels | Scene |
|---|---|---|---|
| Phone (base) | bottom bar: Explore, Inspect, Simulate, Verify, More | one at a time, as a bottom sheet with peek, half and full detents | fills the screen under a translucent app bar |
| Tablet (≥ 768 px) | rail on the left, a button per destination | one at a time, docked beside the scene; collapsible and resizable | between the rail and the panel |
| Desktop (≥ 1200 px) | rail | the explorer as its own column and the context panel on the right, both open by default | between them |

- **`src/ui/layout.js`** (component `responsive-layout`) owns the destinations and the navigation and decides which panel shows what. It sets data attributes only: `data-layout` (`phone`, `tablet`, `desktop`) and `data-sheet` on `.app`, `data-detent` on each panel (`closed`, `peek`, `half`, `full` on a phone; `closed` or `docked` elsewhere), and the panel widths as `--panel-w` and `--explorer-w`. `src/styles/layout.css` places the parts from those attributes, and `src/styles/panels.css` draws the panels, the navigation, the menus and the tables that become cards.
- **`src/ui/sheet.js`** drags a panel between its detents on a phone. It is inert at other sizes. Pointer drags on the panel header move it with an inline transform. On release a flick moves one detent in its direction, otherwise the nearest detent wins. The handle is a button: a tap or Enter cycles the detents, the arrow keys step them and Escape steps down and then closes. The pixel heights of peek and half are published as `--sheet-peek` and `--sheet-half`, so the floating controls sit just above the peek height.
- **The page never scrolls.** `html` and `body` hide their overflow and the app frame, the viewport and the panels use `overflow: clip`, which cannot be scrolled even by `focus()` or by a sheet's translated content. Programmatic focus passes `preventScroll`, and `revealInScroller` (`dom.js`) scrolls only the nearest scrolling list. Only the inside of a panel scrolls.
- **`src/ui/menu.js`** is the menu controller behind More, the app bar's overflow menu and the save-conflict menu. On a desktop the overflow's tool group is shown inline by CSS and the controller stays idle.
- **`src/ui/shell.js`** creates the layout, mounts the app bar (`toolbar.js`, which also builds the floating Fit and camera controls), the explorer, diagnostics, changes, the overlay and the simulation transport (`sim-transport.js`), and keeps the one-line summary under each panel title current: what a peeking sheet shows.
- Tables marked `.cardtable` turn into card lists through a container query on the panel body (narrower than 640 px). Labels and controls in the inspector stack below 420 px.
- **Touch targets** are enforced in the `states` layer: every interactive element is at least `--target` (44 px) in both directions. That layer comes after the components, so it wins over their own sizes. From 768 px with a fine pointer it hands sizing back to the components (`revert-layer`). Nothing depends on hover: the explorer's row actions show on the selected row.
- The renderer takes touch input through pointer events. A tap allows 10 px of movement, a second finger turns the gesture into a pinch or pan, and a finger must rest on a node for 350 ms before a drag moves the node rather than the camera.

## Repository layout by dependency boundary

Dependencies point downwards only.

| Layer | Paths | May depend on | Must not |
|---|---|---|---|
| Semantic core | `src/core/**` (incl. `metamodel.json`, `generate/`) | `jsonc-parser`, itself | import `three`, touch the DOM, use Node APIs, read clock or randomness |
| Persistence client | `src/persist/client.js` | `fetch`, `EventSource` | import the core |
| Renderer | `src/render/*.js` | `three`, itself | import the core or hold domain state |
| UI panels | `src/ui/*.js` | core (queries, parse/analyze, operations, claim methods, generators), persistence client | import the renderer or the session module directly (the session is passed in) |
| Application | `src/app/session.js`, `src/app/main.js` | everything above | contain business rules (`main.js` only routes) |
| Node tools | `tools/workspace.js`, `vite-plugin-exegra.js`, `traceability.js`, `check-spec.js`, `make-benchmark.js` | core, `node:*` | be imported by browser code |
| Agent CLI | `cli/*.js` | core, `tools/workspace.js`, `tools/traceability.js` | edit specification text outside `Project.apply` |

The self-specification states the first and third rules as claims: `core-independent-of-ui` (verified) and `renderer-does-not-own-state` (verified). Those claims are evaluated on relationships declared by hand in the specification, not on the real imports; the assumption `relationships-match-imports` records that. `property-controls.js` and `dialogs.js` import each other, recorded as an unknown on both components.

Other top-level paths: `specs/<project>/` (specification, optional `layout.jsonc`, `evidence/results.json`, `generated/`), `tests/core`, `tests/browser`, `docs/`, `index.html`, `vite.config.js`, `playwright.config.js`, `jsconfig.json`. Interface-level contracts for modules outside the core are in [module-contracts.md](module-contracts.md).

The live list of open architectural limitations is in `specs/exegra/spec.jsonc` (`system.notes`, component `unknowns`), the *Realisation* panel, and `node cli/exegra.js gaps --project exegra`.
