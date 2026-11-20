// The application session: the one object UI modules talk to.
//
// It owns no semantic state of its own. The Project (src/core/project.js) is
// the authority; everything here is either derived from it (scene, placement,
// claim results, simulation) or is interaction state that is deliberately not
// part of the specification (selection, active view, collapsed/hidden sets).

import { Project } from '../core/project.js';
import { listViews, project as projectScene } from '../core/projections.js';
import { layoutScene, chooseLayout, LAYOUT_METHODS } from '../core/layout.js';
import { evaluateClaims, checkTrace } from '../core/claims.js';
import { applyConcordance } from '../core/concordance.js';
import { createTraceCursor } from '../core/engine.js';
import { simulationInput } from '../core/sim-input.js';
import { createEngineRunner } from './engine-runner.js';
import { stepFlow, flowPaths, describeFlow } from '../core/flows.js';
import { requestLog } from '../core/contract-trace.js';
import * as persist from '../persist/client.js';
import { layersOf, reloadFromDisk } from './disk-reload.js';
import { traffic } from './traffic-recorder.js';
import { sha256Hex } from '../core/sha256.js';
import { createReplay, replayChecks, REPLAY_SCENARIO } from '../core/replay.js';
// @ts-ignore provided by tools/vite-plugin-exegra.js
import LINKED from 'virtual:exegra-linked-specs';

/** @typedef {import('../core/types.js').Operation} Operation */
/** @typedef {import('../core/types.js').TransactionResult} TransactionResult */

const STORE_KEY = 'exegra.session';
const PLAY_INTERVAL_MS = 800;
const OVERVIEW_THRESHOLD = 30;

// Specifications shipped with the build. Used only when the development
// persistence service is unavailable (a production build), where the
// application is read-only with respect to disk.
const SHIPPED = import.meta.glob('/specs/*/{spec,layout}.jsonc', { query: '?raw', import: 'default', eager: true });
const SHIPPED_RECORDED = import.meta.glob('/specs/*/evidence/results.json', { import: 'default', eager: true });
// Specifications that live outside specs/ (named by a project's project.jsonc), bundled by the build.
for (const [name, text] of Object.entries(LINKED)) SHIPPED[`/specs/${name}/spec.jsonc`] = text;

function loadStore() {
  try { return JSON.parse(localStorage.getItem(STORE_KEY) ?? '{}') ?? {}; } catch { return {}; }
}

/** @param {any} saved @returns {{selection: string, viewId: string}} */
function prefsOf(saved) {
  return { selection: typeof saved.selection === 'string' ? saved.selection : 'none', viewId: typeof saved.viewId === 'string' ? saved.viewId : 'structural' };
}

/** The project the page asks for: ?project=, else the one remembered, else exegra (recorded with page-loaded). */
export function requestedProject() {
  return new URLSearchParams(location.search).get('project') ?? loadStore().projectName ?? 'exegra';
}

export function createSession() {
  // Traffic: every real event of the session goes to the recorder of this page (src/app/traffic-recorder.js),
  // named by the event ids of Exegra's own specification. The persistence client records its requests and the
  // development server's events through the observer.
  const rec = (/** @type {string} */ id, /** @type {Record<string, any>} */ payload = {}) => traffic.record(id, payload);
  persist.observeTraffic((id, payload, meta) => { traffic.record(id, payload, meta); });
  // A page load is a (re)load of the tab: in-memory state is gone and the stored preferences are read.
  rec('page-reloaded');
  rec('preferences-read');
  /** @type {Map<string, Set<(payload: any) => void>>} */
  const listeners = new Map();
  const emit = (/** @type {string} */ type, /** @type {any} */ payload) => {
    for (const fn of [...(listeners.get(type) ?? [])]) {
      try { fn(payload); } catch (e) { console.error(`[exegra] listener for "${type}" failed`, e); }
    }
  };

  const store = loadStore();
  store.perProject ??= {};
  /** The selection and view last written to the store, as the self-model abstracts it; a write that leaves both unchanged is not a new event. */
  let lastPrefs = prefsOf(store.perProject[store.projectName] ?? {});
  /** The view last announced with view-switched (null after an open: the opened project's view is announced anew). @type {string|null} */
  let announcedView = null;
  /** sha-256 of the spec and layout text in memory: the self-model names texts by their hash. */
  const textHashes = { spec: /** @type {string|null} */ (null), layout: /** @type {string|null} */ (null) };
  let logSeq = 0;
  /** @type {(() => void)|null} */
  let unwatch = null;
  /** @type {(() => void)|null} */
  let unsubscribeProject = null;
  /** @type {ReturnType<typeof setInterval>|null} */
  let playTimer = null;
  // The Simulation tab's runs execute off the main thread. Started now so the engine is loaded before the first run.
  const runner = createEngineRunner({ record: (id, payload) => { traffic.record(id, payload); } });
  /** Increases with every load; a run whose token is no longer current is discarded. */
  let simToken = 0;
  /** Server-side content hashes of the files as last read or written by us. */
  const hashes = { spec: /** @type {string|null} */ (null), layout: /** @type {string|null} */ (null) };
  const pending = { spec: false, layout: false };
  let saving = false;
  /** @type {{file: 'spec'|'layout', current: {text: string, hash: string}}|null} */
  let conflict = null;
  /** @type {{label: string, origin: string}} */
  let lastMeta = { label: '', origin: 'ui' };

  const session = {
    persistent: persist.PERSISTENCE_AVAILABLE,
    /** @type {{name: string, title: string}[]} */
    projects: [],
    projectName: '',
    /** @type {string|null} where the open project's specification is stored */
    specLocation: null,
    project: /** @type {Project} */ (/** @type {any} */ (null)),
    get model() { return session.project?.model ?? null; },
    get diagnostics() { return session.project?.diagnostics ?? []; },

    /** @type {'saved'|'saving'|'conflict'|'error'|'readonly'} */
    saveState: /** @type {any} */ (persist.PERSISTENCE_AVAILABLE ? 'saved' : 'readonly'),
    /** @type {string|null} */
    selection: null,
    /** @type {string|null} */
    hover: null,
    /** Entity ids the scene should emphasise because of the current selection (a claim's involved entities). @type {string[]|null} */
    highlight: null,
    /** @type {{id: string, name: string, projection: string, description: string, declared: boolean}[]} */
    views: [],
    viewId: 'structural',
    ui: {
      collapsed: /** @type {Set<string>} */ (new Set()),
      hidden: /** @type {Set<string>} */ (new Set()),
      isolate: /** @type {string|null} */ (null),
      cameraMode: /** @type {'perspective'|'top'} */ ('perspective'),
      mode: /** @type {'select'|'connect'} */ ('select'),
      focusClaim: /** @type {string|null} */ (null),
      focusScenario: /** @type {string|null} */ (null),
    },
    scene: /** @type {import('../core/types.js').SceneModel} */ ({ viewId: '', projection: '', nodes: [], edges: [], legend: [], notes: [] }),
    placement: /** @type {import('../core/types.js').Placement} */ ({}),
    /**
     * How the current scene is arranged. Presentation only: `requested` is the
     * viewer's choice for this view ('auto' or a method id), `used` the method
     * actually applied, `scores` what 'auto' compared, `aspect` the viewport shape.
     */
    layout: {
      methods: LAYOUT_METHODS,
      requested: 'auto',
      used: 'layered',
      /** @type {Record<string, any>} */
      scores: {},
      aspect: 1.6,
    },
    /** @type {any[]} */
    claimResults: [],
    /** @type {any} */
    recorded: null,
    sim: {
      scenarioId: /** @type {string|null} */ (null),
      faults: /** @type {string[]} */ ([]),
      /** A stepwise view (engine.js createTraceCursor) of the finished run; null while it runs. @type {any} */
      simulation: /** @type {any} */ (null),
      /** The engine is running the loaded scenario; `simulation` is set when it finishes. */
      running: false,
      stepIndex: -1,
      playing: false,
      /** @type {{claimId: string, holds: boolean, stepIndex?: number, explanation: string}[]} */
      checks: [],
      /** The contract events of the whole run as request-log lines (contract-trace.js). @type {import('../core/contract-trace.js').RequestLogEntry[]} */
      requestLog: [],
    },
    /** @type {{seq: number, kind: string, message: string, detail?: any, diagnostics?: any[]}[]} */
    log: [],
    /** The recorder of this page's real events (src/app/traffic-recorder.js). */
    traffic,
    /**
     * Live mode of the simulator panel: the recorded stream replayed through the self-model's scenario
     * live-session (src/core/replay.js). `available` is false when the open specification has no such scenario.
     */
    live: {
      on: false,
      available: false,
      /** @type {import('../core/replay.js').Divergence[]} */
      divergences: /** @type {any[]} */ ([]),
      /** Predictions still waiting for their event. @type {any[]} */
      awaiting: /** @type {any[]} */ ([]),
      /** Wall-clock times of the replayed events by seq, for display only. @type {Map<number, number>} */
      at: new Map(),
      /** The steps added by the last update, for the scene's pulses. @type {any[]} */
      fresh: /** @type {any[]} */ ([]),
      dropped: 0,
    },

    /** @param {string} type @param {(payload: any) => void} fn */
    on(type, fn) {
      if (!listeners.has(type)) listeners.set(type, new Set());
      listeners.get(type)?.add(fn);
      return () => { listeners.get(type)?.delete(fn); };
    },

    /** @param {string} kind @param {string} message @param {any} [detail] */
    note(kind, message, detail) {
      session.log.push({ seq: ++logSeq, kind, message, detail, diagnostics: detail?.diagnostics });
      if (session.log.length > 400) session.log.splice(0, session.log.length - 400);
      emit('log', session.log[session.log.length - 1]);
    },

    /** @param {string} id */
    claimResult(id) { return session.claimResults.find((r) => r.claimId === id); },

    // ---- project lifecycle ------------------------------------------------
    async init() {
      if (session.persistent) {
        try {
          const requestId = traffic.nextRequestId();
          rec('list-intent', { requestId });
          session.projects = await persist.listProjects({ requestId });
          rec('projects-listed', { projects: session.projects.map((p) => p.name) });
        }
        catch (e) { session.note('error', `Could not list projects: ${/** @type {Error} */ (e).message}`); }
      } else {
        const names = [...new Set(Object.keys(SHIPPED).map((p) => p.split('/')[2]))].sort();
        session.projects = names.map((name) => ({ name, title: name }));
      }
      const wanted = new URLSearchParams(location.search).get('project') ?? store.projectName;
      const first = session.projects.find((p) => p.name === wanted) ?? session.projects.find((p) => p.name === 'exegra') ?? session.projects[0];
      if (first) await session.open(first.name);
      else session.note('error', 'No specification projects were found under specs/.');
    },

    /** Re-read the list of projects (after an import). */
    async refreshProjects() {
      if (!session.persistent) return;
      try {
        const requestId = traffic.nextRequestId();
        rec('list-intent', { requestId });
        session.projects = await persist.listProjects({ requestId });
        rec('projects-listed', { projects: session.projects.map((p) => p.name) });
        emit('project', { name: session.projectName });
      }
      catch (e) { session.note('error', `Could not list projects: ${/** @type {Error} */ (e).message}`); }
    },

    /** @param {string} name */
    async open(name) {
      rec('project-open-requested', { name });
      if (session.project && (pending.spec || pending.layout || conflict || saving || session.saveState === 'error' || session.saveState === 'conflict')) {
        rec('open-refused', { name });
        session.note('error', 'Resolve or wait for the pending save before switching projects.');
        emit('project', { name: session.projectName });
        return;
      }
      session.simPlay(false);
      let files;
      const requestId = session.persistent ? traffic.nextRequestId() : 0;
      try {
        if (session.persistent) rec('read-intent', { name, requestId, purpose: 'open' });
        files = session.persistent
          ? await persist.readProject(name, { requestId })
          : { spec: { text: /** @type {string} */ (SHIPPED[`/specs/${name}/spec.jsonc`]), hash: null }, layout: SHIPPED[`/specs/${name}/layout.jsonc`] ? { text: /** @type {string} */ (SHIPPED[`/specs/${name}/layout.jsonc`]), hash: null } : null, recorded: SHIPPED_RECORDED[`/specs/${name}/evidence/results.json`] ?? null };
        if (session.persistent) rec('project-files-read', filesRead(files, requestId));
      } catch (e) {
        if (session.persistent) rec('project-read-failed', { requestId });
        // The current project stays fully functional (subscription and watcher untouched).
        session.note('error', `Could not open project "${name}": ${/** @type {Error} */ (e).message}`);
        emit('project', { name: session.projectName });
        return;
      }
      // The model is derived by the Lean kernel; without it no specification can be read.
      /** @type {Project} */
      let project;
      try {
        project = new Project({ name, specText: files.spec.text, layoutText: files.layout?.text ?? null, layers: layersOf(files) });
      } catch (e) {
        session.note('error', `Could not open project "${name}": ${/** @type {Error} */ (e).message}`);
        emit('project', { name: session.projectName });
        return;
      }
      unwatch?.(); unwatch = null;
      unsubscribeProject?.(); unsubscribeProject = null;
      session.projectName = name;
      // Where the specification is stored, as shown in the source editor.
      session.specLocation = files.spec.path ?? `specs/${name}/spec.jsonc`;
      session.project = project;
      session.recorded = applyConcordance(project.model, files.recorded, files.concordance).recorded;
      hashes.spec = files.spec.hash;
      hashes.layout = files.layout?.hash ?? null;
      pending.spec = pending.layout = false;
      conflict = null;
      session.saveState = session.persistent ? 'saved' : 'readonly';
      unsubscribeProject = session.project.subscribe(onCommit);

      const saved = store.perProject[name] ?? {};
      const has = (/** @type {any} */ id) => typeof id === 'string' && !!session.model?.entities.has(id);
      session.ui.collapsed = new Set((saved.collapsed ?? []).filter(has));
      // First visit to a large model: start from an overview with top-level subsystems
      // closed (double-click opens one). Purely a viewing default; it is remembered once changed.
      if (!store.perProject[name] && (session.model?.byKind.component.length ?? 0) > OVERVIEW_THRESHOLD) {
        for (const c of session.model?.byKind.component ?? []) if (c.data.kind === 'subsystem' && !c.data.parent) session.ui.collapsed.add(c.id);
      }
      session.ui.hidden = new Set((saved.hidden ?? []).filter(has));
      session.ui.isolate = has(saved.isolate) ? saved.isolate : null;
      session.ui.cameraMode = saved.cameraMode === 'top' ? 'top' : 'perspective';
      session.ui.mode = 'select';
      session.ui.focusClaim = has(saved.focusClaim) ? saved.focusClaim : null;
      session.ui.focusScenario = has(saved.focusScenario) ? saved.focusScenario : null;
      session.selection = has(saved.selection) ? saved.selection : null;
      session.hover = null;
      session.viewId = typeof saved.viewId === 'string' ? saved.viewId : 'structural';
      session.sim = emptySim();
      simToken++;
      textHashes.spec = hashes.spec ?? sha256Hex(session.project.specText);
      textHashes.layout = hashes.layout;
      rec('preferences-loaded', { selection: session.selection ?? 'none', viewId: session.viewId });
      announcedView = null;
      rec('project-opened', { name, specHash: textHashes.spec, layoutHash: hashes.layout });

      evaluate();
      if (has(saved.simScenario)) loadSim(saved.simScenario, undefined, false);
      recompute();
      store.projectName = name;
      persistUi();
      if (session.persistent) { rec('watch-intent', { name }); unwatch = persist.watchProject(name, onExternalChange); }
      if (session.live.on) liveRebuild();
      if (session.project.errorCount) session.note('error', `"${name}" loaded with ${session.project.errorCount} validation error(s). Edits are rejected until they are fixed.`, { diagnostics: session.diagnostics.filter((d) => d.severity === 'error') });
      emit('project', { name });
      emit('model', { result: null, entry: null });
      emit('claims', null);
      emit('view', null);
      emit('ui', null);
      emit('selection', { id: session.selection });
      emit('sim', null);
      emit('save', null);
    },

    // ---- mutation ----------------------------------------------------------
    /**
     * @param {Operation|Operation[]} ops @param {{label?: string, origin?: string}} [opts]
     * @returns {TransactionResult}
     */
    apply(ops, opts = {}) {
      const result = session.project.apply(ops, { label: opts.label, origin: opts.origin ?? 'ui' });
      if (!result.ok) {
        session.note('error', `${opts.label ?? 'Change'} rejected: ${result.message}`, { code: result.code, diagnostics: result.diagnostics });
      }
      return result;
    },
    undo() { rec('undo-requested'); return session.project.undo(); },
    redo() { rec('redo-requested'); return session.project.redo(); },

    /** @param {'reload'|'overwrite'} how */
    async resolveConflict(how) {
      if (!conflict) return;
      rec('conflict-resolution-chosen', { how });
      const c = conflict;
      conflict = null;
      if (how === 'reload') {
        hashes[c.file] = c.current.hash;
        pending[c.file] = false;
        rec('reload-requested', { file: c.file, text: c.current.hash });
        const r = session.project.reload(c.file === 'spec' ? { specText: c.current.text } : { layoutText: c.current.text });
        if (!r.ok) {
          session.note('error', r.message ?? 'Reload failed.', { diagnostics: r.diagnostics });
          conflict = c;
          setSaveState('conflict');
          return;
        }
        session.note('info', `Reloaded ${c.file} from disk; the in-memory version was replaced and the undo history was cleared.`);
      } else {
        hashes[c.file] = c.current.hash;
        pending[c.file] = true;
        session.note('info', `Overwriting ${c.file} on disk with the in-memory version.`);
      }
      setSaveState('saved');
      flush();
    },

    // ---- interaction state ---------------------------------------------------
    /** @param {string|null} id @param {{source?: string}} [opts] */
    select(id, opts = {}) {
      if (id !== null && !session.model?.entities.has(id)) id = null;
      const entity = id ? session.model?.entities.get(id) : null;
      let sceneDirty = false;
      if (entity?.kind === 'claim' && session.ui.focusClaim !== id) { session.ui.focusClaim = id; sceneDirty = true; }
      if (entity?.kind === 'scenario' && session.ui.focusScenario !== id) { session.ui.focusScenario = id; sceneDirty = true; }
      const changed = session.selection !== id;
      if (changed) rec('entity-selected', { id: id ?? 'none' });
      session.selection = id;
      const refocus = changed && session.scene.projection === 'references';
      if (refocus) sceneDirty = true;
      updateHighlight();
      if (sceneDirty) recompute();
      if (changed || sceneDirty) { persistUi(); emit('selection', { id, source: opts.source }); }
      if (refocus) emit('fit', { ids: undefined });
    },
    /** @param {string|null} id */
    setHover(id) {
      if (session.hover === id) return;
      session.hover = id;
      emit('hover', { id });
    },
    /** @param {string} viewId */
    setView(viewId) {
      const view = session.views.find((v) => v.id === viewId);
      if (!view) return;
      if (viewId !== session.viewId) rec('view-selected', { view: viewId });
      session.viewId = viewId;
      const sel = session.selection ? session.model?.entities.get(session.selection) : null;
      // Carry the context across: pick the focus the new projection needs from what is selected.
      if (view.projection === 'claims' && sel && sel.kind !== 'claim') {
        const hit = session.claimResults.find((r) => r.involved.includes(sel.id));
        if (hit) session.ui.focusClaim = hit.claimId;
      }
      if (view.projection === 'behavior') {
        if (sel?.kind === 'component') {
          const behaviors = (session.model?.byKind.behavior ?? []).filter((b) => b.data.subject === sel.id).map((b) => b.id);
          const sc = (session.model?.byKind.scenario ?? []).find((s) => (s.data.behaviors ?? []).some((/** @type {string} */ b) => behaviors.includes(b)));
          if (sc) session.ui.focusScenario = sc.id;
        } else if (!session.ui.focusScenario && session.sim.scenarioId) session.ui.focusScenario = session.sim.scenarioId;
      }
      updateHighlight();
      recompute();
      persistUi();
      emit('view', null);
      emit('fit', { ids: undefined });
    },
    /** @param {string} id */
    toggleCollapsed(id) {
      if (session.ui.collapsed.has(id)) session.ui.collapsed.delete(id); else session.ui.collapsed.add(id);
      uiChanged();
      emit('fit', { ids: undefined }); // the layout changes shape; keep the whole scene in view
    },
    /** @param {string} id @param {boolean} hidden */
    setHidden(id, hidden) {
      if (hidden) session.ui.hidden.add(id); else session.ui.hidden.delete(id);
      uiChanged();
    },
    /** @param {string|null} id */
    setIsolate(id) {
      session.ui.isolate = id;
      uiChanged();
      emit('fit', { ids: undefined });
    },
    /** Choose how this view is arranged: 'auto' or one of session.layout.methods. A viewer preference, not a model change. @param {string} method */
    setLayoutMethod(method) {
      const entry = (store.perProject[session.projectName] ??= {});
      (entry.layoutByView ??= {})[session.viewId] = method;
      recompute();
      persistUi();
      emit('ui', null);
      emit('fit', { ids: undefined });
    },
    /** The scene viewport's width/height; 'auto' layout aims at it. @param {number} aspect */
    setViewportAspect(aspect) {
      if (!Number.isFinite(aspect) || aspect <= 0) return;
      const a = Math.max(0.5, Math.min(3.5, aspect));
      if (Math.abs(Math.log(a / session.layout.aspect)) < 0.12) return; // ignore small resizes
      session.layout.aspect = a;
      if (session.model) { recompute(); emit('fit', { ids: undefined }); }
    },
    /** @param {'perspective'|'top'} mode */
    setCameraMode(mode) { session.ui.cameraMode = mode; persistUi(); emit('ui', null); },
    /** @param {'select'|'connect'} mode */
    setMode(mode) { session.ui.mode = mode; emit('ui', null); },
    /** @param {string|null} id */
    focusClaim(id) { session.ui.focusClaim = id; uiChanged(); },
    /** @param {string|null} id */
    focusScenario(id) { session.ui.focusScenario = id; uiChanged(); },

    /** @param {string} id */
    revealSource(id) { emit('reveal-source', { id }); },
    /** @param {string[]} [ids] */
    requestFit(ids) { emit('fit', { ids }); },

    // ---- simulation ------------------------------------------------------------
    /** @param {string|null} scenarioId @param {string[]} [faults] */
    simLoad(scenarioId, faults) { if (session.live.on) liveOff(); loadSim(scenarioId, faults, true); },
    /** @param {string[]} ids */
    simSetFaults(ids) { if (session.live.on) return; loadSim(session.sim.scenarioId, ids, true); },
    simStep() {
      const s = session.sim;
      if (!s.simulation) return;
      if (session.live.on) { if (s.stepIndex < s.simulation.steps.length - 1) { s.stepIndex++; liveChanged(); } return; }
      rec('sim-step-requested');
      if (s.stepIndex < s.simulation.steps.length - 1) s.stepIndex++;
      else if (s.simulation.step()) s.stepIndex = s.simulation.steps.length - 1;
      else { session.simPlay(false); return; }
      rec('sim-step-shown', { stepIndex: s.stepIndex });
      simChanged(true);
    },
    simBack() {
      const s = session.sim;
      if (!s.simulation || s.stepIndex < 0) return;
      if (session.live.on) { s.stepIndex--; liveChanged(); return; }
      rec('sim-back-requested');
      s.stepIndex--;
      simChanged(false);
    },
    simReset() {
      const s = session.sim;
      if (!s.simulation) return;
      if (session.live.on) { s.stepIndex = -1; liveChanged(); return; }
      rec('sim-reset-requested');
      session.simPlay(false);
      s.simulation.reset();
      s.stepIndex = -1;
      simChanged(false);
    },
    simRunToEnd() {
      const s = session.sim;
      if (!s.simulation) return;
      if (session.live.on) { s.stepIndex = s.simulation.steps.length - 1; liveChanged(); return; }
      rec('sim-run-to-end-requested');
      session.simPlay(false);
      s.simulation.run();
      s.stepIndex = s.simulation.steps.length - 1;
      simChanged(false);
    },
    /** @param {number} index */
    simSeek(index) {
      const s = session.sim;
      if (!s.simulation) return;
      if (session.live.on) { s.stepIndex = Math.max(-1, Math.min(index, s.simulation.steps.length - 1)); liveChanged(); return; }
      rec('sim-seek-requested', { stepIndex: index });
      while (s.simulation.steps.length <= index && s.simulation.step()) { /* advance */ }
      s.stepIndex = Math.max(-1, Math.min(index, s.simulation.steps.length - 1));
      simChanged(false);
    },
    /** @param {boolean} playing */
    simPlay(playing) {
      const s = session.sim;
      if (playTimer) { clearInterval(playTimer); playTimer = null; }
      const was = s.playing;
      s.playing = playing && !!s.simulation && !session.live.on;
      if (s.playing) playTimer = setInterval(() => session.simStep(), PLAY_INTERVAL_MS);
      if (was !== s.playing) emit('sim', { pulse: false });
    },
    /**
     * The message flow of the step currently shown: who sent its event and who
     * received it, the paths that takes through the current scene, and a sentence.
     * null before the first step.
     */
    simFlow() {
      const s = session.sim;
      const step = s.simulation && s.stepIndex >= 0 ? s.simulation.steps[s.stepIndex] : null;
      if (!step || !session.model) return null;
      const flow = stepFlow(session.model, step);
      const paths = flowPaths(session.model, session.scene, flow);
      return { flow, paths, text: describeFlow(session.model, flow, paths) };
    },
    /** The trace up to the step currently shown (what the user has "seen so far"). */
    simTrace() {
      const s = session.sim;
      if (!s.simulation) return null;
      const full = s.simulation.trace();
      const steps = full.steps.slice(0, s.stepIndex + 1);
      const atEnd = s.stepIndex === full.steps.length - 1;
      return { ...full, steps, outcome: atEnd ? full.outcome : 'running', final: steps.length ? steps[steps.length - 1].config : full.initial };
    },

    /**
     * Turn the simulator's Live source on or off. While on, the panel and the scene show this application's
     * own recorded events replayed through the self-model (scenario live-session), as they happen.
     * @param {boolean} on
     */
    simLive(on) {
      if (on) liveOn(); else liveOff();
    },

    dispose() {
      liveUnsub?.();
      session.simPlay(false);
      simToken++;
      runner.dispose();
      unwatch?.();
      unsubscribeProject?.();
      listeners.clear();
    },
  };

  // ---- live mode: the recorded stream replayed through the self-model ---------------------
  /** @type {ReturnType<typeof createReplay>|null} */
  let replay = null;
  /** How many recorded events (by seq) the replay has consumed. */
  let replayedSeq = 0;
  /** @type {(() => void)|null} */
  let liveUnsub = null;
  let liveScheduled = false;

  /** Whether the open specification can replay this application's events. */
  const liveAvailable = () => session.model?.entities.get(REPLAY_SCENARIO)?.kind === 'scenario';

  function liveOn() {
    session.live.available = liveAvailable();
    if (!session.live.available) { session.note('error', `Live mode needs the scenario "${REPLAY_SCENARIO}", which Exegra's own specification declares; the open specification has none.`); emit('sim', { pulse: false }); return; }
    session.simPlay(false);
    session.live.on = true;
    session.sim = { ...emptySim(), scenarioId: REPLAY_SCENARIO, running: false };
    liveRebuild();
    liveUnsub = traffic.subscribe(() => {
      if (liveScheduled) return;
      liveScheduled = true;
      // Batched: a burst of events (a save round trip) becomes one update of the panel and the scene.
      queueMicrotask(() => { liveScheduled = false; liveAdvance(); });
    });
  }

  function liveOff() {
    liveUnsub?.(); liveUnsub = null;
    replay = null;
    if (!session.live.on) return;
    session.live.on = false;
    session.live.divergences = [];
    session.live.awaiting = [];
    session.live.fresh = [];
    session.sim = emptySim();
    simChanged(false);
  }

  /** Replay the whole kept stream again (on, or after the self-model changed). */
  function liveRebuild() {
    if (!session.live.on) return;
    session.live.available = liveAvailable();
    if (!session.live.available || !session.model) { liveOff(); return; }
    try { replay = createReplay(session.model, { scenarioId: REPLAY_SCENARIO }); }
    catch (e) { session.note('error', `Live replay could not start: ${/** @type {Error} */ (e).message}`); liveOff(); return; }
    replayedSeq = 0;
    session.sim.stepIndex = -1;
    session.live.at = new Map();
    liveAdvance(true);
  }

  /** Feed the replay the events recorded since the last update. @param {boolean} [rebuilt] */
  function liveAdvance(rebuilt = false) {
    if (!session.live.on || !replay || !session.model) return;
    const s = session.sim;
    const following = rebuilt || s.stepIndex === (s.simulation?.steps.length ?? 0) - 1;
    // The replay keeps a configuration per step; past the recorder's bound it starts again from the kept stream.
    if (!rebuilt && replay.steps.length > traffic.limit) { liveRebuild(); return; }
    const before = replay.steps.length;
    for (const e of traffic.events()) {
      if (e.seq <= replayedSeq) continue;
      replayedSeq = e.seq;
      session.live.at.set(e.seq, e.at);
      // Only the logical sequence number and the payload reach the core; the wall-clock time stays here.
      replay.consume(e.inferred ? { seq: e.seq, id: e.id, payload: e.payload, inferred: true } : { seq: e.seq, id: e.id, payload: e.payload });
    }
    const trace = replay.trace();
    s.simulation = liveCursor(trace);
    if (following) s.stepIndex = trace.steps.length - 1;
    session.live.divergences = replay.divergences.slice();
    session.live.awaiting = replay.pending;
    session.live.dropped = traffic.dropped;
    session.live.fresh = rebuilt ? [] : trace.steps.slice(before);
    liveChanged(!rebuilt && session.live.fresh.length > 0);
  }

  /** A Simulation-shaped view of the live trace: every recorded step is revealed. @param {any} trace */
  function liveCursor(trace) {
    return {
      scenarioId: trace.scenarioId, faults: [], initial: trace.initial, config: trace.final, steps: trace.steps, outcome: 'running', live: true,
      step: () => null, run: () => trace, reset: () => {}, trace: () => trace,
    };
  }

  /** @param {boolean} [pulse] */
  function liveChanged(pulse = false) {
    const s = session.sim;
    const trace = s.simulation?.trace();
    try {
      const shown = trace ? { ...trace, steps: trace.steps.slice(0, s.stepIndex + 1) } : null;
      s.checks = shown && session.model ? [...checkTrace(session.model, shown), ...replayChecks(session.model, session.live.divergences.filter((d) => d.stepIndex <= s.stepIndex), shown.steps.length)] : [];
    } catch (e) { s.checks = []; console.error(e); }
    try { s.requestLog = trace && session.model ? requestLog(session.model, trace) : []; } catch { s.requestLog = []; }
    emit('sim', { pulse, live: true });
  }

  // ---- derivation ------------------------------------------------------------
  function evaluate() {
    const modelHash = textHashes.spec;
    rec('claims-evaluation-requested', { modelHash });
    try {
      session.claimResults = session.model ? evaluateClaims(session.model, { recorded: session.recorded ?? undefined }) : [];
      rec('claim-scenarios-run', { modelHash });
      rec('claims-evaluated', { modelHash });
    } catch (e) {
      session.claimResults = [];
      session.note('error', `Claim evaluation failed: ${/** @type {Error} */ (e).message}`);
    }
    updateHighlight();
  }

  function updateHighlight() {
    const sel = session.selection ? session.model?.entities.get(session.selection) : null;
    if (sel?.kind === 'claim') {
      const r = session.claimResult(sel.id);
      const ids = new Set([...(r?.involved ?? sel.data.subjects ?? []), ...(r?.counterexample?.entities ?? [])]);
      ids.add(sel.id);
      // Entities that have no node in a structural scene are shown on the component they belong to.
      const model = session.model;
      const addBehavior = (/** @type {any} */ b) => { if (b?.kind === 'behavior') { ids.add(b.id); if (typeof b.data.subject === 'string') ids.add(b.data.subject); } };
      for (const id of [...ids]) {
        const e = model?.entities.get(id);
        if (!e) continue;
        if (e.kind === 'behavior') addBehavior(e);
        else if (e.kind === 'port' && e.owner) ids.add(e.owner);
        else if ((e.kind === 'state' || e.kind === 'transition') && e.owner) addBehavior(model?.entities.get(e.owner));
        else if (e.kind === 'scenario') for (const b of e.data.behaviors ?? []) addBehavior(model?.entities.get(b));
      }
      session.highlight = [...ids];
    } else session.highlight = null;
  }

  function recompute() {
    const model = session.model;
    if (!model) {
      session.views = [];
      session.scene = { viewId: session.viewId, projection: '', nodes: [], edges: [], legend: [], notes: ['The specification has syntax errors; the last scene cannot be derived. Fix the source to continue.'] };
      session.placement = {};
      emit('scene', null);
      return;
    }
    try {
      session.views = listViews(model);
      if (!session.views.some((v) => v.id === session.viewId)) session.viewId = session.views[0]?.id ?? 'structural';
      // The view the scene is about to show, once per change (an open, setView, or a view replaced because the
      // specification has no such view): pushScene then restores the camera stored for it.
      if (session.viewId !== announcedView) { announcedView = session.viewId; rec('view-switched', { view: session.viewId }); }
      const view = session.views.find((v) => v.id === session.viewId);
      const s = session.sim;
      const showTrace = view?.projection === 'behavior' && s.simulation && (!session.ui.focusScenario || session.ui.focusScenario === s.scenarioId);
      session.scene = projectScene(model, session.viewId, {
        collapsed: session.ui.collapsed,
        hidden: session.ui.hidden,
        isolate: session.ui.isolate,
        focusClaim: session.ui.focusClaim,
        focusScenario: session.ui.focusScenario,
        claimResults: session.claimResults,
        focusEntity: session.selection,
        trace: showTrace ? s.simulation.trace() : null,
        stepIndex: s.stepIndex,
      });
      const pins = session.project.layout.views[session.viewId]?.positions ?? {};
      const declared = model.entities.get(session.viewId)?.data.display?.layout;
      const requested = store.perProject[session.projectName]?.layoutByView?.[session.viewId] ?? declared ?? 'auto';
      session.layout.requested = requested === 'auto' || LAYOUT_METHODS.some((m) => m.id === requested) ? requested : 'auto';
      if (session.layout.requested === 'auto') {
        const choice = chooseLayout(session.scene, pins, { aspect: session.layout.aspect });
        session.placement = choice.placement;
        session.layout.used = choice.method;
        session.layout.scores = choice.scores;
      } else {
        session.placement = layoutScene(session.scene, pins, { method: session.layout.requested, aspect: session.layout.aspect });
        session.layout.used = session.layout.requested;
        session.layout.scores = {};
      }
    } catch (e) {
      console.error(e);
      session.note('error', `Projection failed: ${/** @type {Error} */ (e).message}`);
    }
    emit('scene', null);
  }

  function uiChanged() {
    recompute();
    persistUi();
    emit('ui', null);
  }

  function persistUi() {
    if (!session.projectName) return;
    store.perProject[session.projectName] = {
      layoutByView: store.perProject[session.projectName]?.layoutByView,
      viewId: session.viewId,
      selection: session.selection,
      collapsed: [...session.ui.collapsed],
      hidden: [...session.ui.hidden],
      isolate: session.ui.isolate,
      cameraMode: session.ui.cameraMode,
      focusClaim: session.ui.focusClaim,
      focusScenario: session.ui.focusScenario,
      simScenario: session.live.on ? store.perProject[session.projectName]?.simScenario ?? null : session.sim.scenarioId,
    };
    try { localStorage.setItem(STORE_KEY, JSON.stringify(store)); } catch { /* storage unavailable: state is simply not remembered */ }
    // The self-model abstracts the store to the selection and the view; a write that changes neither is a stutter step.
    const prefs = prefsOf(store.perProject[session.projectName]);
    if (prefs.selection !== lastPrefs.selection || prefs.viewId !== lastPrefs.viewId) {
      lastPrefs = prefs;
      rec('preferences-written', prefs);
    }
  }

  function emptySim() {
    return { scenarioId: /** @type {string|null} */ (null), faults: /** @type {string[]} */ ([]), simulation: null, running: false, stepIndex: -1, playing: false, checks: [], requestLog: /** @type {import('../core/contract-trace.js').RequestLogEntry[]} */ ([]) };
  }

  /**
   * Load a scenario: derive its engine input and run it to completion off the main thread. Until the
   * trace arrives the run is shown as running (`sim.running`, no `sim.simulation`); the trace's steps
   * then form the cursor that step, back, seek, reset, play and run to end move through.
   * @param {string|null} scenarioId @param {string[]|undefined} faults @param {boolean} announce
   */
  function loadSim(scenarioId, faults, announce) {
    session.simPlay(false);
    const token = ++simToken;
    const model = session.model;
    const scenario = scenarioId && model ? model.entities.get(scenarioId) : null;
    /** @type {import('../core/sim-input.js').SimulationInput|null} */
    let input = null;
    if (!scenario || scenario.kind !== 'scenario' || !model) {
      session.sim = emptySim();
    } else {
      const active = (faults ?? scenario.data.faults ?? []).filter((/** @type {string} */ f) => model.entities.get(f)?.kind === 'fault');
      try {
        input = simulationInput(model, scenario.id, active);
        session.sim = { ...emptySim(), scenarioId: scenario.id, faults: active, running: true };
        session.ui.focusScenario = scenario.id;
      } catch (e) {
        session.note('error', `Scenario "${scenario.id}" could not be loaded: ${/** @type {Error} */ (e).message}`);
        session.sim = emptySim();
      }
    }
    if (announce) simChanged(false);
    else updateChecks();
    if (!input) return;
    const id = /** @type {string} */ (session.sim.scenarioId);
    rec('sim-load-requested', { scenario: id });
    rec('engine-run-intent', { token, scenario: id });
    runner.run(input).then((trace) => {
      rec('sim-trace-ready', { token, steps: trace.steps.length });
      if (token !== simToken || session.live.on) return;
      session.sim.simulation = createTraceCursor(trace);
      session.sim.running = false;
      session.sim.stepIndex = -1;
      simChanged(false);
    }, (e) => {
      rec('sim-run-failed', { token });
      if (token !== simToken || session.live.on) return;
      session.note('error', `Scenario "${id}" could not be run: ${/** @type {Error} */ (e).message}`);
      session.sim = emptySim();
      simChanged(false);
    });
  }

  function updateChecks() {
    const trace = session.simTrace();
    try { session.sim.checks = trace && session.model ? checkTrace(session.model, trace) : []; }
    catch (e) { session.sim.checks = []; session.note('error', `Trace check failed: ${/** @type {Error} */ (e).message}`); }
    // The request log covers the whole run, so the steps still to come show dimmed in the panel.
    try { session.sim.requestLog = session.sim.simulation && session.model ? requestLog(session.model, session.sim.simulation.trace()) : []; }
    catch { session.sim.requestLog = []; }
  }

  /** @param {boolean} pulse whether the step just taken should be animated */
  function simChanged(pulse) {
    updateChecks();
    recompute();
    persistUi();
    emit('sim', { pulse });
  }

  // ---- commits and persistence -------------------------------------------------
  /** @param {{type: string, result: TransactionResult, entry: import('../core/project.js').HistoryEntry}} event */
  function onCommit(event) {
    const { entry } = event;
    // The commit as the self-model names it: its cause (undo, redo and reloads record theirs where they start),
    // then commit-notified with the hash of the text that changed.
    if (entry.specChanged) textHashes.spec = sha256Hex(session.project.specText);
    if (entry.layoutChanged) textHashes.layout = session.project.layoutText === null ? null : sha256Hex(session.project.layoutText);
    if (entry.specChanged || entry.layoutChanged) {
      const file = entry.specChanged ? 'spec' : 'layout';
      if (!['undo', 'redo', 'external'].includes(entry.origin)) {
        if (entry.specChanged) rec('edit-applied', { specHash: textHashes.spec, origin: entry.origin });
        else rec('node-moved', { layoutHash: textHashes.layout });
      }
      rec('commit-notified', { origin: entry.origin, file, text: textHashes[file] });
    }
    if (session.selection && !session.model?.entities.has(session.selection)) session.selection = null;
    for (const set of [session.ui.collapsed, session.ui.hidden]) for (const id of [...set]) if (!session.model?.entities.has(id)) set.delete(id);
    for (const key of /** @type {const} */ (['isolate', 'focusClaim', 'focusScenario'])) {
      const v = session.ui[key];
      if (v && !session.model?.entities.has(v)) session.ui[key] = null;
    }
    if (entry.semanticChanged) {
      evaluate();
      if (session.sim.scenarioId && !session.live.on) loadSim(session.sim.scenarioId, session.sim.faults, false);
      // The self-model may have changed: replay the kept stream through the new one (after this commit's own events).
      if (session.live.on) queueMicrotask(liveRebuild);
    } else updateHighlight();
    recompute();
    session.note('change', entry.label, { revision: entry.revision, origin: entry.origin, affected: entry.affected, semanticChanged: entry.semanticChanged });
    emit('model', event);
    if (entry.semanticChanged) { emit('claims', null); emit('sim', { pulse: false }); }
    emit('selection', { id: session.selection });
    persistUi();
    if (entry.origin !== 'external') {
      if (entry.specChanged) pending.spec = true;
      if (entry.layoutChanged) pending.layout = true;
      lastMeta = { label: entry.label, origin: entry.origin };
      flush();
    }
  }

  /** @param {'saved'|'saving'|'conflict'|'error'|'readonly'} state */
  function setSaveState(state) {
    if (session.saveState === state) return;
    session.saveState = state;
    emit('save', null);
  }

  async function flush() {
    if (!session.persistent || saving || conflict) return;
    saving = true;
    const name = session.projectName;
    try {
      while ((pending.spec || pending.layout) && !conflict && name === session.projectName) {
        const file = pending.spec ? 'spec' : 'layout';
        pending[file] = false;
        setSaveState('saving');
        const text = file === 'spec' ? session.project.specText : session.project.layoutText;
        const requestId = traffic.nextRequestId();
        const textHash = textHashes[file] ?? sha256Hex(text ?? '');
        rec('write-intent', { name, file, text: textHash, baseHash: hashes[file], requestId });
        const res = await persist.writeFile(name, file, text, hashes[file], lastMeta, { requestId, textHash });
        if (name !== session.projectName) break;
        if (res.ok) {
          rec('save-succeeded', { file, hash: res.hash, requestId });
          hashes[file] = res.hash;
          session.note('save', `Saved ${file === 'spec' ? 'spec.jsonc' : 'layout.jsonc'}`, { hash: res.hash });
          // A written file whose journal line failed is still saved; the history line for it is missing.
          if (res.journal && res.journal.written === false) {
            session.note('error', `${file === 'spec' ? 'spec.jsonc' : 'layout.jsonc'} was saved, but ${res.journal.message}`);
          }
        } else if ('conflict' in res && res.conflict) {
          rec('save-conflicted', { file, currentHash: res.current.hash, requestId });
          conflict = { file, current: res.current };
          pending[file] = true;
          session.note('error', `${file === 'spec' ? 'spec.jsonc' : 'layout.jsonc'} changed on disk since it was loaded. Nothing was overwritten; choose "Reload from disk" or "Overwrite disk".`);
          setSaveState('conflict');
        } else {
          rec('save-failed', { file, requestId });
          pending[file] = true;
          session.note('error', `Saving failed: ${'error' in res ? res.error : 'unknown error'}`);
          setSaveState('error');
          break;
        }
      }
      if (!conflict && session.saveState === 'saving') setSaveState('saved');
    } finally {
      saving = false;
    }
  }

  /** @param {{file: 'spec'|'layout'|'recorded'|'products', hash: string|null}} change */
  async function onExternalChange(change) {
    const name = session.projectName;
    if (change.file === 'recorded') {
      const requestId = traffic.nextRequestId();
      try {
        rec('read-intent', { name, requestId, purpose: 'recorded' });
        const files = await persist.readProject(name, { requestId });
        const read = filesRead(files, requestId);
        rec('project-files-read', read);
        if (name !== session.projectName) return;
        rec('recorded-results-adopted', { version: read.recorded });
        session.recorded = applyConcordance(session.project?.model, files.recorded, files.concordance).recorded;
        evaluate();
        recompute();
        emit('claims', null);
        session.note('info', 'Recorded verification results changed on disk; claims were re-evaluated.');
      } catch { /* the next change event will retry */ }
      return;
    }
    if (change.file === 'products') { await onProductsChange(name); return; }
    if (change.hash === hashes[change.file]) return; // our own write
    if (saving || pending[change.file] || conflict) return; // the pending write will surface the conflict
    const requestId = traffic.nextRequestId();
    try {
      rec('read-intent', { name, requestId, purpose: 'external' });
      const files = await persist.readProject(name, { requestId });
      rec('project-files-read', filesRead(files, requestId));
      if (name !== session.projectName) return;
      const current = change.file === 'spec' ? files.spec : files.layout;
      if (!current || current.hash === hashes[change.file]) return;
      if (saving || pending[change.file] || conflict) return; // an edit was made during the round trip; do not replace it
      rec('reload-requested', { file: change.file, text: current.hash });
      const r = reloadFromDisk(session.project, change.file, files);
      if (r.ok) {
        hashes[change.file] = current.hash;
        session.note('info', `${change.file === 'spec' ? 'spec.jsonc' : 'layout.jsonc'} changed on disk and was reloaded.`);
      } else {
        // Keep the last valid model. The stale hash makes the next save a visible conflict instead of a silent overwrite.
        session.note('error', `${r.message} Fix the file, or make an edit here and choose "Overwrite disk".`, { diagnostics: r.diagnostics });
      }
    } catch (e) {
      session.note('error', `Could not re-read the project after an external change: ${/** @type {Error} */ (e).message}`);
    }
  }

  /**
   * A product file changed, was added or was removed: read the project again and re-derive the model from the
   * product layers on disk. The product files are never written here, so there is no pending write of ours to
   * protect, and the platform text and layout in memory are kept as they are.
   * @param {string} name
   */
  async function onProductsChange(name) {
    const requestId = traffic.nextRequestId();
    try {
      rec('read-intent', { name, requestId, purpose: 'external' });
      const files = await persist.readProject(name, { requestId });
      rec('project-files-read', filesRead(files, requestId));
      if (name !== session.projectName) return;
      const before = session.project.revision;
      const r = reloadFromDisk(session.project, 'products', files);
      if (r.ok) {
        if (session.project.revision !== before) session.note('info', 'A product file changed on disk and was reloaded.');
      } else {
        session.note('error', `${r.message} Fix the product file; the last valid model is kept.`, { diagnostics: r.diagnostics });
      }
    } catch (e) {
      session.note('error', `Could not re-read the project after a product file changed: ${/** @type {Error} */ (e).message}`);
    }
  }

  /**
   * project-files-read as the self-model names it: the hashes of the files read, and the version of the recorded
   * results that the server reported in its read-project-ok for the same request.
   * @param {any} files @param {number} requestId
   */
  function filesRead(files, requestId) {
    const answer = traffic.answer('read-project-ok', requestId);
    return { specHash: files.spec.hash, layoutHash: files.layout?.hash ?? null, recorded: answer ? answer.payload.recorded ?? null : null, requestId };
  }

  return session;
}
