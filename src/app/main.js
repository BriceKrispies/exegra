// Application entry: creates the session, mounts the HTML panels and the
// Three.js scene, and wires them together. No business rules live here; this
// file only routes session events to views and view callbacks to the session.

import { createSession, requestedProject } from './session.js';
import { initEngine } from '../core/engine.js';
import { traffic } from './traffic-recorder.js';
import { PERSISTENCE_AVAILABLE } from '../persist/client.js';
import { mountShell } from '../ui/shell.js';
import { mountInspector } from '../ui/inspector.js';
import { mountSourceEditor } from '../ui/source-editor.js';
import { openConnectDialog } from '../ui/dialogs.js';
import { mountSimPanel } from '../ui/sim-panel.js';
import { mountVerificationPanel } from '../ui/verification-panel.js';
import { mountRealisationPanel } from '../ui/realisation-panel.js';
import { mountReader } from '../ui/reader.js';
import { createSceneView } from '../render/scene-view.js';

// The first real event of the page (src/app/traffic-recorder.js): the application module starts.
traffic.record('page-loaded', { persistent: PERSISTENCE_AVAILABLE, project: requestedProject() });
const session = createSession();
const shell = mountShell(session);

const view = createSceneView(shell.sceneHost, {
  onSelect: (id, hit) => {
    // A node selects the element it draws (a module element has no entity of its own); an edge selects its first
    // witness and remembers the edge, so the inspector lists every witness of that derived interaction.
    const node = hit?.kind === 'node' ? session.scene.nodes.find((n) => n.id === hit.sceneId) : null;
    if (node?.elementKind === 'module') session.select(node.id, { source: 'scene', edge: null });
    else session.select(id, { source: 'scene', edge: hit?.kind === 'edge' ? hit.sceneId : null });
    // A tap in the scene brings the inspector forward: at peek on a phone (name, kind, status).
    if (id) shell.revealInspector();
    else shell.dismissInspectorPeek();
  },
  onHover: (id) => session.setHover(id),
  onActivate: (id, hit) => {
    // Double-click on a block with members expands it, on an opened element collapses it (the cut changes).
    const node = hit?.kind === 'node' ? session.scene.nodes.find((n) => n.id === hit.sceneId) : null;
    if (node && (node.collapsed || node.container) && session.currentCut()) session.toggleCollapsed(node.id);
    else session.requestFit([node?.id ?? id]);
  },
  onMoveEnd: (moves) => {
    const ops = moves
      .filter((m) => session.model?.entities.has(m.id))
      .map((m) => ({ type: 'MovePresentationNode', view: session.layoutKey(), id: m.id, x: m.x, z: m.z }));
    if (ops.length) session.apply(ops, { label: ops.length === 1 ? `Move ${ops[0].id}` : `Move ${ops.length} nodes` });
  },
  onConnect: (fromId, toId) => {
    session.setMode('select');
    openConnectDialog(session, fromId, toId);
  },
});

mountInspector(shell.inspector, session);
mountSourceEditor(shell.source, session, { show: () => shell.show('source') });
mountSimPanel(shell.simulation, session);
mountVerificationPanel(shell.verification, session);
mountRealisationPanel(shell.realisation, session);
mountReader(/** @type {HTMLElement} */ (document.getElementById('reader-host')), session);
shell.setStatsProvider(() => view.getStats());

// ---- session -> scene ------------------------------------------------------
function selectionIds() {
  const id = session.selection;
  if (!id) return [];
  const e = session.model?.entities.get(id);
  // A relationship is shown on the edge it was selected on, or else on the derived interaction it is a witness of.
  if (e?.kind === 'relationship') {
    const on = session.selectedEdge ? session.scene.edges.find((x) => x.id === session.selectedEdge && (x.witnesses ?? []).includes(id)) : null;
    const edge = on ?? session.scene.edges.find((x) => !x.pathSummary && (x.witnesses ?? []).includes(id));
    return edge ? [id, edge.id] : [id];
  }
  // A nested entity that has no node of its own is shown on its owner.
  return e?.owner && !session.scene.nodes.some((n) => n.id === id) && !session.scene.edges.some((x) => x.id === id) ? [id, e.owner] : [id];
}

/**
 * The entities to emphasise, or null. Emphasis dims everything else, so it is
 * applied only when at least one emphasised entity is actually drawn in this scene.
 */
function highlightIds() {
  const ids = session.highlight;
  if (!ids) return null;
  const drawn = ids.some((id) => id !== session.selection && (id in session.placement || session.scene.edges.some((e) => e.id === id || e.entityId === id)));
  return drawn ? ids : null;
}

let refitTimer = 0;
const cameraKey = () => `exegra.camera.${session.projectName}.${session.viewId}`;
let restoredCameraFor = '';

function pushScene() {
  view.setScene(session.scene, session.placement);
  view.setSelection(selectionIds());
  view.setHighlight(highlightIds());
  if (restoredCameraFor !== cameraKey()) {
    restoredCameraFor = cameraKey();
    const viewId = session.viewId;
    let saved = null;
    if (session.projectName) traffic.record('camera-restore-requested', { view: viewId });
    try {
      saved = sessionStorage.getItem(cameraKey());
      if (saved) view.setCamera(JSON.parse(saved));
    } catch { saved = null; /* no stored camera */ }
    if (session.projectName) traffic.record(saved ? 'camera-restored' : 'camera-none', saved ? { view: viewId, camera: saved } : { view: viewId });
  }
}

function saveCamera() {
  if (!session.projectName) return;
  const camera = JSON.stringify(view.getCamera());
  traffic.record('camera-saved', { view: session.viewId, camera });
  try { sessionStorage.setItem(cameraKey(), camera); } catch { /* not remembered */ }
}

/** Pointer or wheel input that moved the camera ends: camera-moved, then the camera is saved. */
function cameraMoved() {
  if (!session.projectName) return;
  traffic.record('camera-moved', { camera: JSON.stringify(view.getCamera()) });
  saveCamera();
}

session.on('scene', pushScene);
// Opening a project restores its last selection; that must not open a panel over the scene.
let restoringSelection = false;
session.on('project', () => { restoringSelection = true; queueMicrotask(() => { restoringSelection = false; }); });
session.on('selection', () => {
  view.setSelection(selectionIds());
  view.setHighlight(highlightIds());
  // A selection by any route (scene, search, explorer, claim, link) brings the inspector forward
  // on a phone or a tablet unless another panel is pinned open.
  if (session.selection && !restoringSelection) shell.revealInspector();
});
session.on('ui', () => {
  view.setMode(session.ui.mode);
  view.setCameraMode(session.ui.cameraMode);
});
session.on('project', () => {
  view.setMode(session.ui.mode);
  view.setCameraMode(session.ui.cameraMode);
});
session.on('view', saveCamera);
session.on('fit', ({ ids }) => {
  // Fit after the scene for this state has been handed to the renderer.
  const run = () => view.fit(ids && ids.length ? ids.filter((/** @type {string} */ id) => id in session.placement) : undefined);
  requestAnimationFrame(run);
  // Nodes glide to new positions when the arrangement changes; frame again once they have arrived.
  clearTimeout(refitTimer);
  refitTimer = window.setTimeout(run, 320);
});
session.on('sim', (payload) => {
  if (!payload?.pulse) return;
  const s = session.sim;
  // Live mode: the real events just recorded pulse the components responsible for them (no step-pulsed:
  // that event is the scene's answer to a simulated step, and recording it here would feed itself).
  if (payload.live) {
    const fresh = session.live.fresh;
    const ids = new Set();
    for (const st of fresh) { for (const id of st.responsible) ids.add(id); for (const f of st.fired) { ids.add(f.transition); ids.add(f.to); } }
    view.pulse([...ids].filter((id) => id in session.placement || session.scene.edges.some((e) => e.id === id)));
    const last = session.simFlow();
    if (last?.paths.length) {
      const ev = session.model?.entities.get(last.flow.event);
      view.flow(last.paths, typeof ev?.data?.name === 'string' ? ev.data.name : last.flow.event);
    }
    return;
  }
  const step = s.simulation?.steps[s.stepIndex];
  if (!step) return;
  traffic.record('step-pulsed', { stepIndex: s.stepIndex });
  const ids = new Set(step.responsible);
  for (const f of step.fired) { ids.add(f.transition); ids.add(f.to); }
  view.pulse([...ids].filter((id) => id in session.placement || session.scene.edges.some((e) => e.id === id)));
  // The message itself: from its sender (or from outside) along the drawn edge to each receiver.
  const flow = session.simFlow();
  if (flow?.paths.length) {
    const ev = session.model?.entities.get(flow.flow.event);
    view.flow(flow.paths, typeof ev?.data?.name === 'string' ? ev.data.name : flow.flow.event);
  }
});

// The automatic layout aims at the shape of the scene viewport.
const reportAspect = () => {
  const r = shell.sceneHost.getBoundingClientRect();
  if (r.width > 50 && r.height > 50) session.setViewportAspect(r.width / r.height);
};
let aspectTimer = 0;
new ResizeObserver(() => { clearTimeout(aspectTimer); aspectTimer = window.setTimeout(reportAspect, 180); }).observe(shell.sceneHost);
reportAspect();

window.addEventListener('pagehide', saveCamera);
shell.sceneHost.addEventListener('pointerup', cameraMoved);
shell.sceneHost.addEventListener('wheel', cameraMoved, { passive: true });

// Inspection hook for browser tests and for debugging from the console.
/** @type {any} */ (window).__exegra = { session, view };

// The Lean core derives every model (src/core/parse.js) and runs claim scenarios on the main thread, so it is
// loaded before the first project opens. If it cannot be loaded the application shell still opens and says why
// no specification can be read.
traffic.record('engine-load-requested');
initEngine().then(
  () => { traffic.record('engine-load-settled', { ok: true }); traffic.record('session-init-requested', { persistent: session.persistent, project: requestedProject() }); session.init(); },
  (e) => {
    traffic.record('engine-load-settled', { ok: false });
    session.note('error', `The Lean core could not be loaded, so no specification can be read and no scenario run: ${e?.message ?? e}`);
    traffic.record('session-init-requested', { persistent: session.persistent, project: requestedProject() });
    session.init();
  },
);
