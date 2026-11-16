// Application entry: creates the session, mounts the HTML panels and the
// Three.js scene, and wires them together. No business rules live here; this
// file only routes session events to views and view callbacks to the session.

import { createSession } from './session.js';
import { initEngine } from '../core/engine.js';
import { mountShell } from '../ui/shell.js';
import { mountInspector } from '../ui/inspector.js';
import { mountSourceEditor } from '../ui/source-editor.js';
import { openConnectDialog } from '../ui/dialogs.js';
import { mountSimPanel } from '../ui/sim-panel.js';
import { mountVerificationPanel } from '../ui/verification-panel.js';
import { mountRealisationPanel } from '../ui/realisation-panel.js';
import { createSceneView } from '../render/scene-view.js';

const session = createSession();
const shell = mountShell(session);

const view = createSceneView(shell.sceneHost, {
  onSelect: (id) => {
    session.select(id, { source: 'scene' });
    // A tap in the scene brings the inspector forward: at peek on a phone (name, kind, status).
    if (id) shell.revealInspector();
    else shell.dismissInspectorPeek();
  },
  onHover: (id) => session.setHover(id),
  onActivate: (id) => {
    const e = session.model?.entities.get(id);
    if (e?.kind === 'component' && e.data.kind === 'subsystem') session.toggleCollapsed(id);
    else session.requestFit([id]);
  },
  onMoveEnd: (moves) => {
    const ops = moves
      .filter((m) => session.model?.entities.has(m.id))
      .map((m) => ({ type: 'MovePresentationNode', view: session.viewId, id: m.id, x: m.x, z: m.z }));
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
shell.setStatsProvider(() => view.getStats());

// ---- session -> scene ------------------------------------------------------
function selectionIds() {
  const id = session.selection;
  if (!id) return [];
  const e = session.model?.entities.get(id);
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
    try {
      const saved = sessionStorage.getItem(cameraKey());
      if (saved) view.setCamera(JSON.parse(saved));
    } catch { /* no stored camera */ }
  }
}

function saveCamera() {
  if (!session.projectName) return;
  try { sessionStorage.setItem(cameraKey(), JSON.stringify(view.getCamera())); } catch { /* not remembered */ }
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
  const step = s.simulation?.steps[s.stepIndex];
  if (!step) return;
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
shell.sceneHost.addEventListener('pointerup', saveCamera);
shell.sceneHost.addEventListener('wheel', saveCamera, { passive: true });

// Inspection hook for browser tests and for debugging from the console.
/** @type {any} */ (window).__exegra = { session, view };

// Claim evaluation runs scenarios on the main thread, so the engine is loaded before the first project opens.
// If it cannot be loaded the application still opens; the affected claims report why they could not be checked.
initEngine().then(
  () => session.init(),
  (e) => { session.note('error', `The simulation engine could not be loaded: ${e?.message ?? e}`); session.init(); },
);
