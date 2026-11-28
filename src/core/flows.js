// Message flows of a simulation step: which component sent the event a step
// handles, which components received it, and the path that message takes
// through a projected scene. Pure: reads the model, one trace step and a scene.
//
// A flow is read from the trace, never guessed. The sender is the subject of the
// behavior whose transition emitted the event; an event scheduled by the scenario
// or injected by a fault comes from outside the system. The receivers are the
// subjects of the behaviors that fired a transition on it. A hop is classified
// against the derived model (src/core/abstraction.js), never against whatever
// edge happens to join two drawn nodes: it follows an edge only when a
// relationship between the two components themselves is a witness of the derived
// interaction that edge draws. Otherwise it is "unshown" (such a relationship
// exists, but this view does not draw it) or "undeclared" (no relationship
// connects the two components), whatever the collapse state, so a message between
// components the specification does not connect is visible as such at every level.

import { componentsFor, ancestorsOf } from './query.js';
import { deriveModel, blockAt, witnessOf, endpointElement } from './abstraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').SceneModel} SceneModel */
/** @typedef {import('./engine.js').TraceStep} TraceStep */

/**
 * @typedef {Object} StepFlow
 * @property {string} event        the event the step handles
 * @property {number} time         logical time of the step
 * @property {'deliver'|'drop'|'delay'} kind
 * @property {{kind:'behavior', behavior:string}|{kind:'scenario', step:number}|{kind:'fault', fault:string}} origin
 * @property {string|null} from    the sending component, or null when the event comes from outside
 * @property {{component:string, behavior:string, transition:string}[]} to  receivers, one per firing behavior, in trace order
 */

/**
 * @typedef {{kind:'edge', from:string, to:string, edgeId:string, reverse:boolean}
 *   | {kind:'unshown', from:string, to:string, relationship:string}
 *   | {kind:'undeclared', from:string, to:string}
 *   | {kind:'enter', to:string}
 *   | {kind:'local', node:string}
 *   | {kind:'lost', from:string}} FlowPath
 *   Scene node ids. `edge`: along that scene edge (reverse when the message runs against its direction).
 *   `unshown`: a relationship connects the two components but the scene draws no edge for it.
 *   `undeclared`: no relationship connects the two components. `enter`: from outside the system into a node.
 *   `local`: sender and receiver are drawn as the same node. `lost`: the event was dropped after leaving its sender.
 */

/**
 * The component a behavior describes: its subject, or the owner of a subject port.
 * @param {Model} model @param {string} behaviorId
 * @returns {string|null}
 */
export function behaviorComponent(model, behaviorId) {
  const b = model.entities.get(behaviorId);
  if (b?.kind !== 'behavior') return null;
  return componentsFor(model, behaviorId)[0] ?? null;
}

/**
 * The message flow of one trace step.
 * @param {Model} model @param {TraceStep} step
 * @returns {StepFlow}
 */
export function stepFlow(model, step) {
  const source = step.event.source ?? {};
  /** @type {StepFlow['origin']} */
  let origin;
  /** @type {string|null} */
  let from = null;
  if (source.kind === 'transition' && typeof source.behavior === 'string') {
    origin = { kind: 'behavior', behavior: source.behavior };
    from = behaviorComponent(model, source.behavior);
  } else if (source.kind === 'fault') {
    origin = { kind: 'fault', fault: String(source.fault) };
  } else {
    origin = { kind: 'scenario', step: Number(source.step ?? 0) };
  }
  /** @type {StepFlow['to']} */
  const to = [];
  for (const f of step.fired) {
    const component = behaviorComponent(model, f.behavior);
    if (component) to.push({ component, behavior: f.behavior, transition: f.transition });
  }
  return { event: step.event.id, time: step.time, kind: step.kind, origin, from, to };
}

/**
 * The node drawing a component in this scene: for a scene that draws a derived
 * model, the component's block at that cut; otherwise its own node or its nearest
 * drawn ancestor. null when that node is not drawn.
 * @param {Model} model @param {SceneModel} scene @param {Map<string, any>} drawn scene nodes by id @param {string} componentId
 * @returns {string|null}
 */
function drawnNode(model, scene, drawn, componentId) {
  const d = scene.abstraction ? deriveModel(model, { hierarchy: scene.abstraction.hierarchy, blocks: scene.abstraction.blocks }) : null;
  if (d) { const b = blockAt(d.level, componentId); return b !== null && drawn.has(b) ? b : null; }
  if (drawn.has(componentId)) return componentId;
  for (const a of ancestorsOf(model, componentId)) if (drawn.has(a)) return a;
  return null;
}

/**
 * The relationships between two components, in either direction (endpoints may be
 * ports of them), in declaration order: the base facts a hop between them can be
 * a witness of.
 * @param {Model} model @param {string} a @param {string} b
 * @returns {{id: string, forward: boolean}[]}
 */
function relationshipsBetween(model, a, b) {
  const out = [];
  for (const r of model.byKind.relationship ?? []) {
    const from = endpointElement(model, r.data.from)?.element;
    const to = endpointElement(model, r.data.to)?.element;
    if (from === a && to === b) out.push({ id: r.id, forward: true });
    else if (from === b && to === a) out.push({ id: r.id, forward: false });
  }
  return out;
}

/**
 * The scene edge that draws the derived interaction a relationship is a witness of,
 * or null when the scene does not draw it.
 * @param {Model} model @param {SceneModel} scene @param {string} relationshipId
 */
function edgeOf(model, scene, relationshipId) {
  const d = scene.abstraction ? deriveModel(model, { hierarchy: scene.abstraction.hierarchy, blocks: scene.abstraction.blocks }) : null;
  const i = d ? witnessOf(d, relationshipId).interaction : null;
  return scene.edges.find((e) => (Array.isArray(e.witnesses) ? e.witnesses.includes(relationshipId) : e.entityId === relationshipId) && (!i || (e.from === i.from && e.to === i.to))) ?? null;
}

/**
 * The paths the flow of a step takes through a scene, one per receiver (or one
 * for a dropped event). Components the scene does not draw give no path.
 * @param {Model} model @param {SceneModel} scene @param {StepFlow} flow
 * @returns {FlowPath[]}
 */
export function flowPaths(model, scene, flow) {
  const drawn = new Map(scene.nodes.map((n) => [n.id, n]));
  const sender = flow.from ? drawnNode(model, scene, drawn, flow.from) : null;
  /** @type {FlowPath[]} */
  const out = [];
  if (flow.kind === 'drop') {
    if (sender) out.push({ kind: 'lost', from: sender });
    return out;
  }
  if (flow.kind !== 'deliver') return out;
  const seen = new Set();
  for (const r of flow.to) {
    const receiver = drawnNode(model, scene, drawn, r.component);
    if (!receiver || seen.has(receiver)) continue;
    seen.add(receiver);
    if (!flow.from) { out.push({ kind: 'enter', to: receiver }); continue; }
    if (!sender) continue;
    if (sender === receiver) { out.push({ kind: 'local', node: receiver }); continue; }
    // The base relationships between the two components are the only witnesses a hop can follow; the first one
    // whose derived interaction the scene draws gives the edge (preferring one in the message's direction).
    const between = relationshipsBetween(model, /** @type {string} */ (flow.from), r.component);
    const ordered = [...between.filter((x) => x.forward), ...between.filter((x) => !x.forward)];
    const along = ordered.map((x) => ({ x, edge: edgeOf(model, scene, x.id) })).find((y) => y.edge);
    if (along?.edge) { out.push({ kind: 'edge', from: sender, to: receiver, edgeId: along.edge.id, reverse: along.edge.from !== sender }); continue; }
    if (between.length) out.push({ kind: 'unshown', from: sender, to: receiver, relationship: between[0].id });
    else out.push({ kind: 'undeclared', from: sender, to: receiver });
  }
  return out;
}

/**
 * One line describing a step's flow for people: who sent what to whom, and how.
 * @param {Model} model @param {StepFlow} flow @param {FlowPath[]} paths
 * @returns {string}
 */
export function describeFlow(model, flow, paths) {
  const name = (/** @type {string|null} */ id) => {
    if (!id) return 'outside';
    const e = model.entities.get(id);
    return typeof e?.data?.name === 'string' ? e.data.name : id;
  };
  const source = flow.origin.kind === 'scenario' ? 'outside (scenario)' : flow.origin.kind === 'fault' ? `outside (fault ${flow.origin.fault})` : name(flow.from);
  if (flow.kind === 'drop') return `${flow.event}: sent by ${source}, dropped by a fault before delivery`;
  if (flow.kind === 'delay') return `${flow.event}: delayed by a fault`;
  if (!flow.to.length) return `${flow.event}: sent by ${source}; no behavior took a transition on it`;
  const receivers = [...new Set(flow.to.map((r) => name(r.component)))].join(', ');
  const undeclared = paths.filter((p) => p.kind === 'undeclared').length;
  const unshown = paths.filter((p) => p.kind === 'unshown').length;
  const notes = [undeclared ? `${undeclared} without a declared relationship` : '', unshown ? `${unshown} along a relationship this view does not draw` : ''].filter(Boolean);
  return `${flow.event}: ${source} → ${receivers}${notes.length ? ` (${notes.join('; ')})` : ''}`;
}
