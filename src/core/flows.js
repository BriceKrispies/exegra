// Message flows of a simulation step: which component sent the event a step
// handles, which components received it, and the path that message takes
// through a projected scene. Pure: reads the model, one trace step and a scene.
//
// A flow is read from the trace, never guessed. The sender is the subject of the
// behavior whose transition emitted the event; an event scheduled by the scenario
// or injected by a fault comes from outside the system. The receivers are the
// subjects of the behaviors that fired a transition on it. A path follows an edge
// of the scene only when one connects the two drawn nodes. Otherwise it is either
// "unshown" (a relationship connects the two components, but this view does not
// draw it) or "undeclared" (no relationship connects them), so a message between
// components the specification does not connect is visible as such.

import { componentOf, ancestorsOf } from './query.js';

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
  const subject = b?.data?.subject;
  if (typeof subject !== 'string') return null;
  return componentOf(model, subject)?.id ?? null;
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
 * The node drawing a component in this scene: the component's own node, or the
 * nearest collapsed ancestor that stands for it. null when it is not drawn.
 * @param {Model} model @param {Map<string, any>} drawn scene nodes by id @param {string} componentId
 * @returns {string|null}
 */
function drawnNode(model, drawn, componentId) {
  if (drawn.has(componentId)) return componentId;
  for (const a of ancestorsOf(model, componentId)) if (drawn.has(a)) return a;
  return null;
}

/**
 * A relationship of the model between two components, in either direction
 * (endpoints may be ports of them). The first in declaration order, or null.
 * @param {Model} model @param {string} a @param {string} b
 * @returns {string|null}
 */
function relationshipBetween(model, a, b) {
  for (const r of model.byKind.relationship ?? []) {
    const from = componentOf(model, r.data.from)?.id;
    const to = componentOf(model, r.data.to)?.id;
    if ((from === a && to === b) || (from === b && to === a)) return r.id;
  }
  return null;
}

/**
 * The paths the flow of a step takes through a scene, one per receiver (or one
 * for a dropped event). Components the scene does not draw give no path.
 * @param {Model} model @param {SceneModel} scene @param {StepFlow} flow
 * @returns {FlowPath[]}
 */
export function flowPaths(model, scene, flow) {
  const drawn = new Map(scene.nodes.map((n) => [n.id, n]));
  const sender = flow.from ? drawnNode(model, drawn, flow.from) : null;
  /** @type {FlowPath[]} */
  const out = [];
  if (flow.kind === 'drop') {
    if (sender) out.push({ kind: 'lost', from: sender });
    return out;
  }
  if (flow.kind !== 'deliver') return out;
  const seen = new Set();
  for (const r of flow.to) {
    const receiver = drawnNode(model, drawn, r.component);
    if (!receiver || seen.has(receiver)) continue;
    seen.add(receiver);
    if (!flow.from) { out.push({ kind: 'enter', to: receiver }); continue; }
    if (!sender) continue;
    if (sender === receiver) { out.push({ kind: 'local', node: receiver }); continue; }
    const forward = scene.edges.find((e) => e.from === sender && e.to === receiver);
    const backward = forward ? undefined : scene.edges.find((e) => e.from === receiver && e.to === sender);
    const edge = forward ?? backward;
    if (edge) { out.push({ kind: 'edge', from: sender, to: receiver, edgeId: edge.id, reverse: !forward }); continue; }
    const declared = flow.from ? relationshipBetween(model, flow.from, r.component) : null;
    if (declared) out.push({ kind: 'unshown', from: sender, to: receiver, relationship: declared });
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
