// Compare observations of two overlapping writes with both orders of the specification's scenario.
// The capture contains only observations. All expected outcomes and the winning value come from
// running the model, with opaque values bound to the two concrete submissions by array position.
import { engineInput, runEngine } from './engine.js';

const SCENARIO = 'two-session-edit-race';
const MACHINE = 'shared-base-write-flow';

/** @param {unknown} value */
const nonempty = (value) => typeof value === 'string' && value.length > 0;

/** @param {any} a @param {any} b */
const sameRecord = (a, b) => a?.tenant === b.tenant && a?.record === b.record;

/** @param {import('./types.js').Model} model @param {any[]} attempts */
function predictedOrders(model, attempts) {
  const input = engineInput(model, SCENARIO);
  const steps = input.scenario.steps;
  if (steps.length !== 2 || steps[0].at !== steps[1].at ||
      steps.some((s) => s.event !== 'two-session-write' || !nonempty(s.payload.attempt) || !nonempty(s.payload.value)) ||
      steps[0].payload.attempt === steps[1].payload.attempt || steps[0].payload.value === steps[1].payload.value ||
      steps[0].payload.base !== steps[1].payload.base) throw new Error('The two-editor scenario needs two distinct simultaneous conditional writes from one base.');

  const byActor = new Map(steps.map((s, i) => [s.payload.attempt, attempts[i]]));
  const byValue = new Map(steps.map((s, i) => [s.payload.value, attempts[i].value]));
  return [steps, [...steps].reverse()].map((ordered) => {
    const trace = runEngine({ ...input, scenario: { ...input.scenario, steps: ordered } });
    const replies = new Map();
    for (const step of trace.steps.filter((/** @type {any} */ s) => s.event.id === 'two-session-write')) {
      const decision = step.config.machines[MACHINE]?.vars.decision;
      if (!step.fired.some((/** @type {any} */ f) => f.behavior === MACHINE) || !['accepted','conflict'].includes(decision)) {
        throw new Error('The model did not decide an edit.');
      }
      replies.set(byActor.get(step.event.payload.attempt).id, decision);
    }
    const stored = byValue.get(trace.final.machines[MACHINE]?.vars.stored);
    if (trace.outcome !== 'quiescent' || replies.size !== 2 || stored === undefined) {
      throw new Error('The model did not finish both edits with a stored value.');
    }
    return { order: ordered.map(s => byActor.get(s.payload.attempt).id), replies, stored };
  });
}

/**
 * Each reply belongs to the observer of a single submission. A witnessed transport loss supplies
 * no verdict about that write. A missing response without such a witness is incomplete capture.
 * @param {import('./types.js').Model} model @param {any} capture
 */
export function checkEditHistory(model, capture) {
  /** @param {string} reason @param {number|null} [observationIndex] */
  const incomplete = (reason, observationIndex = null) => ({ verdict: 'inconclusive', orders: [], reason, observationIndex });
  if (capture?.format !== 'exegra-edit-history' || capture.version !== 1 || capture.complete !== true) {
    return incomplete('A complete version-1 edit capture is required.');
  }
  const { attempts, scope, base, observations } = capture;
  if (!nonempty(scope?.tenant) || !nonempty(scope?.record) || !nonempty(base) || !Array.isArray(attempts) ||
      attempts.length !== 2 || attempts.some(a => !sameRecord(a, scope) || a.base !== base || !nonempty(a.id) || typeof a.value !== 'string') ||
      attempts[0].id === attempts[1].id || attempts[0].value === attempts[1].value || !Array.isArray(observations)) {
    return incomplete('Two identified, distinct edits of the same record and base revision are required.');
  }
  let candidates = predictedOrders(model, attempts);
  const ids = new Set(attempts.map(a => a.id));
  const answered = new Set();
  const lost = new Set();
  let read = false;
  for (const [i, obs] of observations.entries()) {
    if (obs?.kind === 'stored') {
      if (!sameRecord(obs, scope) || typeof obs.value !== 'string' || !nonempty(obs.revision)) {
        return incomplete('The durable read must identify the requested tenant, record, revision and value.', i);
      }
      read = true;
      candidates = candidates.filter(c => c.stored === obs.value && obs.revision !== base);
    } else if (obs?.kind === 'reply' || obs?.kind === 'reply-lost') {
      if (!ids.has(obs.attempt)) return incomplete('The reply has no matching submission.', i);
      if (obs.kind === 'reply-lost') {
        if (answered.has(obs.attempt)) return incomplete('The capture marks a received reply as lost.', i);
        lost.add(obs.attempt);
      } else {
        if (!['accepted','conflict'].includes(obs.outcome) || lost.has(obs.attempt)) {
          return incomplete('The reply is unrecognised or also marked lost.', i);
        }
        answered.add(obs.attempt);
        candidates = candidates.filter(c => c.replies.get(obs.attempt) === obs.outcome);
      }
    } else return incomplete('Unrecognised observation.', i);
    if (!candidates.length) {
      return { verdict: 'incompatible', orders: [], reason: obs.kind === 'stored'
        ? 'Neither serial order explains the durable read and preceding replies.'
        : 'Neither serial order explains this reply and the preceding observations.', observationIndex: i };
    }
  }
  if (!read || answered.size + lost.size !== 2) return incomplete('Each attempt needs a reply or a witnessed loss, and the record needs an independent final read.');
  return { verdict: 'compatible', orders: candidates.map(c => c.order), reason: 'The observations agree with a serial order in the model.', observationIndex: null };
}
