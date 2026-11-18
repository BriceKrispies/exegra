// Simulation transport: a compact bar that is visible whenever a scenario is loaded,
// with or without the Simulate panel open, so the messages can be watched travelling
// through the scene while stepping. Docked above the bottom navigation on a phone and
// floating at the bottom of the scene from tablet width up (layout.css). It drives the
// session's simulation functions and holds no state of its own.

import { h, clear, icon } from './dom.js';
import { entityLabel } from '../core/query.js';

/**
 * @param {HTMLElement} el the transport host
 * @param {any} session
 * @param {{show: (dest: string) => void, onVisible: (visible: boolean) => void}} env
 * @returns {() => void} dispose
 */
export function mountSimTransport(el, session, env) {
  el.classList.add('transport');
  /** @param {string} testid @param {string} ic @param {string} label @param {() => void} fn */
  const btn = (testid, ic, label, fn) => h('button', { type: 'button', class: 'transport__btn', 'data-testid': testid, 'aria-label': label, title: label, onclick: fn }, icon(ic, 20));
  const back = btn('transport-back', 'step-back', 'Step back', () => session.simBack());
  const play = btn('transport-play', 'play', 'Play', () => session.simPlay(!session.sim?.playing));
  const step = btn('transport-step', 'step', 'Step', () => session.simStep());
  const end = btn('sim-end', 'run-end', 'Run to end', () => session.simRunToEnd());
  const readout = h('output', { class: 'transport__readout', 'data-testid': 'sim-readout', 'aria-live': 'off' });
  const name = h('span', { class: 'transport__name' });
  // The readout is also the way into the Simulate panel.
  const info = h('button', {
    type: 'button', class: 'transport__info', 'data-testid': 'transport-open', title: 'Open the simulation panel',
    onclick: () => env.show('simulation'),
  }, name, readout);
  clear(el);
  el.append(back, play, step, info, end);

  const render = () => {
    const sim = session.sim ?? {};
    const visible = !!sim.scenarioId && !!session.model;
    el.hidden = !visible;
    env.onVisible(visible);
    if (!visible) return;
    const scenario = session.model.entities.get(sim.scenarioId);
    name.textContent = scenario ? entityLabel(scenario) : sim.scenarioId;
    const s = sim.simulation;
    if (!s) {
      for (const b of [back, play, step, end]) /** @type {HTMLButtonElement} */ (b).disabled = true;
      readout.textContent = sim.running ? 'running…' : 'step -';
      readout.title = sim.running ? 'The engine is running the scenario' : '';
      info.setAttribute('aria-label', `${name.textContent}: ${readout.textContent}. Open the simulation panel.`);
      return;
    }
    const total = s.steps.length;
    const idx = sim.stepIndex ?? -1;
    // Live: every recorded event is already a step; forward moves only within them, and there is nothing to play.
    const canAdvance = s.live ? idx < total - 1 : s.outcome === 'running' || idx < total - 1;
    /** @type {HTMLButtonElement} */ (back).disabled = idx < 0;
    back.title = idx < 0 ? 'Already at the initial configuration' : 'Step back';
    /** @type {HTMLButtonElement} */ (step).disabled = !canAdvance;
    step.title = canAdvance ? 'Step' : `Run ended: ${s.outcome}`;
    /** @type {HTMLButtonElement} */ (play).disabled = s.live || (!canAdvance && !sim.playing);
    play.title = sim.playing ? 'Pause' : canAdvance ? 'Play' : `Run ended: ${s.outcome}`;
    play.setAttribute('aria-label', sim.playing ? 'Pause' : 'Play');
    play.setAttribute('aria-pressed', String(!!sim.playing));
    clear(play).append(icon(sim.playing ? 'pause' : 'play', 20));
    /** @type {HTMLButtonElement} */ (end).disabled = !canAdvance;
    end.title = canAdvance ? 'Run to end' : `Run ended: ${s.outcome}`;
    const t = idx >= 0 ? s.steps[idx]?.time : s.initial?.time;
    readout.textContent = `step ${idx + 1}/${total} · t=${t ?? 0}`;
    readout.title = `Step ${idx + 1} of ${total} executed so far (0 is the initial configuration). Logical time ${t ?? 0}. Outcome: ${s.outcome}.`;
    info.setAttribute('aria-label', `${name.textContent}: ${readout.textContent}. Open the simulation panel.`);
    el.dataset.outcome = s.outcome;
  };

  const offs = [session.on('sim', render), session.on('project', render), session.on('model', render)];
  render();
  return () => { for (const off of offs) off(); };
}
