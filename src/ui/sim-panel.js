// Simulator panel: drives session.sim* and displays the run. The simulation
// engine is the Lean core behind src/core/engine.js, run by the session in a
// Web Worker; this module holds no semantic state.

import { h, clear, revealInScroller } from './dom.js';
import { entityLabel } from '../core/query.js';

const OUTCOME_WORDS = {
  running: 'Running — more events are queued',
  quiescent: 'Quiescent — no events left',
  'step-limit': 'Stopped at the step limit',
  error: 'Stopped on an expression error',
};

const FAULT_EFFECT_WORDS = {
  dropped: 'dropped the event',
  delayed: 'delayed the event',
  enabled: 'enabled a fault-only transition',
  disabled: 'disabled a transition',
  injected: 'injected the event',
};

const IGNORE_WORDS = {
  'no-transition': 'no transition from the current state on this event',
  'guard-false': 'a matching transition exists but its guard is false',
  disabled: 'a matching transition exists but is disabled by a fault',
};

/** @param {any} v */
function fmt(v) {
  if (typeof v === 'string') return JSON.stringify(v);
  return String(v);
}

/** @param {HTMLElement} el @param {any} session */
export function mountSimPanel(el, session) {
  el.classList.add('sim');
  el.setAttribute('data-testid', 'sim-panel');

  // ---- persistent run column (select and controls survive stepping) ----
  const scenarioSelect = /** @type {HTMLSelectElement} */ (h('select', {
    'data-testid': 'sim-scenario', id: 'sim-scenario-select', 'aria-label': 'Scenario',
    onchange: (/** @type {any} */ e) => session.simLoad(e.target.value || null),
  }));
  let selectSignature = '';

  const mkBtn = (/** @type {string} */ tid, /** @type {string} */ label, /** @type {() => void} */ fn) =>
    /** @type {HTMLButtonElement} */ (h('button', { type: 'button', 'data-testid': tid, onclick: fn }, label));
  const btnReset = mkBtn('sim-reset', 'Reset', () => session.simReset());
  const btnBack = mkBtn('sim-back', 'Back', () => session.simBack());
  const btnStep = mkBtn('sim-step', 'Step', () => session.simStep());
  const btnPlay = mkBtn('sim-play', 'Play', () => session.simPlay(!session.sim.playing));
  const btnRun = mkBtn('sim-run', 'Run to end', () => session.simRunToEnd());

  // Source: a declared scenario, or Live: this application's own recorded events replayed through its
  // self-model (session.simLive, src/core/replay.js).
  const btnSourceScenario = /** @type {HTMLButtonElement} */ (h('button', { type: 'button', class: 'sim__source', 'data-testid': 'sim-source-scenario', onclick: () => session.simLive(false) }, 'Scenario'));
  const btnLive = /** @type {HTMLButtonElement} */ (h('button', { type: 'button', class: 'sim__source', 'data-testid': 'sim-live', onclick: () => session.simLive(!session.live?.on) }, 'Live'));
  const sourceGroup = h('div', { class: 'sim__sources', role: 'group', 'aria-label': 'Source' }, btnSourceScenario, btnLive);
  const liveLine = /** @type {HTMLOutputElement} */ (h('output', { class: 'sim__live', 'data-testid': 'sim-live-status', hidden: true }));
  const scenarioDesc = h('p', { class: 'sim__desc' });
  const behaviorsBox = h('div', { class: 'sim__block' });
  const faultsBox = h('div', { class: 'sim__block' });
  const statusLine = /** @type {HTMLOutputElement} */ (h('output', { class: 'sim__status', 'data-testid': 'sim-status' }));

  // Description and behaviors: a collapsed "About this scenario" in a narrow panel, open in a wide one.
  const about = /** @type {HTMLDetailsElement} */ (h('details', { class: 'sim__about', 'data-testid': 'sim-about' },
    h('summary', { class: 'sim__about-summary' }, 'About this scenario'), scenarioDesc, behaviorsBox));
  const runCol = h('section', { class: 'sim__col sim__col--run', 'aria-label': 'Run' },
    h('h3', { class: 'sim__h' }, 'Run'),
    sourceGroup,
    liveLine,
    h('label', { class: 'sim__label', for: 'sim-scenario-select' }, 'Scenario'),
    scenarioSelect,
    faultsBox,
    h('div', { class: 'sim__controls', role: 'group', 'aria-label': 'Simulation controls' }, btnReset, btnBack, btnStep, btnPlay, btnRun),
    statusLine,
    h('p', { class: 'sim__notice' }, 'This executes the declared behavior model deterministically. It is not evidence about deployed software.'),
    about,
  );

  const timelineCol = h('section', { class: 'sim__col sim__col--timeline', 'data-testid': 'sim-timeline', 'aria-label': 'Timeline' });
  // The step column holds the step detail and the checks as two blocks, so a narrow panel can
  // order them separately (sim.css): current step, timeline, checks, then the run settings.
  const stepBody = h('div', { class: 'sim__stepbody' });
  const checksHost = h('div', { class: 'sim__checkshost' });
  const stepCol = h('section', { class: 'sim__col sim__col--step', 'data-testid': 'sim-step', 'aria-label': 'Step' }, stepBody, checksHost);
  el.append(runCol, timelineCol, stepCol);

  // Wide panel (three columns): the scenario's description and behaviors are shown open;
  // narrow: collapsed. The user's own toggle wins until the panel crosses the breakpoint again.
  let wasWide = /** @type {boolean|null} */ (null);
  new ResizeObserver(() => {
    const wide = el.clientWidth >= 900;
    if (wide !== wasWide && el.clientWidth > 0) { wasWide = wide; about.open = wide; }
  }).observe(el);

  /** @param {string} id @param {string} [text] */
  const link = (id, text) => {
    const m = session.model;
    const ent = m?.entities.get(id);
    return h('button', {
      type: 'button', class: 'sim__link', 'data-entity-id': id, title: id,
      onclick: () => session.select(id),
    }, text ?? (ent ? entityLabel(ent) : id));
  };
  /** @param {string} id */
  const nameOf = (id) => { const e = session.model?.entities.get(id); return e ? entityLabel(e) : id; };

  // ---- run column ----
  function renderRun() {
    const model = session.model;
    const s = session.sim;
    const scenarios = model?.byKind.scenario ?? [];
    const sig = scenarios.map((/** @type {any} */ x) => `${x.id}\u0000${entityLabel(x)}`).join('\u0001');
    if (sig !== selectSignature) {
      selectSignature = sig;
      clear(scenarioSelect);
      scenarioSelect.append(h('option', { value: '' }, 'No scenario'));
      for (const sc of scenarios) scenarioSelect.append(h('option', { value: sc.id }, entityLabel(sc)));
    }
    const live = !!session.live?.on;
    el.dataset.live = String(live);
    btnLive.setAttribute('aria-pressed', String(live));
    btnSourceScenario.setAttribute('aria-pressed', String(!live));
    btnLive.disabled = model?.entities.get('live-session')?.kind !== 'scenario';
    btnLive.title = btnLive.disabled
      ? 'This specification has no live-session scenario: Live mode replays Exegra’s own events through Exegra’s own specification.'
      : 'Show this running Exegra’s own events, replayed through its specification, as they happen';
    liveLine.hidden = !live;
    if (live) {
      const d = session.live.divergences.length;
      const w = session.live.awaiting.length;
      liveLine.textContent = `Live: ${s.simulation?.steps.length ?? 0} real events replayed · ${d} divergence${d === 1 ? '' : 's'} · ${w} predicted event${w === 1 ? '' : 's'} awaited${session.live.dropped ? ` · ${session.live.dropped} earlier events dropped` : ''}`;
      liveLine.classList.toggle('sim__live--bad', d > 0);
    }
    scenarioSelect.value = live ? '' : s.scenarioId ?? '';
    scenarioSelect.disabled = !model;

    const scenario = s.scenarioId ? model?.entities.get(s.scenarioId) : null;
    el.dataset.loaded = String(!!scenario);
    scenarioDesc.textContent = scenario ? (scenario.data.description ?? '') : (scenarios.length ? 'Choose a scenario to run it.' : 'This specification declares no scenarios.');

    clear(behaviorsBox);
    if (scenario) {
      behaviorsBox.append(h('h4', { class: 'sim__sub' }, 'Behaviors in the run'));
      const ul = h('ul', { class: 'sim__list' });
      for (const bid of scenario.data.behaviors ?? []) {
        const b = model?.entities.get(bid);
        if (!b) continue;
        ul.append(h('li', null,
          h('span', { class: 'sim__bname' }, entityLabel(b)),
          b.data.subject ? h('span', { class: 'sim__muted' }, ' on ') : null,
          b.data.subject ? link(b.data.subject) : null));
      }
      behaviorsBox.append(ul);
    }

    clear(faultsBox);
    const faults = model?.byKind.fault ?? [];
    faultsBox.append(h('h4', { class: 'sim__sub' }, 'Faults'));
    if (!faults.length) faultsBox.append(h('p', { class: 'sim__muted' }, 'This specification declares no faults.'));
    else {
      const declared = new Set(scenario?.data.faults ?? []);
      const active = new Set(s.faults);
      const ul = h('ul', { class: 'sim__list sim__list--faults' });
      for (const f of faults) {
        const cb = h('input', {
          type: 'checkbox', checked: active.has(f.id), disabled: !scenario || live,
          'data-testid': `sim-fault-${f.id}`,
          onchange: () => {
            const next = new Set(session.sim.faults);
            if (next.has(f.id)) next.delete(f.id); else next.add(f.id);
            session.simSetFaults(faults.map((/** @type {any} */ x) => x.id).filter((/** @type {string} */ id) => next.has(id)));
          },
        });
        ul.append(h('li', { 'data-entity-id': f.id },
          h('label', { class: 'sim__fault', title: f.data.description ?? (scenario ? '' : 'Load a scenario to enable faults') },
            cb,
            h('span', null, entityLabel(f)),
            h('span', { class: 'sim__chip' }, f.data.kind ?? 'fault'),
            declared.has(f.id) ? h('span', { class: 'sim__mark', title: 'This fault is listed in the scenario itself' }, 'declared by scenario') : null)));
      }
      faultsBox.append(ul, h('p', { class: 'sim__muted' }, 'Changing faults restarts the run.'));
    }

    const sim = s.simulation;
    const total = sim ? sim.steps.length : 0;
    const running = sim?.outcome === 'running';
    const canForward = !!sim && (s.stepIndex < total - 1 || (running && !sim.live));
    btnReset.disabled = !sim || (s.stepIndex < 0 && total === 0);
    btnReset.title = sim ? 'Return to the initial configuration' : s.running ? 'The scenario is running' : 'Load a scenario first';
    btnBack.disabled = !sim || s.stepIndex < 0;
    btnBack.title = !sim ? 'Load a scenario first' : s.stepIndex < 0 ? 'Already at the initial configuration' : 'Show the previous step';
    btnStep.disabled = !canForward;
    btnStep.title = !sim ? 'Load a scenario first' : canForward ? 'Execute the next event delivery' : 'The run has ended';
    btnPlay.disabled = !sim || !!sim.live || (!canForward && !s.playing);
    btnPlay.title = !sim ? 'Load a scenario first' : canForward || s.playing ? 'Step automatically' : 'The run has ended';
    btnPlay.textContent = s.playing ? 'Pause' : 'Play';
    btnPlay.setAttribute('aria-pressed', String(!!s.playing));
    btnRun.disabled = !sim || !canForward;
    btnRun.title = !sim ? 'Load a scenario first' : canForward ? 'Execute until the run ends' : 'The run has ended';

    statusLine.textContent = '';
    statusLine.setAttribute('aria-busy', String(!!s.running));
    if (!sim) statusLine.append(s.running ? h('span', { class: 'sim__outcome sim__outcome--running', 'data-testid': 'sim-running' }, 'Running…') : 'No scenario loaded.');
    else {
      const atEnd = s.stepIndex === total - 1;
      const cur = s.stepIndex >= 0 ? sim.steps[s.stepIndex] : null;
      const t = cur ? cur.time : sim.initial.time;
      statusLine.append(
        h('span', { class: ['sim__outcome', `sim__outcome--${sim.outcome}`] }, atEnd ? (OUTCOME_WORDS[/** @type {keyof typeof OUTCOME_WORDS} */ (sim.outcome)] ?? sim.outcome) : 'Running — viewing an earlier step'),
        h('span', null, ` · time ${t}`),
        h('span', null, ` · ${total} step${total === 1 ? '' : 's'} executed`));
    }
  }

  // ---- timeline column ----
  function renderTimeline() {
    clear(timelineCol);
    const s = session.sim;
    const sim = s.simulation;
    timelineCol.append(h('h3', { class: 'sim__h' }, 'Timeline'));
    if (!sim) { timelineCol.append(h('p', { class: 'sim__muted' }, s.running ? 'Running the scenario…' : 'Load a scenario to see its timeline.')); return; }
    const live = !!sim.live;
    /** @type {Set<number>} */
    const diverged = new Set(live ? session.live.divergences.map((/** @type {any} */ d) => d.stepIndex) : []);
    /** @type {Map<number, any>} */
    const firstViolation = new Map();
    for (const c of s.checks) if (!c.holds && !c.pending && typeof c.stepIndex === 'number') {
      const prev = firstViolation.get(c.stepIndex);
      firstViolation.set(c.stepIndex, prev ? { ...prev, claims: [...prev.claims, c.claimId] } : { claims: [c.claimId] });
    }
    // only the first failing step overall is "the" violation point per claim; show on each claim's own first step
    const ol = h('ol', { class: 'sim__rows' });
    /** @param {number} index @param {any[]} kids */
    const row = (index, kids) => h('li', { class: ['sim__row', index > s.stepIndex && 'sim__row--future', index === s.stepIndex && 'sim__row--current'] },
      h('button', {
        type: 'button', class: 'sim__rowbtn', 'data-testid': `sim-row-${index}`,
        'aria-current': index === s.stepIndex ? 'step' : null,
        onclick: () => session.simSeek(index),
      }, kids));
    ol.append(row(-1, [h('span', { class: 'sim__idx' }, '—'), h('span', { class: 'sim__time' }, `t=${sim.initial.time}`), h('span', { class: 'sim__ev' }, live ? 'Page load (declared initial configuration)' : 'Initial configuration')]));
    // Live: the most recent steps only, so a long session stays responsive.
    const LIVE_ROWS = 300;
    const shownSteps = live && sim.steps.length > LIVE_ROWS ? sim.steps.slice(-LIVE_ROWS) : sim.steps;
    if (shownSteps.length < sim.steps.length) ol.append(h('li', { class: 'sim__muted' }, `${sim.steps.length - shownSteps.length} earlier events are not listed.`));
    const t0 = live ? session.live.at.get(sim.steps[0]?.time) ?? 0 : 0;
    for (const st of shownSteps) {
      const at = live ? session.live.at.get(st.time) : undefined;
      const kids = [
        h('span', { class: 'sim__idx' }, `#${st.index}`),
        h('span', { class: 'sim__time', title: live ? 'Logical time: the recorded sequence number' : null }, `t=${st.time}`),
        live && at !== undefined ? h('span', { class: 'sim__muted sim__clock', title: 'Wall-clock time since the first recorded event (display only)' }, `${((at - t0) / 1000).toFixed(2)} s`) : null,
        live && st.event.source?.inferred ? h('span', { class: 'sim__chip', title: 'The development server inferred this event; nothing observed it directly' }, 'inferred') : null,
        st.kind !== 'deliver' ? h('span', { class: ['sim__chip', `sim__chip--${st.kind}`] }, st.kind) : null,
        h('span', { class: 'sim__ev' }, nameOf(st.event.id)),
        h('span', { class: 'sim__sum' }, st.fired.length
          ? st.fired.map((/** @type {any} */ f) => `${nameOf(f.behavior)}: ${nameOf(f.from)} → ${nameOf(f.to)}`).join('; ')
          : st.kind === 'deliver' ? 'nothing fired' : ''),
        st.faults.length ? h('span', { class: 'sim__mark sim__mark--fault', title: st.faults.map((/** @type {any} */ f) => `${nameOf(f.fault)} ${FAULT_EFFECT_WORDS[/** @type {keyof typeof FAULT_EFFECT_WORDS} */ (f.effect)] ?? f.effect}`).join('; ') }, 'fault') : null,
        st.error ? h('span', { class: 'sim__mark sim__mark--bad', title: st.error.message }, 'error') : null,
        firstViolation.has(st.index) ? h('span', { class: 'sim__mark sim__mark--bad', title: `Violates: ${firstViolation.get(st.index).claims.map(nameOf).join('; ')}` }, 'violation') : null,
        diverged.has(st.index) ? h('span', { class: 'sim__mark sim__mark--bad', 'data-testid': `sim-divergence-mark-${st.index}` }, 'divergence') : null,
      ];
      ol.append(row(st.index, kids));
    }
    const list = h('div', { class: 'sim__scroll-inner' }, ol);
    timelineCol.append(list);

    // pending events of the current configuration
    const config = s.stepIndex >= 0 ? sim.steps[s.stepIndex]?.config : sim.initial;
    timelineCol.append(h('h4', { class: 'sim__sub' }, live ? 'Predicted, not yet seen' : 'Pending events'));
    if (!config?.pending?.length) timelineCol.append(h('p', { class: 'sim__muted' }, 'None.'));
    else {
      const tb = h('tbody');
      for (const p of config.pending) tb.append(h('tr', null,
        h('td', { class: 'sim__num', 'data-label': 'Time' }, `t=${p.time}`),
        h('td', { 'data-label': 'Event' }, link(p.event, nameOf(p.event))),
        h('td', { class: 'sim__muted', 'data-label': 'Source' }, sourceWords(p.source))));
      timelineCol.append(h('table', { class: 'sim__table cardtable', 'data-testid': 'sim-pending' },
        h('thead', null, h('tr', null, h('th', { scope: 'col' }, 'Time'), h('th', { scope: 'col' }, 'Event'), h('th', { scope: 'col' }, 'Source'))), tb));
    }
  }

  /** @param {any} src */
  function sourceWords(src) {
    if (!src) return 'unknown';
    if (src.kind === 'scenario') return `scenario input #${src.step + 1}`;
    if (src.kind === 'transition') return `emitted by transition ${nameOf(src.transition)} of behavior ${nameOf(src.behavior)}`;
    if (src.kind === 'fault') return `injected by fault ${nameOf(src.fault)}`;
    if (src.kind === 'recorded') return src.inferred ? 'recorded: inferred by the development server' : 'recorded from the running application; no transition of the model predicted it';
    return String(src.kind);
  }

  // ---- step column ----
  function renderStep() {
    clear(stepBody);
    const s = session.sim;
    const sim = s.simulation;
    stepBody.append(h('h3', { class: 'sim__h' }, 'Step'));
    clear(checksHost);
    if (!sim) { stepBody.append(h('p', { class: 'sim__muted' }, s.running ? 'Running the scenario…' : 'Load a scenario to inspect its steps.')); return; }

    // violation banner
    const bad = s.checks.filter((/** @type {any} */ c) => !c.holds && !c.pending);
    if (bad.length) {
      const banner = h('div', { class: 'sim__banner', role: 'alert', 'data-testid': 'sim-violation-banner' });
      for (const c of bad) banner.append(h('div', null,
        h('strong', null, 'Claim violated: '), link(c.claimId),
        typeof c.stepIndex === 'number' ? ` at step #${c.stepIndex}` : ''));
      stepBody.append(banner);
    }

    const step = s.stepIndex >= 0 ? sim.steps[s.stepIndex] : null;
    const prevConfig = s.stepIndex >= 1 ? sim.steps[s.stepIndex - 1].config : sim.initial;
    if (!step) {
      stepBody.append(h('p', { class: 'sim__muted' }, 'Initial configuration — no event has been delivered yet.'));
    } else {
      stepBody.append(h('h4', { class: 'sim__sub' }, `Step #${step.index} · t=${step.time}`));
      const kindWord = step.kind === 'drop' ? 'Dropped (not delivered)' : step.kind === 'delay' ? 'Delayed (re-queued, not delivered)' : 'Delivered';
      const dl = h('dl', { class: 'sim__kv' },
        h('dt', null, kindWord), h('dd', null, link(step.event.id, nameOf(step.event.id))),
        h('dt', null, 'Source'), h('dd', null, sourceWords(step.event.source)));
      const flow = session.simFlow();
      if (flow) {
        const undeclared = flow.paths.some((/** @type {any} */ p) => p.kind === 'undeclared');
        dl.append(h('dt', null, 'Message'), h('dd', { class: undeclared ? 'sim__flow sim__flow--undeclared' : 'sim__flow', 'data-testid': 'sim-flow' }, flow.text));
      }
      const payload = Object.entries(step.event.payload ?? {});
      if (payload.length) for (const [k, v] of payload) dl.append(h('dt', null, `payload.${k}`), h('dd', { class: 'sim__mono' }, fmt(v)));
      stepBody.append(dl);

      if (step.error) stepBody.append(h('p', { class: 'sim__banner', role: 'alert' }, `Error: ${step.error.message}`));
      if (step.divergences?.length) {
        const box = h('div', { class: 'sim__banner', role: 'alert' });
        for (const d of step.divergences) box.append(h('div', null, h('strong', null, `Divergence (${d.kind}): `), d.explanation));
        stepBody.append(box);
      }
      if (step.calibrated?.length) {
        stepBody.append(h('p', { class: 'sim__muted' }, 'Calibrated from this real event: ',
          step.calibrated.map((/** @type {any} */ c) => `${c.behavior}.${c.variable} = ${fmt(c.value)}`).join('; '),
          ' (the declared initial value stood for the environment when the stream started).'));
      }

      if (step.fired.length) {
        stepBody.append(h('h4', { class: 'sim__sub' }, 'Fired'));
        for (const f of step.fired) {
          const box = h('div', { class: 'sim__fired', 'data-entity-id': f.transition },
            h('div', { class: 'sim__fired-head' }, link(f.behavior), h('span', { class: 'sim__muted' }, ' via '), link(f.transition, f.transition)),
            h('div', null, h('span', { class: 'sim__state' }, nameOf(f.from)), ' → ', h('span', { class: 'sim__state' }, nameOf(f.to))));
          if (f.guard) box.append(h('div', null, h('span', { class: 'sim__muted' }, 'guard '), h('code', { class: 'sim__mono' }, f.guard)));
          for (const c of f.sets) {
            const changed = c.before !== c.after;
            box.append(h('div', { class: 'sim__mono' }, `${c.variable}: `, h('span', { class: 'sim__muted' }, fmt(c.before)), ' → ', h('span', { class: changed ? 'sim__changed' : '' }, fmt(c.after))));
          }
          for (const e of f.emitted) box.append(h('div', null, h('span', { class: 'sim__muted' }, 'emits '), link(e.event, nameOf(e.event)), h('span', { class: 'sim__muted' }, ` for t=${e.time}`)));
          stepBody.append(box);
        }
      } else if (step.kind === 'deliver') stepBody.append(h('p', { class: 'sim__muted' }, 'No behavior fired a transition.'));

      if (step.ignored.length) {
        const common = step.ignored.filter((/** @type {any} */ i) => i.reason === 'no-transition');
        const notable = step.ignored.filter((/** @type {any} */ i) => i.reason !== 'no-transition');
        if (notable.length) {
          stepBody.append(h('h4', { class: 'sim__sub' }, 'Ignored'));
          const ul = h('ul', { class: 'sim__list' });
          for (const i of notable) ul.append(h('li', null, link(i.behavior), ': ', IGNORE_WORDS[/** @type {keyof typeof IGNORE_WORDS} */ (i.reason)] ?? i.reason,
            i.considered?.length ? h('span', { class: 'sim__muted' }, ` (considered ${i.considered.join(', ')})`) : null));
          stepBody.append(ul);
        }
        if (common.length) {
          const ul = h('ul', { class: 'sim__list' });
          for (const i of common) ul.append(h('li', null, link(i.behavior), ': ', IGNORE_WORDS['no-transition']));
          stepBody.append(h('details', { class: 'sim__details' }, h('summary', null, `${common.length} behavior${common.length === 1 ? '' : 's'} had no transition for this event`), ul));
        }
      }

      if (step.faults.length) {
        stepBody.append(h('h4', { class: 'sim__sub' }, 'Faults that acted'));
        const ul = h('ul', { class: 'sim__list' });
        for (const f of step.faults) ul.append(h('li', null, link(f.fault), ' ', FAULT_EFFECT_WORDS[/** @type {keyof typeof FAULT_EFFECT_WORDS} */ (f.effect)] ?? f.effect));
        stepBody.append(ul);
      }

      if (step.responsible?.length) {
        stepBody.append(h('h4', { class: 'sim__sub' }, 'Responsible entities'));
        const chips = h('div', { class: 'sim__chips', 'data-testid': 'sim-responsible' });
        for (const id of step.responsible) chips.append(h('button', {
          type: 'button', class: 'sim__chip sim__chip--entity', 'data-entity-id': id, title: id, onclick: () => session.select(id),
        }, nameOf(id)));
        stepBody.append(chips);
      }
    }

    // configuration
    const config = step ? step.config : sim.initial;
    stepBody.append(h('h4', { class: 'sim__sub' }, 'Configuration'));
    const tbody = h('tbody');
    for (const [bid, m] of Object.entries(config.machines)) {
      const before = step ? prevConfig.machines[bid] : null;
      const vars = Object.entries(m.vars);
      const stateChanged = !!before && before.state !== m.state;
      tbody.append(h('tr', { 'data-entity-id': bid },
        h('td', { class: 'cardtable__title' }, link(bid)),
        h('td', { 'data-label': 'State' }, h('span', { class: ['sim__state', stateChanged && 'sim__changed'] }, nameOf(m.state)), stateChanged ? h('span', { class: 'sim__muted' }, ` (was ${nameOf(before.state)})`) : null),
        h('td', { class: 'sim__mono', 'data-label': 'Variables' }, vars.length ? vars.map(([k, v]) => {
          const ch = !!before && before.vars[k] !== v;
          return h('span', { class: ['sim__var', ch && 'sim__changed'], title: ch ? `changed in this step (was ${fmt(before.vars[k])})` : null }, `${k} = ${fmt(v)}`);
        }) : h('span', { class: 'sim__muted' }, 'no variables'))));
    }
    stepBody.append(h('table', { class: 'sim__table cardtable', 'data-testid': 'sim-config' },
      h('thead', null, h('tr', null, h('th', { scope: 'col' }, 'Behavior'), h('th', { scope: 'col' }, 'State'), h('th', { scope: 'col' }, 'Variables'))), tbody));

    // requests: the contract events of the run as a request log (only when the scenario has any)
    if (s.requestLog.length) {
      const reqs = h('div', { 'data-testid': 'sim-requests', class: 'sim__requests' }, h('h4', { class: 'sim__sub' }, 'Requests'));
      const ol = h('ol', { class: 'sim__rows sim__reqlog' });
      for (const e of s.requestLog) {
        ol.append(h('li', { class: ['sim__row', e.step > s.stepIndex && 'sim__row--future', e.step === s.stepIndex && 'sim__row--current'], 'data-role': e.role },
          h('button', {
            type: 'button', class: 'sim__rowbtn sim__reqbtn', 'data-testid': `sim-request-${e.step}`,
            'aria-current': e.step === s.stepIndex ? 'step' : null,
            title: `Step #${e.step}, t=${e.time}: ${e.event}`,
            onclick: () => session.simSeek(e.step),
          }, h('span', { class: 'sim__idx' }, `#${e.step}`), h('span', { class: ['sim__reqtext', e.role === 'error' && 'sim__bad'] }, e.text))));
      }
      reqs.append(ol);
      checksHost.append(reqs);
    }

    // divergences of the live replay: real events the self-model does not allow, predictions that never came
    if (sim.live) {
      const all = session.live.divergences;
      const box = h('div', { 'data-testid': 'sim-divergences', class: 'sim__divergences' }, h('h4', { class: 'sim__sub' }, `Divergences (${all.length})`));
      if (!all.length) box.append(h('p', { class: 'sim__muted' }, 'None: every recorded event so far is one the self-model allows, and every prediction older than the bound was seen.'));
      else {
        const ol = h('ol', { class: 'sim__rows' });
        for (const d of all.slice(-200)) {
          ol.append(h('li', { class: ['sim__row', 'sim__divergence'], 'data-kind': d.kind },
            h('button', { type: 'button', class: 'sim__rowbtn', title: d.explanation, onclick: () => session.simSeek(d.stepIndex) },
              h('span', { class: 'sim__idx' }, `#${d.stepIndex}`),
              h('span', { class: 'sim__chip sim__chip--bad' }, d.kind),
              h('span', { class: 'sim__reqtext' }, d.explanation))));
        }
        box.append(ol);
      }
      checksHost.append(box);
    }

    // checks
    const checks = h('div', { 'data-testid': 'sim-checks', class: 'sim__checks' }, h('h4', { class: 'sim__sub' }, 'Checks'));
    // A finished run viewed at its last step is a whole trace, not a partial one.
    const runEnded = () => !!s.simulation && s.simulation.outcome !== 'running' && s.stepIndex === s.simulation.steps.length - 1;
    if (!s.checks.length) checks.append(h('p', { class: 'sim__muted' }, 'No invariant or temporal claim covers the behaviors of this scenario.'));
    else {
      const ul = h('ul', { class: 'sim__list' });
      for (const c of s.checks) {
        ul.append(h('li', { class: ['sim__check', !c.holds && !c.pending && 'sim__check--bad'], 'data-entity-id': c.claimId },
          link(c.claimId),
          c.pending
            ? h('div', { class: 'sim__muted' }, `undecided at this point of the run — ${c.explanation}`)
            : c.holds
            ? h('div', { class: 'sim__muted' }, runEnded() ? 'holds on this trace' : 'holds on the trace so far', c.explanation ? ` — ${c.explanation}` : '', runEnded() ? ' (one trace is not a verification)' : ' (a partial trace is not a verification)')
            : h('div', null,
              h('strong', { class: 'sim__bad' }, `VIOLATED at step #${c.stepIndex ?? '?'}`), ` — ${c.explanation}`,
              typeof c.stepIndex === 'number' ? h('button', { type: 'button', class: 'sim__jump', onclick: () => session.simSeek(c.stepIndex) }, 'Jump to step') : null)));
      }
      checks.append(ul);
    }
    checksHost.append(checks);
  }

  // ---- render with focus preservation ----
  function render() {
    const active = document.activeElement;
    const tid = active && el.contains(active) ? active.getAttribute('data-testid') : null;
    const scrollRun = runCol.scrollTop, scrollStep = stepCol.scrollTop, scrollTl = timelineCol.scrollTop;
    renderRun();
    renderTimeline();
    renderStep();
    runCol.scrollTop = scrollRun; stepCol.scrollTop = scrollStep; timelineCol.scrollTop = scrollTl;
    revealInScroller(timelineCol.querySelector('[aria-current="step"]'));
    if (tid && document.activeElement !== active) {
      const next = /** @type {HTMLElement|null} */ (el.querySelector(`[data-testid="${CSS.escape(tid)}"]`));
      if (next && !(/** @type {any} */ (next).disabled)) next.focus({ preventScroll: true });
    }
  }

  const offs = [session.on('sim', render), session.on('model', render), session.on('project', render)];
  render();
  return () => { for (const off of offs) off(); };
}
