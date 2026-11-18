// The traffic recorder: a bounded in-memory stream of the events this running Exegra really
// produces, named by the event ids of its own specification (specs/exegra/spec.jsonc), so the
// stream can be replayed through the self-model (src/core/replay.js) and shown in the simulator
// panel's Live mode.
//
// Each event gets a logical sequence number (`seq`, 1, 2, 3, ...), which is the only time the replay
// and the claim evaluator ever see. The wall-clock time (`at`, from performance.now) is kept here for
// display only and is never handed to the core: `forReplay()` strips it.
//
// Producers call `record(id, payload)` at the code location the specification names for that event.
// Request ids (`requestId`, the correlation field of the contract events) come from `nextRequestId()`.
// The development server's own events arrive with each answer and are appended by the persistence
// client in the order it receives them (src/persist/client.js, tools/vite-plugin-exegra.js).

/** Events kept; older ones are dropped and counted. */
export const RECORDER_LIMIT = 5000;

/**
 * @typedef {{seq: number, id: string, payload: Record<string, any>, at: number, inferred?: boolean}} RecordedEntry
 */

/**
 * @param {{limit?: number, clock?: () => number}} [opts]
 */
export function createTrafficRecorder(opts = {}) {
  const limit = opts.limit ?? RECORDER_LIMIT;
  const clock = opts.clock ?? (() => (typeof performance !== 'undefined' ? performance.now() : 0));
  /** @type {RecordedEntry[]} */
  let entries = [];
  let seq = 0;
  let requestSeq = 0;
  let dropped = 0;
  /** @type {Set<(e: RecordedEntry) => void>} */
  const listeners = new Set();

  return {
    /**
     * Append one real event.
     * @param {string} id event id of the specification
     * @param {Record<string, any>} [payload]
     * @param {{inferred?: boolean}} [meta] inferred: the producer deduced the event rather than observing it
     */
    record(id, payload = {}, meta = {}) {
      /** @type {RecordedEntry} */
      const e = { seq: ++seq, id, payload: JSON.parse(JSON.stringify(payload)), at: clock() };
      if (meta.inferred) e.inferred = true;
      entries.push(e);
      if (entries.length > limit) {
        const over = entries.length - limit;
        entries = entries.slice(over);
        dropped += over;
      }
      for (const fn of [...listeners]) {
        try { fn(e); } catch (err) { console.error('[exegra] traffic listener failed', err); }
      }
      return e;
    },
    /** A fresh correlation id for a request. */
    nextRequestId() { return ++requestSeq; },
    /**
     * The latest kept event with this id that answers `requestId`, or null.
     * @param {string} id @param {number} requestId
     */
    answer(id, requestId) {
      for (let i = entries.length - 1; i >= 0; i--) if (entries[i].id === id && entries[i].payload.requestId === requestId) return entries[i];
      return null;
    },
    /** The events kept, oldest first. */
    events() { return entries.slice(); },
    /** The kept events without wall-clock times: what the replay reads. */
    forReplay() { return entries.map((e) => (e.inferred ? { seq: e.seq, id: e.id, payload: e.payload, inferred: true } : { seq: e.seq, id: e.id, payload: e.payload })); },
    /** How many events were dropped because the buffer was full. */
    get dropped() { return dropped; },
    get limit() { return limit; },
    /** @param {(e: RecordedEntry) => void} fn */
    subscribe(fn) { listeners.add(fn); return () => { listeners.delete(fn); }; },
  };
}

/** @typedef {ReturnType<typeof createTrafficRecorder>} TrafficRecorder */

/** The recorder of this page. Every producer of the application records into it. */
export const traffic = createTrafficRecorder();
