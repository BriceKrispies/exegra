// Fault lifting (src/core/fault-lifting.js, the lift-faults command, WG-5730): a failure mode located at an element
// or an interaction lifts through realisation maps and with a cut, so a deployment-level fault appears at the
// logical level as the interaction failures it causes. The distributed fixture is
// tests/fixtures/multiscale-external/distributed.jsonc, loaded through the command line with --spec.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from '../../cli/commands.js';

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'multiscale-external');
const DISTRIBUTED = path.join(FIXTURES, 'distributed.jsonc');

/** @param {string[]} args @param {string} [file] */
async function lift(args, file = DISTRIBUTED) {
  const r = /** @type {any} */ (await runCommand('lift-faults', ['--spec', file, ...args]));
  assert.equal(r.ok, true, JSON.stringify(r.error));
  return r.result;
}
/** @param {any} result @param {string} id */
const mode = (result, id) => result.modes.find((/** @type {any} */ m) => m.id === id);
/** @param {any} m */
const hit = (m) => m.effects.map((/** @type {any} */ e) => e.interaction);

test('the distributed fixture validates, with logical and deployment hierarchies and its realisation maps holding', async () => {
  const v = /** @type {any} */ (await runCommand('validate', ['--spec', DISTRIBUTED]));
  assert.equal(v.ok, true);
  assert.equal(v.result.errors, 0);
  assert.equal(v.result.warnings, 0);
  const cuts = /** @type {any} */ (await runCommand('cut', ['--spec', DISTRIBUTED]));
  assert.deepEqual(cuts.result.hierarchies.map((/** @type {any} */ h) => h.id), ['logical', 'deployment']);
  const d = /** @type {any} */ (await runCommand('derive', ['--spec', DISTRIBUTED, '--cut', 'shop-leaf']));
  assert.deepEqual(d.result.realisations.map((/** @type {any} */ r) => r.holds), [true, true, true]);
});

// On the distributed fixture a link partition, a host crash and a zone outage each fail exactly the logical interactions their realisation paths carry.
// @evidence fault-lifting-through-realisation
test('a deployment-level failure mode lifts to the logical interactions it affects', async () => {
  const r = await lift(['--cut', 'shop-leaf']);
  // A fault at a network link fails exactly the interaction that link realises.
  assert.deepEqual(hit(mode(r, 'fm-link-a-b-partition')), ['cart-places-order']);
  assert.equal(mode(r, 'fm-link-a-b-partition').failure, 'unavailable');
  // A host fails the interactions whose realisation path runs through it.
  assert.deepEqual(hit(mode(r, 'fm-app-host-b-crash')), ['cart-places-order', 'orders-reserve-stock']);
  // A zone does too, through the hosts placed in it in the deployment hierarchy; nothing else.
  assert.deepEqual(hit(mode(r, 'fm-zone-2-outage')), ['cart-places-order', 'orders-reserve-stock']);
  assert.ok(mode(r, 'fm-zone-2-outage').effects.every((/** @type {any} */ e) => e.via === 'realisation' && typeof e.realisation === 'string'));
  // Never the interaction on the other side of the zone boundary.
  for (const m of r.modes) assert.ok(!hit(m).includes('ui-calls-cart'), m.id);
});

test('a failure mode at a logical element fails the interactions across its boundary directly', async () => {
  const r = await lift(['--cut', 'shop-leaf']);
  const m = mode(r, 'fm-inventory-slow');
  assert.deepEqual(hit(m), ['orders-reserve-stock']);
  assert.equal(m.effects[0].via, 'direct');
  assert.equal(m.failure, 'delayed');
});

// Lifting at the subsystem and the service cuts names the same interactions; an ad hoc cut agrees with the declared one.
// @evidence fault-lifting-through-realisation
test('lifting with a cut gives the failures of the derived interactions and the internal failures of a block', async () => {
  const fine = await lift(['--cut', 'shop-leaf']);
  assert.deepEqual(fine.lifted.map((/** @type {any} */ l) => l.key), ['cart->orders:invokes', 'orders->inventory:invokes']);
  const coarse = await lift(['--cut', 'shop-l1']);
  // cart -> orders crosses from storefront to fulfilment; orders -> inventory is inside fulfilment.
  assert.deepEqual(coarse.lifted.map((/** @type {any} */ l) => l.key), ['storefront->fulfilment:invokes']);
  assert.deepEqual(coarse.lifted[0].failures.map((/** @type {any} */ f) => f.mode), ['fm-app-host-b-crash', 'fm-link-a-b-partition', 'fm-zone-2-outage']);
  assert.deepEqual(coarse.internal.map((/** @type {any} */ b) => [b.block, b.failures.map((/** @type {any} */ f) => f.mode)]), [['fulfilment', ['fm-app-host-b-crash', 'fm-inventory-slow', 'fm-zone-2-outage']]]);
  // The lifted failures name the same logical interactions at every cut; the cut only groups them.
  const flat = (/** @type {any} */ x) => [...x.lifted, ...x.internal].flatMap((/** @type {any} */ g) => g.failures.flatMap((/** @type {any} */ f) => f.interactions.map((/** @type {string} */ i) => `${f.mode}:${i}`))).sort();
  assert.deepEqual(flat(coarse), flat(fine));
  // An ad hoc cut gives the same answer as the declared one.
  assert.deepEqual((await lift(['--depth', '1'])).lifted, coarse.lifted);
});

// The result is equal for a specification with its declarations reversed.
// @evidence fault-lifting-through-realisation
test('the lifting does not depend on the order the specification declares things in', async () => {
  const spec = JSON.parse(fs.readFileSync(DISTRIBUTED, 'utf8'));
  for (const k of ['failureModes', 'realisations', 'relationships', 'components']) spec[k].reverse();
  const dir = fs.mkdtempSync(path.join(fs.realpathSync(process.env.TEMP ?? '/tmp'), 'exegra-lift-'));
  try {
    const file = path.join(dir, 'distributed.jsonc');
    fs.writeFileSync(file, JSON.stringify(spec));
    const a = await lift(['--cut', 'shop-l1']);
    const b = await lift(['--cut', 'shop-l1'], file);
    assert.deepEqual(b, a);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

// Negative fixture: with the realisation maps removed the deployment faults reach no logical interaction.
// @evidence fault-lifting-through-realisation
test('without realisation maps a deployment fault does not lift to the logical interactions', async () => {
  const spec = JSON.parse(fs.readFileSync(DISTRIBUTED, 'utf8'));
  spec.realisations = [];
  const dir = fs.mkdtempSync(path.join(fs.realpathSync(process.env.TEMP ?? '/tmp'), 'exegra-lift-'));
  try {
    const file = path.join(dir, 'unrealised.jsonc');
    fs.writeFileSync(file, JSON.stringify(spec));
    const r = await lift(['--cut', 'shop-leaf'], file);
    // With nothing to say which logical interaction a link or host realises, the fault stays at its own level: it fails
    // only the network-link interactions themselves, and no logical interaction.
    const logical = ['ui-calls-cart', 'cart-places-order', 'orders-reserve-stock'];
    for (const id of ['fm-link-a-b-partition', 'fm-app-host-b-crash', 'fm-zone-2-outage']) assert.deepEqual(hit(mode(r, id)).filter((/** @type {string} */ i) => logical.includes(i)), [], id);
    assert.ok(r.modes.every((/** @type {any} */ m) => m.effects.every((/** @type {any} */ e) => e.via === 'direct')));
    // The logical-level mode still lifts: it needs no realisation.
    assert.deepEqual(hit(mode(r, 'fm-inventory-slow')), ['orders-reserve-stock']);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test('lift-faults refuses a cut that does not exist and a declared cut combined with ad hoc options', async () => {
  const missing = /** @type {any} */ (await runCommand('lift-faults', ['--spec', DISTRIBUTED, '--cut', 'no-such-cut']));
  assert.equal(missing.ok, false);
  const both = /** @type {any} */ (await runCommand('lift-faults', ['--spec', DISTRIBUTED, '--cut', 'shop-l1', '--depth', '1']));
  assert.equal(both.ok, false);
  assert.equal(both.error.code, 'usage.invalid-argument');
});
