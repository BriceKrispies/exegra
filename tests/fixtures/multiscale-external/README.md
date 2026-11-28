# Multiscale external fixtures (WG-5730, WG-5735)

Full multiscale specifications of three systems that are not Exegra, kept for tests and reused by M7 (WG-5698).
They are not registered projects under `specs/`, so nothing that iterates over `specs/` (the conformance goldens
recorder, the vite plugin, the front-door tools) sees them. The command line loads each by path with the inline
project option `--spec`, which every read-only command takes:

```sh
node cli/exegra.js validate    --spec tests/fixtures/multiscale-external/compiler.jsonc
node cli/exegra.js compose-functions --spec tests/fixtures/multiscale-external/compiler.jsonc
node cli/exegra.js derive      --spec tests/fixtures/multiscale-external/distributed.jsonc --cut shop-l1
node cli/exegra.js lift-faults --spec tests/fixtures/multiscale-external/distributed.jsonc --cut shop-l1
```

In a test, `runCommand('derive', ['--spec', file, '--cut', 'shop-l1'])` from `cli/commands.js`, or
`analyzeSpec(fs.readFileSync(file, 'utf8'))` from `src/core/analyze.js`.

| File | What it is | Validates |
|---|---|---|
| `compiler.jsonc` | A compiler pipeline. Logical hierarchy: `compiler` over `frontend` (`lexer`, `parser`, `checker`) and `backend` (`optimiser`, `emitter`), plus the shared `diagnostics` sink every stage reports to. A second hierarchy `ownership` (two teams). Cuts `compiler-l0`, `compiler-l1`, `compiler-stages`. Eight `function` entities attached to elements: one per stage, and the composites `analyse`, `generate` and `compile` (`function.composition`), whose declared signatures equal the composition of their stages' (all stages share the `diagnostic` error union). | cleanly |
| `compiler-mismatch.jsonc` | The same, with `analyse` declaring that it returns `syntax-tree` while its last stage `check` returns `typed-tree`. | `function.composition-returns` at `analyse` and `function.composition-chain` at `compile` (the mismatch cascades up the hierarchy) |
| `distributed.jsonc` | A web shop. Logical hierarchy: `shop` over `storefront` (`web-ui`, `cart`), `fulfilment` (`orders`, `inventory`) and `infrastructure` (hosts and zones). Hierarchy `deployment`: zone 1 holds the edge host and app host A, zone 2 holds app host B and the database host, and each service is placed on its host. Three realisation maps from the logical `invokes` interactions to paths of `network-link` relationships. Cuts `shop-l1` (subsystems), `shop-leaf` (services). Four failure modes: a link partition, a host crash and a zone outage (deployment level) and a slow inventory (logical level). | cleanly; `lift-faults` lifts each mode to the interactions it fails |
| `event-driven.jsonc` | A telemetry platform (WG-5735). Logical hierarchy: `telemetry-platform` over `ingest` (`sensor-gateway`, `edge-filter`), `broker` (the connectors `telemetry-topic` and `alerts-topic`), `processing` (`aggregator`, `alert-rules`) and `delivery` (`notifier`, `dashboard`, `archiver`). Publishes and subscribes through the connectors contract to `notifies` naming the connector. Five behaviours pass a reading to an alert and a notification; `processing-flow` abstracts the aggregator and the rules (the events `rule-req` and `rule-res` are internal to it); the contract `rule-check` is typed by its events and `reading-feed` is not. Cuts `telemetry-l0`, `telemetry-l1`, `telemetry-leaf`. | cleanly; `coherence` holds, `boundary-contracts` reports `gateway-invokes-filter` as untyped on purpose |

The files are generated JSON (valid JSONC). Edit them as data: the compiler one is the one a test mutates to
make its negative variants (`tests/core/function-composition.test.js`); the distributed one is mutated in
`tests/core/fault-lifting.test.js`.

## Candidate decompositions (WG-5735, M7)

`compiler-candidates.json`, `distributed-candidates.json` and `event-driven-candidates.json` are candidates a person gives for each fixture, in the format `decompose --file` reads. Each fixture is run at the grain of its leaves:

```sh
node cli/exegra.js decompose --spec tests/fixtures/multiscale-external/event-driven.jsonc --scope telemetry-platform --grain leaves --file tests/fixtures/multiscale-external/event-driven-candidates.json
```

Each file has candidates that are valid, one of which the tests accept, and at least one that is not: a lexer in two blocks (compiler), the database host in no block (distributed), the gateway apart from the filter it invokes under an untyped contract, rejected by V7 (event-driven). Generated candidates add to them. `docs/assessment/2026-11-27/scripts/m7-evidence.mjs` evaluates and accepts one per fixture and writes the reports under `docs/assessment/2026-11-27/m7/`; `tests/core/decomposition-behaviour.test.js` pins what they say.
