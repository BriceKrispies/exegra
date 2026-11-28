import { evaluateRuns, rat, parseRational } from '../../../../src/core/metric-stats.js';
import { metricVerdict } from '../../../../src/core/metric-claims.js';
// The claim status is decided in Lean since WG-5684 (metric-stats.js no longer has claimStatus).
const claimStatus = (scenarios) => ({ status: metricVerdict({ scenarios, negatives: [], controlNegatives: [] }).label });
// 100 runs of a closed-workload class: 60 normal runs pass (p99 = 20 ms <= 30 ms),
// 40 runs collapse: the client population stalls, only 12 requests are measured, p99 = +inf.
const runs = [];
for (let i = 0; i < 60; i++) runs.push({ seed: 'g'+i, value: rat(20000n), samples: 5000, underpowered: false });
for (let i = 0; i < 40; i++) runs.push({ seed: 'c'+i, value: 'inf', samples: 12, underpowered: true, infinite: 12 });
const spec = (open) => ({ op: '<=', bound: rat(30000n), fraction: parseRational('0.95'), confidence: parseRational('0.95'), openStarted: open });
const asEvaluated = evaluateRuns(runs, spec(true));   // what claims.js -> metric-claims.js does (openStarted defaults true)
const asSpecified = evaluateRuns(runs, spec(false));  // what docs say for a closed class
console.log('as evaluated:', asEvaluated.verdict, 'kept', asEvaluated.kept, 'leftOut', asEvaluated.leftOut, 'passes', asEvaluated.passes, claimStatus([asEvaluated]).status);
console.log('as specified:', asSpecified.verdict, 'kept', asSpecified.kept, 'passes', asSpecified.passes, claimStatus([asSpecified]).status);
