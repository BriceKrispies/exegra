import Exegra.Api.Basic
import Exegra.Verdict
import Exegra.Impact

/-!
Claim verdicts at the call boundary (`src/core/verdict.js`): the shell sends each claim's structure
and its facts, and Lean decides the status (`Exegra.Verdict.status`), the word it is shown with and
whether it is shown established; regressions are decided by `Exegra.Verdict.isRegression`, change
impact by `Exegra.Impact.impacted` and theorem weakening by `Exegra.Impact.weakening`.
-/

namespace Exegra.Api.VerdictPort

def entries : List Entry := [
  { name := "claims.status",
    doc := "{claims: [{claim, facts}]} to [{strength, subject, openAssumptions, freshness, established, label, refused, theorems}]: each claim's status decided from its facts (Exegra.Verdict.status).",
    fn := Verdict.statusValue },
  { name := "verdict.isRegression",
    doc := "{pairs: [{old: status, new: status|null}]} to [bool]: whether each move is a regression (Exegra.Verdict.isRegression).",
    fn := Verdict.regressionValue },
  { name := "facts.decode",
    doc := "{facts: [fact]} to [{ok} | {error}]: whether each fact meets the schema (Exegra.Verdict.decodeFact).",
    fn := Verdict.decodeValue },
  { name := "impact.claims",
    doc := "{edges: [[from, to]], claims: [id], changed: [node]} to the ids of the claims the change re-marks (Exegra.Impact.impacted).",
    fn := Impact.impactValue },
  { name := "theorem.weakening",
    doc := "{items: [{old, new, oldAbout, newAbout}]} to [{weakened, statementChanged}]: whether each change of a lean-theorem claim's theorem weakens it (Exegra.Impact.weakening).",
    fn := Impact.weakeningValue }
]

end Exegra.Api.VerdictPort
