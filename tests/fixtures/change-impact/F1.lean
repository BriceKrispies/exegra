-- The theorem of claim c4 of the change-impact fixture. It is not part of the Lean library: the fixture's
-- recorded theorem check (results.json) names this file as the one defining the theorem and its constant.
namespace ChangeImpact

def f1 (n : Nat) : Nat := n + 1

theorem f1_thm (n : Nat) : f1 n > n := Nat.lt_succ_self n

end ChangeImpact
