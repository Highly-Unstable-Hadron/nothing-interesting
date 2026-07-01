import Game.Metadata

World "Algebra"

Level 2

Title "Choose n n = 1"

namespace Algebra

/--
Choose n 0 = 1 for all n.
```
axiom choose_n0 : choose n 0 = 1
```
-/
TheoremDoc Algebra.choose_n0 as "choose_n0" in "Algebra"
/--
Choose n 1 = n for all n if n ≠ 0.
```
axiom choose_n1 (h : n ≠ 0) : choose n 1 = n
```
-/
TheoremDoc Algebra.choose_n1 as "choose_n1" in "Algebra"
/--
If k > n, choose n k = 0.
```
axiom choose_k_gt_n (h : k > n) : choose n k = 0
```
-/
TheoremDoc Algebra.choose_k_gt_n as "choose_k_gt_n" in "Algebra"

NewTactic «have» induction linarith
NewTheorem Algebra.choose_n0 Algebra.choose_n1 Algebra.choose_k_gt_n

Introduction "
Prove that choose n n = 1 for all n.
Use the `induction` tactic.
If you need to solve any trivial inequalities, like, say `0 < 1` or `k - 1 < k`, use the `linarith` tactic.
"

/--
`choose n n = 1` for all `n`
-/
TheoremDoc Algebra.choose_nn as "choose_nn" in "Algebra"

Statement choose_nn (n : Nat) : choose n n = 1 := by
  induction n with
  | zero =>
    apply choose_n0
  | succ n a =>
    rw [pascal_rule, a]
    simp
    have h : n + 1 > n := by
      linarith
    rw [choose_k_gt_n h]


end Algebra
