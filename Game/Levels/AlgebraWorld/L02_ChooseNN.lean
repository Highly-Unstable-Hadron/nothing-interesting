import Game.Metadata

World "Algebra"

Level 2

Title "Choose n n = 1"

namespace Algebra

/--
_credits: github.com/leanprover-community/NNG4_
# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.  Use `have` for hypothesis/propositions and `let` for explicit objects/functions.


## Example

The simplest usage is like this. If you have `a` in your context and you execute

`have ha : a = 0`

then you will get a new goal `a = 0` to prove, and after you've proved
it you will have a new hypothesis `ha : a = 0` in your original goal.

## Example

If you already have a proof of what you want to `have`, you
can just create it immediately. For example, if you have `a` and `b`
number objects, then

`have h2 : succ a = succ b → a = b := succ_inj a b`

will directly add a new hypothesis `h2 : succ a = succ b → a = b`
to the context, because you just supplied the proof of it (`succ_inj a b`).

## Example

If you have a proof to hand, then you don't even need to state what you
are proving. For example

`have h2 := succ_inj a b`

will add `h2 : succ a = succ b → a = b` as a hypothesis.
-/
TacticDoc «have»

/--
`induction` proves a statement for every natural
number by proving:

* a base case
* an inductive step

Example:

```
induction n with
| zero =>
simp
| succ n ih =>
simp [ih]
```
-/
TacticDoc induction
/--
Solves any trivial inequalities.
-/
TacticDoc linarith
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
