import Game.Metadata
import Game.Common.AlgebraDefs
-- import Game.Common.AlgebraLemmas

World "Algebra"

Level 2

Title "Symmetry"

namespace AlgebraWorld

Introduction
"
Pascal's triangle appears perfectly symmetric.

Explain why.
"


/--
`have` introduces an intermediate result.

Example:
```
have h : a = c := by
rw [h₁, h₂]
```

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
`choose` base cases:
```
axiom choose_00 : choose 0 0 = 1
axiom choose_10 : choose 1 0 = 1
axiom choose_11 : choose 1 1 = 1
```
-/
TheoremDoc AlgebraWorld.choose_00 as "choose_00" in "Algebra"
/--
`choose` base cases:
```
axiom choose_00 : choose 0 0 = 1
axiom choose_10 : choose 1 0 = 1
axiom choose_11 : choose 1 1 = 1
```
-/
TheoremDoc AlgebraWorld.choose_10 as "choose_10" in "Algebra"
/--
`choose` base cases:
```
axiom choose_00 : choose 0 0 = 1
axiom choose_10 : choose 1 0 = 1
axiom choose_11 : choose 1 1 = 1
```
-/
TheoremDoc AlgebraWorld.choose_11 as "choose_11" in "Algebra"


Statement symmetry
  (n k : Nat) :
  choose n k = choose n (n - k) := by
  sorry

NewTactic «have» induction
NewTheorem AlgebraWorld.choose_00 AlgebraWorld.choose_10 AlgebraWorld.choose_11


end AlgebraWorld
