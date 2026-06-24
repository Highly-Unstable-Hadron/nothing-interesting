import Game.Metadata
-- import Game.Common.AlgebraDefs

World "Algebra"

Level 3

Title "A Row of Powers"

namespace Algebra

Introduction
"
Add all entries in a row of Pascal's triangle.  It sums to 2^n.  Apparently.
Prove it by induction.
"

/--
`rowSum n` is the sum of all entries
in row `n` of Pascal's triangle.

```
rowSum n =
Σ choose n k
```

Lean definition:
```
def rowSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), choose n k
```
-/
DefinitionDoc Game.Common.AlgebraDefs.rowSum as "rowSum" in "Algebra"
/--
```
axiom rowSum_step : rowSum (n+1)
    =
  rowSum n * 2
```
Sum of the (n + 1)-th row = 2 * (sum of the n-th row)
-/
TheoremDoc Algebra.rowSum_step as "rowSum_step" in "Algebra"

/--
Sum of the elements of the n-th row of the Pascal's triangle = 2^n
-/
Statement rowSumClosedForm (n : Nat) : rowSum n = 2 ^ n := by
induction n with
  | zero =>
      change 1 = 1
      rfl
  | succ n ih =>
      rw [rowSum_step, ih]
      change 2 ^ (n + 1) = 2 ^ (n + 1)
      rfl


NewTactic rfl change
NewDefinition Game.Common.AlgebraDefs.rowSum
NewTheorem Algebra.rowSum_step

end Algebra
