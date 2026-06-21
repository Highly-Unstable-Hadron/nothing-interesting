import Game.Metadata
import Game.Common.AlgebraDefs
-- import Game.Common.AlgebraLemmas

World "Algebra"

Level 3

Title "A Row of Powers"

namespace AlgebraWorld

Introduction
"
Add all entries in a row of Pascal's triangle.

The answer is unexpectedly simple.
"

/--
`rowSum n` is the sum of all entries
in row `n` of Pascal's triangle.

```
rowSum n =
Σ choose n k
```
-/
DefinitionDoc Game.Common.AlgebraDefs.rowSum as "rowSum"

/--
.
-/
Statement rowSumClosedForm (n : Nat) : rowSum n = 2 ^ n := by

  induction n with
  | zero =>
      sorry

  | succ n ih =>
      sorry

-- NewTactic induction
NewDefinition Game.Common.AlgebraDefs.rowSum
-- NewTheorem AlgebraWorld.choose_00 AlgebraWorld.choose_10 AlgebraWorld.choose_11

end AlgebraWorld
