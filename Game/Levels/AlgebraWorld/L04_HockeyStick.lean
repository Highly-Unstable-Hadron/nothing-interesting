import Game.Metadata
-- import Game.Common.AlgebraDefs

World "Algebra"

Level 4

Title "Hockey Stick Theorem"

namespace Algebra

Introduction "
The hockey-stick theorem is a famous mathematical rule in combinatorics. It states that the sum of
the numbers along any diagonal in Pascal's triangle, starting from any element on the outer edge,
is equal to the element just below and to the opposite side of the diagonal's end.

More formally,
∑(k = r till k = n) choose k r = choose (n + 1) (r + 1)
"

/--
```
axiom sum_extension (k : Nat) (f : Nat -> Nat) :
  ∑ i ∈ Finset.range (k + 1), f i
    = f k +
  ∑ i ∈ Finset.range k, f i
```
Given a function `f` and a number `k`, this theorem states that
the summation of `f` till `k` is equal to the summation of `f` till `k - 1` plus `f (k)`.

# Syntax Tips
You will probably have to program the function `f` that you will give to this theorem as input.
You may be familiar with Python's anonymous function syntax (`lambda x: ...`).  Lean has something
very similar.  Use `fun x => ...` to define an anonymous function that takes `x` as an input.  For
multiple arguments, use `fun a b c => ...`.

For example `fun x => x + 1` is equivalent to `lambda x : x + 1` in Python. (The arrow symbol is typed
using an equal-to sign `=` followed by `>`).

# Usage
```
sum_extension 4 (fun x => x + 1)
```
proves the following goal:
```
∑ i ∈ Finset.range 5, (i + 1)
  = (4 + 1) +
∑ i ∈ Finset.range 4, (i + 1)
```
after simplification.  Use `rw [sum_extension 4 (fun x => x + 1)]` if you want to rewrite the goal state
using this theorem.
-/
TheoremDoc Algebra.sum_extension as "sum_extension" in "Misc"
/--
```
def diagonalSum (n k : Nat) : Nat :=
  ∑ i ∈ Finset.range (k + 1),
    choose (n + i) n
```
Sum of the numbers along any diagonal in Pascal's triangle, starting from any element on the outer
edge. Used in the theorem `hockey_stick`.
-/
DefinitionDoc Game.Common.AlgebraDefs.diagonalSum as "diagonalSum" in "Algebra"

/--
The hockey-stick theorem is a famous mathematical rule in combinatorics. It states that the sum of
the numbers along any diagonal in Pascal's triangle, starting from any element on the outer edge,
is equal to the element just below and to the opposite side of the diagonal's end.

More formally,
∑(k = r till k = n) choose k r = choose (n + 1) (r + 1)

```
theorem hockey_stick
  (n k : Nat) :
  diagonalSum n k
    =
  choose (n + k + 1) (n + 1)
```
Check out `diagonalSum` for the full definition
-/
Statement hockey_stick
  (n k : Nat) :
  diagonalSum n k
    =
  choose (n + k + 1) (n + 1) := by
  rw [diagonalSum]
  induction k with
  | zero =>
    rw [choose_nn]
    change choose n n = 1
    exact choose_nn
  | succ k a =>
    rw [sum_extension (k + 1) (fun i => choose (n + i) n), a, pascal_rule (n + (k + 1)) n]
    rfl

NewTheorem Algebra.sum_extension
NewDefinition Game.Common.AlgebraDefs.diagonalSum

end Algebra
