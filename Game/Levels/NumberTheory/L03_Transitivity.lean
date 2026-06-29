import Game.Metadata

World "Number Theory"

Level 3

Title "Transitivity"

namespace NumberTheory

Introduction "
The final basic property of congruence is **transitivity**.

Suppose

- `a ≡ b [MOD m]`, and
- `b ≡ c [MOD m]`.

Since all three numbers have the same remainder when divided by `m`,
it follows that

`a ≡ c [MOD m]`.

This proof requires rewriting with two hypotheses.
"


/--
Congruence is transitive:

if `a ≡ b [MOD m]` and `b ≡ c [MOD m]`,
then `a ≡ c [MOD m]`.
-/
TheoremDoc NumberTheory.congr_transitive as "congr_transitive" in "NumberTheory"

Statement congr_transitive
  (a b c m : Nat)
  (h1 : Congruent a b m)
  (h2 : Congruent b c m) :
  Congruent a c m := by
    rw [Congruent] at h1 h2
    rw [h2] at h1
    rw [Congruent, h1]

end NumberTheory
