import Game.Metadata

World "NumberTheory"

Level 2

Title "Symmetry"

namespace NumberTheory

Introduction "
Congruence behaves very much like ordinary equality.

One important property of equality is **symmetry**:

if `a = b`, then `b = a`.

Congruence satisfies the same property.
Since `Congruent` is defined using equality of remainders, this proof is just an exercise in rewriting.
"


/--
Congruence is symmetric:

if `a ≡ b [MOD m]`, then `b ≡ a [MOD m]`.
-/
TheoremDoc NumberTheory.congr_symmetric as "congr_symmetric" in "NumberTheory"

Statement congr_symmetric
  (a b m : Nat)
  (h : Congruent a b m) :
  Congruent b a m := by
    rw [Congruent]
    rw [Congruent] at h
    rw [h]

NewDefinition Game.Common.NTDefs.Congruent

end NumberTheory
