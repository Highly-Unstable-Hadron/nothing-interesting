import Game.Metadata

World "NumberTheory"

Level 2

Title "Symmetry"

namespace NumberTheory

Introduction "
Congruence behaves very much like ordinary equality.

One important property of equality is **symmetry**:

if `a = b`, then `b = a`.

Prove that congruence satisfies the same property.
"

Statement
  (a b m : Nat)
  (h : Congruent a b m) :
  Congruent b a m := by
    rw [Congruent]
    rw [Congruent] at h
    rw [h]

end NumberTheory
