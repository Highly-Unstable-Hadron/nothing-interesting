import Mathlib

namespace NumberTheory

open Nat

/-- Congruence modulo `m`. -/
@[simp]
def Congruent (a b m : Nat) : Prop :=
  a % m = b % m

axiom mod_one {a : Nat} : a % 1 = 0
axiom mod_zero {a : Nat} : a % 0 = a
axiom zero_mod {m : Nat} : 0 % m = 0
axiom one_mod_x {a : Nat} : 1 % (a + 1) = 1

axiom pow_succ (a : Nat) : a ^ (n + 1) = a ^ n * a

axiom mod_mod (a m : Nat) : (a % m) % m = a % m

axiom mod_add (a b m : Nat) : (a + b) % m = (a % m + b % m) % m
axiom mod_mul (a b m : Nat) : (a * b) % m = ((a % m) * (b % m)) % m

-- levels
-- theorem congr_reflexive
--   (a m : Nat) :
--   Congruent a a m := by
--   rw [Congruent]

-- theorem congr_symmetric
--   (a b m : Nat)
--   (h : Congruent a b m) :
--   Congruent b a m := by
--   rw [Congruent]
--   rw [Congruent] at h
--   rw [h]

-- theorem congr_transitive
--   (a b c m : Nat)
--   (h1 : Congruent a b m)
--   (h2 : Congruent b c m) :
--   Congruent a c m := by
--   rw [Congruent] at h1 h2
--   rw [h2] at h1
--   rw [Congruent, h1]

-- theorem congr_add
--   (a b c d m : Nat)
--   (ha : Congruent a b m)
--   (hb : Congruent c d m) :
--   Congruent (a + c) (b + d) m := by
--   rw [Congruent] at ha hb
--   rw [Congruent, mod_add a c m, mod_add b d m, ha, hb]

-- theorem congr_mul
--   (a b c d m : Nat)
--   (ha : Congruent a b m)
--   (hb : Congruent c d m) :
--   Congruent (a * c) (b * d) m := by
--   rw [Congruent] at ha hb
--   rw [Congruent]
--   rw [mod_mul a c m, mod_mul b d m, ha, hb]

-- theorem congr_pow
--   (a b m : Nat)
--   (n : Nat)
--   (h : Congruent a b m) :
--   Congruent (a ^ n) (b ^ n) m := by
--   rw [Congruent] at h
--   rw [Congruent]
--   induction n with
--    | zero =>
--       simp
--    | succ n ih =>
--       rw [pow_succ a, pow_succ b, mod_mul (a^n), mod_mul (b^n), ih, h]

end NumberTheory
