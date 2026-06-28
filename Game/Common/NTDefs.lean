import Mathlib

namespace NumberTheory

abbrev gcd := Nat.gcd

def Prime (p : Nat) : Prop :=
  Nat.Prime p

def Bezout (a b : Nat) : Prop :=
  ∃ x y : Int,
    x * a + y * b = gcd a b

axiom gcd_step
  (a b : Nat) :
  gcd a b = gcd b (a % b)

axiom gcd_zero
  (a : Nat) :
  gcd a 0 = a

axiom bezout_identity
  (a b : Nat) :
  Bezout a b

axiom bezout_coprime
  (a b : Nat)
  (h : gcd a b = 1) :
  ∃ x y : Int,
    x * a + y * b = 1

axiom dvd_linearCombination
  (d a b : Nat)
  (x y : Int) :
  d ∣ a →
  d ∣ b →
  d ∣ Int.natAbs (x * a + y * b)

axiom prime_coprime
  (p a : Nat) :
  Prime p →
  ¬ p ∣ a →
  gcd p a = 1

axiom dvd_mul_left
  (a b : Nat) :
  a ∣ a * b

axiom dvd_mul_right
  (a b : Nat) :
  a ∣ b * a

axiom dvd_trans
  (a b c : Nat) :
  a ∣ b →
  b ∣ c →
  a ∣ c

end NumberTheory
