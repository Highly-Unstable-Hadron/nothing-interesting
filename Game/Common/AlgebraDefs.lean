import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib
-- import Mathlib.Algebra.BigOperators.Basic

namespace AlgebraWorld

/--
Internal definition.

This will be locked after Level 2.
-/
def choose (n k : Nat) : Nat := Nat.choose n k

-- def factorial := Nat.factorial

-- axiom chooseFact (n k : Nat) : choose n k = factorial n / ((factorial k) * factorial (n - k))

/--
Sum of all entries in row `n`
of Pascal's triangle.
-/
def rowSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), choose n k

/--
Diagonal sum used in the
hockey-stick identity.
-/
def hockeySum (n k : Nat) : Nat :=
  ∑ i ∈ Finset.range (n + 1), choose i k

-- axiom factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n

axiom pascal_rule  (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1)
axiom choose_00 : choose 0 0 = 1
axiom choose_10 : choose 1 0 = 1
axiom choose_11 : choose 1 1 = 1

end AlgebraWorld
