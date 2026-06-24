import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib
-- import Mathlib.Algebra.BigOperators.Basic

namespace Algebra

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

axiom symmetry : choose n k = choose n (n - k)

axiom choose_n0 : choose n 0 = 1
axiom choose_n1 (h : n ≠ 0) : choose n 1 = n
axiom choose_k_gt_n (h : k > n) : choose n k = 0

axiom rowSum_step : rowSum (n+1) = rowSum n * 2

def diagonalSum (n k : Nat) : Nat :=
  ∑ i ∈ Finset.range (k + 1),
    choose (n + i) i

end Algebra
