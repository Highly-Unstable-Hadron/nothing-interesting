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

/--
Sum of all entries in row `n`
of Pascal's triangle.
-/
def rowSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), choose n k

axiom pascal_rule  (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1)

axiom symmetry : choose n k = choose n (n - k)

axiom choose_n0 : choose n 0 = 1
axiom choose_n1 (h : n ≠ 0) : choose n 1 = n
axiom choose_k_gt_n (h : k > n) : choose n k = 0

axiom rowSum_step : rowSum (n+1) = rowSum n * 2

/--
Hockey stick theorem
-/

def diagonalSum (n k : Nat) : Nat :=
  ∑ i ∈ Finset.range (k + 1),
    choose (n + i) n

axiom sum_extension (k : Nat) (f : Nat -> Nat) :
  ∑ i ∈ Finset.range (k + 1), f i
    = f k +
  ∑ i ∈ Finset.range k, f i

/--
Vandermonde's Identity
-/

def vandermondeSum (m n r : Nat) : Nat :=
  ∑ i ∈ Finset.range (r + 1),
    choose m i * choose n (r - i)

axiom vandermonde_step
  (m n r : Nat) :
  vandermondeSum m (n + 1) (r + 1)
    =
  vandermondeSum m n r
    +
  choose (m + n) (r + 1)

axiom sub_add_cancel (a b : Nat) : a - b + b = a
axiom add_sub_add_cancel (a b c : Nat) : a + (b - c) + c = a + b

/--
Binomial Theorem
-/

def binomialExpansion (x y : Int) (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1),
    choose n k * x^k * y^(n-k)

axiom pow_add (a : Int) (b c : Nat) : a^(b + c) = a^b * a^c
axiom binExp_one : binomialExpansion x y 1 = (x + y)^1
axiom binExp_zero : binomialExpansion x y 0 = (x + y)^0

/-- :) -/

axiom sum_prod_right (k : Nat) (a : Nat -> Int) (b : Int) : (∑ k ∈ Finset.range (k), a k) * b = (∑ k ∈ Finset.range (k), a k * b)
axiom inner_sum_prod_left (r s : Nat) (a : Nat -> Int) (b : Nat -> Int) : (∑ r' ∈ Finset.range r, b r' * (∑ s' ∈ Finset.range s, a s')) = (∑ r' ∈ Finset.range r, ∑ s' ∈ Finset.range s, b r' * a s')

axiom collect_by_degree
  (x y : Int)
  (m n : Nat) :
  (∑ i ∈ Finset.range (m+1),
      ∑ j ∈ Finset.range (n+1),
       (choose m i) * x ^ i * y ^ (m - i) * ((choose n j) * x ^ j * y ^ (n - j)))
  =
  ∑ r ∈ Finset.range (m+n+1),
      (∑ i ∈ Finset.range (r+1), choose m i * choose n (r-i))
       * x^r * y^(m+n-r)

end Algebra
