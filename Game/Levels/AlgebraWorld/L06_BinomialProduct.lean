import Game.Metadata
import Game.Levels.AlgebraWorld.L05_Vandermonde

World "Algebra"

Level 6

Title "Binomial Product"

namespace Algebra

Introduction "
Prove that
```
binomialExpansion x y m * binomialExpansion x y n
= binomialExpansion x y (m + n)
```

It's the final step to proving the binomial theorem.

Just a hint: don't try induction.  And check out your new tactics.
"

/--
Identical to `rw` in usage and syntax, except `rw` doesn't work inside summations while `simp_rw`
does.
-/
TacticDoc simp_rw
/--
```
def binomialExpansion (x y : Int) (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1),
    choose n k * x^k * y^(n-k)
```

The binomial expansion of (x + y) ^ n
-/
DefinitionDoc Game.Common.AlgebraDefs.binomialExpansion as "binomialExpansion" in "Algebra"
/--
```
axiom sum_prod_right
  (k : Nat) (a : Nat -> Int) (b : Int) :
  (∑ k ∈ Finset.range (k), a k) * b
    =
  (∑ k ∈ Finset.range (k), a k * b)
```

(Right-)Distributivity of multiplication over summation
-/
TheoremDoc Algebra.sum_prod_right as "sum_prod_right" in "Algebra"
/--
```
axiom inner_sum_prod_left
  (r s : Nat) (a : Nat -> Int) (b : Nat -> Int) :
  (∑ r' ∈ Finset.range r, b r'
      * (∑ s' ∈ Finset.range s, a s'))
    =
  (∑ r' ∈ Finset.range r,
    ∑ s' ∈ Finset.range s,
      b r' * a s')
```

∑ b * (∑ a) = ∑ ∑ (b * a)
Manipulating nested summations
-/
TheoremDoc Algebra.inner_sum_prod_left as "inner_sum_prod_left" in "Algebra"
/--
```
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
```
Reorders a nested summation by degree of `x` and `y`
-/
TheoremDoc Algebra.collect_by_degree as "collect_by_degree" in "Algebra"

Statement binomial_prod (x y : Int) (m n : Nat) :
  binomialExpansion x y m
  *
  binomialExpansion x y n
  = binomialExpansion x y (m + n) := by
  rw [binomialExpansion, binomialExpansion, binomialExpansion]
  rw [sum_prod_right, inner_sum_prod_left, collect_by_degree x y m n]
  change ∑ r ∈ Finset.range (m + n + 1), (vandermondeSum m n r) * x ^ r * y ^ (m + n - r) =
  ∑ k ∈ Finset.range (m + n + 1), ↑(choose (m + n) k) * x ^ k * y ^ (m + n - k)
  simp_rw [vandermonde]

NewTactic simp_rw
NewDefinition Game.Common.AlgebraDefs.binomialExpansion
NewTheorem Algebra.sum_prod_right Algebra.inner_sum_prod_left Algebra.collect_by_degree

end Algebra
