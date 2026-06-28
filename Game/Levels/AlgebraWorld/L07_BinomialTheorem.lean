import Game.Metadata
import Game.Levels.AlgebraWorld.L06_BinomialProduct

World "Algebra"

Level 7

Title "Binomial Theorem"

namespace Algebra

Introduction "
Let's tie it all up together. This one needs no explanation.

Prove the binomial theorem.
"
/--
```
axiom pow_add (a : Int) (b c : Nat) :
   a^(b + c) = a^b * a^c
```
a^(b + c) = a^b * a^c
Use `rw[pow_add]`
-/
TheoremDoc Algebra.pow_add as "pow_add" in "Algebra"
/--
```
axiom binExp_one :
  binomialExpansion x y 1 = (x + y)^1
```
Base cases for induction. `rw` and `change` don't work on `binomialExpansion` because of the Nat to
Int casts, so proving this statement is surprisingly hard. Which is why this has been given as an
axiom.
-/
TheoremDoc Algebra.binExp_one as "binExp_one" in "Algebra"
/--
```
axiom binExp_zero :
  binomialExpansion x y 0 = (x + y)^0
```
Base cases for induction. `rw` and `change` don't work on `binomialExpansion` because of the Nat to
Int casts, so proving this statement is surprisingly hard. Which is why this has been given as an
axiom.
-/
TheoremDoc Algebra.binExp_zero as "binExp_zero" in "Algebra"
/--
The binomial theorem.
```
theorem binomialTheorem
  (x y : Int)
  (n : Nat) :
  binomialExpansion x y n
    =
  (x + y)^n
```
See `binomialExpansion`
-/
TheoremDoc Algebra.binomialTheorem as "binomialTheorem" in "Algebra"

Statement
  binomialTheorem
  (x y : Int)
  (n : Nat) :
  binomialExpansion x y n
    =
  (x + y)^n := by
  induction n with
  | zero =>
      exact binExp_zero
  | succ n ih =>
      rw [← binomial_prod x y n 1, pow_add (x + y) n 1, ih]
      rw [binExp_one]

NewTheorem Algebra.pow_add Algebra.binExp_one Algebra.binExp_zero

Conclusion "
Congrats!  You have finished the Algebra world! :)

Interestingly, most of the previous levels could have been proven trivially using the binomial
theorem. Do you know how? "

end Algebra
