import Game.Metadata

World "Number Theory"

Level 6

Title "Congruence and Powers"

namespace NumberTheory

Introduction "
We have seen that congruence is preserved by both addition and multiplication.

What about powers?

If

`a ≡ b [MOD m]`,

is it also true that

`aⁿ ≡ bⁿ [MOD m]`?

It is! The proof uses mathematical induction on the exponent `n`.

The base case is immediate since every number raised to the power `0` is `1`.
For the inductive step, rewrite both powers using `pow_succ`, then apply
the multiplication theorem from the previous level.
"

/--
```

axiom pow_succ (a : Nat) :
a ^ (n + 1) = a ^ n * a

```

Rewrites a power with exponent `n + 1` as a product.

For example,

```

x^5 = x^4 * x

```

This theorem is especially useful when proving statements about powers by
induction.
-/
TheoremDoc NumberTheory.pow_succ as "pow_succ" in "NumberTheory"

/--
If

`a ≡ b [MOD m]`,

then

`aⁿ ≡ bⁿ [MOD m]`

for every natural number `n`.
-/
TheoremDoc NumberTheory.congr_pow as "congr_pow" in "NumberTheory"

Statement congr_pow
  (a b m : Nat)
  (n : Nat)
  (h : Congruent a b m) :
  Congruent (a ^ n) (b ^ n) m := by
    rw [Congruent] at h
    rw [Congruent]
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ a, pow_succ b]
        rw [mod_mul (a ^ n) a m, mod_mul (b ^ n) b m]
        rw [ih, h]

NewTheorem NumberTheory.pow_succ NumberTheory.congr_pow
NewTactic induction

end NumberTheory
