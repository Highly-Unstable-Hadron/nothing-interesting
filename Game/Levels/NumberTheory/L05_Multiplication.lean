import Game.Metadata

World "Number Theory"

Level 5

Title "Congruence and Multiplication"

namespace NumberTheory

Introduction "
Congruence is compatible with multiplication too.

Suppose

- `a ≡ b [MOD m]`, and
- `c ≡ d [MOD m]`.

Since replacing a number by another with the same remainder does not change the
remainder of a product, we obtain

`a * c ≡ b * d [MOD m]`.

This proof is almost identical to the previous level. The only difference is
that instead of using `mod_add`, you will use `mod_mul`.
"

/--
```

axiom mod_mul (a b m : Nat) :
(a * b) % m =
((a % m) * (b % m)) % m

```

Reducing each factor modulo `m` before multiplying gives the same remainder
as multiplying first and reducing afterwards.

For example,

- `(17 * 9) % 5 = 3`
- `((17 % 5) * (9 % 5)) % 5 = (2 * 4) % 5 = 3`

Both computations produce the same remainder.
-/
TheoremDoc NumberTheory.mod_mul as "mod_mul" in "NumberTheory"

/--
If

`a ≡ b [MOD m]`

and

`c ≡ d [MOD m]`

then

`a * c ≡ b * d [MOD m]`.
-/
TheoremDoc NumberTheory.congr_mul as "congr_mul" in "NumberTheory"

Statement congr_mul
  (a b c d m : Nat)
  (ha : Congruent a b m)
  (hb : Congruent c d m) :
  Congruent (a * c) (b * d) m := by
    rw [Congruent] at ha hb
    rw [Congruent]
    rw [mod_mul a c m, mod_mul b d m, ha, hb]

NewTheorem NumberTheory.mod_mul

end NumberTheory
