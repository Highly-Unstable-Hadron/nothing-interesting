import Game.Metadata

World "Number Theory"

Level 4

Title "Congruence and Addition"

namespace NumberTheory

Introduction "
One of the most useful properties of congruence is that it behaves well with arithmetic operations.

Suppose

- `a ≡ b [MOD m]`, and
- `c ≡ d [MOD m]`.

Since `a` and `b` have the same remainder modulo `m`, and so do `c` and `d`,
adding the two congruences together should produce another congruence:

`a + c ≡ b + d [MOD m]`.

The helper theorem `mod_add` formalizes the fact that reducing each summand before adding
gives the same remainder as adding first and reducing afterwards.

This level also unlocks a few basic Lean tactics that will be useful throughout the
rest of the game.
"

/--
```
axiom mod_add (a b m : Nat) :
  (a + b) % m =
  (a % m + b % m) % m
```

Reducing two numbers modulo `m` before adding them produces the same remainder
as adding the numbers first and then reducing modulo `m`.

For example,

* `(17 + 9) % 5 = 1`
* `(17 % 5 + 9 % 5) % 5 = (2 + 4) % 5 = 1`

Both computations produce the same remainder.
-/
TheoremDoc NumberTheory.mod_add as "mod_add" in "Number Theory"

/--

-- ```
-- axiom mod_mul (a b m : Nat) :
--   (a * b) % m =
--   ((a % m) * (b % m)) % m
-- ```

-- Reducing two numbers modulo `m` before multiplying them produces the same
-- remainder as multiplying first and then reducing modulo `m`.
-- -/
-- TheoremDoc NumberTheory.mod_mul as "mod_mul" in "NumberTheory"

/--
If

`a ≡ b [MOD m]`

and

`c ≡ d [MOD m]`

then

`a + c ≡ b + d [MOD m]`.
-/
TheoremDoc NumberTheory.congr_add as "congr_add" in "NumberTheory"

Statement congr_add
(a b c d m : Nat)
(ha : Congruent a b m)
(hb : Congruent c d m) :
Congruent (a + c) (b + d) m := by
  rw [Congruent] at ha hb
  rw [Congruent]
  rw [mod_add a c m, mod_add b d m]
  rw [ha, hb]

NewTheorem NumberTheory.mod_add
NewTactic exact apply rfl «have»

end NumberTheory
