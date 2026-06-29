import Game.Metadata

World "Number Theory"

Level 1

Title "Congruence Modulo m"

namespace NumberTheory

Introduction "
In modular arithmetic, two natural numbers are said to be **congruent modulo m** if they have the
same remainder when divided by `m`.

For example,

- `17 ≡ 5 [MOD 4]`, because both leave remainder `1`.
- `13 ≡ 1 [MOD 6]`, because both leave remainder `1`.

In this world, congruence is represented by the predicate `Congruent`.

Your first task is simply to prove that every number is congruent to itself.
"

/--
```
@[simp]
def Congruent (a b m : Nat) : Prop :=
  a % m = b % m
```

Two natural numbers are **congruent modulo** `m` if they have the same remainder when divided by `m`.

You can unfold this definition either with

```
rw [Congruent]
```

or simply

```
simp
```
since the definition is marked with `@[simp]`.
-/
DefinitionDoc Game.Common.NTDefs.Congruent as "Congruent" in "Number Theory"

/--
Reflexivity of congruence.
Every natural number is congruent to itself modulo every modulus.
-/
TheoremDoc NumberTheory.congr_reflexive as "congr_reflexive" in "Number Theory"

Statement congr_reflexive
(a m : Nat) :
Congruent a a m := by
  rw [Congruent]

NewDefinition Game.Common.NTDefs.Congruent
NewTactic rw nth_rewrite change simp «repeat»

end NumberTheory
