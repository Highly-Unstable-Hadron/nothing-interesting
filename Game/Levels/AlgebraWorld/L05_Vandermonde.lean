import Game.Metadata
-- import Game.Common.AlgebraDefs

World "Algebra"

Level 5

Title "Vandermonde's Identity"

namespace Algebra

Introduction "
Vandermonde's Identity is a fundamental combinatorial formula expressing that the sum of products of
binomial coefficients equals a single binomial coefficient. For non-negative integers m, n, and r
where r ≤ m + n, the identity is
∑ (k = 0 till k = r) (choose m k) * (choose n (r - k)) = choose (m + n) r

The `n + 1` in the statement of `vandermonde_identity` is not mathematically necessary but it makes
proving it a whole lot easier.

# induction generalizing
To prove it, you will need a new tool in your belt: `induction <x> generalizing <y> with ..`
It's an extension of the `induction` tactic that allows you to induct better on functions with multiple
arguments.

Say you need to prove `f(x, y, z) = g(x)` by induction on `x`. Your induction hypothesis will eventually
become `f(x, y, z) = g(x)` and goal state `f(x + 1, y, z) = g(x + 1)`.  However, what if, in the process of
manipulating/rewriting the function, you get a goal state of say `f(x + 1, 2 * y, √ z) = g(x + 1)`?
You can no longer substitute the induction hypothesis `f(x, y, z) = g(x)` because the variables `y` and `z`
are different.

Fear not!  You just need to change the first line from `induction x with` to
`induction x generalizing y z with`.  This changes your induction hypothesis to
`∀ (y z), f(x, y, z) = g(x)` instead of just `f(x, y, z) = g(x)`.  Now, you can still substitute this
hypothesis into your goal state by doing `rw [induction_hyp (2 * y) (√ z)]` (or whatever your induction
hypothesis is named and whatever y and z you want).

Remember, you have to give `y` and `z` as arguments in this case before you can use `rw` on it!
"

/--
```
def vandermondeSum (m n r : Nat) : Nat :=
  ∑ i ∈ Finset.range (r + 1),
    choose m i * choose n (r - i)
```

This is simply the summation

∑ (k = 0 till k = r) (choose m k) * (choose n (r - k)) = choose (m + n) r
-/
DefinitionDoc Game.Common.AlgebraDefs.vandermondeSum as "vandermondeSum" in "Algebra"
/--
```
axiom vandermonde_step
  (m n r : Nat) :
  vandermondeSum m (n + 1) (r + 1)
    =
  vandermondeSum m n r
    +
  choose (m + n) (r + 1)
```
Defines a recurrence on `vandermondeSum`.
-/
TheoremDoc Algebra.vandermonde_step as "vandermonde_step" in "Algebra"
/--
```
axiom sub_add_cancel (a b : Nat) : a - b + b = a
```
A nice helper theorem for algebraic simplification.
-/
TheoremDoc Algebra.sub_add_cancel as "sub_add_cancel" in "Misc"
/--
```
axiom add_sub_add_cancel (a b c : Nat) : a + (b - c) + c = a + b
```
Another nice but oddly specific helper theorem for algebraic simplification.
-/
TheoremDoc Algebra.add_sub_add_cancel as "add_sub_add_cancel" in "Misc"

axiom choose_nn : choose n n = 1  -- level 2
/--
Vandermonde's Identity is a fundamental combinatorial formula expressing that the sum of products of
binomial coefficients equals a single binomial coefficient. For non-negative integers m, n, and r
where r ≤ m + n, the identity is
∑ (k = 0 till k = r) (choose m k) * (choose n (r - k)) = choose (m + n) r

```
theorem vandermonde_identity (m n r : Nat) :
  vandermondeSum m (n+1) r
    =
  choose (m + n + 1) r
```
The `n + 1` is not mathematically necessary but it makes proving it a whole lot easier.
-/
Statement vandermonde_identity (m n r : Nat) :
  vandermondeSum m (n+1) r
    =
  choose (m + n + 1) r := by
  induction r generalizing n with
  | zero =>
    rw [vandermondeSum]
    change choose m 0 * choose (n+1) (0 - 0) = choose (m + n + 1) 0
    rw [choose_n0, choose_n0, choose_n0]
  | succ k hk =>
    rw [vandermonde_step, pascal_rule]
    have x := hk (n - 1)
    rw [sub_add_cancel n 1, add_sub_add_cancel] at x
    rw [x]

NewDefinition Game.Common.AlgebraDefs.vandermondeSum
NewTheorem Algebra.vandermonde_step Algebra.sub_add_cancel Algebra.add_sub_add_cancel

end Algebra
