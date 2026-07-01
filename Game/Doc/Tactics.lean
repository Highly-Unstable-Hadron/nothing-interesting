import GameServer
import GameServer.Commands

/--
_credits: github.com/leanprover-community/NNG4_
# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.  Use `have` for hypothesis/propositions and `let` for explicit objects/functions.


## Example

The simplest usage is like this. If you have `a` in your context and you execute

`have ha : a = 0`

then you will get a new goal `a = 0` to prove, and after you've proved
it you will have a new hypothesis `ha : a = 0` in your original goal.

## Example

If you already have a proof of what you want to `have`, you
can just create it immediately. For example, if you have `a` and `b`
number objects, then

`have h2 : succ a = succ b → a = b := succ_inj a b`

will directly add a new hypothesis `h2 : succ a = succ b → a = b`
to the context, because you just supplied the proof of it (`succ_inj a b`).

## Example

If you have a proof to hand, then you don't even need to state what you
are proving. For example

`have h2 := succ_inj a b`

will add `h2 : succ a = succ b → a = b` as a hypothesis.
-/
TacticDoc «have»

/--
`induction` proves a statement for every natural
number by proving:

* a base case
* an inductive step

# Example:

```
theorem : n - 1 + 1 = n := by
  induction n with
  | zero =>
  simp
  | succ n ih =>
  simp [ih]
```

# induction generalizing
Syntax: `induction <x> generalizing <y> with ..`

It's an extension of the `induction` tactic that allows you to induct better on functions with multiple
arguments.

Say you need to prove `f(x, y, z) = g(x)` by induction on `x`. Your induction hypothesis will eventually
become `f(x, y, z) = g(x)` and goal state `f(x + 1, y, z) = g(x + 1)`.  However, what if, in the process of
manipulating/rewriting the function, you get a goal state of say `f(x + 1, 2 * y, √ z) = g(x + 1)`?
You can no longer substitute the induction hypothesis `f(x, y, z) = g(x)` because the variables `y` and `z`
are different.

Fear not!  You just need to change the first line from `induction x with` to
`induction x generalizing y z with`.  This changes your induction hypothesis to
`∀ (y z), f(x, y, z) = g(x)` instead of just `f(x, y, z) = g(x)`.

Now, you can still substitute this hypothesis into your goal state by doing
`rw [induction_hyp (2 * y) (√ z)]` (or whatever your induction hypothesis is named and whatever y
 and z you want).

Remember, you have to give `y` and `z` as arguments in this case before you can use `rw` on it!
-/
TacticDoc induction

/--
Solves any trivial inequalities, like, say `0 < 1` or `k - 1 < k`.
Just type `linarith` to use it.
-/
TacticDoc linarith

/--
Identical to `rw` in usage and syntax, except `rw` doesn't work inside summations while `simp_rw`
does.
```
simp_rw [h1, h2, ← h3]
```
-/
TacticDoc simp_rw


/--
`simp` simplifies the goal using known definitions and theorems.

Example:
```
example : 0 + n = n := by
simp
```
-/
TacticDoc simp

/--
_credits: github.com/leanprover-community/NNG4_
## Summary

If `h` is a proof of `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s.

### Variants

* `rw [← h]` (changes `Y` to `X`)
* `rw [h] at h2` (changes `X` to `Y` in hypothesis `h2` instead of the goal)
* `rw [h] at *` (changes `X` to `Y` in the goal and all hypotheses)

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw [add_zero]`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw [h]` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:

```
Objects:
  x y : ℕ
Assumptions:
  h : x = y + y
Goal:
  succ (x + 0) = succ (y + y)
```

then

`rw [add_zero]`

will change the goal into `succ x = succ (y + y)`, and then

`rw [h]`

will change the goal into `succ (y + y) = succ (y + y)`, which
can be solved with `rfl`.

### Example:

You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:

```
Objects:
  x y : ℕ
Assumptions:
  h1 : x = y + 3
  h2 : 2 * y = x
Goal:
  y = 3
```
then `rw [h1] at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
-/
TacticDoc rw
