import Game.Metadata
import Game.Common.GraphParity

World "GraphTheory"

Level 4

Title "Odd-Degree Vertices Come In Pairs"
namespace GraphTheoryGame

Introduction
"
The Handshake Lemma tells us that the sum of all degrees is even.

Use this fact to show that the number of odd-degree vertices is even.
"

Statement
  (G : Graph) :
  Even (oddDegreeCount G) := by

  sorry

/--
_credits: github.com/leanprover-community/NNG4_
# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.


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
NewTactic «have»

end GraphTheoryGame
