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
  Hint "Use the `handshake_lemma` you proved last level"
  have evensum : Even (sumDegrees G) := by
    rw [Even]
    use (edgeCount G)
    rw [handshake_lemma]
    ring_nf
  have f1 := even_sum_even_odds (DegreeContributions G) evensum
  rw [oddDegreeCount, OddDegreeContributions]
  exact f1

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
NewTactic «have» use
/--
`Even a` is literally `∃ k, k + k = a` (there exists some natural number `x` such that `x + x = a`).

Use `rw [Even]` to expand it to this definition.
-/
DefinitionDoc Mathlib.Algebra.Group.Even as "Even"
/--
`Odd a` is literally `∃ k, 2*k + 1 = a` (there exists some natural number `k` such that `2*k + 1 = a`).

Use `rw [Odd]` to expand it to this definition.
-/
DefinitionDoc Mathlib.Algebra.Group.Odd as "Odd"
/--
```
-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
def OddDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Odd x)
-- number of nodes with odd degree
def oddDegreeCount (G : Graph) : Nat := (OddDegreeContributions G).card
```
`oddDegreeCount G` gives you the number of vertices in the graph with odd degree.
-/
DefinitionDoc Game.Common.GraphParity.oddDegreeCount as "oddDegreeCount"
/--
```
-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
def EvenDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Even x)
-- number of nodes with even degree
def evenDegreeCount (G : Graph) : Nat := (EvenDegreeContributions G).card
```
`evenDegreeCount G` gives you the number of vertices in the graph with even degree.
-/
DefinitionDoc Game.Common.GraphParity.evenDegreeCount as "evenDegreeCount"
/--
```
-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
def EvenDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Even x)
```
`EvenDegreeContributions G` returns a multiset (a set with possibly repeated elements) containing
the degrees of the vertices in the graph `G` whose degree is even, i.e. `{ ∀ v ∈ G.V, (degree v) if Even (degree v) }`
-/
DefinitionDoc Game.Common.GraphParity.EvenDegreeContributions as "EvenDegreeContributions"
/--
```
-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
def OddDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Odd x)
```
`OddDegreeContributions G` returns a multiset (a set with possibly repeated elements) containing
the degrees of the vertices in the graph `G` whose degree is odd, i.e. `{ ∀ v ∈ G.V, (degree v) if Odd (degree v) }`
-/
DefinitionDoc Game.Common.GraphParity.OddDegreeContributions as "OddDegreeContributions"
/--
```
-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
```
`DegreeContributions G` returns a multiset (a set with possibly repeated elements) containing
the degrees of each vertex of the graph `G`, i.e. `{ ∀ v ∈ G.V, degree v }`
-/
DefinitionDoc Game.Common.GraphParity.DegreeContributions as "DegreeContributions"
/--
```
-- if the sum of a sequence of numbers is even, the number of odd numbers in the sequence must be even
axiom even_sum_even_odds (A : Multiset Nat) (hA : Even (A.sum)) : Even (A.filter (fun a => Odd a)).card
```
`even_sum_even_odds A hA` is the proof that the total number of odd numbers in `A` must be even if
`∑ (a ∈ A)` is even.  The hypothesis that the sum of the elements of `A` is even is `hA`.
-/
TheoremDoc GraphTheoryGame.even_sum_even_odds as "even_sum_even_odds" in "GraphTheory"
/--
The sum of the degrees of the vertices is twice the number of the edges in a graph.
`theorem handshake_lemma (G : Graph) : sumDegrees G = 2 * edgeCount G`
-/
TheoremDoc GraphTheoryGame.handshake_lemma as "handshake_lemma" in "GraphTheory"

NewDefinition Mathlib.Algebra.Group.Even Mathlib.Algebra.Group.Odd Game.Common.GraphParity.oddDegreeCount Game.Common.GraphParity.evenDegreeCount
  Game.Common.GraphParity.OddDegreeContributions Game.Common.GraphParity.EvenDegreeContributions Game.Common.GraphParity.DegreeContributions
NewTheorem GraphTheoryGame.even_sum_even_odds GraphTheoryGame.handshake_lemma


end GraphTheoryGame
