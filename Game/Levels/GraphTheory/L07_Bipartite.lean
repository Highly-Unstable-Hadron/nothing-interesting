import Game.Metadata

World "GraphTheory"

Level 7

Title "Bipartite Graphs Have No Odd Cycles"

namespace GraphTheoryGame

Introduction
"
A valid 2-colouring prevents odd cycles.
"

Statement (G : Graph) : OddCycle G → ¬ Bipartite G := by
  intro hC hBip
  cases hBip with
  | intro c hc =>
      have h := oddCycle_opposite_color hc hC
      rw [hC.hsame] at h
      contradiction

/--
The proof that the starting and ending nodes of paths of odd length in a bipartite graph are of
different colours.
```
axiom oddCycle_opposite_color (hc : ValidColoring G c) (hC : OddCycle G)
  : c hC.start ≠ c hC.finish
```
-/
TheoremDoc GraphTheoryGame.oddCycle_opposite_color as "oddCycle_opposite_color" in "GraphTheory"
/--
`Bipartite G` is the proposition that a graph is two-colourable, i.e.
```
def Bipartite (G : Graph) : Prop :=
  ∃ c, ValidColoring G c
```
See the definition of `ValidColoring` and `Color` for more. Use `rw [Bipartite]` to expand this definition.
-/
DefinitionDoc Game.Common.GraphColouring.Bipartite as "Bipartite"
/--
Defines a cycle of odd-length in a graph.

```
structure OddCycle (G : Graph) where
  start : Nat
  finish : Nat
  hsame : finish = start
```
`start` is the first (arbitrarily chosen) node of the cycle, `finish` is the last node of the cycle.
`hsame` is the hypothesis that `start` and `finish` correspond to the same node, i.e. that the path
forms a cycle. That it is a cycle of odd-length is not explicitly encoded in this definition, see
theorem `oddCycle_opposite_color` for that.
-/
DefinitionDoc Game.Common.GraphColouring.OddCycle as "OddCycle"

NewDefinition Game.Common.GraphColouring.Bipartite Game.Common.GraphColouring.OddCycle
NewTheorem GraphTheoryGame.oddCycle_opposite_color

Conclusion "Time for the boss levels"

end GraphTheoryGame
