import Game.Metadata

World "GraphTheory"

Level 3

Title "Handshake Lemma"

namespace GraphTheoryGame
Introduction
"
The total degree sum equals twice the number of edges.

Prove it by induction on the number of edges.
"

Statement
  (G : Graph) :
  sumDegrees G
    =
  2 * edgeCount G := by
  induction G using graph_induction with
  | h0 =>
      rw [sumDegrees, emptyGraph, edgeCount]
      change 0 = 2 * 0
      simp


  | hstep G e hnotin ih =>
      rw [sumDegrees_addEdge, ih]
      rw [edgeCount_addEdge]
      ring_nf
      exact hnotin
      exact hnotin

/--
`edgeCount G` gives you the number of edges in graph G.
-/
DefinitionDoc Game.Common.GraphDefs.edgeCount as "edgeCount"
/--
`axiom edgeCount_addEdge (G : Graph) (e : Edge) (h : e ∉ G.E) : edgeCount (addEdge G e) = edgeCount G + 1`

`edgeCount_addEdge` is states that adding an edge to a graph increases its `edgeCount` (number of edges in the graph) by 1.
-/
TheoremDoc GraphTheoryGame.edgeCount_addEdge as "edgeCount_addEdge" in "GraphTheory"
/--
Helps you induct on graphs, one edge at a time. Use with the `induction` tactic as follows:
## Usage:
```
induction G using graph_induction
... (base case)
... (inductive step)
```
Immediately after the first line, the goal state will update to show the base case.
As soon as the base case is proven, the goal state will update to show the inductive case.
The induction assumption(s) will be usable as a named hypothesis (automatically named, visible above your goal state)
to prove the inductive case.
-/
TheoremDoc GraphTheoryGame.graph_induction as "graph_induction" in "GraphTheory"

NewTactic ring_nf intro induction
NewTheorem GraphTheoryGame.graph_induction GraphTheoryGame.edgeCount_addEdge
NewDefinition Game.Common.GraphDefs.edgeCount

end GraphTheoryGame
