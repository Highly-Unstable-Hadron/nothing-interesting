import Game.Metadata

World "GraphTheory"

Level 1

Title "One Edge Contributes Two"

namespace GraphTheoryGame

Introduction
"
An edge contributes 1 to the degree of each endpoint.

How much does it contribute in total?

`one_edge_graph` is defined as:
```
def one_edge_graph : Graph :=
{
  V := { 1, 2 },        // vertices
  E := { Edge.mk 1 2 }  // edges
}
```

It is a graph with 2 vertices (labelled 1 and 2 respectively) and a single edge between them.
"

def h : 1 ≠ 2 := by simp

@[simp]
def one_edge_graph : Graph :=
{
  V := { 1, 2 },
  E := { (Edge.mk 1 2 h) }
}

Statement : sumDegrees (one_edge_graph) = 2 := by
  Hint "Try `change`ing it to something equivalent (...wait doesn't this just say 1 + 1 = 2?)"
  -- rw [sumDegrees]
  -- change degree one_edge_graph 1 + degree one_edge_graph 2 = 2
  -- repeat rw [degree]
  change 1 + 1 = 2
  simp

Conclusion "That was easy, wasn't it"

NewTactic simp change


end GraphTheoryGame
