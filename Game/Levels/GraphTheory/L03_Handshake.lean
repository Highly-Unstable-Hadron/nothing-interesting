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

/--
The sum of the degrees of the vertices is twice the number of the edges in a graph.
-/
Statement handshake_lemma
  (G : Graph) :
  sumDegrees G
    =
  2 * edgeCount G := by
  refine graph_induction_on_edges
    (P := fun G => sumDegrees G = 2 * edgeCount G)
    ?base ?step G
  -- apply graph_induction_on_edges

  · simp

  · intro G e hnotin ih

    rw [sumDegrees_addEdge G e hnotin]
    rw [edgeCount_addEdge G e hnotin]
    rw [ih]

    ring
  -- induction G using graph_induction_on_edges with

  -- | h0 =>
  --     simp

  -- | hstep G e hnotin ih =>

  --     rw [sumDegrees_addEdge G e hnotin]
  --     rw [edgeCount_addEdge G e hnotin]
  --     rw [ih]

  --     ring

NewTactic ring intro refine
NewTheorem GraphTheoryGame.handshake_lemma
NewDefinition Game.Common.GraphDefs.edgeCount Game.Common.GraphParity.edgeCount_addEdge Game.Common.GraphParity.graph_induction_on_edges

end GraphTheoryGame
