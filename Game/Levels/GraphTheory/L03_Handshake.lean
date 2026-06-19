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
`theorem handshake_lemma (G : Graph) : sumDegrees G = 2 * edgeCount G`
-/
Statement handshake_lemma
  (G : Graph) :
  sumDegrees G
    =
  2 * edgeCount G := by
  refine graph_induction
    (P := fun G => sumDegrees G = 2 * edgeCount G)
    ?base ?step G
  -- apply graph_induction

  · simp

  · intro G e hnotin ih

    rw [sumDegrees_addEdge G e hnotin]
    rw [edgeCount_addEdge G e hnotin]
    rw [ih]

    ring
  -- induction G using graph_induction with

  -- | h0 =>
  --     simp

  -- | hstep G e hnotin ih =>

  --     rw [sumDegrees_addEdge G e hnotin]
  --     rw [edgeCount_addEdge G e hnotin]
  --     rw [ih]

  --     ring

/--
-/
DefinitionDoc Game.Common.GraphDefs.edgeCount as "edgeCount"
/--
-/
DefinitionDoc Game.Common.GraphParity.edgeCount_addEdge as "edgeCount_addEdge"
/--
-/
DefinitionDoc Game.Common.GraphParity.graph_induction as "graph_induction"

NewTactic ring intro refine
NewTheorem GraphTheoryGame.handshake_lemma
NewDefinition Game.Common.GraphDefs.edgeCount Game.Common.GraphParity.edgeCount_addEdge Game.Common.GraphParity.graph_induction

end GraphTheoryGame
