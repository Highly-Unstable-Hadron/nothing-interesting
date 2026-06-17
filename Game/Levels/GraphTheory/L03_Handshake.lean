import Game.Metadata
namespace GraphTheoryGame

World "GraphTheory"

Level 3

Title "Handshake Lemma"

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

  induction G using graph_induction_on_edges with

  | h0 =>
      simp

  | hstep G e hnotin ih =>

      rw [sumDegrees_addEdge G e hnotin]
      rw [edgeCount_addEdge G e hnotin]
      rw [ih]

      ring

end GraphTheoryGame
