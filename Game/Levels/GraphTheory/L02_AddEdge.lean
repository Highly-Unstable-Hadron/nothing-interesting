import Game.Metadata
namespace GraphTheoryGame

World "GraphTheory"

Level 2

Title "Adding One Edge"

Introduction
"
We know what happens to the total degree sum when we add an edge.
Use the helper lemma.
"

Statement
  (G : Graph)
  (e : Edge)
  (h : e ∉ G.E) :
  sumDegrees (addEdge G e)
    =
  sumDegrees G + 2 := by

  rw [sumDegrees_addEdge G e h]

end GraphTheoryGame
