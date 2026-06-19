import Game.Metadata

World "GraphTheory"

Level 2

Title "Adding One Edge"

namespace GraphTheoryGame
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

Conclusion ":)"

NewTactic rw
NewDefinition Game.Common.GraphDefs.sumDegrees Game.Common.GraphDefs.Graph Game.Common.GraphDefs.Edge Game.Common.GraphParity.sumDegrees_addEdge

end GraphTheoryGame
