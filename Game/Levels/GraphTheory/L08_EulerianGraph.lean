import Game.Metadata
import Game.Common.GraphEuler

World "GraphTheory"

Level 8

Title "Eulerian Graphs Have Even Degrees"

namespace GraphTheoryGame

Introduction
"
In an Eulerian graph, every vertex has even degree.
"

Statement
  (G : Graph) :
  Eulerian G →
  oddDegreeCount G = 0 := by
  sorry

end GraphTheoryGame
