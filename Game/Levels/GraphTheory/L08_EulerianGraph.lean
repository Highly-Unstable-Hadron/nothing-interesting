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
  AllEvenDegrees G := by

  intro h

  exact eulerian_implies_even G h

end GraphTheoryGame
