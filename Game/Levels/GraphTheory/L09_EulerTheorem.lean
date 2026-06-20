import Game.Metadata
import Game.Common.GraphEuler

World "GraphTheory"

Level 9

Title "Euler's Theorem"

namespace GraphTheoryGame

Introduction
"
A graph is Eulerian exactly when every vertex has even degree.
"

Statement
  (G : Graph) :
  Eulerian G ↔ AllEvenDegrees G := by

  constructor

  · exact eulerian_implies_even G

  · exact even_implies_eulerian G

end GraphTheoryGame
