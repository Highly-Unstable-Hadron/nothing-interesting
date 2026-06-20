import Game.Metadata
import Game.Common.GraphColouring

World "GraphTheory"

Level 5

Title "A Valid 2-Colouring"

namespace GraphTheoryGame

Introduction
"
Provide a colouring of this graph.
"

Statement :
  ∃ c, ValidColoring squareGraph c := by
  sorry
  -- use squareColoring
  -- exact squareColoring_valid

NewTactic use cases

end GraphTheoryGame
