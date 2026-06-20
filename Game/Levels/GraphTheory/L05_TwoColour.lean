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
  have c' (n : Nat) : Color := if n == 0 ∨ n == 2 then Color.red else Color.blue
  use c'
  sorry
  -- use squareColoring
  -- exact squareColoring_valid

NewTactic cases

end GraphTheoryGame
