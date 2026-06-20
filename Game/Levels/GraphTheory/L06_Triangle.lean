import Game.Metadata
import Game.Common.GraphColouring

World "GraphTheory"

Level 6

Title "Triangle Is Not 2-Colourable"

namespace GraphTheoryGame

Introduction
"
A triangle cannot be coloured using only two colours.
"

Statement :
  ¬ Bipartite triangleGraph := by
  sorry
  -- intro h

  -- obtain ⟨c, hc⟩ := h

  -- exact triangle_not_colorable c hc

NewTactic contradiction

end GraphTheoryGame
