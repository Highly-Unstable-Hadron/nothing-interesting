import Game.Metadata
import Game.Common.GraphColouring

World "GraphTheory"

Level 7

Title "Bipartite Graphs Have No Odd Cycles"

namespace GraphTheoryGame

Introduction
"
A valid 2-colouring prevents odd cycles.
"

Statement
  (G : Graph) :
  Bipartite G →
  NoOddCycle G := by

  sorry
  -- intro h

  -- apply bipartite_no_odd_cycle

  -- exact h

end GraphTheoryGame
