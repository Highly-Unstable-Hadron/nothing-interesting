import Game.Metadata

-- namespace GraphTheoryGame

World "GraphTheory"

Level 1

Title "One Edge Contributes Two"

Introduction
"
An edge contributes 1 to the degree of each endpoint.

How much does it contribute in total?
"

-- TheoremDoc one_edge_contributes_two "
-- One edge contributes 2 to the sum of degrees.
-- "

Statement :
  1 + 1 = 2 := by
  simp

Conclusion "That was easy, wasn't it"

NewTactic simp exact apply

-- end GraphTheoryGame
