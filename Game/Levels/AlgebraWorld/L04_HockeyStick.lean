import Game.Metadata
import Game.Common.AlgebraDefs

World "Algebra"

Level 4

Title "Hockey Stick Theorem"

namespace Algebra

Intro "Prove .."

Statement hockey_step (n k : Nat) :
  diagonalSum n (k + 1) = diagonalSum n k + choose (n + k + 1) (k + 1) := sorry

end Algebra
