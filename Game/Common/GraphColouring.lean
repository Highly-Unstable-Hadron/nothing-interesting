import Game.Common.GraphDefs

namespace GraphTheoryGame

/-
  Colours
-/

inductive Color where
| red
| blue
deriving DecidableEq

/-
  Adjacency
-/

def adjacent (G : Graph) (u v : Nat) : Prop :=
  ∃ e ∈ G.E,
    (e.fst = u ∧ e.snd = v) ∨
    (e.fst = v ∧ e.snd = u)

/-
  Valid colourings
-/

def ValidColoring
  (G : Graph)
  (c : Nat → Color) : Prop :=
  ∀ u v,
    adjacent G u v →
    c u ≠ c v

/-
  Bipartite graphs
-/

def Bipartite (G : Graph) : Prop :=
  ∃ c, ValidColoring G c

/-
  Tiny helper:
  removes one layer of unfolding without
  removing any mathematical content.
-/

theorem validColoring_adjacent
  {G : Graph}
  {c : Nat → Color}
  (hc : ValidColoring G c)
  {u v : Nat}
  (h : adjacent G u v) :
  c u ≠ c v := by
  exact hc u v h

/-
  Concrete graphs for Levels 5 and 6.
-/

def e01 : Edge :=
  ⟨0, 1, by decide⟩

def e12 : Edge :=
  ⟨1, 2, by decide⟩

def e23 : Edge :=
  ⟨2, 3, by decide⟩

def e30 : Edge :=
  ⟨3, 0, by decide⟩

def e20 : Edge :=
  ⟨2, 0, by decide⟩

/-
  0 -- 1
  |    |
  3 -- 2
-/

def squareGraph : Graph :=
{ V := {0,1,2,3}
  E := {e01, e12, e23, e30} }

/-
  0
  |\
  | \
  |  \
  1---2
-/

def triangleGraph : Graph :=
{ V := {0,1,2}
  E := {e01, e12, e20} }

end GraphTheoryGame
