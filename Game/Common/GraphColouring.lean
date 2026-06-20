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

@[simp]
def ValidColoring (G : Graph) (c : Nat → Color) : Prop :=
  ∀ e ∈ G.E, c e.fst ≠ c e.snd

/-
  Bipartite graphs
-/

def Bipartite (G : Graph) : Prop := ∃ c, ValidColoring G c

/-
  Tiny helper:
  removes one layer of unfolding without
  removing any mathematical content.
-/

theorem validColoring_adjacent
  {G : Graph} {c : Nat → Color}
  (hc : ValidColoring G c) (e : Edge) (he : e ∈ G.E) :
  c e.fst ≠ c e.snd := by
  exact hc e he

/-
  Concrete graphs for Levels 5 and 6.
-/

def e01 : Edge := ⟨0, 1, by decide⟩
def e12 : Edge := ⟨1, 2, by decide⟩
def e23 : Edge := ⟨2, 3, by decide⟩
def e30 : Edge := ⟨3, 0, by decide⟩
def e20 : Edge := ⟨2, 0, by decide⟩

/-
  0 -- 1
  |    |
  3 -- 2
-/

def squareGraph : Graph :=
{ V := {0,1,2,3}
  E := {e01, e12, e23, e30} }

@[simp]
axiom square_edges (e : Edge) (he : e ∈ squareGraph.E) :
    e = e01 ∨
    e = e12 ∨
    e = e23 ∨
    e = e30

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

axiom neq_red : col ≠ Color.red → col = Color.blue
axiom neq_blue : col ≠ Color.blue → col = Color.red
axiom triangle_edge_01 : e01 ∈ triangleGraph.E
axiom triangle_edge_12 : e12 ∈ triangleGraph.E
axiom triangle_edge_20 : e20 ∈ triangleGraph.E

end GraphTheoryGame
