import Game.Metadata

World "GraphTheory"

Level 5

Title "A Valid 2-Colouring"

namespace GraphTheoryGame

Introduction
"
Provide a colouring of this graph.
"

Statement : ∃ c, ValidColoring squareGraph c := by
  Hint "Use `let` to define a function that maps every node to a colour.  Did you know that `simp`
   can be given arguments?"
  let cc (n: Nat) : Color := if n = 0 ∨ n = 2 then Color.red else Color.blue
  use cc
  rw [ValidColoring]
  intro e he
  cases square_edges e he with
  | inl h =>
      simp [cc, e01, h]
  | inr h =>
      cases h with
      | inl h' =>
          simp [cc, e12, h']
      | inr h' =>
          cases h' with
          | inl h'' =>
              simp [cc, e23, h'']
          | inr h'' =>
              simp [cc, e30, h'']
/--
It's a list of all the edges in the following graph:
```
  0 -- 1
  |    |
  3 -- 2
```
Use `cases square_edges e he` multiple times to prove that a property `P` holds on each of the edges.
-/
TheoremDoc GraphTheoryGame.square_edges as "square_edges" in "GraphTheory"
/--
```
theorem color_self_eq (c : Nat → Color) (v : Nat) :
  c v = c v :=
  rfl
```

Proves reflexivity on `c v`/`Color`.
-/
TheoremDoc GraphTheoryGame.color_self_eq as "color_self_eq" in "GraphTheory"
/--
```
def ValidColoring
  (G : Graph)
  (c : Nat → Color) : Prop :=
  ∀ e ∈ G.E, c e.fst ≠ c e.snd
```
A valid colouring of a graph `G` is one where each node is assigned some colour such that no two
adjacent nodes have the same colour. Use `rw [ValidColoring]` to expand its definition in your proofs.
-/
DefinitionDoc Game.Common.GraphColouring.ValidColoring as "ValidColoring"
/--
A hard-coded square graph with 4 vertices:
```
  0 -- 1
  |    |
  3 -- 2
```
```
def squareGraph : Graph :=
{ V := {0,1,2,3} --vertices
  E := {e01, e12, e23, e30} } --edges
```
-/
DefinitionDoc Game.Common.GraphColouring.squareGraph as "squareGraph"
/--
```
inductive Color where
| red
| blue
```
The possible colours a node could be assigned. `Color` here models a bipartite graph, i.e. a graph
where each node can receive one of 2 possible colours. There are additional constraints on bipartite graphs
modelled in `ValidColoring`. To reference the possible colours, use `Color.red` or `Color.blue`.
-/
DefinitionDoc Game.Common.GraphColouring.Color as "Color"

DefinitionDoc Or.inl as "inl"

DefinitionDoc Or.inr as "inr"

NewTactic cases «let»
NewDefinition Game.Common.GraphColouring.ValidColoring Game.Common.GraphColouring.squareGraph
  Game.Common.GraphColouring.Color Or.inl Or.inr
NewTheorem GraphTheoryGame.square_edges GraphTheoryGame.color_self_eq

Conclusion "Nicee!!  Time for something harder"

end GraphTheoryGame
