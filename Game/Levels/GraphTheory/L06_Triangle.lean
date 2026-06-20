import Game.Metadata

World "GraphTheory"

Level 6

Title "Triangle Is Not 2-Colourable"

namespace GraphTheoryGame

Introduction
"
Prove that a triangle graph cannot be coloured using only two colours.
By triangle graph, we mean:
```
def triangleGraph : Graph :=
{ V := {0,1,2}
  E := {e01, e12, e20} }
-- e01, e12 and e20 are the edges of the graph
```
It looks like this:
```
  0
  |\
  | \
  |  \
  1---2
```

To make your life easier, the following axioms have been added:
```
-- if a vertex is not colored red, it is colored blue
axiom neq_red : col ≠ Color.red → col = Color.blue
-- and vice versa
axiom neq_blue : col ≠ Color.blue → col = Color.red
-- proofs that the edges e01, e12 and e20 are a part of the graph
axiom triangle_edge_01 : e01 ∈ triangleGraph.E
axiom triangle_edge_12 : e12 ∈ triangleGraph.E
axiom triangle_edge_20 : e20 ∈ triangleGraph.E
theorem validColoring_adjacent
  {G : Graph} {c : Nat → Color} -- implicit arguments, the graph and the color mapping
  (hc : ValidColoring G c) (e : Edge) (he : e ∈ G.E) :
  c e.fst ≠ c e.snd := by
  exact hc e he
```

## Usage
```
have he : c 0 ≠ Color.red
have he' : c 0 = Color.blue := by exact (neq_red he)
```

`validColoring_adjacent` can be used like
```
have hc : ValidColoring G c
have : c 0 ≠ c 1 := by exact (validColoring_adjacent hc e01 triangle_edge_01)
```

Now off you go!
"

Statement (c : Nat → Color) (hc : ValidColoring triangleGraph c) : False := by
    Hint "P.S. To prove `False`, use the `contradiction` tactic when you see two obviously contradictory
      hypotheses in your goal state."
    have c01 : c 0 ≠ c 1 := by exact (validColoring_adjacent hc e01 triangle_edge_01)
    have c02 : c 2 ≠ c 0 := by exact (validColoring_adjacent hc e20 triangle_edge_20)
    have c12 : c 1 ≠ c 2 := by exact (validColoring_adjacent hc e12 triangle_edge_12)
    rw [ValidColoring] at hc
    cases h : c 0 with
    | red =>
      have f1 : c 1 = Color.blue := by
        rw [h] at c01
        symm at c01
        apply neq_red at c01
        exact c01
      have f2 : c 2 = Color.blue := by
        rw [h] at c02
        apply neq_red at c02
        exact c02
      have f2' : c 2 ≠ Color.blue := by
        rw [f1] at c12
        symm at c12
        exact c12
      contradiction
    | blue =>
      have f1 : c 1 = Color.red := by
        rw [h] at c01
        symm at c01
        apply neq_blue at c01
        exact c01
      have f2 : c 2 = Color.red := by
        rw [h] at c02
        apply neq_blue at c02
        exact c02
      have f2' : c 2 ≠ Color.red := by
        rw [f1] at c12
        symm at c12
        exact c12
      contradiction
/--
```
theorem validColoring_adjacent
  {G : Graph} {c : Nat → Color} -- implicit arguments, the graph and the color mapping
  (hc : ValidColoring G c) (e : Edge) (he : e ∈ G.E) :
  c e.fst ≠ c e.snd := by
  exact hc e he
```

`validColoring_adjacent` can be used like
```
have hc : ValidColoring G c  -- G is a graph, c is a colour mapping
have : c 0 ≠ c 1 := by exact (validColoring_adjacent hc e01 triangle_edge_01)
```
-/
TheoremDoc GraphTheoryGame.validColoring_adjacent as "validColoring_adjacent" in "GraphTheory"
/--
```
-- if a vertex is not colored red, it is colored blue
axiom neq_red : col ≠ Color.red → col = Color.blue
-- and vice versa
axiom neq_blue : col ≠ Color.blue → col = Color.red
```

## Usage
```
have he : c 0 ≠ Color.red
have he' : c 0 = Color.blue := by exact (neq_red he)
```
similarly for neq_blue
-/
TheoremDoc GraphTheoryGame.neq_blue as "neq_blue" in "GraphTheory"
/--
```
-- if a vertex is not colored red, it is colored blue
axiom neq_red : col ≠ Color.red → col = Color.blue
-- and vice versa
axiom neq_blue : col ≠ Color.blue → col = Color.red
```

## Usage
```
have he : c 0 ≠ Color.red
have he' : c 0 = Color.blue := by exact (neq_red he)
```
similarly for neq_blue
-/
TheoremDoc GraphTheoryGame.neq_red as "neq_red" in "GraphTheory"
/--
```
def triangleGraph : Graph :=
{ V := {0,1,2}
  E := {e01, e12, e20} }
-- e01, e12 and e20 are the edges of the graph
```

It looks like this:
```
  0
  |\
  | \
  |  \
  1---2
```
-/
DefinitionDoc Game.Common.GraphColouring.triangleGraph as "triangleGraph"
/--
Proofs that the edges e01, e12 and e20 are a part of the graph
```
axiom triangle_edge_01 : e01 ∈ triangleGraph.E
axiom triangle_edge_12 : e12 ∈ triangleGraph.E
axiom triangle_edge_20 : e20 ∈ triangleGraph.E
```
-/
DefinitionDoc Game.Common.GraphColouring.triangle_edge_01 as "triangle_edge_01"
/--
Proofs that the edges e01, e12 and e20 are a part of the graph
```
axiom triangle_edge_01 : e01 ∈ triangleGraph.E
axiom triangle_edge_12 : e12 ∈ triangleGraph.E
axiom triangle_edge_20 : e20 ∈ triangleGraph.E
```
-/
DefinitionDoc Game.Common.GraphColouring.triangle_edge_12 as "triangle_edge_12"
/--
Proofs that the edges e01, e12 and e20 are a part of the graph
```
axiom triangle_edge_01 : e01 ∈ triangleGraph.E
axiom triangle_edge_12 : e12 ∈ triangleGraph.E
axiom triangle_edge_20 : e20 ∈ triangleGraph.E
```
-/
DefinitionDoc Game.Common.GraphColouring.triangle_edge_20 as "triangle_edge_20"

NewTactic contradiction symm
NewTheorem GraphTheoryGame.validColoring_adjacent GraphTheoryGame.neq_blue GraphTheoryGame.neq_red
NewDefinition Game.Common.GraphColouring.triangleGraph Game.Common.GraphColouring.triangle_edge_01
  Game.Common.GraphColouring.triangle_edge_12 Game.Common.GraphColouring.triangle_edge_20

Conclusion "Awesome!!"

end GraphTheoryGame
