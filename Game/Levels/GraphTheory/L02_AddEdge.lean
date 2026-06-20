import Game.Metadata

World "GraphTheory"

Level 2

Title "Adding One Edge"

namespace GraphTheoryGame
Introduction
"
We know what happens to the total degree sum when we add an edge.
Use the helper lemma.
"

Statement
  (G : Graph)
  (e : Edge)
  (h : e ∉ G.E) :
  sumDegrees (addEdge G e)
    =
  sumDegrees G + 2 := by
  Hint "Check your unlocked theorems"
  rw [sumDegrees_addEdge G e h]

Conclusion ":)"

/--
```
def degree (G : Graph) (v : Nat) : Nat := (G.E.filter (fun e => incident v e)).card
```
`degree G v` where `G` is a graph and `v` is a vertex gives you the number of edges which have `v` as one of their endpoints.
-/
DefinitionDoc Game.Common.GraphDefs.degree as "degree"
/--
```
def sumDegrees (G : Graph) : Nat := G.V.sum (fun v => degree G v)
```
The sum of the degrees of all the vertices in the graph. See definition of `degree` for more.
-/
DefinitionDoc Game.Common.GraphDefs.sumDegrees as "sumDegrees"
/--
```
structure Graph where
  V : Finset Nat
  E : Finset Edge
```
A graph is a set of vertices V (each vertex represented as a natural number) and a set of edges E
(each edge represented by an ordered pair `(a, b)` where `a != b`. See the definition of Edge for more info)

For a graph `G`, you can access its vertex set so: `G.V`, and its edge set so: `G.E`.
-/
DefinitionDoc Game.Common.GraphDefs.Graph as "Graph"
/--
```
structure Edge where
  fst : Nat
  snd : Nat
  hne : fst ≠ snd
```
Edges are ordered pairs of natural numbers `(fst, snd)` where `fst != snd`.
`fst` indicates the vertex the edge arises out of and `snd` indicates the vertex the edge goes into.
-/
DefinitionDoc Game.Common.GraphDefs.Edge as "Edge"
/--
```
sumDegrees_addEdge (G : Graph) (e : Edge) (h : e ∉ G.E) : sumDegrees (addEdge G e)  = sumDegrees G + 2
```
Adding one new edge increases the total degree sum by 2.
-/
TheoremDoc GraphTheoryGame.sumDegrees_addEdge as "sumDegrees_addEdge" in "GraphTheory"

NewDefinition Game.Common.GraphDefs.degree Game.Common.GraphDefs.sumDegrees Game.Common.GraphDefs.Graph Game.Common.GraphDefs.Edge
NewTheorem GraphTheoryGame.sumDegrees_addEdge

end GraphTheoryGame
