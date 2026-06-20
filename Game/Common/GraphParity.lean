import Game.Common.GraphDefs
import Mathlib

namespace GraphTheoryGame

/--
The set of vertices of odd degree.
Used in Level 4.
-/
-- def OddDegreeVertices (G : Graph) : Finset Nat := G.V.filter (fun v => Odd (degree G v))
-- def EvenDegreeVertices (G : Graph) : Finset Nat := G.V.filter (fun v => Even (degree G v))

-- multiset of degrees of each vertex
def DegreeContributions (G : Graph) := (Multiset.map (degree G) G.V.val)
def OddDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Odd x)
def EvenDegreeContributions (G : Graph) := (DegreeContributions G).filter (fun x => Even x)

-- number of nodes with odd degree
def oddDegreeCount (G : Graph) : Nat := (OddDegreeContributions G).card
-- number of nodes with even degree
def evenDegreeCount (G : Graph) : Nat := (EvenDegreeContributions G).card

-- if the sum of a sequence of numbers is even, the number of odd numbers in the sequence must be even
axiom even_sum_even_odds (A : Multiset Nat) (hA : Even (A.sum)) : Even (A.filter (fun a => Odd a)).card

/-
  --------------------------------------------------
  Degree-change lemmas
  --------------------------------------------------
-/

/--
Adding an edge increases the degree of its left endpoint by 1.
-/
axiom degree_addEdge_left
  (G : Graph)
  (e : Edge)
  (h : e ∉ G.E) :
  degree (addEdge G e) e.fst
    =
  degree G e.fst + 1

/--
Adding an edge increases the degree of its right endpoint by 1.
-/
axiom degree_addEdge_right
  (G : Graph)
  (e : Edge)
  (h : e ∉ G.E) :
  degree (addEdge G e) e.snd
    =
  degree G e.snd + 1

/--
All other degrees remain unchanged.
-/
axiom degree_addEdge_other
  (G : Graph)
  (e : Edge)
  (v : Nat)
  (hv₁ : v ≠ e.fst)
  (hv₂ : v ≠ e.snd)
  (h : e ∉ G.E) :
  degree (addEdge G e) v
    =
  degree G v

/-
  --------------------------------------------------
  Counting lemma
  --------------------------------------------------
-/

/--
Adding one new edge increases the total degree sum by 2.
-/
axiom sumDegrees_addEdge
  (G : Graph) (e : Edge) (h : e ∉ G.E) : sumDegrees (addEdge G e)  = sumDegrees G + 2

/-
  --------------------------------------------------
  Graph induction
  --------------------------------------------------
-/

/--
Induction on the number of edges.

This is the induction principle students use
for the Handshake Lemma.
-/
axiom graph_induction
  (P : Graph → Prop)
  (G : Graph)
  (h0 : P emptyGraph)
  (hstep :
    ∀ G e,
      e ∉ G.E →
      P G →
      P (addEdge G e))
  :
  P G

-- axiom graph_induction'
--   (n : Nat)
--   (P : Graph → Prop)
--   (G : Graph)
--   (h0 : P (isolatedGraph n))
--   (hstep :
--     ∀ G e,
--       e ∉ G.E →
--       P G →
--       P (addEdge G e))
--   :
--   P G


@[simp]
axiom edgeCount_addEdge
  (G : Graph)
  (e : Edge)
  (h : e ∉ G.E) :
  edgeCount (addEdge G e)
    =
  edgeCount G + 1

theorem handshake_lemma (G : Graph) :
  sumDegrees G
    =
  2 * edgeCount G := by
  induction G using graph_induction with
  | h0 =>
      rw [sumDegrees, emptyGraph, edgeCount]
      change 0 = 2 * 0
      simp


  | hstep G e hnotin ih =>
      rw [sumDegrees_addEdge, ih]
      rw [edgeCount_addEdge]
      ring_nf
      exact hnotin
      exact hnotin

end GraphTheoryGame
