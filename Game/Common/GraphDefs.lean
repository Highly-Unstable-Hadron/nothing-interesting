import Mathlib

namespace GraphTheoryGame

structure Edge where
  fst : Nat
  snd : Nat
  hne : fst ≠ snd
deriving DecidableEq

structure Graph where
  V : Finset Nat
  E : Finset Edge

def incident (v : Nat) (e : Edge) : Prop :=
  e.fst = v ∨ e.snd = v

instance (v : Nat) : DecidablePred (incident v) := by
  intro e
  unfold incident
  infer_instance

def degree (G : Graph) (v : Nat) : Nat :=
  (G.E.filter (fun e => incident v e)).card

def sumDegrees (G : Graph) : Nat :=
  G.V.sum (fun v => degree G v)

def edgeCount (G : Graph) : Nat :=
  G.E.card

def emptyGraph : Graph :=
{
  V := ∅,
  E := ∅
}

def addEdge (G : Graph) (e : Edge) : Graph :=
{
  V := G.V,
  E := insert e G.E
}

@[simp] theorem edgeCount_empty :
    edgeCount emptyGraph = 0 := by
  simp [edgeCount, emptyGraph]

@[simp] theorem sumDegrees_empty :
    sumDegrees emptyGraph = 0 := by
  simp [sumDegrees, emptyGraph]

end GraphTheoryGame
