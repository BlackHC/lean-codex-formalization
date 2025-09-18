import Mathlib

/-!
### Stage 1 — Graph-theoretic foundations

This module develops the initial deterministic graph lemmas requested in
Stage 1 of the project plan.  We work with labelled simple graphs on `Fin n`
and provide convenient constructors together with basic edge-count identities.
Each statement is accompanied by sanity checks on small examples to ensure the
Lean formalization matches the intended combinatorial quantities.
-/

namespace Codex

open SimpleGraph

/-- Stage 1 helper: build a labelled simple graph on `Fin n` from a finite list of
unordered edges.  The constructor is defined via `SimpleGraph.fromEdgeSet`, so
loops are discarded automatically. -/
def graphOfEdgeFinset (n : ℕ) (edges : Finset (Sym2 (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin n)))

@[simp]
lemma graphOfEdgeFinset_adj {n : ℕ} {edges : Finset (Sym2 (Fin n))} {u v : Fin n} :
    (graphOfEdgeFinset n edges).Adj u v ↔ s(u, v) ∈ edges ∧ u ≠ v := by
  classical
  simp [graphOfEdgeFinset, SimpleGraph.fromEdgeSet_adj]

section EdgeCount

variable {V : Type*} [Fintype V]

/-- Stage 1 definition: the number of edges in a finite simple graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

@[simp]
lemma edgeCount_bot [DecidableRel ((⊥ : SimpleGraph V).Adj)] :
    edgeCount (⊥ : SimpleGraph V) = 0 := by
  classical
  simp [edgeCount]

lemma edgeCount_le_of_subgraph {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) :
    edgeCount G ≤ edgeCount H := by
  classical
  simpa [edgeCount] using Finset.card_le_card (edgeFinset_mono h)

lemma edgeCount_completeGraph (n : ℕ) :
    edgeCount (SimpleGraph.completeGraph (Fin n)) = Nat.choose n 2 := by
  classical
  have htop := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
  have : edgeCount (⊤ : SimpleGraph (Fin n)) = (Fintype.card (Fin n)).choose 2 := by
    simpa [edgeCount] using htop
  simpa [SimpleGraph.completeGraph, Fintype.card_fin] using this

end EdgeCount

/-- Sanity check: the complete graph on three labelled vertices has three edges. -/
example : edgeCount (SimpleGraph.completeGraph (Fin 3)) = 3 := by
  classical
  have h := edgeCount_completeGraph (n := 3)
  have : Nat.choose 3 2 = 3 := by decide
  simpa [this] using h

end Codex
