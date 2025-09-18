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

/-- Stage 1 definition: the number of labelled copies of `H` inside `G` is the
`Fintype` cardinality of graph embeddings from `H` to `G`. -/
noncomputable def countCopies {α β : Type*} [Fintype α] [Fintype β]
    (H : SimpleGraph α) (G : SimpleGraph β) : ℕ :=
  Fintype.card (H ↪g G)

section CopyCounting

variable {α β : Type*} [Fintype α] [Fintype β]

open Function

/-- Stage 1 lemma: embeddings between complete graphs correspond exactly to
type embeddings, so the copy count reduces to `Function.Embedding`. -/
lemma countCopies_completeGraph_eq_card :
    countCopies (SimpleGraph.completeGraph α) (SimpleGraph.completeGraph β)
      = Fintype.card (α ↪ β) := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f => f.toEmbedding
      invFun := fun f => SimpleGraph.Embedding.completeGraph f
      left_inv := ?_
      right_inv := ?_ }
  · intro f; ext v; rfl
  · intro f; ext v; rfl

/-- Stage 1 lemma: the number of labelled embeddings from a complete graph on
`α` to one on `β` is the descending factorial counting injections between the
vertex sets. -/
lemma countCopies_completeGraph_eq_descFactorial :
    countCopies (SimpleGraph.completeGraph α) (SimpleGraph.completeGraph β)
      = (Fintype.card β).descFactorial (Fintype.card α) := by
  classical
  calc
    countCopies (SimpleGraph.completeGraph α) (SimpleGraph.completeGraph β)
        = Fintype.card (α ↪ β) :=
      countCopies_completeGraph_eq_card (α := α) (β := β)
    _ = (Fintype.card β).descFactorial (Fintype.card α) :=
      (Fintype.card_embedding_eq (α := α) (β := β))

/-- Stage 1 lemma specialized to labelled graphs on `Fin`. -/
lemma countCopies_completeGraph_fin (k n : ℕ) :
    countCopies (SimpleGraph.completeGraph (Fin k))
        (SimpleGraph.completeGraph (Fin n)) = Nat.descFactorial n k := by
  classical
  calc
    countCopies (SimpleGraph.completeGraph (Fin k))
        (SimpleGraph.completeGraph (Fin n))
        = (Fintype.card (Fin n)).descFactorial (Fintype.card (Fin k)) :=
      countCopies_completeGraph_eq_descFactorial (α := Fin k) (β := Fin n)
    _ = Nat.descFactorial n k := by simp [Fintype.card_fin]

/-- Sanity check: there are six labelled embeddings of the complete graph on
two vertices into the complete graph on three vertices. -/
example :
    countCopies (SimpleGraph.completeGraph (Fin 2))
        (SimpleGraph.completeGraph (Fin 3)) = 6 := by
  classical
  simp [countCopies_completeGraph_fin]

end CopyCounting

end Codex
