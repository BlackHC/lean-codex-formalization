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
open Set

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

section EdgeInduced

variable {V : Type*}

/-- Stage 1 construction: the edge-induced subgraph of `G` determined by a set of
edges keeps precisely those edges of `G` lying in the set.  All vertices remain
available because the paper's combinatorics works with labelled graphs. -/
def edgeInducedSubgraph (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u, v) ∈ E
  symm _ _ h := by
    refine And.intro h.1.symm ?_
    simpa [Sym2.eq_swap] using h.2
  loopless v h := G.loopless v h.1

noncomputable instance instDecidableRel_edgeInducedSubgraph (G : SimpleGraph V)
    (E : Set (Sym2 V)) [DecidableRel G.Adj] :
    DecidableRel (edgeInducedSubgraph G E).Adj := by
  classical
  intro u v
  change Decidable (G.Adj u v ∧ s(u, v) ∈ E)
  infer_instance

@[simp]
lemma edgeInducedSubgraph_adj {G : SimpleGraph V} {E : Set (Sym2 V)} {u v : V} :
    (edgeInducedSubgraph G E).Adj u v ↔ G.Adj u v ∧ s(u, v) ∈ E := Iff.rfl

lemma edgeInducedSubgraph_le (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeInducedSubgraph G E ≤ G := fun _ _ h => h.1

lemma edgeInducedSubgraph_mono {G : SimpleGraph V} {E E' : Set (Sym2 V)}
    (h : E ⊆ E') : edgeInducedSubgraph G E ≤ edgeInducedSubgraph G E' := by
  intro u v hv
  exact ⟨hv.1, h hv.2⟩

@[simp]
lemma edgeSet_edgeInducedSubgraph (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (edgeInducedSubgraph G E).edgeSet = G.edgeSet ∩ E := by
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  simp [edgeInducedSubgraph, Set.mem_inter_iff]

@[simp]
lemma edgeInducedSubgraph_sup (G : SimpleGraph V) (E F : Set (Sym2 V)) :
    edgeInducedSubgraph G (E ∪ F)
      = edgeInducedSubgraph G E ⊔ edgeInducedSubgraph G F := by
  ext u v
  simp [edgeInducedSubgraph, Set.mem_union, SimpleGraph.sup_adj, and_or_left]

@[simp]
lemma edgeInducedSubgraph_inf (G : SimpleGraph V) (E F : Set (Sym2 V)) :
    edgeInducedSubgraph G (E ∩ F)
      = edgeInducedSubgraph G E ⊓ edgeInducedSubgraph G F := by
  ext u v
  constructor
  · intro h
    rcases h with ⟨hadj, hmem⟩
    rcases hmem with ⟨hE, hF⟩
    exact ⟨⟨hadj, hE⟩, ⟨hadj, hF⟩⟩
  · rintro ⟨⟨hadjE, hE⟩, ⟨_, hF⟩⟩
    exact ⟨hadjE, ⟨hE, hF⟩⟩

section EdgeCount

variable [Fintype V]

@[simp]
lemma edgeCount_edgeInducedSubgraph {G : SimpleGraph V} [DecidableRel G.Adj]
    (E : Finset (Sym2 V))
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet) :
    edgeCount (edgeInducedSubgraph G (E : Set (Sym2 V))) = E.card := by
  classical
  have hEdgeSet :
      (edgeInducedSubgraph G (E : Set (Sym2 V))).edgeSet = (E : Set (Sym2 V)) := by
    simp [edgeSet_edgeInducedSubgraph, Set.inter_eq_right.mpr hE]
  have hEdgeFinset :
      (edgeInducedSubgraph G (E : Set (Sym2 V))).edgeFinset = E := by
    simp [SimpleGraph.edgeFinset, hEdgeSet]
  simp [edgeCount, hEdgeFinset]

/-- Sanity check: removing one edge from `K₃` leaves a two-edge subgraph. -/
example :
    edgeCount
        (edgeInducedSubgraph (SimpleGraph.completeGraph (Fin 3))
          (({s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))} :
              Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))
        = 2 := by
  classical
  have hsubset :
      (({s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))} :
          Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))
          ⊆ (SimpleGraph.completeGraph (Fin 3)).edgeSet := by
    intro e he
    have : e = s((0 : Fin 3), (1 : Fin 3)) ∨ e = s((0 : Fin 3), (2 : Fin 3)) := by
      simpa [Finset.mem_coe] using he
    rcases this with h | h <;> subst h <;>
      simp [SimpleGraph.completeGraph]
  have hcard :
      ({s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))} :
          Finset (Sym2 (Fin 3))).card = 2 := by decide
  simpa [hcard] using
    edgeCount_edgeInducedSubgraph
      (G := SimpleGraph.completeGraph (Fin 3))
      (E := {s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))})
      hsubset

end EdgeCount

end EdgeInduced

end Codex
