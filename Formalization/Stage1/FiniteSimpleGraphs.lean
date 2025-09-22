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

lemma graphOfEdgeFinset_edgeSet_subset {n : ℕ}
    (edges : Finset (Sym2 (Fin n))) :
    (graphOfEdgeFinset n edges).edgeSet ⊆ (edges : Set (Sym2 (Fin n))) := by
  intro e he
  classical
  have hmem :
      e ∈ (edges : Set (Sym2 (Fin n))) ∧
        e ∉ {f : Sym2 (Fin n) | f.IsDiag} := by
    simpa [graphOfEdgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff]
      using he
  exact hmem.1

lemma graphOfEdgeFinset_edgeSet_finite {n : ℕ}
    (edges : Finset (Sym2 (Fin n))) :
    ((graphOfEdgeFinset n edges).edgeSet).Finite := by
  classical
  exact (edges.finite_toSet.subset (graphOfEdgeFinset_edgeSet_subset edges))

noncomputable instance instFintypeGraphOfEdgeFinsetEdgeSet {n : ℕ}
    (edges : Finset (Sym2 (Fin n))) :
    Fintype (graphOfEdgeFinset n edges).edgeSet :=
  (graphOfEdgeFinset_edgeSet_finite edges).fintype

instance instDecidableRel_graphOfEdgeFinsetAdj {n : ℕ}
    (edges : Finset (Sym2 (Fin n))) :
    DecidableRel (graphOfEdgeFinset n edges).Adj := by
  classical
  simpa [graphOfEdgeFinset] using
    (inferInstance : DecidableRel
      (SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin n)))).Adj)

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

/-- Stage 1 helper: the explicit `Finset` of edges used by
`graphOfEdgeFinset` removes diagonal entries. -/
@[simp]
lemma edgeFinset_graphOfEdgeFinset {n : ℕ}
    (edges : Finset (Sym2 (Fin n)))
    [inst : Fintype (graphOfEdgeFinset n edges).edgeSet] :
    (graphOfEdgeFinset n edges).edgeFinset
      = edges.filter fun e => ¬ e.IsDiag := by
  classical
  haveI := inst
  ext e
  constructor
  · intro he
    have heSet : e ∈ (graphOfEdgeFinset n edges).edgeSet := by
      simpa [SimpleGraph.edgeFinset] using he
    have hePair :
        e ∈ (edges : Set (Sym2 (Fin n))) ∧
          e ∉ {f : Sym2 (Fin n) | f.IsDiag} := by
      simpa [graphOfEdgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff]
        using heSet
    have heFin : e ∈ edges := by
      simpa [Finset.mem_coe] using hePair.1
    have heNoDiag : ¬ e.IsDiag := by
      simpa [Set.mem_setOf_eq] using hePair.2
    simp [Finset.mem_filter, heFin, heNoDiag]
  · intro he
    have heData := Finset.mem_filter.mp he
    have heFin : e ∈ edges := heData.1
    have heNoDiag : ¬ e.IsDiag := heData.2
    have hePair :
        e ∈ (edges : Set (Sym2 (Fin n))) ∧
          e ∉ {f : Sym2 (Fin n) | f.IsDiag} := by
      refine ⟨?_, ?_⟩
      · simpa [Finset.mem_coe] using heFin
      · simpa [Set.mem_setOf_eq] using heNoDiag
    have heSet : e ∈ (graphOfEdgeFinset n edges).edgeSet := by
      simpa [graphOfEdgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff]
        using hePair
    simpa [SimpleGraph.edgeFinset] using heSet

@[simp]
lemma edgeCount_graphOfEdgeFinset {n : ℕ}
    (edges : Finset (Sym2 (Fin n))) :
    edgeCount (graphOfEdgeFinset n edges)
        = (edges.filter fun e => ¬ e.IsDiag).card := by
  classical
  have h := congrArg Finset.card
    (edgeFinset_graphOfEdgeFinset (n := n) (edges := edges)
      (inst := (graphOfEdgeFinset n edges).fintypeEdgeSet))
  unfold edgeCount
  exact h

/-- Stage 1 helper: when the edge list contains no diagonals, the constructor
realizes the expected edge count. -/
lemma edgeCount_graphOfEdgeFinset_of_loopless {n : ℕ}
    (edges : Finset (Sym2 (Fin n)))
    (hdiag : ∀ e ∈ edges, ¬ e.IsDiag) :
    edgeCount (graphOfEdgeFinset n edges) = edges.card := by
  classical
  have hfilter : edges.filter (fun e => ¬ e.IsDiag) = edges := by
    ext e
    by_cases hmem : e ∈ edges
    · simp [Finset.mem_filter, hmem, hdiag _ hmem]
    · simp [Finset.mem_filter, hmem]
  simpa [hfilter] using
    edgeCount_graphOfEdgeFinset (n := n) (edges := edges)

/-- Sanity check: the complete graph on three labelled vertices has three edges. -/
example : edgeCount (SimpleGraph.completeGraph (Fin 3)) = 3 := by
  classical
  have h := edgeCount_completeGraph (n := 3)
  have : Nat.choose 3 2 = 3 := by decide
  simpa [this] using h

/-- Sanity check: constructing `K₃` with one edge removed via `graphOfEdgeFinset`
records exactly two edges. -/
example :
    edgeCount
        (graphOfEdgeFinset 3
          {s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))})
        = 2 := by
  classical
  have h01 : ¬ (s((0 : Fin 3), (1 : Fin 3))).IsDiag := by decide
  have h02 : ¬ (s((0 : Fin 3), (2 : Fin 3))).IsDiag := by decide
  have hdiag : ∀ e ∈ ({s((0 : Fin 3), (1 : Fin 3)),
        s((0 : Fin 3), (2 : Fin 3))} : Finset (Sym2 (Fin 3))), ¬ e.IsDiag := by
    intro e he
    have : e = s((0 : Fin 3), (1 : Fin 3))
        ∨ e = s((0 : Fin 3), (2 : Fin 3)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using he
    cases this with
    | inl h => simpa [h] using h01
    | inr h => simpa [h] using h02
  simpa using
    edgeCount_graphOfEdgeFinset_of_loopless (n := 3)
      (edges := {s((0 : Fin 3), (1 : Fin 3)), s((0 : Fin 3), (2 : Fin 3))})
      hdiag

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

/-- Stage 1 lemma: isomorphic host graphs admit equally many labelled copies. -/
lemma countCopies_congr_right {H : SimpleGraph α}
    {G G' : SimpleGraph β} (e : G ≃g G') :
    countCopies H G = countCopies H G' := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f => e.toEmbedding.comp f
      invFun := fun f => e.symm.toEmbedding.comp f
      left_inv := ?_
      right_inv := ?_ }
  · intro f; ext v; simp
  · intro f; ext v; simp

/-- Stage 1 lemma: isomorphic pattern graphs yield the same copy count in any
ambient host. -/
lemma countCopies_congr_left {H H' : SimpleGraph α}
    {G : SimpleGraph β} (e : H ≃g H') :
    countCopies H G = countCopies H' G := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f => f.comp e.symm.toEmbedding
      invFun := fun f => f.comp e.toEmbedding
      left_inv := ?_
      right_inv := ?_ }
  · intro f; ext v; simp
  · intro f; ext v; simp

/-- Sanity check: permuting the vertices of `K₂` does not affect copy counts. -/
example :
    countCopies (SimpleGraph.completeGraph (Fin 2))
        (SimpleGraph.completeGraph (Fin 3))
      = countCopies (SimpleGraph.completeGraph (Fin 2))
        (SimpleGraph.completeGraph (Fin 3)) := by
  classical
  simpa using
    countCopies_congr_left
      (G := SimpleGraph.completeGraph (Fin 3))
      (e := SimpleGraph.Iso.completeGraph (Equiv.swap (0 : Fin 2) 1))

end CopyCounting

section DoubleCounting

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

open Classical
open scoped BigOperators
open Equiv

/--
Stage 1 bijection: embeddings of `J` into `H` correspond exactly to the
embeddings of `J` into `G` whose image lies inside the range of a fixed
embedding `f : H ↪g G`.  This realizes the counting argument behind the
double-counting identity `(\#\text{copies of `J` inside `H`}) = M_{J,H}` used
in \eqref{double_count} of the paper.
-/
noncomputable def embeddingsIntoRangeEquiv (J : SimpleGraph α)
    (H : SimpleGraph β) (G : SimpleGraph γ) (f : H ↪g G) :
    (J ↪g H)
      ≃ {ψ : J ↪g G // Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding} := by
  classical
  let toFun : (J ↪g H)
      → {ψ : J ↪g G // Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding} :=
    fun φ =>
      ⟨f.comp φ, by
        intro x hx
        rcases hx with ⟨v, rfl⟩
        exact ⟨φ v, rfl⟩⟩
  let invFun :
      {ψ : J ↪g G // Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding}
        → (J ↪g H) :=
    fun ψ =>
      let hmem : ∀ v, ∃ w, f.toEmbedding w = ψ.1.toEmbedding v := by
        intro v
        have hv : ψ.1.toEmbedding v ∈ Set.range ψ.1.toEmbedding := ⟨v, rfl⟩
        exact ψ.2 hv
      let preimage : α → β := fun v => Classical.choose (hmem v)
      have hpreimage : ∀ v, f.toEmbedding (preimage v) = ψ.1.toEmbedding v :=
        fun v => Classical.choose_spec (hmem v)
      { toEmbedding :=
          { toFun := preimage
            inj' := by
              intro u v huv
              have : f.toEmbedding (preimage u) = f.toEmbedding (preimage v) :=
                congrArg f.toEmbedding huv
              have : ψ.1.toEmbedding u = ψ.1.toEmbedding v := by
                simpa [preimage, hpreimage] using this
              exact ψ.1.injective this }
        map_rel_iff' := by
          intro u v
          have hf :=
            (f.map_adj_iff (v := preimage u) (w := preimage v)).symm
          have hψ := ψ.1.map_adj_iff (v := u) (w := v)
          have hf' :
              H.Adj (preimage u) (preimage v)
                ↔ G.Adj (f (preimage u)) (f (preimage v)) := by
            simpa [preimage] using hf
          have hpre_u : f (preimage u) = ψ.1 u := by
            simpa [preimage] using hpreimage u
          have hpre_v : f (preimage v) = ψ.1 v := by
            simpa [preimage] using hpreimage v
          have hψ' :
              G.Adj (f (preimage u)) (f (preimage v)) ↔ J.Adj u v := by
            simpa [hpre_u, hpre_v] using hψ
          exact hf'.trans hψ' }
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_ }
  · intro φ
    ext v
    -- evaluate the chosen preimage in `invFun (toFun φ)`
    have hmem : ∀ u, ∃ w, f.toEmbedding w = (toFun φ).1.toEmbedding u := by
      intro u; exact ⟨φ u, rfl⟩
    have hpreimage :
        ∀ u, f.toEmbedding (Classical.choose (hmem u))
            = (toFun φ).1.toEmbedding u :=
      fun u => Classical.choose_spec (hmem u)
    have hpreimage_eq :
        ∀ u, Classical.choose (hmem u) = φ u := by
      intro u
      apply f.injective
      simpa [toFun, SimpleGraph.Embedding.comp] using hpreimage u
    have hEval :
        (invFun (toFun φ)) v = Classical.choose (hmem v) := by
      simp [invFun, toFun]
    simpa [hEval] using hpreimage_eq v
  · intro ψ
    ext v
    have hmem : ∀ u, ∃ w, f.toEmbedding w = ψ.1.toEmbedding u := by
      intro u
      have hu : ψ.1.toEmbedding u ∈ Set.range ψ.1.toEmbedding := ⟨u, rfl⟩
      exact ψ.2 hu
    have hpreimage :
        ∀ u, f.toEmbedding (Classical.choose (hmem u)) = ψ.1.toEmbedding u :=
      fun u => Classical.choose_spec (hmem u)
    have hEval :
        (invFun ψ) v = Classical.choose (hmem v) := by
      simp [invFun]
    have := hpreimage v
    change (f.comp (invFun ψ)) v = ψ.1 v
    simp [hEval] at this
    simpa [hEval] using this

@[simp]
lemma countCopies_subtype (J : SimpleGraph α) (H : SimpleGraph β)
    (G : SimpleGraph γ) (f : H ↪g G) :
    Fintype.card
        {ψ : J ↪g G // Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding}
      = countCopies J H := by
  classical
  simpa [countCopies] using
    (Fintype.card_congr (embeddingsIntoRangeEquiv (J := J) (H := H) (G := G) f)).symm

lemma countCopies_subtype_completeGraph (J : SimpleGraph α) (H : SimpleGraph β)
    (n : ℕ) (f : H ↪g SimpleGraph.completeGraph (Fin n)) :
    Fintype.card
        {ψ : J ↪g SimpleGraph.completeGraph (Fin n) |
            Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding}
      = countCopies J H := by
  simpa using countCopies_subtype (J := J) (H := H)
      (G := SimpleGraph.completeGraph (Fin n)) f

lemma uniformProbability_double_count (J : SimpleGraph α) (H : SimpleGraph β)
    (n : ℕ) (f : H ↪g SimpleGraph.completeGraph (Fin n)) :
    ((Fintype.card
        {ψ : J ↪g SimpleGraph.completeGraph (Fin n) |
            Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding} : ℚ)
          /
        countCopies J (SimpleGraph.completeGraph (Fin n)))
      =
        (countCopies J H : ℚ)
          / countCopies J (SimpleGraph.completeGraph (Fin n)) := by
  classical
  have h := countCopies_subtype_completeGraph (J := J) (H := H) (n := n) f
  have hcast :
      (Fintype.card
          {ψ : J ↪g SimpleGraph.completeGraph (Fin n) |
              Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding} : ℚ)
        = countCopies J H := by exact_mod_cast h
  have hcast' :
      ((Fintype.card
          {ψ : J ↪g SimpleGraph.completeGraph (Fin n) |
              Set.range ψ.toEmbedding ⊆ Set.range f.toEmbedding} : ℕ) : ℚ)
        = countCopies J H := by exact_mod_cast h
  exact congrArg (fun x : ℚ => x / countCopies J (SimpleGraph.completeGraph (Fin n))) hcast'

/-- Sanity check: for `J = K₂` and `H = K₃`, exactly three of the six labelled copies of
`K₂` inside `K₃` lie in a fixed labelled copy of `K₃` inside `K₄`. -/
example :
    ((Fintype.card
          {ψ : SimpleGraph.completeGraph (Fin 2)
              ↪g SimpleGraph.completeGraph (Fin 4) |
                Set.range ψ.toEmbedding ⊆
                  Set.range
                    (SimpleGraph.Embedding.completeGraph
                      (Fin.castLEEmb (show 3 ≤ 4 by decide))).toEmbedding}
          : ℚ)
        /
        countCopies (SimpleGraph.completeGraph (Fin 2))
          (SimpleGraph.completeGraph (Fin 4)))
      =
        (countCopies (SimpleGraph.completeGraph (Fin 2))
            (SimpleGraph.completeGraph (Fin 3)) : ℚ)
          /
        countCopies (SimpleGraph.completeGraph (Fin 2))
          (SimpleGraph.completeGraph (Fin 4)) := by
  classical
  let f : SimpleGraph.completeGraph (Fin 3)
      ↪g SimpleGraph.completeGraph (Fin 4) :=
    SimpleGraph.Embedding.completeGraph (Fin.castLEEmb (show 3 ≤ 4 by decide))
  have hf :=
    uniformProbability_double_count
      (J := SimpleGraph.completeGraph (Fin 2))
      (H := SimpleGraph.completeGraph (Fin 3))
      (n := 4) f
  simpa [f] using hf


-- TODO (Stage 1): Revisit the constant-fibre argument for embeddings into a fixed
-- copy of `J` inside `K_n`.  The previous attempt relied on extending embeddings
-- to permutations of `Fin n`, but the construction used non-existent
-- `Function.Embedding` helpers.  Once the permutation extension is rebuilt,
-- restore the lemma computing the probability that a random labelled copy of `H`
-- contains a fixed copy of `J`.

end DoubleCounting

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
