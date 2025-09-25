import Mathlib
import Formalization.Stage1.FiniteSimpleGraphs

/-!
### Stage 2 — Random graph model

This module begins Stage 2 of the formalization plan by modelling the
binomial random graph `G(n, p)` as a product probability measure on the
indicator variables for each potential edge.  We work with the explicit
index set of non-diagonal pairs in `Sym2 (Fin n)` so that the resulting
simple graphs have no loops.  The definitions introduced here establish
the random graph as a measurable function into `SimpleGraph (Fin n)` and
record basic sanity checks on small examples.

TODO (Stage 2): extend these constructions with the expectation and
integrability lemmas described in the roadmap, notably the
`integrable_countCopies` statement from §2 of the paper.
-/

namespace Codex

open Classical
open Sym2
open scoped BigOperators MeasureTheory ProbabilityTheory
open MeasureTheory

/-- The index type for undirected edges on `Fin n` obtained by removing the
looping pairs from `Sym2 (Fin n)`.  Each element corresponds to one possible
edge in the binomial random graph. -/
def EdgePairs (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

namespace Stage2

variable {n : ℕ}

instance instFintypeEdgePairs (n : ℕ) : Fintype (EdgePairs n) := by
  classical
  refine Fintype.subtype
    (((Finset.univ : Finset (Sym2 (Fin n))).filter fun e => ¬ e.IsDiag)) ?_
  intro e
  by_cases he : e.IsDiag
  · simp [Finset.mem_filter, he]
  · simp [Finset.mem_filter, he]

/-- The Bernoulli `PMF` on `Bool` with parameter `p ∈ [0, 1]`.  We work with
nonnegative reals internally so that the associated `Measure` is a genuine
probability measure without additional bookkeeping. -/
noncomputable def bernoulliPMF (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨p, hp.1⟩ (by exact_mod_cast hp.2)

/-- The Bernoulli probability measure on `Bool` with parameter `p ∈ [0, 1]`. -/
noncomputable def bernoulliMeasure (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : Measure Bool :=
  (bernoulliPMF p hp).toMeasure

instance isProbabilityMeasure_bernoulli (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p hp) := by
  dsimp [bernoulliMeasure]
  infer_instance

/-- The product measure describing independent edge indicators for `G(n,p)`. -/
noncomputable def gnpSampleMeasure (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Measure (EdgePairs n → Bool) :=
  Measure.pi fun _ : EdgePairs n => bernoulliMeasure p hp

instance instIsProbabilityMeasure_gnpSampleMeasure (n : ℕ) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (gnpSampleMeasure (n := n) (p := p) hp) := by
  classical
  simpa [gnpSampleMeasure] using
    (Measure.pi.instIsProbabilityMeasure
      (μ := fun _ : EdgePairs n => bernoulliMeasure p hp))

/-- Extend an outcome on the edge index set to a Boolean indicator on all of
`Sym2 (Fin n)` by forcing diagonal elements to be absent. -/
noncomputable def edgeIndicator (ω : EdgePairs n → Bool) : Sym2 (Fin n) → Bool :=
  fun e => if h : ¬ e.IsDiag then ω ⟨e, h⟩ else false

@[simp]
lemma edgeIndicator_diag (ω : EdgePairs n → Bool) (e : Sym2 (Fin n))
    (he : e.IsDiag) : edgeIndicator (n := n) ω e = false := by
  classical
  simp [edgeIndicator, he]

@[simp]
lemma edgeIndicator_nonDiag (ω : EdgePairs n → Bool) (e : Sym2 (Fin n))
    (he : ¬ e.IsDiag) : edgeIndicator (n := n) ω e = ω ⟨e, he⟩ := by
  classical
  simp [edgeIndicator, he]

/-- The random edge set extracted from an indicator configuration. -/
noncomputable def edgeSet (ω : EdgePairs n → Bool) : Set (Sym2 (Fin n)) :=
  {e | edgeIndicator (n := n) ω e = true}

/-- The simple graph realised by a given outcome of the edge indicators. -/
noncomputable def gnpGraph (ω : EdgePairs n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (edgeSet (n := n) ω)

/-- The `G(n,p)` random variable viewed as a function into labelled simple
graphs on `Fin n`. -/
noncomputable def gnp (n : ℕ) : (EdgePairs n → Bool) → SimpleGraph (Fin n) :=
  gnpGraph (n := n)

@[simp]
lemma gnp_adj (ω : EdgePairs n → Bool) {u v : Fin n} :
    (gnp (n := n) ω).Adj u v ↔
      edgeIndicator (n := n) ω s(u, v) = true ∧ u ≠ v := by
  classical
  simp [gnp, gnpGraph, edgeSet, edgeIndicator]

instance instMeasurableSpaceSimpleGraphFin (n : ℕ) :
    MeasurableSpace (SimpleGraph (Fin n)) := ⊤

@[measurability]
lemma measurable_gnp (n : ℕ) : Measurable (gnp (n := n)) := by
  classical
  simpa [gnp] using (measurable_of_finite (f := gnpGraph (n := n)))

/-- The distribution of `G(n,p)` obtained by pushing forward the product
measure on edge indicators. -/
noncomputable def gnpDistribution (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Measure (SimpleGraph (Fin n)) :=
  (gnpSampleMeasure (n := n) (p := p) hp).map (gnp (n := n))

/-- Stage 2 random variable: the number of labelled copies of `H` inside the
random graph `G(n,p)` realised by an indicator configuration. -/
noncomputable def countCopiesRV {k n : ℕ} (H : SimpleGraph (Fin k)) :
    (EdgePairs n → Bool) → ℕ :=
  fun ω => countCopies H (gnp (n := n) ω)

@[simp]
lemma countCopiesRV_apply {k n : ℕ} (H : SimpleGraph (Fin k))
    (ω : EdgePairs n → Bool) :
    countCopiesRV (n := n) H ω = countCopies H (gnp (n := n) ω) := rfl

lemma measurable_countCopiesRV {k n : ℕ} (H : SimpleGraph (Fin k)) :
    Measurable
      (fun ω : EdgePairs n → Bool =>
        (countCopiesRV (n := n) H ω : ℝ)) := by
  classical
  have hGraph :
      Measurable
        (fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ)) := by
    simpa using
      (measurable_of_finite
        (f := fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ)))
  simpa [countCopiesRV] using hGraph.comp (measurable_gnp (n := n))

/-- Stage 2 bound: the copy-counting random variable is integrable because it is
bounded by the descending factorial `n.descFactorial k` for every configuration.
-/
lemma integrable_countCopies {k n : ℕ} (H : SimpleGraph (Fin k)) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    Integrable
      (fun ω : EdgePairs n → Bool =>
        (countCopiesRV (n := n) H ω : ℝ))
      (gnpSampleMeasure (n := n) (p := p) hp) := by
  classical
  have hBound :
      ∀ ω : EdgePairs n → Bool,
        ‖(countCopiesRV (n := n) H ω : ℝ)‖
          ≤ (Nat.descFactorial n k : ℝ) := by
    intro ω
    have hNat :
        (countCopies H (gnp (n := n) ω) : ℝ)
          ≤ (Nat.descFactorial n k : ℝ) := by
      exact_mod_cast
        countCopies_le_descFactorial
          (H := H) (G := gnp (n := n) ω)
    have hNonneg :
        0 ≤ (countCopies H (gnp (n := n) ω) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    simpa [countCopiesRV, abs_of_nonneg hNonneg] using hNat
  have hFinite :
      HasFiniteIntegral
        (fun ω : EdgePairs n → Bool =>
          (countCopiesRV (n := n) H ω : ℝ))
        (gnpSampleMeasure (n := n) (p := p) hp) := by
    refine HasFiniteIntegral.of_bounded
      (μ := gnpSampleMeasure (n := n) (p := p) hp)
      (f := fun ω : EdgePairs n → Bool =>
        (countCopiesRV (n := n) H ω : ℝ))
      (C := (Nat.descFactorial n k : ℝ)) ?_
    exact Filter.Eventually.of_forall hBound
  refine ⟨(measurable_countCopiesRV (n := n) H).aestronglyMeasurable, hFinite⟩

/-- Sanity check: counting labelled copies of `K₁` in `G(2, 0)` defines an
integrable real-valued random variable. -/
example :
    Integrable
      (fun ω : EdgePairs 2 → Bool =>
        (countCopiesRV (n := 2)
            (SimpleGraph.completeGraph (Fin 1)) ω : ℝ))
      (gnpSampleMeasure (n := 2) (p := 0) (⟨le_rfl, by norm_num⟩)) := by
  have hp0 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, by norm_num⟩
  simpa [hp0]
    using
    integrable_countCopies
      (n := 2)
      (H := SimpleGraph.completeGraph (Fin 1))
      (p := 0)
      (hp := hp0)

lemma gnpDistribution_apply (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (s : Set (SimpleGraph (Fin n))) (hs : MeasurableSet s) :
    gnpDistribution (n := n) (p := p) hp s =
      gnpSampleMeasure (n := n) (p := p) hp ((gnp (n := n)) ⁻¹' s) := by
  classical
  simpa [gnpDistribution] using
    Measure.map_apply (measurable_gnp (n := n)) hs

lemma bernoulliMeasure_singleton_true (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp {True} = ENNReal.ofReal p := by
  classical
  have :=
    PMF.toMeasure_apply_singleton
      (bernoulliPMF p hp)
      (True)
      (by simpa using (measurableSet_singleton (a := True)))
  simpa [bernoulliMeasure, bernoulliPMF, PMF.bernoulli_apply,
    ENNReal.ofReal_coe_nnreal] using this

lemma bernoulliMeasure_singleton_false (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp {False} = ENNReal.ofReal (1 - p) := by
  classical
  have :=
    PMF.toMeasure_apply_singleton
      (bernoulliPMF p hp)
      (False)
      (by simpa using (measurableSet_singleton (a := False)))
  have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  simp [bernoulliMeasure, bernoulliPMF, PMF.bernoulli_apply,
    ENNReal.ofReal_coe_nnreal, hp', sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] at this
  simpa [hp'] using this

lemma bernoulliMeasure_univ (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp (Set.univ : Set Bool) = 1 := by
  classical
  simpa using (measure_univ (bernoulliMeasure (p := p) hp))

lemma gnpCylinderMeasure (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (S : Finset (EdgePairs n)) (b : EdgePairs n → Bool) :
    gnpSampleMeasure (n := n) (p := p) hp
        {ω | ∀ e ∈ S, ω e = b e}
      = ∏ e in S,
          (if b e then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
  classical
  let s : EdgePairs n → Set Bool := fun e =>
    if h : e ∈ S then {b e} else Set.univ
  have hSet :
      {ω | ∀ e ∈ S, ω e = b e} =
        Set.pi Set.univ s := by
    ext ω; constructor
    · intro hω
      intro e _
      by_cases he : e ∈ S
      · have := hω e he
        simp [s, he, this]
      · simp [s, he]
    · intro hω e he
      have : ω e ∈ {b e} := by
        simpa [s, he] using hω e trivial
      simpa using this
  have hs : ∀ e, MeasurableSet (s e) := by
    intro e
    by_cases he : e ∈ S
    · simp [s, he]
    · simp [s, he]
  have hprod :=
    Measure.pi_pi_aux
      (μ := fun _ : EdgePairs n => bernoulliMeasure p hp)
      (s := s)
      (hs := hs)
  have hUniv :
      ∏ e : EdgePairs n, bernoulliMeasure p hp (s e)
        = ∏ e ∈ S, bernoulliMeasure p hp (s e) := by
    refine
      (Finset.prod_subset (s := S)
        (t := (Finset.univ : Finset (EdgePairs n)))
        (by intro e he; simp) ?_).symm
    intro e he hnot
    simp [s, hnot, bernoulliMeasure_univ, hp] 
  have hEdge :
      ∏ e ∈ S, bernoulliMeasure p hp (s e)
        = ∏ e in S,
            (if b e then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    have : s e = {b e} := by simp [s, he]
    simp [this, bernoulliMeasure_singleton_true,
      bernoulliMeasure_singleton_false, hp.1, hp.2]
  have hRewrite := hUniv.trans hEdge
  have hMeasure :
      gnpSampleMeasure (n := n) (p := p) hp
          (Set.pi Set.univ s)
        = ∏ e in S,
            (if b e then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
    simpa [hRewrite] using hprod
  simpa [hSet] using hMeasure

/-- Sanity check: for `n = 2`, the empty indicator configuration realises the
empty graph. -/
example :
    ¬ (gnp (n := 2) (fun _ : EdgePairs 2 => false)).Adj 0 1 := by
  classical
  simp [gnp_adj]

/-- Sanity check: the configuration selecting the unique off-diagonal pair in
`Fin 2` realises the single edge `0-1`. -/
example :
    (gnp (n := 2)
      (fun e : EdgePairs 2 => if e.1 = s((0 : Fin 2), (1 : Fin 2)) then true else false)).Adj 0 1 := by
  classical
  have hpair :
      s((0 : Fin 2), (1 : Fin 2)).IsDiag = False := by decide
  have hneq : (0 : Fin 2) ≠ 1 := by decide
  simp [gnp_adj, edgeIndicator, hpair, hneq]

end Stage2

end Codex
