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

/-- Stage 2 transfer: the copy-counting random variable remains integrable when pushed
forward to the distribution on simple graphs. -/
lemma integrable_countCopies_distribution {k n : ℕ}
    (H : SimpleGraph (Fin k)) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Integrable
      (fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ))
      (gnpDistribution (n := n) (p := p) hp) := by
  classical
  have hRV :=
    integrable_countCopies (n := n) (H := H) (p := p) hp
  have hMeas :
      AEStronglyMeasurable
        (fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ))
        (gnpDistribution (n := n) (p := p) hp) := by
    simpa using
      (measurable_of_finite
        (f := fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ))).aestronglyMeasurable
  refine
    (integrable_map_measure
      (μ := gnpSampleMeasure (n := n) (p := p) hp)
      (f := gnp (n := n))
      (g := fun G : SimpleGraph (Fin n) => (countCopies H G : ℝ))
      hMeas
      (measurable_gnp (n := n)).aemeasurable).mpr
      ?_
  simpa [countCopiesRV] using hRV

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

/-- Sanity check: integrability is preserved on the push-forward distribution. -/
example :
    Integrable
      (fun G : SimpleGraph (Fin 2) =>
        (countCopies (SimpleGraph.completeGraph (Fin 1)) G : ℝ))
      (gnpDistribution (n := 2) (p := 0) (⟨le_rfl, by norm_num⟩)) := by
  have hp0 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, by norm_num⟩
  simpa [hp0]
    using
      integrable_countCopies_distribution
        (n := 2)
        (H := SimpleGraph.completeGraph (Fin 1))
        (p := 0)

/-- For distinct vertices `u ≠ v`, the `G(n,p)` edge event corresponds to the
evaluation map on the coordinate indexed by `{u, v}`. -/
lemma edgeEvent_eq_eval_preimage {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    {ω : EdgePairs n → Bool | (gnp (n := n) ω).Adj u v}
      = (fun ω => ω ⟨s(u, v), by
            classical
            simpa [Sym2.mk_isDiag_iff, h]⟩)
          ⁻¹' ({true} : Set Bool) := by
  classical
  have he : ¬(s(u, v)).IsDiag := by simpa [Sym2.mk_isDiag_iff, h]
  ext ω
  have :
      (gnp (n := n) ω).Adj u v ↔
        (edgeIndicator (n := n) ω (s(u, v)) = true) := by
    simpa [gnp_adj, h]
  simpa [Set.preimage, this, edgeIndicator_nonDiag (n := n) (ω := ω)
      (e := s(u, v)) he]

/-- Bernoulli product measure sanity check: the probability of `true` is `p`. -/
lemma bernoulliMeasure_singleton_true (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp ({true} : Set Bool) = ENNReal.ofReal p := by
  classical
  have hTrue :
      bernoulliMeasure p hp ({true} : Set Bool)
        = (bernoulliPMF p hp) true := by
    simpa [bernoulliMeasure] using
      PMF.toMeasure_apply_singleton
        (bernoulliPMF p hp)
        true
        (by simpa using (measurableSet_singleton (a := true)))
  have hMass :
      (bernoulliPMF p hp) true = ENNReal.ofNNReal ⟨p, hp.1⟩ := by
    simp [bernoulliPMF, PMF.bernoulli_apply]
  have hCoe :
      ENNReal.ofNNReal ⟨p, hp.1⟩ = ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_eq_coe_nnreal hp.1).symm
  exact hTrue.trans (hMass.trans hCoe)

/-- Bernoulli product measure sanity check: the probability of `false` is `1 - p`. -/
lemma bernoulliMeasure_singleton_false (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp ({false} : Set Bool) = ENNReal.ofReal (1 - p) := by
  classical
  have hFalse :
      bernoulliMeasure p hp ({false} : Set Bool)
        = (bernoulliPMF p hp) false := by
    simpa [bernoulliMeasure] using
      PMF.toMeasure_apply_singleton
        (bernoulliPMF p hp)
        false
        (by simpa using (measurableSet_singleton (a := false)))
  have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hMass :
      (bernoulliPMF p hp) false = ENNReal.ofNNReal (1 - ⟨p, hp.1⟩) := by
    simp [bernoulliPMF, PMF.bernoulli_apply]
  have hNNReal :
      (1 - ⟨p, hp.1⟩ : NNReal) = ⟨1 - p, hp'⟩ := by
    ext
    have hle : (⟨p, hp.1⟩ : NNReal) ≤ (1 : NNReal) := by
      exact_mod_cast hp.2
    simpa using (NNReal.coe_sub hle)
  have hCoe :
      ENNReal.ofNNReal (1 - ⟨p, hp.1⟩) = ENNReal.ofReal (1 - p) := by
    simpa [hNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp').symm
  exact hFalse.trans (hMass.trans hCoe)

/-- Bernoulli product measure sanity check: total mass equals one. -/
lemma bernoulliMeasure_univ (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    bernoulliMeasure p hp (Set.univ : Set Bool) = 1 := by
  classical
  simpa using (measure_univ (μ := bernoulliMeasure p hp))

/-- The probability that the random graph `G(n,p)` places an edge between two
distinct vertices is exactly `p`.  We state the result in terms of the measure
of the corresponding event, which naturally lives in `ℝ≥0∞`. -/
lemma gnp_edge_measure {n : ℕ} {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    {u v : Fin n} (h : u ≠ v) :
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | (gnp (n := n) ω).Adj u v}
      = ENNReal.ofReal p := by
  classical
  have hEval :=
    MeasureTheory.measurePreserving_eval
      (μ := fun _ : EdgePairs n => bernoulliMeasure p hp)
      ⟨s(u, v), by
        simpa [Sym2.mk_isDiag_iff, h]⟩
  have hSet : MeasurableSet ({true} : Set Bool) := by simp
  have hTrue := bernoulliMeasure_singleton_true (p := p) hp
  have hEvent := edgeEvent_eq_eval_preimage (n := n) (u := u) (v := v) h
  have hMeasureSet :
      (gnpSampleMeasure (n := n) (p := p) hp)
          {ω : EdgePairs n → Bool | (gnp (n := n) ω).Adj u v}
        = (gnpSampleMeasure (n := n) (p := p) hp)
            ((fun ω : EdgePairs n → Bool =>
                ω ⟨s(u, v), by
                  simpa [Sym2.mk_isDiag_iff, h]⟩)
              ⁻¹' ({true} : Set Bool)) := by
    simpa using congrArg
      (fun s => (gnpSampleMeasure (n := n) (p := p) hp) s) hEvent
  calc
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | (gnp (n := n) ω).Adj u v}
        = (gnpSampleMeasure (n := n) (p := p) hp)
            ((fun ω : EdgePairs n → Bool =>
                ω ⟨s(u, v), by
                  simpa [Sym2.mk_isDiag_iff, h]⟩)
              ⁻¹' ({true} : Set Bool)) := hMeasureSet
    _ = (bernoulliMeasure p hp) ({true} : Set Bool) := by
      simpa using
        hEval.measure_preimage
          (μa := gnpSampleMeasure (n := n) (p := p) hp)
          (μb := bernoulliMeasure p hp)
          (s := {true})
          (hSet.nullMeasurableSet)
    _ = ENNReal.ofReal p := hTrue

/-- Sanity check: in `G(3, 1/2)` the edge event between vertices `0` and `1`
has probability mass `1/2` with respect to the product measure. -/
example :
    (gnpSampleMeasure (n := 3) (p := (1 : ℝ) / 2)
        (⟨by norm_num, by norm_num⟩))
        {ω : EdgePairs 3 → Bool | (gnp (n := 3) ω).Adj 0 1}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hp : 0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 ≤ 1 := by constructor <;> norm_num
  simpa using gnp_edge_measure (n := 3) (p := (1 : ℝ) / 2) hp (u := 0) (v := 1)
    (by decide : (0 : Fin 3) ≠ 1)

lemma gnpDistribution_apply (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (s : Set (SimpleGraph (Fin n))) (hs : MeasurableSet s) :
    gnpDistribution (n := n) (p := p) hp s =
      gnpSampleMeasure (n := n) (p := p) hp ((gnp (n := n)) ⁻¹' s) := by
  classical
  simpa [gnpDistribution] using
    Measure.map_apply (measurable_gnp (n := n)) hs

lemma edgeIndicator_iIndepFun (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ProbabilityTheory.iIndepFun
      (fun e (ω : EdgePairs n → Bool) => ω e)
      (gnpSampleMeasure (n := n) (p := p) hp) := by
  classical
  simpa [gnpSampleMeasure]
    using
      (ProbabilityTheory.iIndepFun_pi
        (μ := fun _ : EdgePairs n => bernoulliMeasure p hp)
        (X := fun _ : EdgePairs n => (fun b : Bool => b))
        (mX := fun _ => measurable_id.aemeasurable))

/-- Probability of realising a prescribed finite set of edges in `G(n,p)` equals `p`
raised to the number of constraints. -/
lemma gnpCylinderMeasure_assign (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (S : Finset (EdgePairs n)) (assign : EdgePairs n → Bool) :
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = assign e}
      =
        ∏ e ∈ S,
          if assign e then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
  classical
  have hindep :=
    edgeIndicator_iIndepFun (n := n) (p := p) hp
  have hmeas :
      ∀ e ∈ S,
        MeasurableSet
          ((fun ω : EdgePairs n → Bool => ω e) ⁻¹'
            ({assign e} : Set Bool)) := by
    intro e _
    have hBool : MeasurableSet ({assign e} : Set Bool) := by simp
    simpa using hBool.preimage (measurable_pi_apply e)
  have hset :
      {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = assign e} =
        ⋂ e ∈ S,
          (fun ω : EdgePairs n → Bool => ω e) ⁻¹'
            ({assign e} : Set Bool) := by
    classical
    ext ω; constructor
    · intro hω
      refine Set.mem_iInter₂.mpr ?_
      intro e he
      have hval := hω e he
      simpa [Set.preimage, Set.mem_setOf_eq] using hval
    · intro hω e he
      have hmem := Set.mem_iInter₂.mp hω e he
      simpa [Set.preimage, Set.mem_setOf_eq] using hmem
  have hproduct :=
    hindep.measure_inter_preimage_eq_mul
      (μ := gnpSampleMeasure (n := n) (p := p) hp)
      (S := S)
      (sets := fun e => ({assign e} : Set Bool))
      (by
        intro e he
        simpa using (hmeas e he))
  have hfactor (e : EdgePairs n) :
      (gnpSampleMeasure (n := n) (p := p) hp)
          ((fun ω : EdgePairs n → Bool => ω e) ⁻¹'
            ({assign e} : Set Bool))
        =
          if assign e then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
    have hEval :=
      MeasureTheory.measurePreserving_eval
        (μ := fun _ : EdgePairs n => bernoulliMeasure p hp) e
    have hBool : MeasurableSet ({assign e} : Set Bool) := by simp
    have hTrue := bernoulliMeasure_singleton_true (p := p) hp
    have hFalse := bernoulliMeasure_singleton_false (p := p) hp
    have hMeasure :=
      hEval.measure_preimage
        (μa := gnpSampleMeasure (n := n) (p := p) hp)
        (μb := bernoulliMeasure p hp)
        (s := {assign e})
        (hBool.nullMeasurableSet)
    by_cases hassign : assign e
    · have hset : ({assign e} : Set Bool) = {true} := by simpa [hassign]
      have hBern := by simpa [hassign] using hTrue
      simpa [gnpSampleMeasure, hset, hassign, hBern] using hMeasure
    · have hset : ({assign e} : Set Bool) = {false} := by
        have : assign e = false :=
          by simpa [hassign] using Bool.eq_false_of_ne_true hassign
        simpa [this]
      have hBern := by
        have : assign e = false :=
          by simpa [hassign] using Bool.eq_false_of_ne_true hassign
        simpa [this] using hFalse
      simpa [gnpSampleMeasure, hset, hassign, hBern] using hMeasure
  classical
  calc
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = assign e}
        = (gnpSampleMeasure (n := n) (p := p) hp)
            (⋂ e ∈ S,
              (fun ω : EdgePairs n → Bool => ω e) ⁻¹'
                ({assign e} : Set Bool)) := by
          simpa [hset]
    _ =
        ∏ e ∈ S,
            (gnpSampleMeasure (n := n) (p := p) hp)
              ((fun ω : EdgePairs n → Bool => ω e) ⁻¹'
                ({assign e} : Set Bool)) :=
          hproduct
    _ =
        ∏ e ∈ S,
            if assign e then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
          refine Finset.prod_congr rfl ?_
          intro e he
          simp [hfactor]

lemma gnpCylinderMeasure (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (S : Finset (EdgePairs n)) :
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = true}
      = ENNReal.ofReal (p ^ S.card) := by
  classical
  have hassign :=
    gnpCylinderMeasure_assign (n := n) (p := p) hp S (fun _ => true)
  have hp_nonneg : 0 ≤ p := hp.1
  have hprod :
      (gnpSampleMeasure (n := n) (p := p) hp)
          {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = true}
        = ∏ e ∈ S, ENNReal.ofReal p := by
    simpa [hassign]
  have hpowConst :
      ∏ e ∈ S, ENNReal.ofReal p = (ENNReal.ofReal p) ^ S.card := by
    classical
    refine Finset.prod_eq_pow_card ?_
    intro e he
    rfl
  have hpow := ENNReal.ofReal_pow hp_nonneg S.card
  calc
    (gnpSampleMeasure (n := n) (p := p) hp)
        {ω : EdgePairs n → Bool | ∀ e ∈ S, ω e = true}
        = ∏ e ∈ S, ENNReal.ofReal p := hprod
    _ = (ENNReal.ofReal p) ^ S.card := hpowConst
    _ = ENNReal.ofReal (p ^ S.card) := by
      simpa using hpow.symm

/- TODO (Stage 2): Leverage `gnpCylinderMeasure` to compute expectations for the
copy-counting random variables and deduce the `M_H p^{e(H)}` formula. -/

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
