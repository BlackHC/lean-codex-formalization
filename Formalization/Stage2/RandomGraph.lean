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

lemma gnpDistribution_apply (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (s : Set (SimpleGraph (Fin n))) (hs : MeasurableSet s) :
    gnpDistribution (n := n) (p := p) hp s =
      gnpSampleMeasure (n := n) (p := p) hp ((gnp (n := n)) ⁻¹' s) := by
  classical
  simpa [gnpDistribution] using
    Measure.map_apply (measurable_gnp (n := n)) hs

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
