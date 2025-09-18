import Mathlib

/-!
### Stage 0 — Project setup

This module records the initial project namespace and a minimal sanity check
that Lean can see the `SimpleGraph` API from `mathlib`.  The actual
formalization will live in later modules following the staged plan from the
`README`.
-/

namespace Codex

/-- Stage 0 sanity check: the empty simple graph on one vertex. -/
def stage0EmptyGraph : SimpleGraph (Fin 1) := ⊥

example : ¬ stage0EmptyGraph.Adj (0 : Fin 1) (0 : Fin 1) := by
  simp [stage0EmptyGraph]

end Codex
