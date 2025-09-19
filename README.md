# Lean Formalization of *On the Second Kahn--Kalai Conjecture*

This repository aims to formalize the results from the manuscript contained in `paper/Finding_the_threshold-rev4.tex` using Lean 4.

## Repository Structure

- `paper/`: source `.tex` of the target paper.
- `Formalization/`: Lean source files for the project (currently a placeholder).
- `Formalization.lean`: entry point for the Lean library.

The project uses Lean `v4.24.0-rc1` (see `lean-toolchain`). The plan below records the steps needed to turn the paper into a complete Lean development and tracks how intermediate claims will be verified mechanically.

## Development Environment Constraints

- After the container launches there is no internet access. Commands such as `lake update` and `lake exe cache get` will fail inside the session. Record any dependency changes directly in `lakefile.lean` and notify the maintainer so they can refresh caches outside the container.

## Formalization Plan

The roadmap below interleaves *construction* steps with explicit strategies for
*verifying* every intermediate definition, lemma, and theorem in Lean.  Each
stage identifies the concrete checks, supporting automation, and sanity tests
that guarantee the mechanized statements coincide with those of the paper.

### Stage 0 — Project Setup

- [x] Add `mathlib` as a dependency in `lakefile.lean`.
- [x] Establish a project-wide namespace (currently `Codex`) and record linting/CI commands (`lake build`, `lake exe cache get` if needed).
- [x] Create a scratch file (`Formalization/Scratch.lean`) for experiments before incorporating statements into the main hierarchy.

*Status (Stage 0):* The namespace `Codex` now lives in `Formalization/Basic.lean`, accompanied by a trivial `SimpleGraph` sanity check so future imports confirm access to `mathlib`.  A dedicated scratchpad (`Formalization/Scratch.lean`) is available for experiments.  Because the interactive container has no internet connectivity, dependency refreshes must be coordinated with the maintainer outside the session; record any required updates in `lakefile.lean` and leave the `lake update` checkbox unchecked until confirmation arrives.

### Stage 1 — Graph-Theoretic Foundations

Goal: formalize the deterministic combinatorial ingredients used across the paper.

Key tasks and Lean checks:

1. **Finite simple graphs.**
   - [x] Use `SimpleGraph` from `mathlib` with vertex type `Fin n` and define helper constructors for labelled graphs on `Fin n` with explicit edge sets.
   - [x] Verify basic facts about edge counts (`e(H)`) and subgraph inclusion with Lean lemmas, tagging the most important ones with `@[simp]` or `@[simp, aesop_safe]` for later automation.
   - [x] Create test lemmas (e.g., `example : e (completeGraph (Fin 3)) = 3 := by decide`) to confirm the definitions match combinatorial intuition.

2. **Copy counting (`M_{H', H}`).**
   - [x] Define `countCopies (H' H : SimpleGraph (Fin n)) : ℕ` as the number of embeddings of `H'` into `H` (using `SimpleGraph.embedding`), quotienting by automorphisms if needed.
   - [x] Prove double-counting identities, e.g., the equality `π_H(J₀ ⊆ 𝐇) = M_{J,H} / M_J` via Lean proofs using `Fintype.card` and symmetry.
   - [x] Validate the combinatorial identities with small examples (`Fin 3`, `Fin 4`) inside Lean using `dec_trivial` or `simp [countCopies]` to ensure the formulas have the correct normalization factors.

3. **Monotonicity and edge-induced subgraphs.**
   - [x] Formalize the edge-induced subgraph construction and show that the number of edges is preserved as required.
   - [x] Provide automation lemmas showing the closure of subgraphs under intersection/union when needed for counting arguments.
   - [x] Use Lean's rewriting tools (`by_cases`, `simp`, `finset.induction`) to verify every structural property, recording each as a lemma reusable in later stages.

*Status (Stage 1):* Stage 1 utilities in `Formalization/Stage1/FiniteSimpleGraphs.lean` now build graphs from explicit edge sets and prove the foundational edge-count lemmas (including monotonicity of `edgeCount` and the `n.choose 2` formula for complete graphs).  Edge-induced subgraphs, together with union/intersection closure lemmas and finite edge-count computations, are available to support the upcoming copy-counting and subgraph arguments.  The copy-counting API confirms that isomorphic pattern or host graphs yield identical enumerations of labelled embeddings.  A new bijection between embeddings establishes the double-counting identity `π_H(J₀ ⊆ 𝐇) = M_{J,H} / M_J`, completing the Stage 1 checklist and setting the stage for the probabilistic development in Stage 2.

### Stage 2 — Random Graph Model and Expectations

Goal: formalize the probabilistic objects \(G(n,p)\) and compute expectations used in the thresholds.

Lean tasks:

1. **Probability space for `G(n, p)`.**
   - [ ] Model `G(n, p)` as the product measure on edge indicators. Use `SimpleGraph` and random edge subsets, employing `MeasureTheory` and `Probability` APIs in `mathlib`.
   - [ ] Define `gnp (n : ℕ) (p : ℝ)` returning a random variable valued in `SimpleGraph (Fin n)`.
   - [ ] Confirm measurability and integrability obligations explicitly with Lean proofs (`measurable_gnp`, `integrable_countCopies`) and tag the statements with documentation notes referencing the paper.

2. **Random variables counting subgraphs.**
   - [ ] For each finite graph `H'`, define `countCopiesInRandomGraph` returning a random variable `Z_{H'}`. Use independence to show `ℙ[Z_{H'} ≥ t]` type statements.
   - [ ] Prove the expectation formula `𝔼[Z_{H'}] = M_{H'} * p^{e(H')}` using Lean's independence lemmas.
   - [ ] Check the expectation formula on small graphs by evaluating `simp`/`ring` proofs in the `Fin 2` or `Fin 3` cases, providing examples that the symbolic formula matches manual calculations.

3. **Tail bounds via Markov.**
   - [ ] Formalize Markov's inequality using `mathlib`'s version and instantiate it for `Z_{H'}`. This verifies the inequalities `p_E ≤ p_Etilde ≤ p_crit`.
   - [ ] Capture the instantiated inequalities as Lean lemmas (`pE_le_pEtilde`, `pEtilde_le_pCrit`) and add `@[simp]` or `lemma` wrappers to make them directly reusable in Stage 3.

### Stage 3 — Threshold Definitions

Goal: encode \(p_E(H)\), \(\tilde{p}_E(H)\), and \(p_\mathsf{c}(H)\) as Lean definitions and derive the easy inequalities.

Lean tasks:

1. **Define thresholds.**
   - [ ] Implement `pE H`, `pEtilde H`, and `pCrit H` as `ℝ` defined via `Inf`/`Sup` over sets of parameters satisfying the corresponding probability or expectation constraints.
   - [ ] Show that the `Inf` is achieved for nonempty sets by proving nontriviality (e.g., using `0 ≤ p ≤ 1`).
   - [ ] Immediately prove characterization lemmas (`lemma pE_def`) that rewrite each definition into the equivalent inequality from the paper, ensuring the Lean definition matches the informal one.

2. **Prove inclusion bounds.**
   - [ ] Encode the arguments from §2.1 (Markov-based inequalities) to show `pE ≤ pEtilde` and `pEtilde ≤ pCrit`.
   - [ ] Verify the algebraic rewritings such as `(1 / (2 * M_{H'}))^(1 / e(H'))` in Lean, ensuring hypotheses handle the nonempty subgraph case (`e(H') ≥ 1`).
   - [ ] Build automation lemmas using `gcongr`, `nlinarith`, and `positivity` to verify inequalities without manual rewriting, and capture intermediate results as `@[simp]` theorems where appropriate.

3. **Continuity and monotonicity lemmas.**
   - [ ] Prove helper results to handle the `max`/`min` formulations: e.g., `pE H = sup_{H' ⊆ H} ...`.
   - [ ] Sanity-check these results on enumerated finite graphs (e.g., compute `pE` for paths of length 2) using Lean's `by decide` or `interval_cases` to ensure the definitions produce reasonable values.

### Stage 4 — Spread Lemma (Lemma 2.1)

Goal: mechanize the probabilistic combinatorial lemma underpinning the main theorem.

Lean tasks:

1. **Statement preparation.**
   - [ ] Define the notion of an `R`-spread distribution over subgraphs using Lean's probability kernels.
   - [ ] Relate it to a finite list of subgraphs `G₁, …, G_M` by taking the uniform measure on that list.
   - [ ] Verify equivalence with the paper's definition by proving bidirectional lemmas (`spread_iff_uniform_support`) and tagging them with `@[simp]`/`@[iff]` as appropriate.

2. **Leverage existing results.**
   - [ ] Formalize or port `Theorem 1.6` from `fracKK_annals` if available; otherwise, implement the argument sketched in the paper by combining concentration bounds for edge counts with the black-box `spread` inequality.
   - [ ] Each imported result should be restated and proved in Lean, verifying prerequisites (e.g., Chernoff bounds) from `mathlib`.
   - [ ] Use Lean's rewrite tactics to double-check the hypotheses line up: provide convenience lemmas that translate between Lean's statements and the constants/notation in the paper.

3. **Final lemma proof.**
   - [ ] Assemble the above to prove Lemma 2.1 exactly as stated, keeping constants explicit (`∃ C` such that …).
   - [ ] Introduce helper lemmas that isolate each probabilistic estimate and unit-test them by instantiating with toy parameters in Lean, ensuring the inequality structure is correct before combining them.

### Stage 5 — Main Theorem (Theorem 1.1)

Goal: combine all previous stages to formalize the main inequality.

Lean tasks:

1. **Define the uniform distribution `π_H`.**
   - [ ] Express `π_H` over copies of `H` using `Fintype` enumerations and show it is `R`-spread with `R = 1 / (2 * pEtilde H)`.
   - [ ] Provide the Lean proof of the double-counting identity `π_H(J₀ ⊆ 𝐇) = M_{J,H} / M_J`.
   - [ ] Verify the normalization (`∑ π_H = 1`) using `simp` lemmas and add a small `example` with a concrete graph confirming the probability measure is valid.

2. **Apply the spread lemma.**
   - [ ] Instantiate Lemma 2.1 with `k = e(H)` and `R = 1 / (2 * pEtilde H)` to deduce the desired bound.
   - [ ] Translate the result back into the statement about thresholds (`pCrit H ≤ L * pEtilde H * log (e(H))`).
   - [ ] Record each translation as a named lemma (`main_theorem`) and provide a structured proof script that clearly references the supporting lemmas, making it easy to audit the Lean derivation.

3. **Document constant dependencies.**
   - [ ] Track universal constants inside Lean proofs to output an explicit `L`. Store them in a dedicated namespace for reuse.
   - [ ] Confirm constant propagation by writing Lean lemmas that show each constant remains positive/bounded; these serve as automated regression tests when constants change.

### Stage 6 — Additional Components

- [ ] **Hamiltonian cycle calculation.** Provide a Lean computation (or estimate) establishing `pEtilde(H) ≍ 1/n` for Hamiltonian cycles, mirroring the remark in the paper.  Cross-check the computation with a small `#eval` or `norm_num` verification.
- [ ] **Bibliographic remarks.** Optionally, create Lean doc-strings referencing the relevant literature for maintainability.
- [ ] **Automation health checks.** Use `#synth`/`#simp?` and `library_search` within doc-strings to record the tactics that succeed on intermediate results, ensuring future refactors can reproduce the same proofs.

## Verification Checklist

- Maintain a `#check`/`#eval` scratchpad for each new definition before moving it into the hierarchy.
- Each stage introduces definitions and lemmas that should be accompanied by Lean proofs; placeholders (e.g., `by admit`) should be avoided in the final development.
- Attach validation lemmas/examples to every new definition to show it behaves correctly on toy instances.
- After significant additions, run `lake build` (and `lake test` if a test harness is added) to ensure the code compiles.
- Maintain documentation within Lean files (`/-! ### ... -/` blocks) describing the relationship between the formal proofs and the paper's arguments.
- Use `#lint` to catch missing `simp`/`instance` lemmas and guarantee all intermediate statements are fully verified.

## Next Steps

1. [ ] Close the remaining Stage 1 checkbox by proving the double-counting identity for `π_H(J₀ ⊆ 𝐇)`.
2. [ ] After Stage 1 is complete, begin Stage 2 by modeling `G(n,p)` and introducing the associated expectation lemmas.

Progress and deviations from this plan should be recorded either in this README or in additional markdown notes within the repository.
