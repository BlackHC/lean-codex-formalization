# Agent Instructions for `lean-codex-formalization`

## Scope

These instructions apply to the entire repository. Update this file if new subdirectories require finer-grained guidance.

## Primary Goals

1. Follow the staged formalization plan recorded in `README.md` when adding Lean code. Each commit should advance one of the listed tasks or document why a deviation is necessary.
2. Ensure every mathematical definition, lemma, or theorem introduced from the paper is accompanied by a Lean proof or an explicit TODO comment that references the corresponding stage in the README, plus a sanity-check lemma/example that tests the statement on a toy instance whenever feasible.
3. Keep the documentation synchronized: whenever the plan evolves, update both `README.md` and this file so future work can trace the intended workflow.

## Workflow Requirements

- **Dependencies:** Before pushing significant Lean changes, verify that the dependency configuration in `lakefile.lean` imports `mathlib` and run `lake update` if new packages are added.
- **Build checks:** Run `lake build` after modifying Lean files. Record the command in the PR/testing notes.
- **Linting:** Execute `#lint` (or `lake exe lint` when available) before each commit to confirm that the intermediate results are fully verified and there are no unintentional omissions.
- **File organization:**
  - Place section-specific developments under `Formalization/`, using filenames that mirror the paper (e.g., `SpreadLemma.lean`, `Thresholds.lean`).
  - Keep exploratory work in clearly named scratch files and clean them before merging.
- **Documentation:**
  - Use module doc-strings (`/-! ### ... -/`) in Lean files to reference the corresponding section or result in the paper.
  - Cross-reference the numbering from the paper (e.g., “Lemma 2.1”) within comments to ease navigation.

## Collaboration Notes

- When adding new intermediate results, explicitly state whether they correspond to definitions, lemmas, or theorems in the paper and cite the equation or section label. Pair each with a quick verification (e.g., `example`, `simp` check, or concrete evaluation) demonstrating the definition behaves as expected.
- Prefer reusable abstractions (e.g., graph embeddings, probabilistic estimates) rather than ad-hoc constructions to facilitate later proofs.
- If an argument requires an external result (such as concentration inequalities), document its source and consider proving a reusable version in a separate module.

Maintaining this workflow ensures the project remains aligned with the target paper and that every intermediate claim becomes a verified Lean statement.
