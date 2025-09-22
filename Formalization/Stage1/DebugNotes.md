# Stage 1 debugging notes (2024-)

* The attempt to extend embeddings `J ↪g K_n` to permutations of `Fin n` relied on
  `Function.Embedding.comp`/`equivRange` and `Equiv.toPerm`.  Mathlib only exposes
  these constructions for `Embedding`, so the earlier code failed to compile.  We
  removed the broken lemmas and will rebuild the argument directly with
  `Embedding` utilities or a group-action approach.
* The combinatorial probability lemma
  `uniformProbability_contains_fixed` was rolled back until the permutation
  extension is reconstructed.  The foundational bijection
  `embeddingsIntoRangeEquiv` and its ratio corollary remain available for the
  double-counting argument.
