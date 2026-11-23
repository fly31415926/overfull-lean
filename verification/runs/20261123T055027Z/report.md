# Native multigraph actual-copy capacity continuation — 20261123T055027Z

Base: verified heads `ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6` (tree `8e59576eb2b94c02b6b1072c4afaf29543540db6`). Attempt branch: `continuation-attempt/20261123T055027Z`.

## Mathematical advance and new Lean source

The new `Overfull/MultigraphMatchingProbabilityCapacities.lean` is a source-level attempt to port the checked finite-weight/capacity arguments from simple edges to genuine multigraph edge copies. It scales the native perfect-matching distribution, derives exact unit marginals per copy, bounds weighted selected-copy pools, aggregates bounded pattern statistics, and proves the correct parallel-copy multiplicity bound for a pattern requiring some copy between a specified pair. Parallel copies remain separate elements of `E`. No numbered manuscript statement or hypothesis was modified, and no new axiom/admission was introduced.

The final result is deliberately different from the old simple-graph bound one: an internal endpoint pair with m parallel original copies has pattern weight at most m, not necessarily at most one. This is the interface needed before reserve rounding in the two-core branch of Corollary 4.6. Actual boundary compression and residual no-overfull protection remain separate obligations.

## Genuine checks

- The execution environment lacked `lean`, `lake`, and the previous workspace checkout. Direct Git transport failed with `Could not resolve host: github.com`. Therefore targeted Lean compilation, strict `lake build --wfail`, `python3 scripts/verify.py`, and the stock `Audit.lean` were **NOT RUN** for the new source.
- An exact-rational finite check of two-vertex k-parallel-copy models for k=1,...,8 passed 510 pool equalities and confirms that the shared endpoint-pair pattern's scaled weight can be k. This is finite experimental evidence only.
- The last fully verified run remains `20261123T042619Z`: 3,675 strict build jobs and the unchanged 11,927-declaration audit passed; coverage remains 47/69.

## Next steps

Compile this source under Lean 4.24.0 and pinned mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, repair all errors, add a reviewed source/declaration map, then run the complete unchanged verifier before promoting either verified branch. Next formalize native two-core boundary compression: retain all matching copies touching the exceptional set plus zero or one old-core crossing copy according to parity, prove the `|Z|+1` bound and uncovered-core parity, and align the resulting statistic with the source boundary pattern.
