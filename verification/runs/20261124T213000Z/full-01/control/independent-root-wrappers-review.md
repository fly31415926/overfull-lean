# Independent semantic review of the root reconstruction wrappers

Reviewer: infrastructure/recovery agent, distinct from the author of these seven Lean modules.

This is a source and statement review. A complete successful fresh Lean build and stock kernel audit are still required; a historical reported pass is not reused. The reviewed mathematical statements have no `sorry`, extra axiom, external proof oracle, assumed residual factorization, or supplied coloring hypothesis.

## Public Proposition 4.16 endpoint

`Overfull.frequent_pattern_result_one_factorization` quantifies its positive tolerance and order threshold before the finite vertex type, arbitrary finite core index type, graph, and actual `CircuitPatterns.FrequentPatternResult`. The only core-cardinality choice is three or four. Lower density and core-size conditions express the usual hierarchy. The conclusion partitions every original residual edge copy into exactly the residual degree many disjoint perfect matchings.

The proof derives even total order from positive regularity and no overfull set. It does not add even order as an external premise to the proposition. The extra additive unit in the terminal error budget is paid by a uniform order threshold; simple-graph degree at most the ambient order converts the record's relative error and reserve estimates to the required ambient budget.

Three cores use the proved three-core terminal theorem after an arbitrary finite equivalence. Four cores use the record's actual stored embedding `R.code`, made into an equivalence. The label fibers are the actual enlarged cores. `joining_pairPool_card` compares the same original unordered edges under injective subtype-forgetting maps; it does not substitute an abstract graph with unrelated multiplicities. The actual stored reserve and forest supply are passed unchanged. The forest-shape condition is requested only in the all-odd branch where the record supplies it.

`four_core_parity` exhausts exactly zero, two, or four odd fibers of an even-order partition. `four_core_terminal_one_factorization` takes the minimum of the three previously chosen tolerances and maximum of their order thresholds. Its even, two-odd, and all-odd branches use their respective constructive terminals, with no new residual-coloring assumption.

## Public Theorem 4.17 endpoint

`Overfull.regular_core_one_factorization` permits every positive density parameter and every finite core index type of cardinality three or four. The robust range condition `tau <= min alpha 1 / 256000` is a fixed sufficient interpretation of a sufficiently small ordinary robust range. The original input is an even-order simple regular host, no overfull set, disjoint covering robust cores and exceptional set, and the literal linear budget `a + |Z| + 1 <= epsilon*n`.

The public statement does not assume nonnegative error. The proof derives it from the lower core-degree hypothesis, actual core embedding into the original regular host, and a nonempty core ensured by the positive order threshold and density. Arbitrary positive density is normalized internally by `min alpha 1`, and the original density/core-size hypotheses imply the weaker normalized ones.

The final one-factorization concerns all original edge copies, with degree-palette many perfect matchings, pairwise disjoint and covering all copies. It is not a factorization of only the final residual.

## Uniformity and dependency order

The `Frequent` wrapper obtains the frequent reduction's surviving robustness before requesting the terminal error, lowers robustness by a minimum where necessary, factors the actual record, and restores the original deleted perfect-matching prefix.

The `Bounded` wrapper fixes the exceptional bound first and reduces the robust range internally. Its positive tolerance and order threshold precede the host. This makes it a family of available results indexed by the possible exceptional cardinality.

The `Regular` wrapper chooses the whole positive tolerance function `f(t)` before the absorption theorem chooses its finite bound `T`. Only then does it take a finite maximum of the order thresholds `nB(t)` for `t <= T`. Thus no graph-dependent exceptional cardinality is used to retroactively choose the initial tolerance. Foreign-edge, absorption, and frequent-pattern prefixes are restored in reverse order on original copies. Exact degree identities show that the restored palette size is the original regular degree.

## Scope boundary and pending checks

This review supports exactly the full pinned 4.16 and 4.17 claims, conditional on successful compilation and full audit. It does not close the nonregular three-core continuation, the Section 6 reduction, or the main theorem. The separately preserved current manuscript excerpts were inspected: the standing notation explicitly makes partition unions disjoint and gives every sufficiently small positive robust range with every positive neighborhood parameter at most that range. Lemma 4.13 matches its pinned block byte-for-byte. The 4.16 and 4.17 blocks match their pinned hashes after precisely one documented spelling change from `$1$-factorization` to `one-factorization` each. The notation's raw API excerpt omits its terminal newline; that sole formatting difference is recorded. No whole-manuscript identity is asserted. The recovery identity and the new run's evidence remain distinct.

The final compiler corrections were independently re-inspected: the parity proof spells out the four residues in each case; the pattern transport unfolds the existing cut/quotient definitions and simplifies the stored code equivalence; the terminal wrapper opens its existing `Compression` namespace; the frequent wrapper transports equality-decision instances by proof irrelevance; the regular wrapper derives `Nonempty I` from the already-present cardinality 3/4 hypothesis. None changes a public assumption or conclusion.

The final strict command `lake build --wfail Overfull.FourCoreReduction.Regular` passed in `development/root-regular-03`: actual child and wrapper exit 0, no changed inputs, and log SHA256 `26631d72540cbaa0e91a7d6782017a2a06382be22f23b50f8dab0b8385a24be6`. Each of the seven final source files below was checked against that genuine command's recorded input hash and exact archived source. This focused pass still does not replace the pending complete kernel audit.

The five current documentation files were reviewed for precise scope and provenance. The distinction between the original-host no-overfull hypothesis and the derived central no-overfull certificate is explicit. Current coverage is conditioned on the actual fresh full-run and preservation receipts; historical checkpoint counts remain identified as historical. The generated final source map contains 25 modules and 63 public proof declarations, with no inferred private/generated declaration count.

## Final reviewed source and documentation hashes

Reviewed at UTC: 2026-11-24T21:55:02.184226+00:00

| Source | SHA256 |
|---|---|
| `Overfull/TerminalFour/Parity.lean` | `cd91353cbfb7f03db82e6957084fda3298b46ac101ac54753640abb26b3574bc` |
| `Overfull/TerminalFour/PatternTransport.lean` | `ce0364a630fb817389ea42dd1630ef2ea9b8614a52ffaec59950ed2bb06716ca` |
| `Overfull/TerminalFour/Result.lean` | `36c5eabe1173480d6e8772546ec48f8668005b6177e1fc77ef692f675a9d9b1a` |
| `Overfull/TerminalFour/Theorem.lean` | `85b5e9f3ebc770a88e4386d44d66665eba4a4030011f321ed1c5356a77f09c30` |
| `Overfull/FourCoreReduction/Bounded.lean` | `d9d522804612de306959ca3d32ca383ce76c01cf2e0439b3d2a078b305bbb658` |
| `Overfull/FourCoreReduction/Frequent.lean` | `773f1d107600812625cd0aeb619d20d2706cfc6a850b140ebd5db696d468ecd8` |
| `Overfull/FourCoreReduction/Regular.lean` | `182c4596a1095ed33e58ef4a2059c51a75fbe1edc9b1d96f622aefde1cbf9fe1` |
| `README.md` | `65270b9b1ea6cdb4b1865787571d72e93158b5bda8ee9e30393a3e7a984c2ef8` |
| `docs/four-core-continuation-verification.md` | `49d85411db0e85354a0a5cf5e09933c5b88ad284750774eea193e895a4cc43a1` |
| `docs/four-core-continuation-semantic-review.md` | `80da1d262fd5d7acfbb13e7caada17ebdcbc91272e72795c4a9f2e8e5357e74e` |
| `docs/continuation-handoff.md` | `d3bd70117b88c5d2e8c2cea14263f1d0787025dd10785be0cdd6f7c3bce5b1b1` |
| `docs/next-verification-target.md` | `df4c426990cd918fac213ff43de67e67e935ef4f3ada32df579987f67b4656d1` |
| `docs/coverage.json` | `af106e3ead08548698b4878811497e71ffa4c8ed88e889ed811a260ced7677a3` |
| `docs/manuscript-source.json` | `35384073f99510f8e3a765aa8fe0aec4f9670acdc27d653956f94774ad1553b8` |
| `docs/four-core-continuation-source.json` | `c73da1fb351ed0a8a4fd0033552320be0644ee98bfc36d2f891ffda8df7e4db1` |
