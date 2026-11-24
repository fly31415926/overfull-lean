# Independent review of the three-core terminal composition

## Result and limits

**No semantic gap, omitted original-host assumption, quantifier-order cycle, or unsupported mathematical conclusion was found in the reviewed outer composition.** This is a read-only source review by the native-geometry agent. It is not a replacement for compilation, the full axiom audit, or the preservation checker. No Lean execution was performed as part of this review. The final outer dependency build and full audit have their own command receipts.

The reviewer independently inspected `ThreeCore.lean`, `CompletedFactorization.lean`, and the semantic-review document. The six central/contraction/odd modules listed below were implemented by this reviewer, so their inclusion here is an integration self-check, not an independent second authorship review of those six files. The verification-setup agent separately reported a full semantic review of those six modules to the parent.

The reviewed `CompletedFactorization.lean` includes the corrected proof order: it splits the parity proposition while the conclusion is still `Nonempty (...)`, constructs the appropriate residual coloring within that branch, and then invokes restoration. This preserves the same theorem statement and avoids an impermissible elimination from a proposition into a coloring type.

The final reviewed versions also normalize decidable equality on the actual residual/original edge-copy types by `Subsingleton.elim`. This aligns finite-set operations and the existing one-factorization interface; it changes no edge set, copy identity, hypothesis, or conclusion.

## Source identities

The exact preceding verified public checkpoint is `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`, with tree `5d031253d02d0d0878422f8fbc367f04b812450c`. The hashes below identify the source bytes reviewed in this continuation, not a new verified or published commit.

| Reviewed file | SHA256 |
| --- | --- |
| `Overfull/Terminal/ThreeCore.lean` | `0b3088e0a199d67f58d580a8cce48777cfd81625ee9a3249d05c62fe3aa092b1` |
| `Overfull/Terminal/CompletedFactorization.lean` | `f73eb10d44c333f03f6a103eaa621955c50ae6337bb90c49f52bb9f886a24435` |
| `docs/three-core-terminal-semantic-review.md` | `ea6cd1b3bc1cf02576492c40e8efc5910de8650476edcd70ce60f4f411209ad4` |
| `Overfull/Terminal/Contraction.lean` | `405b8e7b3f2d8b1b692632aec60707a355df9d417056707d8ac22a0cd7521fa4` |
| `Overfull/Terminal/CentralCuts.lean` | `5ca689fd09c4838c8620a950aa38884fc8b39b14a8eab079d82e1e2161527b13` |
| `Overfull/Terminal/CentralMatchings.lean` | `2d2901129a3bc1d13bd529d6abf1b8c35fe3fd72becad7b54944c9be9c1492c5` |
| `Overfull/Terminal/CentralFactorization.lean` | `cb29f0cc83e5b69fd3f92d13b02bca75c93a83992f3c422a3f661627548a7823` |
| `Overfull/Terminal/OddGluing.lean` | `1c375e5388a215230424c057928383024fbcf624d54b8a3041fd70ed326ddc93` |
| `Overfull/Terminal/OddFactorization.lean` | `e1957ec7fe99d68ac4cc9a728a8a8d02d012eedfa39d8485a19a4c3d54e5bf3d` |

Supporting interfaces were also read in `Prefix.lean`, `PrefixResult.lean`, `CoreBridge.lean`, `RemainingProfile.lean`, `Reassembly.lean`, and `ClosedCores.lean` to check what the outer theorem actually receives and constructs.

## Original hypotheses and public conclusion

The public coloring and one-factorization statements quantify over the original finite simple graph and its actual three covering parts. They retain all the needed hypotheses: positive fixed density and robustness parameters; `ν ≤ τ ≤ min α 1 / 64`; sufficiently large even order; exact regularity of degree `h`; the lower bound `α n ≤ h`; no original `h`-overfull set; pairwise disjoint covering parts of order at least `α n`; actual simple-core embeddings into the induced parts; robust expansion and core degree at least `h-a`; and `0 ≤ a` with `a+1 ≤ ε n`.

Evenness concerns the vertex order. No parity condition on the regular degree is introduced. The output coloring has palette `Fin h` on the original simple graph's edge-copy type. The one-factorization theorem applies the existing regular-host color-class result to produce exactly `h` pairwise disjoint perfect matchings with union all original copies.

There is no supplied joining decomposition, completed matching prefix, residual coloring, complementary coloring, central coloring, odd-leaf coloring, or contracted no-overfull certificate in either public statement. Conditional transport/gluing helpers have such inputs locally, but the public proof constructs those inputs before invoking them.

## Quantifier order and numerical normalization

`ThreeCore.lean` first fixes `β = min α 1`. It obtains the prefix theorem's positive output robustness `θ ≤ τ/2` before it requests any residual error. The completed-prefix theorem then supplies a positive common error tolerance `η` and a common minimum part order for residual parameters `(β/2, θ, τ/2)`. Only then does the prefix theorem choose the original positive `ε` and positive order threshold `n₀` for those requests. The host, vertex type, part sets, core graphs, regular degree, and error are quantified afterward.

The public range bound implies `τ/2 ≤ (β/2)/64`, so the residual two-odd theorem receives its required range. Lowering `α` to `β` preserves both original degree and part-order lower bounds. The prefix output explicitly provides the final minimum part orders, residual degree at least `(β/2)|Uᵢ|`, and `a ≤ η|Uᵢ|`; these are not inferred from unrecorded asymptotic notation.

The residual core-degree bridge uses `rounds ≤ h` when converting natural subtraction to real subtraction. The final error is still the actual common `a`: its degree lower bound is `(h-rounds)-a`, with no silent truncation or lost deletion term.

## Exhaustive residual cases and exact copies

The prefix result gives precisely the all-even and exactly-two-odd alternatives. In the all-even case, the exact remaining joining set is empty, each cut is empty, and the closed-core theorem constructs every component coloring. In the other case, the third label is chosen distinctly from both odd labels; the permutation is checked to cover all three indices, so its part is even and the reordered parts still cover the original vertex set.

`exists_residual_primary_family` transports the retained original primary pieces to the actual `afterDeletions` edge type. It supplies exactly `h-rounds` actual matchings, pairwise copy disjointness, exact coverage of the two odd cuts, and singleton cut cardinalities at both odd parts. The conversion from `cutOn M A` to `M ∩ cutEdges A` is an exact finite-set equality.

The two-apex contraction retains distinct core vertices and distinguishes the two odd apices. Its edge subtype keeps each surviving original copy separately. Core incidences preserve the original degree; each apex incidence corresponds exactly to an original odd-cut copy. Thus the singleton-cut partition gives the exact residual degree at both apices. Embedded simple cores retain their degree and robust parameters under vertex equivalence.

The central no-overfull argument uses the actual transported exterior matching cover. A shore with at most one core vertex cannot contain an edge internal to the core, so all its internal edges are covered by the `k` supplied matchings and have total count at most `k floor(|X|/2)`. The small-cut theorem puts one side of any putative violating odd cut in that situation. Regularity and even order handle the complement. The necessary host upper-degree bound is derived from the simple core and error bound, rather than added as an unstated premise.

The central coloring follows from the completed bounded-input theorem. Both odd leaf colorings follow from the one-apex shore theorem. Singleton-label restoration uses the same central color on each actual original copy, including edges between the two odd leaves. The generic retained-copy gluer is used; the proof does not assume that the even shore has empty cut in this branch.

The residual coloring is transported through the exact edge-copy equivalence to the surviving original-copy subtype. Restoration assigns disjoint prefix and residual palettes, and `rounds ≤ h` identifies their total size with `h`. The final conclusion therefore concerns the original host and all its copies.

## Source scope and accounting

The semantic-review document correctly identifies a **three-core subcase** of Proposition 4.16, whose pinned statement hash is `1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c`. The full proposition also contains four-core cases. No four-core compatible-circuit theorem, four-core terminal completion, full regular theorem, or main theorem is asserted by these new declarations.

The stated intended numbered coverage remains 48/69, with all 69 numbered assertion records unchanged. The document's full-audit and preservation paragraphs describe the required checks; this source review does not establish that those checks have run or passed. Genuine focused failures and subsequent successes remain in their recorded run directories. No proof source, existing theorem statement, audit file, coverage record, or root import was edited as part of this review.
