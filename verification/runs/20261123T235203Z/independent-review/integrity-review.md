# Independent integrity review: native star continuation

**The source and static integration review passed.** No mathematical defect was found in the eight new modules under their explicit hypotheses. All eight current source files match genuine successful strict target-build receipts and retained source snapshots. The complete frozen verifier, full transitive axiom audit, supplementary preservation checker, packaging, and public branch updates remain separate gates; this review does not infer their success.

This independent review wrote only to `/workspace/scratch/0f64d20031b0/native-star-review/`. It did not edit the candidate, run Lean, rerun any build, execute the preservation checker, or publish anything. The review’s source hashes, full public-proof inventory, exact receipt paths and hashes, and static integration observations are recorded in `integrity-review.json`.

## Reviewed candidate and predecessor

- Worktree: `/workspace/scratch/0f64d20031b0/overfull-native-star`.
- Run: `20261123T235203Z`.
- Verified local predecessor: `af8dca22ef67d66d0de3f6d89954d31f06a4d2fa`.
- Exact predecessor tree: `5ddefa9b77dfaf2d1cf09df1d7e2d4b541346a85`.
- Predecessor inventory: **2,507 tracked files, 12,811 audited proof declarations, and 1,979 completed-result mappings**.
- Numbered scope: **47 of 69 complete; full two-core Corollary 4.6 and the main theorem remain unproved**.

The prepared manifest correctly identifies the verified local predecessor and records `verified_local_publication_blocked_by_automatic_review_at_input_freeze`. Its public-commit field is not populated with the local hash. Later network receipts must establish the public correspondence independently. Publication status is not used to weaken a mathematical or preservation gate.

## Exact new source identities

The independent lexical public inventory and generated source manifest agree on **eight modules and 84 explicit public theorem/lemma declarations**. This count excludes private and generated support; only the actual full audit can determine their complete number and axiom dependencies.

| Module | Public proofs | SHA-256 | Strict receipt |
| --- | ---: | --- | --- |
| `CommonPalette` | 9 | `ee8740cb65855a3654df71dee2517b01f7e4315e236828b6138c516a2b86acaf` | `common-strict-01` |
| `IncidencePartition` | 16 | `e1e8e84a8e5c982de230137edea0ae8d6813cf7074194a48d83a3fe28f4948fa` | `incidence-build-01` |
| `NativeBalance` | 6 | `d358b54a4357990b840bb1ac2b532bd0308c91e08c18611edb3efe1d96e7d9f8` | `native-balance-03` |
| `ReserveInjection` | 11 | `f4e41178404a179fed082284157ea1636a6bc216a5ad1ae08ba3c4f9701402fc` | `reserve-02` |
| `StarAccounting` | 18 | `e0b7aa80906e77186e677cba6dfaebeb61050bcf47cc71e36a645d4e6b4af4fb` | `star-accounting-build-01` |
| `StarChoice` | 6 | `7cc6ee673227a937cbaa2f674684083fb2bcd22d74433ffe76743df19b6429fa` | `choice-available-01` |
| `StarExtension` | 12 | `9a8b0603d674615f7258599351b42c2aa1d5d86c5b520bd2b3bf6f11973a716e` | `extension-available-01` |
| `TwoStars` | 6 | `a8fd371129726216c4df1e5f65f841ae233aff477e7422ceea32589f0b23d86d` | `two-stars-build-01` |

For each listed receipt I checked the exact target command `lake build --wfail Overfull.NativeStar.<module>`, its passed status and exit 0, its actual final build-success marker, the recorded unchanged-input list, and byte equality between the retained source snapshot and the current file. The final `two-stars-build-01` receipt also records all eight current source hashes. Earlier failed attempts are present and have not been replaced by their later successful source text.

## Mathematical review

### Actual copies and original assignment

The reserve injection retains the original edge identity through the actual residual subtype. A parent matching’s `some σ` signature supplies a copy to the assigned old core; compression retains that exceptional incidence; reserve avoidance proves that it survives. Pairwise disjoint **boundaries**, rather than any unproved disjointness of parent matchings, give injectivity across reserve indices. Matching gives exactly one such copy per boundary, and the selected-family count uses actual pairwise-disjoint intersections.

The incidence partition uses the representative’s original assignment label on the later host. The joining, assigned-old-core star, and same-label exceptional pools are disjoint and cover the full incidence set. It does not silently recompute a residual representative or collapse parallel copies into neighbors. The internal exceptional bundle is separately counted and is never assumed to satisfy the old-core multiplicity bound.

The key native chain is derived:

`j_z + |star_z| + t_z = h`, `r ≤ |star_z|`, hence `j_z + t_z ≤ h-r ≤ D`.

The same-label two-exception bundle identification does not require its entire assigned fiber to contain only the two exceptions; it remains valid with an old core in that fiber. This avoids the inappropriate stronger premise of the older pair-fiber lemma.

### Protected traces and exact balance

Protected joining-freeness follows from an actual trace equality between a selected boundary and a joining class. Its hypothetical joining incidence would be the boundary’s unique assigned-star incidence, contradicting the disjoint partition. Merely counting selected indices would not suffice; the new theorem derives the actual selected-star cardinality from the disjoint reserve family.

The native balance theorem proves the protected-copy count and both color-image counts, then derives

`|remaining copies| = |remaining colors| = h-s-j_z-t_z ≥ h-s-D`.

Its remaining premises are explicit: the actual selected reserve traces and an injective coloring of the actual internal bundle avoiding protected and joining-used colors. The common-bundle theorem constructs such colors for the same-label two-exception case from both combined degree bounds. It imposes no false exceptional-to-exception bound `t≤b`.

### Available-only Hall budgets

The final choice and extension interfaces count row conflicts on `F.filter`, where `F` is the actual remaining palette. Protected reserve classes outside `F` cannot enter this row count. The global-load wrappers are valid stronger-premise consequences; the sequential theorem calls the available-only interface.

Column conflicts are injected into the actual blocked-copy pool counted by `starWeight`. The exceptional endpoint is handled separately by the explicitly required center-freeness on available colors. Asymmetric Hall then yields an actual equivalence and the endpoint-disjoint singleton insertion proves matching.

For two stars, the first center lies outside the second core and the second center lies outside the first core. These facts prove actual pool disjointness and that the first insertion cannot occupy the second center. The first star’s actual parallel-copy multiplicity controls the increase in available-color load; the second star’s parallel-copy multiplicity controls the increase in blocked-copy weight. The second Hall call therefore uses derived `D+b` and `h/8+b` bounds after the first insertion. The final theorem derives matching, pairwise copy disjointness, exact base-plus-two-pool coverage, unavailable-color preservation, center coverage on each available palette, and placement of every selected actual copy.

The theorem’s exact pool/cardinality and base initialization certificates remain explicit inputs. Its +2-copy/+4-support growth is relative to the initialized family, which may already include prescribed boundaries and a bundle. It is not automatically the final footprint bound relative to the earlier joining palette.

## Static integration and preservation review

The reviewed generated checker has SHA-256 `cc66c9a1d5ee609a349a79c834f017d592c8d6c74341a53f74e9ea8298bbb8bf`.

### Final publication-metadata delta

The final actual checker has the hash above. The previously reviewed checker was `e79cbc50d9dc26050e7c1792286ad960c5a37fdd0f3bf339879ce92f8c3e8892`. I independently reversed only the four publication-text substitutions shown by the retained executed preparer and its final version. The reconstructed old checker reproduces that earlier SHA-256 **byte for byte**. This establishes that the final delta affects exactly five lines: the publication-status string in the manifest consistency check and output metadata, one publication note, and two generated-report sentences.

**No proof or mathematical/preservation gate changed.** The publication metadata equality now requires the accurate blocked-by-automatic-review-at-input-freeze value. All other predicate text, proof/declaration preservation checks, frozen-input checks, exact verifier edits, axiom checks, result counts, and raw execution-log checks are unchanged. The prior pending-state preflight and the subsequent blocked-state preflight are both retained. The external JSON report records the exact substitutions, unified diff, source-preparer hashes, and both preflight hashes.

This is a read-only comparison, not a run of either checker. The complete audit, preservation result, package and any later publication require their own genuine receipts. The automatic review rejection is recorded as publication status; it is not a Lean failure or evidence that the new candidate was published.

I independently verified the following against the committed predecessor:

- `scripts/verify.py` equals the predecessor plus exactly the four recorded additive substitutions: new source-map registration, zero-numbered-assertion scope gate, complete declaration-map prefix, and result-map entry.
- `Overfull.lean` equals the entire preceding import prefix and documentation with exactly the two recorded NativeBalance/TwoStars imports inserted at the existing boundary. Their import closure covers all eight new modules.
- Every one of the **2,497 predecessor paths outside the explicit current-file allowance** is byte-identical. This includes all **562 preceding nonroot Lean files**, the unchanged stock `Audit.lean`, and all **13 preceding declaration maps**.
- The parsed coverage record differs only in its top-level scope string. All 69 assertion records, statement hashes, completion flags and the main-theorem flag remain unchanged.
- The new manifest has the exact eight current paths/hashes, 84 public declarations, zero completed numbered assertions, and honest local/public predecessor metadata.
- The checker pins 2,507/12,811/1,979; compares every preceding declaration’s name/module/axiom set and all preceding completed-result values; preserves prior declaration-map bytes and summary metadata; and requires new audited declarations to be exactly the new-module inventory.
- The checker requires actual source/input hashes, frozen candidate hashes and verifier-result hashes to coincide. It cross-checks the raw full audit, imported-module lists, strict build success marker, genuine command status, and exact stage-log concatenation. It does not accept a stale earlier audit as current verification.
- The full-run recorder is byte-identical to the preceding recorder except for the new source-snapshot directory. It still freezes the full input inventory and rejects changes during execution.
- The packaging script still requires an actual successful full verifier, a successful supplementary receipt tied to the exact checker/output/report hashes, unchanged checked bytes, the expected baseline head, and archive/bundle verification.

The initial documentation still described a public-only baseline preparer. I reported that discrepancy to the integration owner; the final guide now distinguishes the archived original review from the local-baseline adaptation. The original preparers and guide are retained as adaptation evidence. No mathematical or preservation gate was removed to make this correction.

## Concrete next native integration target

The next work should connect the conditional star assembly to the native weighted joining construction, with the original palette size `h` retained throughout.

| Branch or obligation | Existing entry points | Necessary connection |
| --- | --- | --- |
| Odd joining decomposition | `exists_twoOddJoining_decomposition_with_reserved_primary`, `primarySeed`, `primarySeed_extension_unique` | Seed all `h` primaries injectively; protected labels are the images of the forced reserve singleton primaries; derive count-one and seed-weight `≤4b≤h/8`. |
| Even joining decomposition | `exists_evenJoining_decomposition`, `EvenJoiningDecomposition` fields | Use empty seeds in the weighted grouping and the actual protected set in `Fin h`; do not shrink to `h-s` before applying the original weight threshold. |
| Weighted grouping | `WeightedPalette.exists_star_weighted_matching_grouping` | Supply at most two actual exceptional resources, degree/multiplicity/regularity inputs and piece capacity `|I|≤L(h-s-32D)`; retain per-class weight `≤h/8`. |
| Native reserve replacement | `reserveClasses_other`, `reserveClasses_at`, `reserveClasses_joining`, `reserveClasses_cut_eq` | Prove exact protected traces, then show the reserve-initialized class equals the weighted joining class at every available label. |
| Bundle initialization | Native common-bundle coloring and actual copy partition | Add the bundle only at its own image colors and prove matching/disjointness. All these colors are excluded from each remaining palette. |
| Final native star wrapper | `native_remaining_star_balance`, `exists_two_star_extension_on_available` | Instantiate both exact remaining pools and palettes, transfer available-only load/weight certificates, preserve protected boundaries and parity, and prove full exceptional coverage. |

A useful sharper footprint proof separates color cases. A protected color is its prescribed boundary, with at most three copies and six support vertices. An unprotected bundle-used color receives no star insertion because it lies outside both remaining palettes, so it adds only one edge. Any other color receives at most two star edges. With `L≥1`, these cases yield the intended final `6L+4` support bound relative to the weighted joining palette, rather than adding a crude bundle increment to the generic two-star increment. This case argument is prospective and is not a theorem claimed by this review.

Similarly, exact final copy coverage can bound the old-core color load by joining degree plus the two full star multiplicities, at most `D+2b`. The protected star copies and later remaining copies belong to the same actual full star pool; they should not be charged as independent additional families. Native parameter bounds, robustness transfer, actual robust matching completion, full two-core Corollary 4.6 and final factorization remain separate proof obligations.

The detailed next-stage contract and proof sequence are in `next-native-weighted-plan.md`. That document is prospective design only; it contains no newly compiled theorem or promoted assertion.
