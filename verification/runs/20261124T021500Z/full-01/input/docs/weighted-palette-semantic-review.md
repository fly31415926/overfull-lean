# Semantic review: weighted palette ingredients

## Result and scope

Read-only review completed on 2026-11-23 after the successful recorded strict build of `Overfull.WeightedPalette.Grouping` at 23:12:14 UTC. No semantic defect was found in the five source modules identified below. Their hypotheses support their stated conclusions, including the relevant zero, empty, and equality boundary cases.

This review examined theorem statements, definitions, proof structure, exact source hashes, and the genuine retained focused compiler/build receipts. It did not edit Lean sources, rerun a full build, or perform a new axiom audit. The reviewer previously implemented `Loads.lean`; the other four modules were reviewed as a nonauthor. Kernel compilation is separate evidence from this semantic assessment.

The baseline public commit is `c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2`. These modules add weighted grouping and finite Hall ingredients. They do not complete actual exceptional-star insertion, native parity/reserve wrappers, robust core completion, factorization, Corollary 4.6, or the main theorem.

## Reviewed source identities

| Module under `Overfull/WeightedPalette/` | SHA-256 | Public theorem declarations | Definitions |
|---|---|---:|---:|
| `Loads.lean` | `9581f824693839be24c8dbc880516d76019238412700253bc3704273fb0fa1b4` | 18 | 2 |
| `Extension.lean` | `c01cbd4e88b1800b5d5cc495ba2e7348686972e9e633e7f7330e2d78e39411ac` | 1 | 0 |
| `StarWeights.lean` | `d0e5473bdba64dc65c08bb83fad14d3f14b5549603f4c4bff31be91d0aa8ae2f` | 17 | 2 |
| `AsymmetricHall.lean` | `89f1818188bf9677304fa264dbf4ae0f2e22e8079353bf73630bace9dc3425ea` | 3 | 0 |
| `Grouping.lean` | `3f1d6ff5e30f6f3fd7b20274177b3c9376c0215dacbce3e01e33cc552b187944` | 2 | 0 |

The source-level inventory is 41 public theorems and four definitions. This inventory is not a count of generated/private declarations. No `sorry`, `admit`, `axiom`, or `unsafe` token occurs in these five sources.

## 1. Load accounting and zero cases

`paletteWeight A c w i` sums the natural-valued item weights in the actual color fiber inside `A`. `paletteWeight_sum` partitions the original total exactly. Monotonicity is justified by nonnegative natural weights. The insertion/update lemmas explicitly require the inserted item to be absent from the previous domain and preserve all previous assignments there.

`overloadedPalettes A c w q W` uses the threshold `W-q`, with natural subtraction. Every member consumes at least `W-q+1`, which is always positive. Consequently the generic overload cardinality theorem is valid even without `q <= W`. That hypothesis is nevertheless necessary for interpreting an available color as having room for a new item of weight at most `q`; `Extension.lean` explicitly supplies and uses it.

For the specialization `b <= D` and `128*D <= h`, the natural-number proofs establish `6*b <= h/8` and the strict inequality `h < 13*(h/8-6*b+1)`, retaining every remainder modulo eight. No real division or hidden positive denominator is used.

When `D=0`, a total-weight bound by `D*h` forces zero total weight, and the overloaded count is zero. When `h=0`, these arithmetic hypotheses force `D=b=0`; the threshold, gap, and Hall arithmetic statements remain true. The theorem asserting a strictly positive protected margin separately requires `0<h`. A coloring with codomain `Fin 0` can only be supplied on an empty domain, so the fiber identities do not assert the existence of an impossible coloring.

## 2. Dynamic extension counts seeds and protects only new pieces

`exists_weighted_palette_extension` requires `P` to be a subset of the complete target set `T`. Every resource total is bounded on **all of `T`**, including the seeds. At an induction stage, the currently colored domain is `A=P union U`, which is proved to lie in `T`; therefore the partial total is bounded by the same genuine full total. No seed weight is omitted or assumed to be free.

The seed certificates explicitly cover properness, the number of seed items per color, and the seed weight per resource/color. New-item weight bounds apply only to `T \ P`, as intended. Seed items may use protected labels in `Q`; only surplus items are required to avoid `Q`. The induction preserves every seed label and excludes `Q` at every new insertion.

The forbidden palette is the union of endpoint-conflict colors, all protected labels, and the dynamically overloaded colors for every resource. Its cardinality is bounded by `B + Q.card + card(resource type)*K`. The separate item-count capacity argument supplies a color strictly below capacity. The resource update then uses the old load at most `W-q`, the new item weight at most `q`, and `q<=W` to retain load at most `W`.

The strict margin excludes `h=0` from this existence theorem. A zero capacity `L=0` forces `T` empty, so no nonempty insertion is claimed in that case. An empty resource type is allowed; all resource obligations and its contribution to forbidden colors are then empty/zero. The hypotheses are sufficient conditions, not assertions that every possible trivial coloring must satisfy the strict margin.

## 3. Star weights preserve original copy identities and old-core endpoints

`starBlockedCopies G z U M` filters the actual `exceptionCorePool G z U` by whether `G.otherEnd z e` lies in the support of `M`. Pool membership already asserts incidence at `z` and membership of that other endpoint in `U`. Thus merely occupying the exceptional endpoint `z` does not charge the whole star.

The equality with `G.edgesTo z (U intersect support M)` and `starWeight_eq_sum_parallel` show that every original parallel copy is counted separately. The local bound assumes the actual multiplicity `(G.parallelEdges z v).card <= b` at each `v` in `U`; it does not replace multiplicity by a count of distinct neighbors. Three-copy pieces cost at most `6*b`; two-copy primary pieces cost at most `4*b`.

The total-weight double count sums, for each original star copy, the number of pieces occupying that copy's old-core endpoint. Edge-disjointness and containment in `S` bound this support load by the actual degree in `S`. The resulting total is at most `D` times the actual star-pool size, and hence at most `D*h` under the explicit degree cap at `z`.

`starBlockedCopies_biUnion` identifies the blocked-copy set of an entire union exactly with the union of the piece blocked-copy sets. Its cardinality is at most the sum of their cardinalities, even if supports overlap. `starWeight_groupedCopies_le` therefore controls the **whole grouped color class**, not merely individual small pieces. No matching or disjoint-support assumption is needed for this upper bound.

These are valid for arbitrary finite `U`; native old-core disjointness and the derivation of the multiplicity cap from core-complement error are later instantiation tasks. The module does not claim to have already supplied those native inputs.

## 4. Actual-copy grouping bridge

`exists_star_weighted_matching_grouping` derives item and total resource weights from the actual `starWeight` definitions and incidence hypotheses. All indexed pieces, including seeds, contribute to its total. It allows at most two resources, so their overload contribution is at most `26*D`; together with endpoint conflicts this gives the conservative protected bound `Q.card + 32*D`.

The capacity inequality is transferred in the correct direction: the exact forbidden-color bound `6*D + Q.card + card(resource type)*(13*D)` is at most the conservative bound. Its available gap is consequently at least the gap used in the supplied capacity assumption. Natural subtraction is handled explicitly by the proof.

The output combines the dynamic load bound with `starWeight_groupedCopies_le`, obtaining the actual whole-class bound `h/8` for each resource. Existing actual-copy grouping lemmas give matching classes, pairwise edge-disjointness, preservation of the union of all original pieces, class size at most `3*L`, support size at most `6*L`, and vertex color-load at most `D`.

Protected classes are identified exactly with the union of their prescribed seed pieces by `groupedCopies_eq_seed_on_protected_color`. Thus an unseeded protected label remains empty, and a protected singleton seed receives no surplus. The equality alone does not select native reserve boundaries or prove any parity statement.

The theorem preserves the union of `M`; it does not assert that this union equals `S` or all joining copies. Such coverage, seed properness/count/weight, native reserve alignment, and joining-cut parity must still be provided by the relevant decomposition wrapper. The explicit seed resource bound is an input certificate, not a circular assumption that all surplus pieces have already been grouped.

## 5. Asymmetric Hall, empty sides, and equality thresholds

`exists_equiv_of_asymmetric_conflicts` is valid at the non-strict boundary `a+b=m`, where `m` is the common finite order. Every row has at least `m-a >= b` allowed partners. For a nonempty set of rows of size at most `b`, one row supplies enough neighbors. For a larger set, every column has a neighbor because a column has at most `b` forbidden rows. The explicit empty-set branch establishes the remaining Hall case.

Equal empty types are permitted. The bound `a+b<=0` then forces `a=b=0`, and the finite Hall/equivalence construction is still valid. Cases `a=0` or `b=0` and equality in the size bound do not require a strict inequality or an inhabited type.

`exists_star_equiv_of_conflict_bounds` remains an abstract relation theorem. It explicitly requests balanced finite sides, the lower bound on their common cardinality, and both actual conflict bounds. It does not silently assume that the genuine remaining star-copy set and genuine free-color set have already been shown to satisfy those inputs.

## Genuine focused verification evidence inspected

The final source of each module has a retained successful recorded strict build:

| Receipt directory under `development/` | Strict build target | Result |
|---|---|---|
| `loads-build-001` | `Overfull.WeightedPalette.Loads` | Exit 0; 3,163 jobs |
| `extension-build-001` | `Overfull.WeightedPalette.Extension` | Exit 0; 3,164 jobs |
| `star-002` | `Overfull.WeightedPalette.StarWeights` | Exit 0; 3,173 jobs |
| `hall-002` | `Overfull.WeightedPalette.AsymmetricHall` | Exit 0; 3,106 jobs |
| `grouping-build-001` | `Overfull.WeightedPalette.Grouping` | Exit 0; 3,176 jobs |

All five receipts record `inputs_changed_during_command: []`, and their target source snapshots match the hashes above. Earlier development snapshots correctly preserve earlier revisions; those differences do not retroactively invalidate their recorded attempts. In particular, the unsuccessful `loads-001` parsing attempt remains genuine retained evidence, followed by the successful corrected check and strict build.

## Remaining proof obligations

The proved ingredients now include dynamic multi-resource palette extension, the actual-copy weight bounds, the actual matching-grouping bridge, protected seed-union preservation, and a suitable asymmetric Hall theorem. The following remain outside their conclusions:

1. Derive the actual remaining star-pool partition and the combined bound `joining_degree(z) + shared_internal_bundle_size <= h-r` from surviving reserved assigned-core incidences.
2. Choose colors for the actual shared internal exceptional bundle while preserving every prescribed reserve color.
3. Establish the exact equality between each remaining star-copy count and its exact current free-palette count after removing all prescribed and shared-bundle copies/colors.
4. Instantiate the two Hall relations with those actual finite sets, construct the second star after the first, and prove the resulting matching/coverage/disjointness/prescription statements for their actual unions.
5. Supply native odd/even primary seed certificates and obtain weighted joining palettes with the required exact cut parity and reserve alignment.
6. Assemble the native star completion, final footprint/load/uncovered-core parity interfaces, robust core completion, factorization, and reconstruction.

No completed numbered assertion or main-theorem status is inferred from these ingredient results alone.
