# Semantic review of the full four-odd-parts construction

**Status: semantic review and strict compilation of the full public theorem passed.** The strict check used `-DwarningAsError=true`. The complete project build and transitive axiom audit are recorded separately in [verification/results.json](../verification/results.json) and [verification/axioms.log](../verification/axioms.log). Their exact source and input hashes bind that evidence to the published checkpoint; this semantic review does not substitute for those checks.

Reviewed target: Lemma 4.15, `three:lem:four-odd`, in the pinned manuscript `Four_Robust_Component_Cases_2026-11-20.tex` (file SHA-256 `4605bdf3ee5b241a7b52dd59d08537fa0a439335cd6f119394cddd4609efffc1`). The inspected source is `Four_Robust_Component_Cases_2026-11-21.tex` (file SHA-256 `ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`); its Lemma 4.15 statement is byte-identical under the pinned inventory convention. The recovered statement hash is `95942bcc2f458912f740b61cecad49f74bcfe9e8679ec1a30e2819e039591eb0`, equal to the original inventory hash.

The review covers the statements, definitions, and argument composition in `Overfull/FourOdd/Basic.lean`, `Allocation.lean`, `PairPools.lean`, `Pools.lean`, `Capping.lean`, `CutBounds.lean`, `OriginalGraph.lean`, `MinorityPairing.lean`, `MatchingShapes.lean`, `Matching.lean`, `MatchingPreprocessing.lean`, `StarAssembly.lean`, `Star.lean`, `Relabeling.lean`, `RelabelGraph.lean`, `Quantitative.lean`, and `Theorem.lean`. The completed matching wrapper has also been reviewed: it constructs the actual minority pairing from the prepared cross-copy subtype, discharges the exact singleton counts, and attaches the already constructed complement decomposition. The full public theorem has now passed the strict build, including its integer, real-bound, ratio, and surplus-circuit statements.

## Exact input and output correspondence

The public statement is `Overfull.FourOdd.four_odd_parts_decomposition`.

| Manuscript item | Formal representation and check |
| --- | --- |
| Finite graph with every vertex of degree `h` | A loopless `Multigraph V E` with finite vertex and actual edge-copy types; `∀ v, G.degree v = h`. Proving the result for this model includes the simple-graph case. |
| No `h`-overfull set | `∀ X : Finset V, ¬ G.IsOverfull h X`. The proof derives the needed cut inequalities from this original-graph assumption. |
| Partition into four odd parts | A total label map `V → Fin 4`, with every fiber having odd cardinality. Fibers are disjoint and cover the vertex type by construction; odd cardinality also makes each of the four fibers nonempty. |
| Joining edges | `joiningCopies G label`, the exact original copies with distinct endpoint labels. `joiningGraph` restricts only the edge-copy type and retains the original vertex type and endpoints. |
| Boundary degree at most `a` | `∀ v, (G.degreeOn (joiningCopies G label) v : ℝ) ≤ a`. This is the degree among original joining copies, rather than the degree of a quotient label. |
| Prescribed perfect matching or three-edge star | `LabelForestShape F0`, which lists precisely the three perfect matchings and the four stars on four labels. |
| Every prescribed pair has at least `r0` copies | The cardinality of the actual pair pool in `joiningQuotient G label` is at least `r0`, for every pair in `F0`. |
| Forest-cut supply inequality | The public theorem includes `r0 * forestCutCount F0 A ≤ (joiningCut G label A).card` for every label shore `A`. The new proof needs only the individual pair supplies, so this additional manuscript hypothesis is safely redundant. |
| Two sufficiently small ratios | The public theorem supplies the absolute sufficient bound `1/1000` for both `a / h` and `((h : ℝ) - r0) / h`. |
| Exactly `h` primary matchings | `Decomposition.primary_card = h`, and every primary member is an actual matching whose projection is injective and has one of the specified forest shapes. |
| Surplus matchings project to circuits of length at most four | Every nonprimary part is an actual matching consisting of two distinct copies with the same projected label pair. `Decomposition.surplus_circuit` proves that it is a quotient circuit and has exact length two, hence length at most four. |
| Decomposition of all joining edges | Parts are nonempty and pairwise disjoint, and their finite union is `univ` in the joining-copy type. This is exactly all original joining copies. |

The quotient retains the joining-copy type. In particular, projecting two distinct original copies to the same unordered label pair does not collapse those copies. This is essential for the surplus two-edge circuits.

## Original cut assumptions are discharged

`CutBounds.lean` proves the original-graph cut consequences from regularity and the absence of overfull sets. The handshake identity gives cut parity. An odd shore has at least `h` crossing copies. Toggling an arbitrary vertex of an even shore produces an odd shore; the resulting cut identity proves that the original vertex contributes at most half of the even cut.

`OriginalGraph.lean` then identifies quotient degrees with original cuts of single label fibers, and identifies quotient cuts with original cuts of unions of fibers. The cardinalities and incident-copy degrees are transported through the injective map from joining-copy subtypes to original copies. Consequently:

- Every quotient label has degree at least `h` and degree congruent to `h` modulo two.
- The cut separating any two labels from the other two has even cardinality.
- Each original vertex contributes at most half of that cut.

The last condition is the decisive extra input for the matching case when the crossing pools are small. It is proved from the original no-overfull hypothesis, rather than assumed after truncation.

## Safe truncation and exact singleton quotas

`PairPools.lean` applies ordinary bipartite edge coloring followed by equitable balancing. A pool of `n` actual copies, with a prescribed singleton count `q`, is split into exactly `q` singleton copies and actual two-copy matching parts when `q ≤ n`, `n ≡ q` modulo two, and the degree bound is at most `(n + q) / 2`. The pair parts are disjoint and cover the exact complement of the singleton set.

The cap construction either retains the whole pool or retains `B` or `B+1` copies, preserving parity. It simultaneously constructs a matching-pair partition of every removed copy. Thus capping does not introduce an unchecked small leftover.

`Capping.lean` keeps the prescribed forest pools unchanged. The retained singleton-label cut bound follows in two cases: either every incident pool is unchanged, or one changed pool retains at least `B` copies and an incident prescribed pool supplies at least `r0`. The inequality `h ≤ r0 + B` is then sufficient. All pool parities and all discarded decompositions remain explicit outputs.

## Matching branch

The cross set is the actual cut between the two prescribed matching pairs. Its retained cardinality is even. Its half-incidence bound survives capping: if nothing changed, the original even-cut bound applies; if something changed, the retained cross set has at least `B ≥ 2D` copies and every original vertex still has degree at most `D`.

`MinorityPairing.lean` contracts only the smaller refinement class on each side of this actual bipartite graph. The contracted minority vertices have degrees at most half the number of cross copies; the remaining vertices retain their original degree bounds. König coloring and equitable balancing then provide actual two-copy matchings, with each minority copy in a different color class. Original matching validity is proved by mapping each original endpoint incidence into the contracted graph.

This construction yields exact mixed-row and mixed-column counts equal to the corresponding minima of the two original label totals. `MatchingShapes.lean` classifies every pair as opposite, shared-row, shared-column, or parallel. The first three types contribute primary pieces after the shared-row and shared-column types receive distinct compatible singleton copies. Endpoint avoidance is proved using the original degree bound and an injective allocation. Parallel types become surplus two-edge circuits.

The two distinguished pools are split using the exact quotas dictated by the mixed-side counts, before any augmentation. The remaining singletons have equal cardinalities and pair across disjoint label pairs. `Matching.lean` proves the exact total of `h` primary pieces and exact coverage of the retained cross and singleton copies. The preprocessing output also contains the decomposition of every other copy. No general admissible-transition theorem or residual compatibility hypothesis is required.

## Star branch

Let `t_i` be the retained size of each of the three off-star pools, `N` their sum, and `q = h - N`. The retained leaf cut identities and parities give a feasible singleton quota `q + t_i` in the opposite star arm. The singleton/pair theorem realizes that quota and accounts for every other arm copy as a surplus pair.

Exactly `t_i` singleton copies pair with the opposite off-star copies. The two label pairs are disjoint, which proves that each resulting piece is an actual matching and projects to a perfect matching. The remaining three arm pools all have cardinality `q`.

`StarAssembly.lean` uses Hall pairing twice on those three equal pools. Pairwise edge disjointness bounds every endpoint load by the original degree bound `D`; the strict inequality `12D < q` supplies the Hall margin. Each resulting three-copy piece is an actual matching, and its injective label projection is the entire star. The assembly includes every capped and unused pair, and proves the exact primary count `N + q = h`.

## Constants and boundary cases

Both constructions use `B = 2D + (h - r0)`, with natural subtraction. Under `D > 0`, `1000D ≤ h`, and `999h ≤ 1000r0`, the checked scalar bounds provide all cap reserves and endpoint-avoidance margins. In particular, the star proof establishes `3(B+1) + 12D < h`; the matching proof has the stronger convenient reserve `8(B+1) + 4D ≤ h`.

The real boundary parameter is handled with `D = ⌊a⌋₊`. Every integral boundary degree at most `a` is at most this floor, and `1000a ≤ h` implies `1000D ≤ h`. The proof therefore introduces no additive rounding loss. When `h > 0`, the original odd-cut lower bound forces a joining edge and hence forces `D > 0`; this positivity is derived, not added to the original-graph theorem.

The ratio statement explicitly assumes `h > 0`, as its ordinary mathematical ratios require. The integer and undivided real versions separately handle `h = 0`: a zero-regular loopless graph has no edge copies, and the empty decomposition has exactly zero primary parts.

## Review finding and scope

No semantic mismatch or circular conclusion assumption was found in the reviewed construction. The new proof is an alternative proof of the exact Lemma 4.15 conclusion, with a stronger surplus length bound. It does not establish the general compatible-circuit theorem, and it does not by itself establish the terminal factorization proposition or the main theorem.

Strict checks of `PairPools.lean`, `StarAssembly.lean`, `Star.lean`, the full matching wrapper, and `Theorem.lean` have passed. The six principal pool/star existence theorems have separately been checked to depend only on `propext`, `Classical.choice`, and `Quot.sound`. An independent check of `four_odd_decomposition_nat`, `four_odd_decomposition_real`, `four_odd_parts_decomposition`, and `Decomposition.surplus_circuit` likewise returned only those three standard axioms. The separate project-wide build, source-manifest checks, and full transitive axiom audit are recorded in `verification/results.json` and its accompanying complete logs; the recorded hashes identify the checked source and documentation.
