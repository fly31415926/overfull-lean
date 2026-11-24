# Next proof target after bounded-input factorization

Prepared on 2026-11-24 by the terminal-route agent. This is a read-only source and interface assessment, not a new Lean verification result. No repository source was changed and no build was run for this assessment. The note is outside the repository so that it cannot change the parent agent's frozen audit inputs.

## Recommendation

The closest unfinished numbered assertion is **Proposition 4.16**, `three:prop:terminal`. Its full statement is the terminal factorization of the graph produced by Lemma 4.13. It includes **both three and four cores**. The new `Overfull.bounded_input_one_factorization` supplies the previously missing final factorization of a central graph with **two robust cores and two contracted vertices** in the four-core, exactly-two-odd case.

This does **not** make Proposition 4.16 a short consequence of Corollary 4.6. Two separate tasks remain:

1. Actual boundary-prefix completion, simultaneous contractions, cut certificates, and label-preserving reconstruction must be composed on the original edge copies.
2. The four-core all-even and exactly-two-odd branches still require a compatible circuit partition for an admissible Eulerian **four-label** quotient. The repository proves the at-most-three-label theorem, ordinary four-label Eulerian circuit decompositions, and several safe-deletion kernels. It does not prove the required four-label compatibility theorem under the original half-cut hypotheses.

The best first implementation target is consequently a **uniform terminal theorem for exactly three cores**, with no decomposition, coloring, matching completion, or residual factorization supplied as a hypothesis. All its required combinatorial existence theorems are available. Its contraction and reconstruction infrastructure is reusable in the four-core branch that now benefits from the completed two-core case of Corollary 4.6. It should be reported as a proved subcase of Proposition 4.16, not as completion of the full numbered assertion.

## Source identity and current coverage

The actual manuscript read for this assessment is:

`/workspace/scratch/f234ea3483b7/overfull_revision/baseline/Four_Robust_Component_Cases_2026-11-21.tex`

Its SHA-256 is `ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.

The exact statement blocks were compared with the pinned hashes in `docs/coverage.json`. The relevant matches are:

| Assertion | Label | Exact statement SHA-256 |
| --- | --- | --- |
| Lemma 3.1 | `single:lem:coloring` | `e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe` |
| Corollary 3.2 | `three:cor:critical` | `64b4da9bb77675dc01c8895e7b9fed92dd289050eae127f581b2aa1be8d1c747` |
| Corollary 3.4 | `mixed:cor:critical` | `a10bd00d11bfe929bdb4aacd0aa5afeca45abd3bcf9762d08dc19f8d0a3d2d36` |
| Theorem 3.5 | `bip:thm:main` | `59ed7a06b9e3942cf1229f57310dab66368e2883b757f816982ca46988a5cb3b` |
| Corollary 3.6 | `bip:fac:bipartite-case` | `8efee731304f329a622425f0d64dc19a1096cf6b1d7b19724b7a6bde211a74d8` |
| Corollary 3.7 | `pad:cor:all` | `0f000713ac09b666b85374553a5e41a7009051198603a9bb1fc274755f9b9a2f` |
| Proposition 4.16 | `three:prop:terminal` | `1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c` |
| Theorem 4.17 | `three:thm:regular-four` | `b271893680e87b1c06c35172a138050dbf84009964eb618dce53c53ba595e322` |

The current coverage file identifies 4.13, 4.14, and 4.15 as complete, and 4.16/4.17 and the listed section 3 assertions as unfinished. The parent is separately auditing the new Corollary 4.6 completion. This assessment supplies neither a full-audit result nor permission to promote further numbered assertions.

## What Proposition 4.16 actually assumes

The printed statement is:

> The graph obtained in Lemma 4.13, which is covered by its q parts, has a one-factorization.

The preceding reduction, not an arbitrary unspecified terminal certificate, supplies its mathematical hypotheses. In explicit form the terminal graph has:

- Even order, is simple and h-regular, has no h-overfull set, and has q disjoint covering parts with q in {3,4}.
- A simple spanning robust core in each part, of minimum degree at least h-a.
- Fixed positive lower bounds for h and every part order relative to the ambient order; fixed robust parameters with sufficiently small range.
- Arbitrarily small a/h, with the robustness chosen before that requested error.
- If all four parts are odd, a perfect matching or three-edge star F0 on their labels and an integer r0 with h-r0 arbitrarily small relative to h. Every pair of F0 has at least r0 actual joining edges, and every union of parts has cut size at least r0 times the F0 cut count.

The exact Lean output is `Overfull.CircuitPatterns.FrequentPatternResult`, defined in `Overfull/CircuitPatterns/Result.lean`. Fields include the actual residual `G`, degree `h`, deletion sequence `N`, `rounds`, `graph_eq`, `degree_eq`, `perfect`, `present`, `regular`, `safe_prefixes`, `no_overfull`, `degree_positive`, `retained_degree`, enlarged `U`, embedded cores `H`, `core_enlargement`, `core_disjoint`, `cover`, `core_embed`, `error_bound`, `core_degree`, `core_robust`, `reserve`, `reserve_error`, `code`, `forest_shape`, `pair_supply`, and `cut_supply`.

`Overfull.circuit_frequent_boundary_pattern` in `Overfull/CircuitPatterns/Frequent.lean` returns that record. In particular, it chooses `νout > 0` before `∀ δ > 0`, and only then chooses the input tolerance and order threshold. A terminal composition must retain this order. Its retained-degree bound is `k / (3 * patternBound t) ≤ h`. Thus an initial density α gives terminal density at least `α / (3 * patternBound t)`; enlarged parts retain at least their original density.

## A concrete first theorem to implement

Proposed new theorem name, not an existing declaration:

`Overfull.three_core_terminal_one_factorization`

Proposed new module, not an existing file:

`Overfull/Terminal/ThreeCore.lean`

Use the original simple-graph host to reuse the existing arbitrary-finite-core completion theorem. A suitable theorem schema is:

```
fix α > 0, ν > 0, ν ≤ τ, with τ sufficiently small relative to α
∃ ε > 0, ∃ n0 > 0, ∀ finite V and simple graph G on V,
  ∀ U : Fin 3 → Finset V, ∀ H i : SimpleGraph (U i), ∀ h : Nat, ∀ a : Real,
  n0 ≤ |V|, Even |V|,
  G is h-regular, α|V| ≤ h, G has no h-overfull set,
  the U i are disjoint and cover V, and α|V| ≤ |U i|,
  H i embeds into G[U i], H i is robust (ν,τ),
  degree(H i) ≥ h-a, 0 ≤ a, a+1 ≤ ε|V|
  → an exact partition of all original G edge copies into h perfect matchings.
```

The eventual numerical bound on τ should be chosen from the packing and factorization interfaces; it should not be advertised as already proved. The version above is stronger than the three-core terminal output needed from 4.13 because it does not use any forest supply.

To apply it to `FrequentPatternResult`, set the density to `α/(3*patternBound t)`, choose the requested δ after the terminal tolerance, and raise the original order threshold. Since the terminal host is simple, `h ≤ |V|`; choosing δ at most half the terminal ε and making `1 ≤ ε|V|/2` converts `a ≤ δh` into `a+1 ≤ ε|V|`. This is a legitimate quantifier composition and does not fix δ after observing the graph.

### Three-core all-even branch

The actual parity-retaining decomposition already exists:

- `Overfull.FourOdd.exists_evenJoining_decomposition` in `Overfull/ResidualPalette/PaletteParity.lean` takes the original host regularity, no-overfullness, at most three labels, and even fibers.
- It constructs `EvenJoiningDecomposition`: nonempty actual matchings of at most three copies, pairwise copy disjointness, exact joining-copy coverage, and even cut size at every part for every piece.
- `EvenJoiningDecomposition.exists_palette` in `Overfull/ResidualPalette/JoiningGrouping.lean` groups them into any chosen number r of palette classes satisfying the explicit capacity inequalities, with exact coverage, matching, parity, support size and vertex-load bounds.

Choose `r = ceil(h/100)` and a natural incidence bound from the real core error, then derive the palette inequalities from sufficiently small a/h. The required finite-family packing engine is already `CircuitPatterns.exists_boundary_completion` in `Overfull/CircuitPatterns/Completion.lean`, used with empty Z. It accepts arbitrary finite core index I, actual disjoint joining matchings, even uncovered core footprints, footprint size bounds, and certified core rules. `ForeignPackingSchedule.exists_epoch_parameters` supplies the uniform rules and output robustness.

After completion/deletion, prove the residual has no joining copies, each part has even order, and each induced host has exact degree h-r with robust residual core. `NativeTerminal.inducedHost`, `inducedCore`, and their regularity/robustness lemmas provide the host transport. The stronger `NativeCore.exists_uniform_independent_exterior_factorization` with s=0 can factor each component directly, without deriving a new no-overfull certificate. Alternatively Corollary 4.6's one-core branch applies after proving no-overfullness.

### Three-core exactly-two-odd branch

`Overfull.FourOdd.exists_twoOddJoining_decomposition` in `Overfull/CompatibleCircuits/TwoOddDecomposition.lean` already constructs exactly h primary actual matchings and surplus even pieces. It records:

- Exact original joining-copy partition and disjointness.
- Primary pieces of at most two copies; surplus pieces of at most three.
- Exactly one crossing copy at each odd part in each primary.
- Correct per-part odd/even parity in each primary and even per-part cuts in each surplus.

Select h-r primary pieces to retain. `TwoOddJoiningDecomposition.exists_protected_palette` in `Overfull/ResidualPalette/ProtectedGrouping.lean` preserves every selected primary as an entire palette class, without surplus. Complete/delete the other r classes. Its margin is `6*D + Q.card < h`, so with `Q.card=h-r` the mathematical requirement is `6*D<r`. No star-weighted palette or exceptional-star resources are needed for this terminal graph.

The residual joining copies are exactly h-r primary pieces. Construct the central host by contracting the two odd parts to distinct vertices and discarding their internal copies, while retaining every internal copy of the one even part and every joining copy. This **simultaneous central contraction** is not supplied by the new single-shore host definitions and remains real implementation work.

Prove its h-r regularity, even order, embedded robust core, and no-overfullness. The whole-union/toggle proof needs only the supplied parity and matching certificates: any union separating the two contracted vertices has at least one crossing copy from each primary, and any even union has an even number of crossings per primary, with at most one incidence at each retained core vertex. A separately formalized connected-path theorem is unnecessary for these inequalities. `Overfull.SmallCuts.small_cut_lemma` then reduces a possible violating odd cut to a whole union changed at at most one core vertex.

The central host has one robust core and two other vertices, so `Overfull.bounded_input_factorization`/`bounded_input_one_factorization` apply. Each odd leaf is factored using `BoundaryExtension.contract`, `contractCore`, and the one-apex/independent-exterior theorem. Restore its prescribed labels using `BoundaryExtension.exists_singleton_boundary_extension`.

### Reconstruction common to both branches

The new general `NativeTerminal.exists_glued_retained_coloring` in `Overfull/NativeTerminal/ColoringGlue.lean` works for an arbitrary covering family of shores. It asks for equality on each common original copy; it does not identify parallel edges by their endpoints. It can glue all three or four leaf/central restrictions once the central-contraction pullback is constructed.

`NativeTerminal.reassembledColoring` and `exists_reassembled_one_factorization` in `Overfull/NativeTerminal/Reassembly.lean` restore actual deleted matching copies. Since the arbitrary-core packing result is currently phrased for `SimpleGraph.Subgraph` and `afterDeletions`, a bridge from those deletions to the actual multigraph residual-copy subtype is still needed. Existing `Replacement.embeddedCore` in `Overfull/Replacement/Graph.lean` and `ForceMatching.embeddedCore` in `Overfull/ForceMatching/Residual.lean` provide simple-core embeddings; they do not remove that residual identity obligation.

The resulting theorem must derive the remaining matching family, contraction colorings and overlap labels. Supplying any of them as hypotheses would produce only a conditional reconstruction lemma.

## What remains for all four cores

| Terminal case | Available combinatorics | Actual remaining work |
| --- | --- | --- |
| Four even parts | Quotient half-cut admissibility and even degrees can be derived; ordinary four-label Eulerian circuit partition exists | Compatible partition existence under original incidence classes; grouping for pieces of size at most four; completion, restriction and reconstruction |
| Exactly two odd parts | Actual virtual augmentation and original-host admissibility tools exist | Four-label compatible partition; primary/surplus lift and exact residual; central host with two cores plus two vertices; cut proof; apply the newly complete Corollary 4.6; leaf labels and gluing |
| Four odd parts, no dominant center | Full `FourOdd.four_odd_parts_decomposition`; full `Overfull.boundary_extension` | Prefix grouping/completion; transport singleton/triple boundary coloring and positive singleton reserve to each residual core; glue extensions |
| Four odd parts, dominant center | Same full four-odd decomposition; general core completion; one-core factorization | Complete/remove non-center colors; central contraction to one robust core and three independent vertices; exact regularity and core transport; singleton leaf restoration and gluing |

The available four-odd theorem is `Overfull.FourOdd.four_odd_parts_decomposition` in `Overfull/FourOdd/Theorem.lean`. It takes the original host conditions, actual pair supplies and forest-cut supplies, and explicit ratio bounds `a/h ≤ 1/1000` and `(h-r0)/h ≤ 1/1000`. It constructs exactly h primary forest-shaped actual matchings; every surplus part is a two-edge circuit. Its underlying stronger version needs only the pair supplies. Thus this case does not need a general four-label compatible-circuit theorem.

`Overfull.boundary_extension` in `Overfull/BoundaryExtension/Full.lean` is the full prescribed singleton/triple extension and requires a positive linear number of singleton colors. In the nondominant case the proof must establish that number from the center counts; it cannot use just the fact that every color has size one or three.

The dominant-center central host has **independent** exterior vertices. The stronger `NativeCore.exists_uniform_independent_exterior_factorization` with s=3 eliminates the manuscript's separate central no-overfull argument in this branch. The same theorem handles every singleton-apex leaf. This simplification is already justified by an existing proved interface, rather than assuming the terminal factorization.

For four-label grouping, `NativeReserve.exists_bounded_palette_extension` in `Overfull/ResidualPalette/PaletteGrouping.lean` is already parameterized by an arbitrary conflict-degree bound B. It can be reused with the derived `8*D` bound. The specialized `exists_bounded_matching_grouping` and `EvenJoiningDecomposition` currently hard-code piece size at most three; they require a generalized wrapper or a new four-copy variant. This is bookkeeping around a proved greedy extension, separate from the unproved compatible-partition existence.

A suitable separate combinatorial target is a four-label analogue of `Multigraph.exists_compatibleCircuitPartition_of_card_le_three` from `Overfull/CompatibleCircuits/AtMostThree.lean`, accepting **only** even degrees and `AdmissibleOn` for the actual incidence classes. `Overfull/CompatibleCircuits/FourLabel.lean` supplies ordinary circuits and preserves compatibility when the whole input is already compatible; that stronger input is not implied by quotient half-cut admissibility. Safe-deletion and small-kernel lemmas likewise do not already constitute the missing theorem.

## Why the section 3 assertions are not immediate

Lemma 3.1 assumes a simple, possibly nonregular graph of maximum degree Δ≥n/4, one robust core of order at least n/4, no Δ-overfull set, and `a+|Z|+1≤εn`. Here Z can grow linearly with n; it is not bounded by two or three. The already proved `Overfull.robust_auxiliary_completion` in `Overfull/AuxiliaryCompletion.lean` makes an even regular host with an additional robust core. It leaves the original Z in place. Corollary 4.6 therefore cannot be applied directly to that host.

There is a useful longer route avoiding the four-label obstruction: a complete three-core terminal theorem can be composed with `Overfull.foreign_edge_reduction`, `Overfull.bounded_exceptional_absorption`, and `Overfull.circuit_frequent_boundary_pattern` to prove the three-core subcase of regular Theorem 4.17. Auxiliary completion then gives the q=2 subcase of ordinary Theorem 1.2, which is sufficient for the manuscript proof of Lemma 3.1. This would still require the actual parameter composition and restriction/reassembly proofs; it is not an existing numbered closure. It may be the best route to a further complete numbered assertion if the four-label combinatorics proves lengthy.

Corollary 3.2 excludes all three ordinary critical outcomes and depends on more than the q=2 ordinary branch. Corollaries 3.4 and 3.6 and Theorem 3.5 involve a robust bipartite core or mixed ordinary/bipartite structure, so the ordinary-core bounded-input theorem does not furnish their main factorization. Corollary 3.7 combines all five exclusions. None follows just by instantiating the new theorem.

Theorem 4.17 is the natural next full theorem after Proposition 4.16: the foreign-edge reduction, bounded-exceptional absorption and frequent-pattern reduction are already available. Its remaining outer work must choose a positive tolerance function for each eventual exceptional bound **before** the absorption thresholds select that bound, preserve robustness through those choices, and reassemble all actual deletions. The existing quantifier order of the reduction interfaces supports that construction, but it has not been carried out here.

## Suggested division of the next implementation

1. **Three-core prefix and parameters:** construct the actual even/two-odd palettes, run arbitrary-core boundary completion, and expose the exact residual joining-copy identity and robust residual cores. No final coloring input.
2. **Central contraction and gluing:** define a copy-preserving contraction of two disjoint odd shores, prove regularity/core transport and the whole-cut/toggle inequalities, derive no-overfullness, apply bounded-input, and pull back the central labels to the odd leaf boundaries.
3. **Four-label combinatorics, independently:** prove the admissible Eulerian four-label compatible partition theorem. Until this is done, all-four-odd and all-three-core results should be tracked as subcases only.

The immediate first two tasks can proceed without awaiting the third. They should culminate in a genuine theorem under the original three-core terminal hypotheses and a focused audit, followed by an honest coverage entry for that subcase. Full Proposition 4.16 promotion requires all four parity cases and the outer application to the actual Lemma 4.13 result.
