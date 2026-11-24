# Semantic review of reconstructed ordinary-core factorization

This review concerns the recreated supporting proofs and the unchanged
recovered public wrappers. Compilation and transitive axiom evidence are
recorded separately by the strict verifier; this prose is not a substitute
for that evidence.

## Public statement preservation

`OrdinaryFactorization/Full.lean` is byte-identical to the recovered file.
Its public theorems quantify the positive error and order threshold before
the host graph and its complement coloring. The hypotheses retain the
original even host order, even sufficiently large robust core, bounded
exterior, regularity, density, small core deficit and colorable actual core
complement. The conclusion retains actual original multigraph copies.
The wrapper derives error nonnegativity and accepts any positive `α` by
using `min α 1` internally.

## Quantitative cut and palette

The recreated paired-cut theorem permits overlapping footprint families.
It does not choose a separate cut for each footprint. A finite weighted
expectation argument subtracts the probability of all bad orientations
and obtains one good cut balancing a positive fraction of the entire
family. The robustness parameter precedes requested error tolerances, and
the order threshold precedes the graph and the footprint family.

For a complement color class, regularity and palette saturation cover
every exterior vertex. Removing the class's internal core copies gives a
matching with an even core footprint of size at most the exterior size.
The recovered matching-split theorem constructs equal exterior shores for
each balanced footprint. Pigeonholing over actual exterior subsets gives
one split shared by enough original labels. The generous denominator
`2^(2*s+4)` absorbs both finite losses and supplies positive linear slack.
The first-group embedding is chosen after the reserved labels and avoids
them; no survival assumption is imposed on a prechosen arbitrary palette.

## Original-copy and residual consistency

The first-half construction retains original complementary labels and
uses the existing reserve repair to complete actual matchings. The
residual graph is the exact complement of those deleted copies. The
residual reserve proof uses the established pointwise preservation of
inherited labels and transports actual cut membership. The same reserved
labels and exterior split therefore apply to the graph being factored.

The selected-copy construction keeps every internal complementary copy
and every nonreserved exterior copy. At each exterior vertex the original
color map is a bijection onto the `k` colors, so the selected degree is
exactly `k-|J|`. Palette compression colors those exterior copies. Every
uncolored copy has both endpoints in the sparse core, allowing the proved
greedy extension theorem to color it with the same palette.

Equal augmented shore sizes, host regularity and a crossing unselected
graph imply equal selected degree sums. Equal exterior shore sizes and
exterior saturation remove the exterior contributions, giving equality
on the core shores. The balanced-coloring theorem then supplies balanced
small footprints with the required load bounds. Robust bipartite packing
constructs their completions. Every remaining copy crosses the same
augmented partition, so the existing completion theorem applies König's
theorem to the actual regular residue and reconstructs the whole host.

## Scope limits

This establishes the ordinary-core statement through the bounded exterior
route. It does not establish the general bipartite-core factorization,
the compatible spanning setup or absorber, the full fixed-pattern lemma,
the two-core branch of Corollary 4.6, terminal Proposition 4.16, or the main
theorem. The numbered inventory remains the original 69 statements.
