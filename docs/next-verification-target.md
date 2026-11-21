# Next verification target: boundary extension and terminal factorization

The continuation after the frequent-pattern reduction is **Lemma 4.14**,
label `three:lem:boundary`. The public reduction is
`Overfull.frequent_boundary_pattern`; its implementation and precise
scope are documented in [frequent-pattern.md](frequent-pattern.md).
The definitive counted status is in `verification/results.json` after
the strict build and transitive axiom audit. A source declaration or this
continuation note does not by itself certify a manuscript assertion.

**The main theorem remains unverified.** In particular, the frequent
pattern's actual residual is not yet supplied with a one-factorization.
Do not use the later terminal proposition as a proved input when extending
the current work.

## Source correspondence

The numbered inventory remains pinned to
`Four_Robust_Component_Cases_2026-11-20.tex`. The complete statement
blocks below were compared with
`Four_Robust_Component_Cases_2026-11-21.tex` and have identical hashes.

| Assertion | Label | Statement SHA256 |
| --- | --- | --- |
| Lemma 4.13 | `three:lem:pattern` | `557d62e4c4ab7c00ac7cc29fa403d80601a2b9851e7c7eb62cdeb4caa1d40c3b` |
| Lemma 4.14 | `three:lem:boundary` | `67baedd4ae2e0451a8842fd27ea0976f50db94c9054eacd2f5dd40ce2cfa21e3` |
| Lemma 4.15 | `three:lem:four-odd` | `95942bcc2f458912f740b61cecad49f74bcfe9e8679ec1a30e2819e039591eb0` |
| Proposition 4.16 | `three:prop:terminal` | `1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c` |
| Corollary 4.6 | `three:lem:bounded-input` | `86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26` |

## Required conclusion of Lemma 4.14

The input is an odd core `U` of sufficiently large order `m`, an ambient
graph with degree `d` at every vertex of `U`, a small core error, and a
proper `d`-coloring of the actual boundary of `U`. Each boundary color has
one or three edges; at least `γm` colors have one edge. The required output
is an actual extension of that prescribed coloring through the core, with
all original boundary color labels preserved. It is not enough to prove
that the uncolored core can be colored independently.

The positive density and degree reserve, ordinary robust parameters,
initial error tolerance, and order threshold must have their stated
uniform order of dependence. The low-degree vertices outside `U` are not
required to make the whole ambient graph regular.

### Suggested implementation sequence

1. **Represent the actual boundary coloring.** Retain its edge copies,
   labels, properness at both ends, and the partition of colors into the
   size-one and size-three classes. Derive the bound on each core vertex's
   boundary incidence from the embedded core degree.
2. **Complete the size-three classes.** Their three covered core vertices
   leave even uncovered order because `U` is odd. Apply the proved adaptive
   ordinary packing with a reserve of at least `γm`. Derive the footprint
   and cumulative-incidence conditions; do not assume admissibility of
   every intermediate input. Each completed color saturates `U`, although
   the outside vertices need not all be saturated.
3. **Construct the one-core contraction with edge copies.** Keep the exact
   remaining edges having an end in `U` and identify all outside ends to a
   new vertex `z`. The result has even order and is regular of degree equal
   to the number of remaining size-one colors. Several boundary edges may
   become parallel edges, so use the actual multigraph model. Retain a
   bijection between these edge copies and the labeled original boundary.
4. **Prove no overfull set in the contraction.** Supply the actual residual
   robust core and the current degree/error bounds to the proved small-cut
   theorem. With one exceptional vertex, every potentially offending odd
   cut reduces, up to complement, to a singleton cut. Its size equals the
   regular degree. The no-overfull conclusion is to prove, not to place in
   the contraction's definition.
5. **Factor and align the labels.** Apply a proved bounded-input
   factorization, construct the permutation agreeing with the distinct
   remaining boundary labels at `z`, undo the contraction, and restore the
   completed size-three colors. Check exact extension on the boundary and
   properness on all newly colored core edges.

The first four steps can be formalized before the needed factorization
input is available. A theorem conditional on that input must be labeled
as a reduction, not counted as the complete Lemma 4.14.

## The unresolved bounded-input dependency

**Corollary 4.6** is not presently a checked factorization theorem. It
concerns even-order regular **multigraphs** with no overfull set and either
one robust core plus at most three exceptional vertices, or two robust
cores plus at most two exceptional vertices, under fixed linear density
bounds and sufficiently small core error.

Its manuscript proof uses **Lemma 4.4** (`two:short:fixed-pattern`) and
**Corollary 4.5** (`two:thm:two-four-exceptions`). Lemma 4.4 retains a heavy
one- or two-core pattern having at most `4-q` internal exceptional pairs.
Its terminal components also use the unresolved **Lemma 4.2**
(`two:lem:ordinary-special`). These inputs must be supplied as actual
factorizations, or discharged by another fully proved argument.

The new simple-graph pattern code provides reusable rounding, numerical
cut accounting, and realization ideas. It does not directly prove this
multigraph assertion. In a multigraph, an internal exceptional pair can
have many parallel copies; its pattern weight need not be at most one.
The paired exceptional parts and their edge copies must therefore remain
in the one-/two-core construction. Do not reuse the simple-graph
`frequent_no_internal` conclusion without proving a replacement hypothesis.

## Compatible circuits for Lemma 4.15 and Proposition 4.16

The manuscript invokes Fan--Zhang's compatible-circuit theorem through
its consequence for Eulerian quotients on at most four vertices.
`docs/coverage.json` records this external dependency as not yet
formalized or matched to a checked declaration. A bibliography reference
is not a Lean proof of the required theorem.

A useful precise target is the following restricted theorem on actual
loopless multigraph edge copies. Partition the incidences at each quotient
vertex into classes. Assume Eulerian degree and, for every label cut `X`
and incidence class `J`,

```text
2 * |J ∩ cut(X)| ≤ |cut(X)|.
```

Construct an exact edge decomposition into connected 2-regular compatible
subgraphs, including parallel-edge 2-circuits, with at most one incidence
from any one class at each vertex. On at most four labels these circuits
have length at most four. Prove that classes recording actual original
endpoints make every circuit lift to an actual matching. Treat
disconnected quotients and virtual edge copies explicitly.

For **Lemma 4.15**, use the actual pair and cut supplies in
`FrequentPatternResult`. Construct and reserve the small family of copies
of the forest, add the two virtual perfect-matching families, verify every
class inequality after the reserved deletions, and decompose the remaining
augmented quotient. Count the circuits using zero, one or two virtual
edges. Pair the two one-virtual path families using the proved Hall
theorem, with compatibility established from actual endpoint conflicts.
Retain parity forests and partition the discarded Eulerian edges into
surplus circuits. The conclusion must have exactly `h` primary boundary
matchings, plus the surplus circuit matchings, partitioning the actual
joining-edge set.

For **Proposition 4.16**, formalize the zero-, two-, and four-odd-part cases.
The surplus-circuit distribution must prove its per-color size and
endpoint-disjointness bounds, and the adaptive completion must retain a
fixed positive degree reserve. Every contracted terminal graph must be
constructed with its degree, parity, robust core, edge-copy labels and
no-overfull property. The final palette alignment must give an actual
one-factorization of the original residual graph.

## Existing interfaces to reuse

| Need | Available interface |
| --- | --- |
| Exact ordinary adaptive packing and finite-prefix robustness | `Overfull.adaptive_ordinary_packing`, `Overfull.adaptive_ordinary_packing_prefix` |
| Actual small-cut classification | `Overfull.SmallCuts.small_cut_lemma`, `Overfull.SmallCuts.minority_sum_le_one` |
| Exact whole-cut subtraction and safe toggles | `Patterns.afterDeletions_cut_accounting`, `Patterns.whole_toggles_safe`, `Patterns.no_overfull_after_pattern_deletions` |
| Finite matching compatibility | `Overfull.bipartite_hall_iff` |
| Four-label forest classification and explicit shapes | `Patterns.odd_leafForest_classification`, `Patterns.LabelForestShape` |
| Actual surviving pair and forest-cut supply | `Patterns.reserved_boundaryPool_card`, `Patterns.forest_supply_of_pair_supply` |
| Fan and sparse multigraph coloring inputs | `Multigraph.first_fan`, `Multigraph.edgeColoring_sparse_vertex_deletion_real` |
| Actual frequent-pattern residual | `Overfull.frequent_boundary_pattern`, `Patterns.FrequentPatternResult` |

Here `Patterns` and `Multigraph` abbreviate their namespaces under
`Overfull`. Preserve the distinction between proved helper reductions,
external unformalized inputs, and complete numbered manuscript results in
all coverage updates.
