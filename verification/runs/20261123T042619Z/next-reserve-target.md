# Next target: native multigraph boundary patterns and reserves

This is a fresh read-only source assessment for run `20261123T042619Z`.
It identifies the next proof obligations after the recreated assigned-part,
selected-cut, and joining composition modules. Proposed constructions below
are mathematical proof plans, not additional checked Lean declarations.
The run's actual compiler and complete-audit records determine what passed.
No identity with the lost earlier unpublished draft or research note is claimed.

## What the present assigned-part stage supplies

For a specified actual perfect matching `M : Finset E`, a disjoint partition
into original cores `U₀,U₁` and exceptions `Z` determines an explicit label
map into `Fin 3`. Its fibers are the two original cores enlarged by their
matching-assigned exceptions and the endpoint support of the selected
internal exceptional copies. When `Z.card ≤ 2`, the third fiber is empty
or has two vertices; there is at most one selected internal exceptional
copy. The representative `M` is retained throughout.

The selected cuts of the enlarged cores equal

```lean
T := G.cutOn M U₀ ∩ G.cutOn M U₁
```

and the selected cut of the exceptional pair support is empty. The new
parity theorem uses exactly `T.card % 2`. This does not by itself identify
`T.card` with a statistic in a separately defined source boundary-pattern
code. That identification still needs its own encoding theorem.

For the regular non-overfull host, the constructed labels and derived
parities feed the checked joining decomposition. No reserve, residual
regularity/no-overfull result, palette, or final factorization is obtained
merely by making this composition.

## Original source hypotheses that must remain visible

The [authorized statement excerpts](../20261122T235931Z/authorized-manuscript-recovery.md)
contain the exact hash-matched original statements of 4.4, 4.5 and 4.6.
For the targeted branch of 4.6, retain the finite even-order loopless
multigraph, original regular degree `k`, no `k`-overfull set, two disjoint
ordinary robust cores, at most two remaining vertices, fixed positive
linear degree/core-order bounds, and the original sufficiently-small-error
and sufficiently-large-order quantifier order.

The host is a multigraph. Its cores contain specified simple robust spanning
graphs; that condition does not make the whole host simple. The checked
representation is `SmallCuts.Core G U`, with an injective map from each
simple core's actual edges to host edge copies. The fixed-pattern 4.4
route additionally uses a scaled perfect-matching decomposition and a
boundary pattern of weight at least `c*k`. Its permitted exceptional-pair
count is `4-q`; no argument may replace that by zero for a general
multigraph. The specialization with two cores and two exceptions has at
most one pair. Full 4.5 still permits five exceptions.

## The smallest useful native bridge

First supply **actual-copy boundary compression and weighted pool capacity
for the two-core case**. This is narrower than proving all reserve selection
or the complete general fixed-pattern lemma.

For each specified perfect matching, keep every selected copy incident with
`Z`. Among the selected copies `T` between the two old cores, keep either
none or one according to the parity of `T.card`. If an odd number is
required, choose an actual member of the nonempty finite set `T`.
The proposed compressed set `F` should satisfy:

1. `F ⊆ M`, so it is a matching on original copies.
2. Every matching copy incident with an exceptional vertex is retained.
3. No selected copy is internal to an old core.
4. At most one selected copy joins the two old cores, with its count
   congruent to `T.card` modulo two.
5. `F.card ≤ Z.card + 1` and explicit corresponding vertex/footprint bounds.
6. The uncovered vertex set in each original core has even cardinality.
7. The internal exceptional pair and assigned-core data agree with those
   of the supplied `M`, rather than an unrelated existential matching.

This proposed proof uses the exact selected-cut identities already provided
by the present stage. The matching copies touching `Z` have cardinality at
most `Z.card`: each touches at least one exceptional vertex, and matching
uniqueness gives disjoint nonempty exceptional endpoint sets. The selected
cross-core copy is disjoint from those copies because `M` is a matching.
The selected-degree handshake then gives the uncovered-core parity.
These arguments must be formalized; they are not claimed compiled here.

Encode this compressed data in a finite pattern type recording exceptional
pairs, the assigned core of each unpaired exception, and the optional
core-to-core crossing. A graph-independent `CircuitPatterns.Pattern Z`
already exists with four fixed label slots and a forest field. Its finite
cardinality formulas can be reused if a new actual-copy encoding relation
is supplied. For two cores, the nonexceptional forest is empty or one edge,
so a specialized construction can avoid porting the entire four-core
simple-graph compression theorem at once. Do not assume that the old
`Encodes` relation applies: it explicitly takes a `SimpleGraph` subgraph.

## Actual edge-copy capacities from the native distribution

Start from `MultigraphMatchingProbability.Distribution G k S`, whose samples
are finite sets of actual copies. It records nonnegative sample weights
summing to one, perfect matchings, and marginal `1/k` for each copy.
`exists_distribution` constructs it from positive regular degree and the
original no-overfull condition.

For a finite code `code : S → P`, define scaled sample weights
`w s = k * D.weight s` and pattern weights by the already graph-independent
`CircuitPatterns.aggregateWeight w code`. Prove the following native
versions, retaining all selected copies:

- Scaled weights sum to `k`, and each actual copy has marginal exactly one.
- Any selected `F s ⊆ D.matching s` has total weight at one copy at most one.
- For every actual-copy pool `A : Finset E`,
  `∑ s, w s * ((F s ∩ A).card : ℝ) ≤ A.card`.
- If a pattern statistic is bounded by its selected pool usage, aggregate
  it to the same actual capacity bound.
- Positive pattern weight yields a representative with exactly that code.

The finite aggregation equalities already have no graph hypothesis.
The scaled-marginal and actual-pool capacity results after them currently
use the simple-graph distribution, so those interfaces require a native
multigraph proof. This separates a small, exact counting obligation from
the later geometric reserve construction.

## Why the simple-graph internal-pair shortcut cannot be reused

`CircuitPatterns.EncodedDistribution.internal_pair_weight_le_one` uses a
fixed exceptional endpoint pair as one particular simple edge. Every sample
with that pattern contains that same edge, and its scaled marginal is one.
For a multigraph, samples may use different parallel copies of the same
endpoint pair. The correct immediate upper bound is the cardinality of
the whole parallel-copy pool, not necessarily one.

For example, on two vertices joined by `k > 1` parallel copies, the `k`
single-copy perfect matchings with probability `1/k` have scaled weight
one each. Grouping them by their shared exceptional endpoint pair produces
one pattern of weight `k`. This is a mathematical counterexample to a
blanket transfer of the simple-edge weight bound; it is not a new finite
experiment or a counterexample to the manuscript theorem.

Consequently, do not reuse `internal_pairs_empty_of_weight_gt_one`,
`rounded_internal_pattern_zero`, or the `frequent_no_internal` and
`selected_no_internal` fields of the existing `PatternSelection` for a
native multigraph without proving their extra premises. The general
numerical rounding lemmas remain true under their stated hypotheses;
what fails is the unjustified universal weight-at-most-one premise.
A native selection structure must permit the source's exceptional pair.

## Existing checked interfaces and exact files

| File | Existing interface | Useful role and limit |
| --- | --- | --- |
| `Overfull/MatchingPolytope.lean` | `Multigraph.exists_perfectMatching_distribution` | Native actual-copy distribution under positive regular degree and no overfull set. |
| `Overfull/MultigraphMatchingProbability.lean` | `Distribution`, `exists_distribution`, `Distribution.expected_cut`, `Distribution.family_failure_probability` | Native marginals and simultaneous probabilistic cut control; selected cut APIs need explicit conversion where necessary. |
| `Overfull/MultigraphMatchingProbability.lean` | `remaining_regular`, `remaining_cut_count`, `cutFailure_iff_actual_cut` | Exact residual degree/cut accounting after one supplied perfect matching; residual no-overfull is not automatic. |
| `Overfull/CircuitPatterns/Weights.lean` | `aggregateWeight`, `aggregateWeight_nonneg`, `aggregateWeight_statistic`, `aggregateWeight_sum`, `aggregateWeight_pos_witness` | Graph-independent finite aggregation can be reused directly. Later scaled/capacity declarations in that file use the simple-graph distribution. |
| `Overfull/CircuitPatterns/Encoding.lean` | `Pattern`, `patternBound`, `card_pattern`, `card_pattern_le` | Finite abstract pattern type and bounds are reusable. `Encodes`, `actualInternalPairs`, and the encoding constructors use simple subgraphs. |
| `Overfull/CircuitPatterns/Rounding.lean` | `exists_maximum_weight`, `maximum_weight_lower_bound`, `reserve_floor_bounds`, `remainingWeight`, `proposedMultiplicity`, `prefix_pair_reserve` | Numerical selection/reserve arithmetic can be reused after native capacities and a genuine finite code are proved. |
| `Overfull/CircuitPatterns/Selection.lean` | `PatternSelection`, `exists_pattern_selection` | Not a direct native interface: both the host and distribution are simple, and the result forces no internal exceptional pair. |
| `Overfull/CircuitPatterns/ReservedEdges.lean` | `reserved_boundaryPool_card` | Template for realizing a numerical reserve as surviving original edges; its ambient graph is simple and must be ported to actual-copy pools. |
| `Overfull/SmallCuts.lean` | `Core`, `small_cut_lemma` | Already native to multigraphs with embedded simple robust cores. The uniform order threshold precedes all host types and graphs. |
| `Overfull/Patterns/Absorption.lean` | `absorb_all_with_reserved_neighbors` | Existing simple-host absorption interface exposes the needed deficiency bound `h-r ≤ a₁`; it does not derive native reserve supply. |

## Reserve and safety obligations that remain after the bridge

A subsequent proof must realize selected multiplicities by pairwise disjoint
actual perfect matchings, reserve the required copy supply in each pattern
pool, and prove the required bound on the residual degree minus the reserve.
The assigned exceptional vertices need enough surviving incidences into
exactly their assigned core or pair; the paired case must be retained.

No-overfull safety must be proved for the actual residual. Deleting a
perfect matching gives the checked regular-degree decrement, but its odd
cut can lose more than one copy. Original no-overfull alone therefore does
not prove residual no-overfull. Reuse the native small-cut theorem and
exact cut accounting to establish the required protected-cut/large-cut
alternative with all quantitative hypotheses explicit.

Only then can the current joining interfaces be applied to that residual,
followed by source-level palette grouping, robust completion, regular
auxiliary graphs and reconstruction of a one-factorization. The original
quantifier order and robust core error estimates must survive these steps.
No numbered assertion is newly completed by this research note.

## Refinement: at most five native assignment signatures

The following is an independently assessed **uncompiled proposed next
lemma**, suggested during this run. It can precede the more detailed
boundary compression above. It does not identify the proposed signature
with the original manuscript's complete boundary pattern.

Fix the original disjoint cover `U₀,U₁,Z`, with `Z.card ≤ 2`. A coarse
signature for a perfect matching can have type

```lean
Option (↥Z → Fin 2)
```

Use `none` exactly when the selected internal exceptional copies are
nonempty. Otherwise use `some σ`, where `σ z` is the unique original core
containing the other endpoint of the actual matching copy at `z`.
Perfectness and the disjoint cover guarantee that this core exists when
there is no selected internal exceptional copy; matching uniqueness and
disjoint cores guarantee uniqueness. This specifies a signature for the
supplied representative, including its actual endpoint assignment.

For `none`, a selected internal copy has two distinct exceptional
endpoints. The checked pair-support subset and zero-or-two cardinality
facts, together with `Z.card ≤ 2`, imply `pairPart = Z` and `Z.card = 2`.
No exceptional vertex can simultaneously be assigned to a core, by
matching uniqueness. The three actual fibers therefore equal `U₀,U₁,Z`,
independently of which parallel internal copy was selected.

For `some σ`, the third fiber is empty, and the other fibers equal

```text
U₀ ∪ {z ∈ Z | σ z = 0},
U₁ ∪ {z ∈ Z | σ z = 1}.
```

Thus the constructed vertex labels and all their fiber cardinalities
are constant among perfect matchings with the same coarse signature.
In particular, the checked matching-cut parity result fixes the parity
of the old-core crossing count on each signature. The exact count, or
a separately defined source pattern statistic, is not thereby fixed.

The signature type has cardinality `1 + 2 ^ Z.card ≤ 5`. Some codes may
be unrealizable, which does not obstruct this upper bound. For a native
finite perfect-matching distribution on a positive `k`-regular host, set
`w s = (k : ℝ) * D.weight s` and aggregate these weights by the coarse
signature. Since all weights are nonnegative and their total is `k`,
some signature has weight **at least `(k : ℝ) / 5`**. Positivity of `k`
makes that weight positive and supplies an actual representative with
the signature. This proposal reuses only graph-independent aggregation
and maximum-weight facts after proving the native scaled marginal
identities; it does not invoke the simple-graph internal-pair shortcut.

For clarity, the proposed pool-capacity conclusion needs a usage
hypothesis. Let `A : Finset E` be an actual-copy pool such that every
sample with a fixed signature `t` contains at least one selected copy
in `A`. Then

```text
weight(t)
  ≤ Σ s, w(s) * card(M(s) ∩ A)
  = card A.
```

The first inequality uses nonnegative weights and the stated usage
condition. The equality sums the scaled marginal of one over each
actual copy in `A`. It is valid with parallel copies and provides
`card A ≥ k/5` for a heavy signature whenever that usage condition holds.

The condition holds for these specific pools:

- For `none`, all actual copies internal to `Z`.
- For `some σ` and each `z ∈ Z`, all actual copies from `z` to the
  particular original core `U_(σ z)`.
- If the fixed fiber parity forces an odd old-core crossing count,
  all actual copies between `U₀` and `U₁`.

The first pool can contain many parallel copies of the same endpoint
pair; its capacity is its whole copy count. No bound of one on the
signature's weight follows. Likewise, copy capacity does not assert
many distinct neighbors, simultaneous disjoint reserves, a surviving
reserve after deletions, or residual no-overfull safety.

An appropriate next formalization order is therefore: define the coarse
native signature; prove constant actual assigned fibers; derive the
five-signature weighted pigeonhole bound; prove the generic actual-copy
pool inequality and the listed usage instances. Boundary compression,
source-pattern identification and the reserve/safety constructions remain
separate obligations. No new Lean file or theorem was created for this
refinement in the present run.
