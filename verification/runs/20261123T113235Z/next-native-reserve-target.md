# Next target: simultaneous native boundary realization

This is a read-only assessment recorded after the current candidate was
frozen. **Every proposed theorem and construction below is unproved future
work.** This note adds no Lean result or completed numbered assertion.
The run's actual verification records determine what the current sources
prove.

## One precise proposed theorem

**Proposed, unproved:** `exists_native_boundary_schedule` should construct
all prescribed native boundary matchings simultaneously, under an explicit
capacity inequality for each original edge-copy pool.

Fix the original finite multigraph, a disjoint covering partition
`U₀,U₁,Z` with `Z.card ≤ 2`, and the existing native matching distribution.
Use this finite family of actual-copy pools:

| Pool kind | Original copies | Core-endpoint arity |
| --- | --- | ---: |
| Internal exceptional pool | Both endpoints in `Z` | 0 |
| Exceptional-to-core pool `(z,i)` | From `z ∈ Z` to `Uᵢ` | 1 |
| Old-core crossing pool | From `U₀` to `U₁` | 2 |

There are at most `2 * Z.card + 2 ≤ 6` pool kinds. The intended native
catalog must prove their pairwise disjointness as sets of actual copies.
Parallel copies must remain distinct elements of the edge type.

Let `m p : ℕ` be the prescribed multiplicity of each native signature. Every
signature with positive multiplicity must be realized by an actual
positive-weight sample. Let `c b p ∈ {0,1}` record whether its compressed
boundary uses pool `b`, and let `d b = ∑ p, m p * c b p` be the total demand.
The crossing statistic can be defined using a positive-weight representative;
the existing constancy result supplies independence of that choice on the
positive-weight support. Set the statistic to zero outside that support.

The proposed theorem's quantitative assumptions are:

1. At every old-core vertex, each boundary pool has at most `A` incident
   copies, where `A : ℕ`.
2. For every demanded pool, `d b + 4 * A < (pool b).card`.

Its proposed conclusion is a family `F p j : Finset E`, for `j : Fin (m p)`,
such that every round is a matching covering `Z`, distinct rounds are
edge-disjoint, and each round uses exactly `c b p` copies of each pool.
The rounds have the assigned parts, optional exceptional endpoint pair,
signature and crossing parity prescribed by `p`. Both old cores have even
uncovered order. For the union `D` of the selected copies, the construction
should also prove the exact accounting identity

```text
(pool b \ D).card + ∑ p, m p * c b p = (pool b).card.
```

**The exceptional pair is an endpoint-pair pattern, not one common selected
edge copy across rounds.** If several rounds use that pair, edge-disjointness
requires different actual parallel copies in those rounds. The same
distinction applies to the other pool patterns.

## Existing APIs and facts available for the construction

The pool-selection theorem
[`CircuitPatternRealization.exists_pool_selection`](../../../Overfull/CircuitPatterns/Realization.lean)
is already graph-independent: its edge type `E` is arbitrary. Its later
`SimpleGraph` wrappers must be replaced by native multigraph round assembly.
The same file supplies `chosen_pool_card`, `chosen_support_card_le`, and
`capacity_of_real_slack`.

The intended per-round core-endpoint budget is four: at most `Z.card ≤ 2`
exceptional-to-core endpoints, plus two endpoints from the optional
old-core crossing. An internal exceptional pair has arity zero. Proving
this native slot-budget identity remains part of the proposed construction.
The current compression and its exact parity are available in
[`BoundaryCompression`](../../../Overfull/AssignedParts/BoundaryCompression.lean),
[`CompressionCuts`](../../../Overfull/AssignedParts/CompressionCuts.lean), and
[`NativePatternConstruction`](../../../Overfull/AssignedParts/NativePatternConstruction.lean).

The source core-deficit hypotheses can supply the incidence assumption.
[`OneCore.complement_degree_le_error`](../../../Overfull/OneCore/Complement.lean)
bounds each core vertex's degree outside its embedded simple core.
Every boundary-pool copy incident with that vertex lies in this complement.
The native pool-subset specialization and integer conversion still need
proof. This argument counts parallel copies; it assumes no distinct-neighbor
bound and does not infer one.

The exact exceptional-to-core capacities are established in
[`ExactPoolWeights`](../../../Overfull/AssignedParts/ExactPoolWeights.lean).
The internal-pair weight equals its full original copy-pool cardinality by
[`signatureWeight_none_eq_internalPool`](../../../Overfull/AssignedParts/HeavySignature.lean).
For crossing pools, use the selected-copy capacity in
[`NativeWeights`](../../../Overfull/AssignedParts/NativeWeights.lean) and the
constant compressed crossing statistic. Do not reuse a simple-host bound
of one on the weight of an exceptional endpoint-pair pattern.

## Numerical assumptions that rounding can supply

The graph-independent APIs in
[`CircuitPatterns/Rounding.lean`](../../../Overfull/CircuitPatterns/Rounding.lean)
include `proposed_demand_le`, `proposedMultiplicity_le_weight`,
`pair_cut_discard_bound`, `prefix_pair_reserve`, and
`accepted_natural_residual_bounds`. Their native instantiation remains
unproved future work.

The inequality `m p ≤ weight p` ensures that every positive multiplicity
has a positive-weight representative. Existing native aggregation supplies
that representative without replacing its code by an unrelated matching.

For a possible sufficient slack choice, take a positive real allowance
`a' = a + 1` and `0 < η ≤ 1`. Discard signatures that demand a pool of size
less than `L = 6 * a' / η`. The existing real-slack lemma with endpoint budget
four then converts the proposed demand bounds into a strict natural-number
capacity inequality using `A = floor a'`. At most six pool kinds gives a
sparse-pool discard bound of at most `6 * L` in the existing union-bound
argument. This is a proposed parameter specialization, not a checked native
selection theorem. The source's uniform parameter order must be preserved.

## What remains new and what this would not settle

The concrete next work is the native pool catalog and statistics, the
core-incidence specialization, the demand-slot construction, and assembly
of the selected copies into actual matching rounds with exact accounting.
This uses an existing finite selector but still requires genuine native
proofs of all its hypotheses and all required round properties.

After this proposed theorem, robust-core completion remains to be
constructed while retaining the prescribed copies and accounting for
previous deletions. Combining exact pool accounting with
`prefix_pair_reserve` can then turn numerical reserves into actual surviving
copy counts.

**Residual no-overfull safety remains a separate gap.** Deleting perfect
matchings proves regularity of the residual, but does not alone protect its
odd cuts. Native small-cut classification, exact cut losses, and the
protected-cut/large-cut alternatives must still be proved for every actual
deletion prefix. Neither this note nor the proposed boundary-schedule
theorem establishes that safety, the required near-reserve residual-degree
bound after all discards, or the final one-factorization.
