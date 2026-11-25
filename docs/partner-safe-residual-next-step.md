# Next native safe-residual step: partner pools and whole-cut demands

This is a source-based plan for the continuation after the protected two-pair
external construction. It records an actual obstruction in the existing
two-exception code and the first lemmas needed to remove it. The proposed
extensions below have **not** been proved by this document. They do not promote
any numbered assertion: the numbered inventory remains 51/69, and the main
theorem remains unverified.

## What the external endpoint still takes as input

`NativeCore/TwoPairExternal.lean` constructs the complete external palette in
the branch where the original representative matching has exactly two internal
exceptional edges and `Z.card ≤ 5`. Its inputs still include an actual
reserve-avoiding residual `H = residualGraph G N T`, its regularity and
no-overfull property, and retained simple cores on the original shores. In
particular, with the notation of that endpoint, it requires

```text
degree_H(v) = h
degree_C0(v), degree_C1(v) ≥ h - D
h ≤ r + D
0 < h, 128*D ≤ h, 2*t ≤ h, 0 < L
|V|*D ≤ 2*L*(h - t - 40*D).
```

The final inequality is an inequality of natural numbers, with truncated
subtraction as in the Lean statement. The palette capacity is `2*L`. The
parameter `L` here must not be confused with the real sparse-pool threshold
called `L` in the old reserve-selection code.

The next native task is to construct such a safe residual from the original
regular non-overfull host, while preserving the **actual** partner reserve.
`NativeReserve.exists_linear_partner_boundary_reserve` already supplies a
linear reserve for the full partner code, but supplies neither these deletion
matchings nor these residual estimates.

## The first obstruction is the exceptional-pair pool

`NativeReserve/Greedy.lean` defines the old pool type by

```text
PoolKind Z = pair | exception(z : Z, i : Fin 2) | crossing
poolCopies pair = G.internalOn univ Z.
```

This definition intentionally puts every exceptional internal copy into one
pool. Under `Z.card ≤ 2`, all copies in that pool have the same two endpoints.
Two downstream facts depend on this:

- `poolCopies_specialEnds` says every copy in the pair pool has exceptional
  endpoint set exactly `Z`.
- `NativeCutWeights.poolCopies_cut_uniform` says every copy in a pool has the
  same cut membership for a shore containing each old core wholly or not at
  all.

Both statements fail for this pool definition when there are more exceptions.
For example, take four distinct exceptions `a,b,c,d` and copies with endpoints
`{a,b}` and `{c,d}`. They belong to the same old pair pool. The whole shore
`X = {a}` contains neither old core, but only the first copy crosses it. This
example already occurs in the two-pair case. Replacing the old coarse signature
with `PartnerSignature Z`, or replacing a cardinality hypothesis `≤ 2` by
`≤ 5`, cannot repair that failure.

This is the first structural extension needed by both the whole-cut accounting
and the greedy realization. The latter must preserve each selected copy's
exceptional endpoints when it chooses a different copy from the same pool.

## Refine pools by unordered exceptional endpoint pair

Add a new pool interface in a new module, leaving the old two-exception
interface unchanged. Its kinds should be:

| Kind | Original copies in the pool | Fixed exceptional endpoints |
| --- | --- | --- |
| An unordered pair of distinct vertices of `Z` | Every copy with exactly that endpoint pair | That two-element set |
| An exception `z : Z` and core index `i : Fin 2` | `exceptionCorePool G z.val U_i` | `{z.val}` |
| Old-core crossing | `coreCrossingPool G U₀ U₁` | Empty |

Use an unordered pair representation, such as a non-diagonal `Sym2 Z` or a
two-element subset. Ordered pairs would duplicate pools and invalidate the
pairwise-disjointness calculation. Every parallel copy must remain present;
the refinement must not replace a pool by a single representative copy.

The number of kinds is
`choose(Z.card, 2) + 2*Z.card + 1`, hence at most 21 for five exceptions. This
finite counting claim is a target to prove for the chosen Lean representation,
not a currently registered theorem of the proposed interface.

The first useful endpoint is the full-partner analogue of
`RoundedPools.compressedBoundary_pool_usage`: two perfect matchings with the
same full partner signature have the same zero-or-one use of every refined
pool in their compressed boundaries. In schematic form:

```text
partnerSignature G M U₀ Z = partnerSignature G N U₀ Z
  ⇒ ∀ j,
    card (compressedBoundary G M U₀ U₁ Z ∩ partnerPoolCopies j) =
    card (compressedBoundary G N U₀ U₁ Z ∩ partnerPoolCopies j),
```

with each cardinality at most one. This can be proved without a bound on
`Z.card`; the bound of five is needed later for finite loss estimates.

The exact existing dependencies are:

- `AssignedParts/PartnerSignatures.lean`:
  `partnerSignature_pair_iff`, `matchingPartner_eq_of_mem`,
  `partnerSignature_first_core_iff`,
  `assignedParts_eq_of_partnerSignature_eq`, and
  `exists_parallel_of_partnerSignature_eq`.
- The compression identities `compressedBoundary_internalOn`,
  `compressedBoundary_retains_exceptional`, and
  `compressedBoundary_coreCrossing_card`.
- `AssignedParts/MatchedCuts.lean`:
  `corePart_card_parity`. Full partner-code equality fixes the first assigned
  core, so this fixes the retained old-core crossing parity. The old theorem
  `coreCrossing_parity_eq_of_signature_eq` is restricted to the coarse code
  and at most two exceptions; use its underlying parity argument instead.

For an exceptional pair, the partner code fixes its endpoint pair and a
matching uses at most one parallel copy. For an exception/core pool, the code
fixes that exception's assigned core. For the crossing pool, compression
retains zero or one old-core crossing according to the assigned-core parity.

Define demands on the full code space only after this invariant is available.
A representative-sample definition, with demand zero for a code absent from
the distribution, follows the existing `crossingDemand` approach and avoids
silently treating an inconsistent arbitrary partner code as realizable. An
explicit pair-demand formula must likewise account for reciprocal partners
on realizable codes.

## Whole-cut accounting to build next

On the refined pools, prove fixed exceptional endpoints, pairwise disjointness,
and coverage of every compressed-boundary copy. Then the new pair case of
cut uniformity holds for every shore because copies in that pool are parallel.
The exception/core and crossing cases reuse the existing whole-core membership
argument.

The direct target chain is:

1. Refined `poolCopies_specialEnds`, `poolCopies_pairwiseDisjoint`, and
   `compressedBoundary_exists_pool`.
2. Full-partner compressed-boundary usage, and pool-demand capacity against
   `partnerSignatureWeight`.
3. Refined `poolCopies_cut_uniform`, `native_cut_count_eq_sum_pools`, and
   `partnerWholeCutDemand_at_sample`.
4. `partnerWholeCutDemand_capacity` and positivity of whole-cut demand for
   odd shores and codes of positive weight.

Several parts are already general enough and should be reused directly:

| Existing interface | What it already supplies |
| --- | --- |
| `NativeReserve/PartnerPacking.lean` | Full-code weights, a heavy actual representative, and disjoint actual compressed reserves |
| `AssignedParts.NativeWeights.aggregate_capacity` | Weighted capacity for any finite code type and selected subsets of the distribution matchings |
| `NativeCutWeights.compressedBoundary_whole_cut_parity` | Whole-cut parity for arbitrary exceptional sets; no two-exception restriction |
| `NativeCutWeights.originalCores_whole` | Each old core lies wholly on one side of a whole-union shore |
| `NativeCutWeights.completed_native_cutOn_eq` | Completing a boundary by old-core internal copies preserves its whole cuts, for arbitrary `Z` |
| `WeightedSafety.residual_weighted_odd_cut` and `residual_proposed_cut_dichotomy` | Residual cut certificates for any finite pattern type |
| `WeightedSafety.residual_no_overfull_of_pattern_counts` | The final no-overfull implication from actual completed matchings, retained robust cores, exact whole-cut counts, weighted capacities, and protected small even cuts |

The last theorem is already generic in the pattern type, the core index type,
and `Z`. It can be instantiated with `PartnerSignature Z` once the new counts,
weights, and protected selection have been constructed. A new foundational
small-cut theorem is not the first missing step.

## Realization and retained-degree estimates still need proofs

`NativeReserve/AcceptedRealization.lean` and `Schedule.lean` are not immediately
reusable by changing their signature type. Their existing proof uses compressed
boundaries of size at most three, total greedy core-end allowance six,
`6*floor(a)` for forbidden incidences, and slack `8*a`. For five exceptions,
the general compression bound is at most six copies. Prove a parameterized
version of that schedule or establish a fresh bound from the new template
sizes. Preserve actual reserve avoidance and exact per-pool usage; do not
assume the old slack constants still work.

After that, extend rounded multiplicities, sparse-pool rejection, and protected
small-even-cut rejection to the full code. The old numerical losses come from
five coarse codes, at most six pools, and at most 16 whole shores. For five
exceptions, the available elementary bounds are `7^5` full codes, at most 21
refined pools, and at most `2^(2+5) = 128` whole shores. These identify which
estimates must be recomputed; they are not a proved final retained-degree
bound, and the old `104*a/η` bound must not be carried over unchanged.

The complete safe-residual construction must then:

- realize accepted boundaries outside the actual partner reserve;
- complete them inside the original robust cores and control core degree
  loss, still avoiding that reserve;
- derive regularity of the residual by deletion of disjoint perfect
  matchings;
- apply the generic weighted safety theorem using the constructed whole-cut
  demands and protection;
- verify the explicit degree, reserve, and palette budgets required by the
  external endpoint from the original hypotheses.

The heavy representative is chosen over the entire partner-code space. It
cannot be assumed to have exactly two exceptional pairs just because the
two-pair external construction is now available.

## Remaining external branches and final completion

With at most five exceptions, zero exceptional pairs can leave five unpaired
exceptions, and one exceptional pair can leave three. Those cases still need
native simultaneous multi-star assembly, exact preservation of the whole
protected boundary, and weighted palettes with enough resources for their
actual stars. Existing two-resource weighting statements cannot be applied as
if they supplied arbitrary many star resources. Any sharing of resources
across stars needs its own verified argument.

For the two-pair branch, the current external construction handles both no
remaining exception and the actual fifth exception. Its exact cover is
`joiningCopies H label ∪ exceptionalCopies H univ Z`; it does not claim to
cover all original-core internal copies. Completing the external colors
inside robust cores, factoring the terminal remainder, and connecting those
steps from the original hypotheses remain necessary. Existing completion and
terminal interfaces should be reused only after their hypotheses have been
derived for the constructed residual.

The appropriate next milestone is a checked partner-pool usage and whole-cut
accounting module, followed by its realized protected-selection construction.
None of those milestones alone justifies promoting Lemma 4.4, Corollary 4.5,
or the main theorem.
