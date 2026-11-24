# Native two-core reserve completion: scope and proof map

The final interface is
`Overfull.NativeReserve.exists_native_reserve_completion_parameters` in
`Overfull/NativeReserve/CompletionConstruction.lean`. It constructs the
reserve and the completed matching family from the original host. The
compiler records and full-audit status are in
`verification/runs/20261123T201422Z/`; this proof map is not a replacement
for a completed fresh verification of the exact sources.

## Formalized statement

Fix positive parameters `α,c,ν,σ,δ`, with `α≤1`, `ν≤τ≤α/8`,
`σ<1/2`, and `σ≤α/300`. The theorem chooses positive `ξ,θ` and an
integer `n₀≥1` before the vertex type, edge-copy type, host, or degree.

Let `G` be an `n`-vertex multigraph with a finite actual edge-copy type,
`n≥n₀`, regular degree `k≥αn`, and no `k`-overfull vertex set. Suppose
the old cores `U₀,U₁` and exceptional set `Z` are pairwise disjoint and cover the vertices,
`|Z|≤2`, and each core has at least `cn` vertices. Each embedded simple
core is a robust `(ν,τ)` expander and has minimum degree at least `k-a`,
where `0<a≤ξn`.

The conclusion constructs integers `r,h,q`, an original perfect matching
`M`, a reserve `Q` of `r` pairwise disjoint compressed boundaries with the
same native assignment signature as `M`, and `q` pairwise disjoint actual
perfect matchings `Nⱼ`. Every `Nⱼ` avoids every reserved original copy.
They satisfy

```text
r ≥ k/30,     h+q=k,     r≤h,     h-r≤δn.
```

The actual residual `R = G \ ⋃ⱼ Nⱼ` is `h`-regular and contains no
`h`-overfull vertex set. Each old vertex set `Uᵢ` still contains an
embedded robust `(θ,σ)` core of minimum degree at least `h-a`.
The surviving core graph is the actual unused graph of the corresponding
core matching packing, with its original copy embedding.

The original parent matching `M` need not survive intact. Its assignment
is retained for the next stage. The reserve consists of small boundary
matchings; its parent perfect matchings are allowed to overlap. Empty
boundaries are permitted when the native signature requires no boundary
copy. No fractional matching distribution of a residual is assumed.

## Construction and numerical accounting

1. The original matching distribution is scaled so every original edge
   copy has marginal one. A signature of weight `w₀≥k/5` has an actual
   representative. Arbitrary parallel copies of an exceptional pair are
   retained as distinct copies.
2. Choose `r=⌊w₀/3⌋`. For `k≥30`, `r≥k/30` and `3r≤w₀`. A forbidden
   set smaller than a signature's weight cannot meet every selected
   boundary of that signature. Induction therefore packs `r` disjoint
   boundaries, each of size at most three.
3. The fixed rounded proposal is
   `mₚ=⌊(1-η)(wₚ-r·1[p=p₀])⌋`. Rounding loses at most five units.
   Its demands refer throughout to the original weighted distribution.
4. Discard signatures using any pool with fewer than `L` copies. There
   are at most six native pools, so this loses at most `6L` rounds.
   Test all even whole-core shores against the same original proposal.
   At most sixteen tests discard at most another `32a/η` rounds.
5. The actual reserve consumes at most one third of every original pool.
   Thus at least two thirds remain before accepted rounds are selected.
   With `L=12a/η`, a demanded surviving pool has the `8a` slack needed
   to avoid used copies and conflicting core endpoints. Actual sigma
   slots realize every accepted round with the prescribed pool counts.
6. The remaining degree satisfies
   `r≤h≤r+ηk+5+104a/η`. Each selected boundary covers `Z`, uses at most
   three actual copies, and leaves an even uncovered order in both old
   cores. Its footprint has at most six vertices. Disjointness and the
   original core-complement degree bound give footprint load at most `a`.
7. Uniform robust packing completes all selected boundaries in the two
   original cores. The added copies lie only inside the old cores and
   avoid the reserved boundary copies. Exact embedded-copy identities
   identify each retained core with the packing's actual unused graph.
8. Whole-core cut-copy sets are unchanged by these internal completions.
   Odd whole cuts have at least `h` surviving copies. Each even whole
   cut either has at least `2a` surviving copies or its entire original
   cut-copy set is untouched. Core-incidence bounds and original
   no-overfull safety control its one-vertex toggles. The robust small-cut
   classification then proves absence of every residual overfull set.

The parameter choice supplies all initial size/error budgets before
selection. It also gives the core-packing horizons and the final margin.
The bound `k≤2n` follows from a nonempty simple core and `a≤n`; applying
the numerical setup with `δ/2` therefore yields `h-r≤δn`.

## Module map

| Modules | Proof responsibility |
| --- | --- |
| `WeightedPacking`, `PackingConstruction` | Actual-copy avoidance, disjoint boundary reserve and its signature/parity certificates. |
| `Rounding`, `RoundedPools` | One-third reserve, native pool demands and original weighted capacities. |
| `DenseSelection`, `ProtectedSelection` | Fixed proposal, sparse-pool discards and protected even-cut tests. |
| `ProtectedPacking` | Exact reserved-copy counts and the two-thirds initial pool remainder. |
| `Realization`, `Greedy`, `Schedule`, `AcceptedRealization` | Disjoint actual edge-copy selection with endpoint avoidance and exact per-round pool use. |
| `BoundaryProperties`, `Construction` | Exact native signatures, uncovered parity and complete boundary selection with cut certificates. |
| `Residual`, `CutSafety`, `WeightedSafety`, `NativeCutWeights` | Exact actual residual accounting, native weighted cuts and no-overfull criteria. |
| `CompletionFootprints`, `CorePacking`, `CompletionParameters` | Actual forbidden sets, original-core packing and uniform quantitative choices. |
| `CompletionGlue`, `RetainedCore`, `CompletionCuts` | Perfect completion, actual surviving embedded cores and unchanged whole-cut copies. |
| `CompletionConstruction` | The uniform original-host end-to-end reserve-completion theorem. |

The source manifest records every public theorem name and exact source
hash. The complete transitive axiom audit additionally includes private and
generated proof declarations. `Audit.lean` is unchanged, and the permitted
logical axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

## Exact limit of the result

This completes a supporting reserve-and-safe-residual stage. It does not
construct the remaining palette grouping, regular auxiliary graphs, or the
full factorization of the two-core branch of Corollary 4.6. No numbered
manuscript assertion is added: **47/69 remain complete and 22 remain open**.
The main theorem remains unproved. The original five-exception hypothesis
of Corollary 4.5 is not changed by this two-exception construction.

See `native-reserve-semantic-review.md`, `native-reserve-source.json`, and
`continuation-handoff.md` for the review, exact proof inventory, and next
obligations. The run's recovery provenance distinguishes the one exact
recovered source from newly reconstructed sources and historical checks.
