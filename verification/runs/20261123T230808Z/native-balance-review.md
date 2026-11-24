# Read-only next-step review: native assigned-star incidence balance

## Decisive finding

The proposed route is mathematically sufficient and has suitable existing
original-copy interfaces. For an unpaired exception, prove the actual
disjoint incidence partition and inject the `r` surviving reserved copies
into its assigned old-core star pool. These give

```text
j_z + |starPool_z| + t_z = h,
r <= |starPool_z|,
therefore j_z + t_z + r <= h,
and j_z + t_z <= h-r <= D.
```

The existing joining-degree bound `j_z<=D` alone does not yield the needed
remaining-star order bound. The original-core multiplicity bound `b`
does **not** bound a bundle between two exceptional vertices. This review
does not use or recommend an assumption `t<=b`.

This is a read-only mathematical/interface assessment. The theorem names
proposed below are contracts for future work, not existing Lean results or
compiler-checked declarations. No Lean, root, documentation, configuration,
or verifier input was changed, and no build was run for this review.

## Existing reserve interfaces and the exact injection route

Use the original host `G`, representative `M`, partition `U0,U1,Z`, reserve
packing `Q : BoundaryPacking G U0 U1 Z M r`, removed family `N,T`, and actual
residual `H := residualGraph G N T`. Suppose
`coarseSignature G M U0 Z = some sigma`, and put
`U_z := if sigma z = 0 then U0 else U1` for `z : Z`.

The following existing public interfaces suffice:

| Required step | Existing interface | Source |
|---|---|---|
| Same unpaired assignment for every reserve parent | `BoundaryPacking.perfect`, `BoundaryPacking.sameSignature` | `Overfull/NativeReserve/PackingConstruction.lean` |
| Parent uses an actual copy from `z` to its assigned old core | `AssignedParts.signature_some_uses_exceptionCorePool` | `Overfull/AssignedParts/SignaturePools.lean` |
| The original incident copy survives compression | `AssignedParts.mem_exceptionalCopies_of_incident`, `AssignedParts.compressedBoundary_retains_exceptional` | `Overfull/AssignedParts/BoundaryCompression.lean` |
| Reserved boundaries avoid every removed copy | `BoundaryPacking.boundary_disjoint_removed` | `Overfull/ExceptionalPalette/ReserveCopies.lean` |
| Identify original copies inside the residual subtype | `BoundaryPacking.mem_residualBoundary`, `BoundaryPacking.residualBoundary_image` | `Overfull/ExceptionalPalette/ReserveCopies.lean` |
| Distinct reserve indices cannot choose the same retained copy | `BoundaryPacking.pairwise_disjoint`, or `BoundaryPacking.residualBoundary_disjoint` | `PackingConstruction.lean`, `ReserveCopies.lean` |
| Residual endpoints retain the original edge | definition of `MultigraphMatchingProbability.remainingGraph` | `Overfull/MultigraphMatchingProbability.lean` |
| Identify the actual other endpoint from the edge | `Multigraph.edge_eq_otherEnd`, `Multigraph.otherEnd_eq_of_edge` | existing multigraph endpoint API |

For each `i : Fin r`, compose `Q.sameSignature i` with the representative's
`some sigma` equation. Apply `signature_some_uses_exceptionCorePool` to
`Q.perfect i`, obtaining an original copy `e_i` in
`Q.parent i intersect exceptionCorePool G z U_z`. Its incidence at `z` puts
it in `exceptionalCopies`; the public compression retention theorem puts
the **same** copy in `Q.boundary i`.

The avoidance hypothesis
`forall j in T, Disjoint (N j) (removedCopies Q.boundary univ)` gives
`e_i` a witness that it is not removed. Lift it to the residual edge subtype.
Its residual edge is definitionally the same unordered original edge.
Transport the old-core other-endpoint condition using the edge identity
and `otherEnd_eq_of_edge`, rather than presuming a syntactic identity of
arbitrarily chosen endpoint expressions.

This constructs an injection

```text
f : Fin r -> exceptionCorePool H z U_z
```

with `f i` belonging to `Q.residualBoundary N T i`. Injectivity follows from
pairwise disjointness of the compressed boundaries. **Disjoint parent
perfect matchings are not required.** The cardinal inequality follows from
the injection and `Fintype.card_fin`/`Fintype.card_coe`.

`BoundaryPacking.reserved_exceptional_degree` is useful related evidence,
but alone counts only incidences at the exception; it does not assert that
those incidences go to the assigned old core. The explicit `some sigma`
witness above supplies the missing destination information. The private
`compressed_inter_exception_pool` in `RoundedPools.lean` is unnecessary.
The public distribution-dependent `compressedBoundary_pool_usage` is also
unnecessary; this route adds no new distribution input to the native lemma.

**Proposed first contract:**
`BoundaryPacking.exists_residual_assigned_star_injection`, with the native
disjoint-core/exceptional partition and cover assumptions, unpaired signature,
and reserve-avoidance hypothesis. Return the injection above and its exact
boundary membership. Derive `residual_assigned_star_pool_card_ge` as a direct
cardinality corollary.

## Actual incidence partition contract

Fix the original representative's assignment labels on the residual host.
At `z`, separate its incidence copies into:

1. `H.incidenceEdges z intersect joiningCopies H label`;
2. `exceptionCorePool H z U_z`;
3. mutual exceptional copies whose other exceptional endpoint has the same
   assigned label as `z`.

Derive disjointness and exhaustive union from the original vertex partition,
the original assignment's actual label fibers, and `|Z|<=2`. If two
exceptions `z1,z2` have the same assigned old core, the third pool is
`pairFiberCopies H z1 z2`, of common cardinality `t` at both endpoints.
If they have different assigned cores, all their mutual copies are joining
copies and the third pool is empty (`t_z=0`). A lone exception also has an
empty third pool. Looplessness excludes an incidence with no other endpoint.

Useful existing interfaces are `AssignedParts.assignedLabel_fibers`,
`NativeReserve.assignedLabel_on_core₀`, `NativeReserve.assignedLabel_on_core₁`,
`NativeReserve.mem_pairFiberCopies_iff`, and
`NativeReserve.pairFiberCopies_incident`.

**Important interface limit:** `pairFiberCopies_eq_nonjoining_incidence`
assumes the entire assigned fiber is exactly `{x,y}`. That hypothesis is
false when two unpaired exceptions share an old core whose vertices are
also in the fiber. Reuse the pair-pool definition and membership/incident
lemmas there, but prove the new three-way partition.

**Proposed contracts:**

- `assigned_star_incidence_partition`: exact pairwise-disjoint union of the
  three actual incidence pools above.
- `assigned_star_degree_balance`: under `H.degree z=h`, the exact count
  `j_z + starPool_z.card + t_z = h`.
- `residual_assigned_off_core_degree_le`: combine that count with the
  reserve injection to obtain `j_z+t_z+r<=h`, hence `j_z+t_z<=h-r`; append
  the existing native residual error bound `h-r<=D`.

The untruncated inequality also proves `r<=h`, so no natural-subtraction
conclusion needs an unsupported lower-bound premise.

## Common-bundle-first colors and the subsequent balance

For same-core exceptions let `j1+t<=D` and `j2+t<=D`. Then

```text
t + j1 + j2 <= 2*D.
```

Let the protected color set have size `s`, with `2*s<=h` and `128*D<=h`.
These imply `2*D<=h-s`. For a joining palette `C`, existing
`JoiningPalette.usedColors_card` and
`JoiningPalette.freeColors_card_add_degree` identify each joining-used
palette size with its actual joining incidence `j_i`.

The common unprotected joining-free palette

```text
(C.freeColors z1 intersect C.freeColors z2) \ protectedColors
```

has at least `h-s-j1-j2` colors by the union bound on the three forbidden
sets. Because `t+j1+j2<=h-s`, it has at least `t` colors. A finite injection
therefore colors every actual mutual copy distinctly, outside all
protected labels and outside the joining-used palettes of both endpoints.
It adds no old-core endpoint and is internal to their common assigned fiber.
This count uses no old-core multiplicity bound on the mutual bundle.

For exact subsequent star balance, additional **explicit identities** are
needed: every protected label was joining-free at each exception; its
prescribed boundary supplies exactly one assigned-star copy there; those
selected copies are distinct; and bundle colors are distinct and disjoint
from protected/joining-used colors. Native odd protected singleton crossings
and even empty classes can supply the joining-free identity via
`residualBoundary_joining_singleton`/`residualBoundary_joining_empty` and
their old-core endpoint characterization. Generic weighted grouping alone
does not assert it.

If exactly `s` reserved star copies are removed, the incidence partition
gives the remaining copy count `h-j_z-t-s`. The same disjoint color
accounting gives that free-color count. Thus

```text
|remainingStar_z| = |remainingFree_z|
                 = h-s-j_z-t
                 >= h-s-D.
```

This is the actual balance needed by
`exists_star_equiv_of_conflict_bounds`. The first star and the second star
must still be constructed sequentially, with actual matching, copy coverage,
prescription preservation and updated conflict bounds proved for their
unions. Those assembly and native wrapper proofs remain future work.
