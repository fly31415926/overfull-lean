# Semantic review: native reserve balance and actual star extensions

## Result and review boundary

The final source contracts in the eight modules below passed this semantic
review. No defect was found in their incidence accounting, actual-copy
cardinalities, endpoint-conflict relation, available-color load bounds, or
sequential construction. The review was completed on 2026-11-24 after the
successful recorded strict build of `Overfull.NativeStar.TwoStars` at
00:00:18 UTC.

The review examined the actual definitions and proof bodies, final source
hashes, and genuine focused build receipts. It did not modify Lean sources,
rerun the compiler, execute the integration preparer, or perform a complete
axiom audit. The reviewer authored `ReserveInjection.lean` and
`NativeBalance.lean`; the other modules were reviewed as a nonauthor.
Compilation and the complete audit provide separate evidence. Their exact
status is recorded by the run receipts and
[the verification guide](native-star-verification.md).

These are supporting constructions. They complete no numbered manuscript
assertion. Coverage remains **47 of 69**, and full Corollary 4.6, robust
factorization, and the main theorem remain unproved. In particular, the
native weighted odd/even wrappers and the complete assembly of their
reserve prescriptions, parity, and actual colored copies remain to be
instantiated.

## Reviewed source identities

Each file is under `Overfull/NativeStar/`. The source manifest
[native-star-source.json](native-star-source.json) is the authoritative
public theorem inventory; the complete declaration map additionally records
private and generated proof declarations.

| Module | SHA-256 |
|---|---|
| `ReserveInjection.lean` | `f4e41178404a179fed082284157ea1636a6bc216a5ad1ae08ba3c4f9701402fc` |
| `IncidencePartition.lean` | `e1e8e84a8e5c982de230137edea0ae8d6813cf7074194a48d83a3fe28f4948fa` |
| `NativeBalance.lean` | `d358b54a4357990b840bb1ac2b532bd0308c91e08c18611edb3efe1d96e7d9f8` |
| `CommonPalette.lean` | `ee8740cb65855a3654df71dee2517b01f7e4315e236828b6138c516a2b86acaf` |
| `StarAccounting.lean` | `e0b7aa80906e77186e677cba6dfaebeb61050bcf47cc71e36a645d4e6b4af4fb` |
| `StarChoice.lean` | `7cc6ee673227a937cbaa2f674684083fb2bcd22d74433ffe76743df19b6429fa` |
| `StarExtension.lean` | `9a8b0603d674615f7258599351b42c2aa1d5d86c5b520bd2b3bf6f11973a716e` |
| `TwoStars.lean` | `a8fd371129726216c4df1e5f65f841ae233aff477e7422ceea32589f0b23d86d` |

## 1. Original assignments and residual copies remain distinct objects

The native specialization uses the fixed label
`AssignedParts.assignedLabel G M U₀ U₁ Z` from the **original** graph and
representative matching. The host of the incidence calculation can be a
different graph `H` on the same vertex type, with a different edge type.
In `NativeBalance`, that host is `NativeReserve.residualGraph G N T`;
its edges are surviving original copies, represented by a subtype.

No step silently recomputes the assignment from a matching in the residual
host. `Overfull.NativeStar.assigned_incidence_partition` and
`assigned_degree_balance` explicitly retain the original label while
counting actual incidences in `H`. The unpaired hypothesis is the exact
equation `coarseSignature G M U₀ Z = some σ`. It is not a claim about a
paired signature or an arbitrary assignment of exceptions.

Every copy set is a finite set of edge identifiers. Parallel copies remain
distinct throughout subtype transport, reserve selection, color assignment,
and coverage. Multiplicities appear only as cardinalities of actual
parallel-edge pools. No proof replaces a star by its set of distinct
neighbors.

## 2. Surviving reserve copies provide a genuine injection

The methods in `Overfull.NativeReserve.BoundaryPacking` use a supplied
native boundary packing `Q`, the two old cores disjoint from `Z`, a cover
of the vertex set, the unpaired signature, and the survival hypothesis

```text
∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ).
```

This hypothesis protects the entire reserved family from the selected
removals. It supplies survival of all `r` reserved incidences, including
those outside a later selected protected subfamily.

`boundary_assigned_star_nonempty` obtains an actual assigned-core copy
from each perfect parent using its common signature. Incidence at the
exception places the copy among the exceptional copies retained by the
compressed boundary. The boundary is a matching, so
`boundary_assigned_star_card` strengthens nonemptiness to exactly one.
Only the boundaries need to be pairwise edge-disjoint; no disjointness of
their perfect parents is assumed.

`mem_residual_exceptionCorePool` proves the exact equivalence between
membership of a residual subtype copy and membership of its original
value in the corresponding original pool. The image equality
`residualBoundary_inter_exceptionCorePool_image` then transfers the
exact-one intersection through removal. The proof creates a residual
subtype witness only after proving that its original copy survives.

`exists_residual_assigned_star_injection` chooses one such actual copy for
each index in `Fin r`. Pairwise disjoint residual boundaries establish
injectivity. Its conclusion also retains the boundary membership of each
chosen copy. Consequently `reserved_assigned_star_card_le` derives
`r ≤ star.card`; this is a conclusion of the native reserve data, rather
than an unexplained later assumption.

`residualBoundary_incidence_eq_assigned_star` proves that every incidence
of a reserved boundary at the exception is its unique assigned-core copy.
This rules out an additional reserved joining or internal-bundle incidence
at that exception. For an injective selection `q` on an arbitrary finite
index set `A`, `selected_residual_assigned_star_card` proves

```text
((A.biUnion (fun i => Q.residualBoundary N T (q i))) ∩ star).card = A.card.
```

The exact selected count uses actual disjoint copy sets. It does not follow
merely from counting selected indices, and the theorem supplies the missing
disjointness argument. Empty selections and `r = 0` are allowed.

## 3. The internal exceptional bundle is counted separately

`joiningIncidenceCopies H label z` consists of actual joining copies
incident with `z`. `exceptionInternalPool H label Z z` consists of actual
incidences whose other endpoint lies in `Z` and has the same label as `z`.
For a core `U` disjoint from `Z`, with the appropriate constant-label and
fiber-containment properties, `incidence_partition` proves that these
sets and `exceptionCorePool H z U` are pairwise disjoint and cover exactly
`H.incidenceEdges z`.

The original unpaired signature supplies those label properties for
`U = if σ z = 0 then U₀ else U₁`. Thus, writing `j_z` for the joining
degree, `S_z` for the assigned star pool, and `t_z` for the internal
exceptional pool size, `assigned_degree_balance` proves

```text
j_z + |S_z| + t_z = degree_H(z).
```

For a residual degree `h`, the native reserve injection gives `r ≤ |S_z|`.
`native_off_core_degree_bound` therefore derives the combined bound

```text
j_z + t_z ≤ h - r ≤ D.
```

This is the bound needed to retain a remaining palette of size at least
`h-s-D`. Separate assertions `j_z ≤ D` and `t_z ≤ D` would only imply the
weaker loss `2D`. The proof uses the combined incidence identity and the
surviving reserve, so it incurs only the single loss `D`.

There is no old-core multiplicity hypothesis on copies between two
exceptions. In particular, the internal bundle is not bounded by `b` merely
because exceptional-to-old-core multiplicities are bounded by `b`.
For `Z = {x,y}`, `exceptionInternalPool_pair_eq` identifies the same-label
internal pool with the actual mutual `pairFiberCopies H x y`; if the
labels differ, `exceptionInternalPool_pair_eq_empty` makes it empty.
These statements do not require the entire label fiber to be `{x,y}`.
They remain valid when the fiber also contains an old core.

## 4. Protected traces and exact remaining-copy/color balance

`joiningUsedColors C z` is the set of labels whose actual joining class
contains `z` in its support. `joiningUsedColors_card` uses the supplied
`JoiningPalette` matching, disjointness, and coverage interface to identify
its cardinality with the actual joining degree. It is not an arbitrary
set of the right cardinality.

For a protected reserve index `i` and its label `j`, the native trace
condition is the set equality

```text
R.residualBoundary N T i ∩ joiningCopies H originalLabel = C.classes j.
```

`protected_joining_color_free_of_reserve_trace` derives that this class
does not contain the exception in its support. A hypothetical joining
incidence would also be a reserved incidence; the exact reserve-incidence
lemma would place it in the assigned star pool, contradicting the disjoint
incidence partition. Merely bounding the size of the class would not prove
this fact.

For a same-label pair of exceptions, `exists_native_common_bundle_coloring`
identifies both internal pools with the same actual mutual bundle and
constructs an injective coloring of all its copies. The colors avoid the
protected set and the joining-used colors at both endpoints. Its numerical
conditions are `4*D ≤ h` and `2*|Q| ≤ h`, together with the native combined
endpoint bounds. The two joining-used sets may overlap. No disjointness
between them is required by the common-palette union bound.

`native_remaining_star_balance` takes an injective reserve selection `q`
and an injective protected label assignment `f` on a finite set `A`, the
exact native trace for each selected index, and an injective coloring of
the actual internal pool avoiding those protected and joining-used colors.
It defines the objects whose cardinalities it proves:

```text
S    = the actual assigned star pool;
P    = selected residual reserve boundaries intersected with S;
Qcol = A.image f;
Jcol = joiningUsedColors C z;
Bcol = the image of the actual internal-bundle coloring.
```

The result derives `|P| = |Qcol| = |A|` and `|Bcol| = |B|`, and proves

```text
|S \ P| = h - |A| - |Jcol| - |B|
        = |remainingStarColors Qcol Jcol Bcol|,
h - |A| - D ≤ |S \ P|.
```

The protected/joining color disjointness is derived from the exact traces;
the other disjointness statements follow from the supplied bundle-color
avoidance. Selected reserve cardinality is derived from the actual
boundaries. Natural subtraction is justified by these set partitions and
cardinality identities. This theorem does not assume a target equality of
remaining cardinalities as its premise.

The theorem still requires the native trace and actual bundle coloring.
It does not itself choose the native odd/even joining palette, insert whole
protected boundaries into that palette, or establish the matching and load
properties of the resulting initialized family.

## 5. Hall conflicts concern available colors and actual endpoints

For a remaining star-copy set `A` and a remaining color set `F`, the
relation in `exists_star_choice_on_available` forbids precisely those
colors whose current class occupies the copy's old-core endpoint. Each
element of `A` remains a separate row, including all parallel copies.
The exceptional endpoint is handled by the separate explicit condition
that it is free in every available class.

`star_row_conflicts_card` identifies the row count exactly with

```text
(F.filter (fun j => otherEnd(z,e) ∈ support(C j))).card.
```

`star_column_conflicts_le` injects the conflicting remaining copies into
the actual blocked-copy pool counted by `WeightedPalette.starWeight` for
the whole class. The full assigned-star pool may be larger than `A`; using
it gives a valid upper bound. The weight tests old-core endpoint support,
so it does not replace the separate exceptional-endpoint freeness premise.

The Hall hypotheses are explicit:

```text
|A| = |F|,                 h-s-D ≤ |A|,
b ≤ D,                    128*D ≤ h,              2*s ≤ h,
available row load ≤ D+b, available class weight ≤ h/8+b.
```

The previously checked natural-number lemma `star_hall_margin` proves
`(D+b) + (h/8+b) ≤ h-s-D`, including integer-division remainders.
Asymmetric Hall then yields an equivalence `A ≃ F` avoiding every conflict.
`matching_union_star_singleton` derives matching after insertion from the
old matching and the two endpoint-freeness facts. No preexisting coloring
of the remaining star is assumed.

The global-load versions of `exists_star_choice` and
`exists_star_extension` remain valid stronger-input wrappers. Their proofs
restrict a global load bound to `F`. The native application should use the
more precise `_on_available` variants when protected reserves have already
been inserted.

## 6. Sequential construction derives the second conflict budget

`coloredStarCopies A c j` contains exactly the original copies assigned
to `j`. The color fibers are disjoint and cover `A`, and an injective
assignment gives at most one copy in each color. A new copy therefore adds
at most two support vertices to one class.

Away from the first center `x`, the color-support load of the whole first
star is bounded by its actual incidence, then by the cardinality of the
parallel-copy pool from `x` to the vertex. For a second core `U₁` excluding
`x`, this increases its available-color load by at most `b` under the
explicit multiplicity bound. Injectivity is unnecessary for this load
estimate.

For the column estimate, injectivity ensures that one color of the first
star occupies at most one vertex of `U₁`. If the second center-to-core
multiplicities are at most `b`, that color blocks at most `b` actual
second-star copies. Subadditivity of `starWeight` under actual copy union
then raises the second resource bound from `h/8` to at most `h/8+b`.

`exists_two_star_extension_on_available` performs the two Hall choices
sequentially. Its initial family `C` is assumed to consist of pairwise
edge-disjoint matchings, disjoint from both remaining star pools. Each
pool has its own actual set `A₀` or `A₁` and available palette `F₀` or `F₁`,
with exact cardinality equality, lower bound `h-s-D`, and an initially free
center. Initial loads are at most `D` only on the corresponding `F₀` or
`F₁`; initial class weights are at most `h/8` only on that same palette.

The geometric hypotheses are `x ≠ y`, `y ∉ U₀`, and `x ∉ U₁`. They prove
that the actual star pools are disjoint and that insertion of the first
star cannot occupy the second center. The cores themselves need not be
disjoint. The two explicit parallel bounds concern `x` to vertices of
`U₁` and `y` to vertices of `U₁`. These supply the two different second-step
increments described above. No exceptional-to-exception multiplicity bound
is used.

After the first insertion, the proof establishes its second-palette load
bound `D+b`, weight bound `h/8+b`, copy disjointness, and center freeness,
then makes the second Hall choice against those extended classes. This
addresses conflicts between the two stars even when they meet the same
old-core vertices.

The output gives both actual equivalences and derives:

- every final class is a matching and different classes are edge-disjoint;
- the final union is exactly the initial union together with `A₀` and `A₁`;
- each initial class is retained;
- each class gains at most two copies and four support vertices;
- every label outside `F₀ ∪ F₁` retains its exact initial class;
- each center is covered in every color of its available palette;
- each original new copy belongs to the class prescribed by its own
  selected equivalence.

These growth bounds are relative to the supplied initialized family `C`,
which may already contain protected boundaries and an internal bundle.
They are not an automatic final footprint bound relative to the earlier
joining palette.

## 7. Protected colors: the remaining native integration issue

Inserting a whole protected reserved boundary may put an old-core vertex
into an additional protected color. Thus the global number of classes
containing that vertex need not remain bounded by the joining-degree
budget `D`. A native construction cannot silently reuse a global `D` load
certificate for the reserve-extended family.

The checked APIs avoid that unnecessary global premise. All row bounds
used by the two-star construction are restricted to `F_z`, and all initial
weight bounds are likewise requested only for colors in `F_z`. The global
accounting lemmas in `StarAccounting` have explicit global hypotheses;
the available-only helpers in `TwoStars` do not invoke those hypotheses.
Protected labels excluded from `F_z` therefore contribute no Hall conflicts.

The next native assembly must prove the concrete restriction certificate.
For the intended initialization, protected boundaries are inserted only in
`Qcol`, the internal bundle only in `Bcol`, and
`F_z = univ \ (Qcol ∪ Jcol_z ∪ Bcol)`. Proving that the initialized class
equals its original weighted joining class for every `j ∈ F_z` will
transfer the joining load `D` and weight `h/8` directly. Membership outside
`Jcol_z` then supplies center freeness. This equality is a precise remaining
native obligation; it is not already a consequence of the standalone
two-star theorem or of a numerical palette bound.

## 8. Parity, prescriptions, and unfinished native composition

`starExtended_cut_eq` proves exact preservation of every label-fiber cut
when each added actual copy has equal endpoint labels. It requires no
two-vertex-fiber premise. Repeated use can preserve an already established
joining-cut parity through the star insertions. It does not supply the
initial odd/even joining parity, prove that all protected boundary
insertions have the required trace, or package a final native palette.

The next composition still has the following concrete obligations:

1. Use the weighted grouping construction at the native odd/even palette
   choice point. Derive its seed properness, seed-count and seed-weight
   certificates, full indexed-piece coverage, and the capacity bound with
   the original `h` retained. Do not attempt to decorate an independently
   chosen unweighted existential palette with an unproved weight bound.
2. In the odd branch, preserve the designated primary seeds and exact
   reserve traces; in the even branch, preserve the protected empty traces.
   Recover the joining-cut parity from the appropriate decomposition.
3. Insert the selected whole residual boundaries and, where present, the
   common internal exceptional bundle. Prove actual matching, disjointness,
   prescribed-copy retention, and the available-color restriction
   certificates described above.
4. Instantiate `native_remaining_star_balance` at each exception and feed
   its actual copy sets and color sets to the sequential extension. Prove
   the final native coverage and prescription statements, including colors
   already covered by joining, protected, or bundle copies.
5. Transport the internal-copy cut equality into the full parity and
   uncovered-core interfaces. Derive the required final footprint and load
   estimates from the initialized family's genuine bounds.
6. Complete robust core factorization and the remaining reconstruction
   steps before promoting a numbered manuscript assertion.

This review found no new mathematical obstruction in the proved reserve,
incidence, balance, or sequential Hall ingredients. It leaves the native
composition obligations explicit and makes no claim that their hypotheses
have already been simultaneously instantiated.
