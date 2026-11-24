# Remaining final protected-residual factorization route

Status: **analysis of a remaining composition, not a completed two-core theorem**.
Prepared during run `20261124T010000Z` by the agent owning
`NativeAssembly/BaseClasses`, `NativeBundles`, `NativeTwoStars`, and `Paired`.
The following separates existing Lean interfaces, the additional one-core
ingredient compiled in this run, and the two-core work still required.

## Conclusion

After completing all nonprotected external colors, the intended final
residual has degree `s = r / 2`. Its old cores remain robust and almost
`s`-regular. Its only copies outside the old-core internal edge sets should
be the selected, unmodified native reserve boundaries. This special shape
permits reduction to one-core factorization: split along the original
assigned shores; if these shores are odd, contract the opposite shore to a
single apex and align the two palettes on their common crossing copies.

The one-core factorization engine already exists. In particular,
`Overfull.TerminalComplement.exists_uniform_terminal_factorization` and
`exists_uniform_terminal_one_factorization` allow one unrestricted apex,
boundedly many other exterior vertices, and a small bound on each ordinary
exterior vertex's incidences outside the robust core. They require neither
a supplied complementary coloring nor a no-overfull hypothesis. Setting
that ordinary incidence bound to zero covers the proposed pieces.

The new module `Overfull/NativeCore/IndependentExterior.lean` also proves a
direct independent-exterior specialization, including the actual
complementary coloring and the full one-core factorization. It does **not**
construct the terminal pieces, their embedded cores, or the final two-core
factorization. No numbered source assertion is promoted by this report.

## Exact completed one-core ingredient

The following declarations are in namespace `Overfull.NativeCore`:

| Declaration | Proved input-to-output content |
| --- | --- |
| `edgesTo_exterior_eq_empty` | `G.internalEdges Uᶜ = ∅` implies `G.edgesTo x Uᶜ = ∅` for every `x ∉ U`. |
| `complement_colorable_of_independent_exterior` | For a regular `k`-degree host, arbitrary deleted copy set `H`, independent exterior, complementary degree at most `a` on `U`, and `2*a < k`, constructs `Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k)`. There is no exterior-cardinality bound here. |
| `complement_colorable_of_independent_exterior_real` | The same exact-copy conclusion for a nonnegative real error, using its natural floor. |
| `core_complement_colorable_of_independent_exterior` | For `C : SmallCuts.Core G U`, derives the complementary degree bound from regularity and `k-a ≤ degree(C)` and constructs the coloring. |
| `exists_uniform_independent_exterior_factorization` | For fixed positive density and robustness parameters and fixed exterior bound `s`, produces a positive tolerance and order threshold before all graph data. Every sufficiently large even-order regular host with independent exterior, a robust old core, linear degree, and sufficiently small core error is edge-colorable with its degree. Either original core parity is allowed. |
| `exists_uniform_independent_exterior_one_factorization` | Returns exactly `k` pairwise disjoint perfect matchings whose union contains every original edge copy. |

The complement proof uses
`Multigraph.exists_kMinimal_subset` and
`Multigraph.first_fan_of_core_degree`. In a hypothetical minimal
noncolorable restriction, the first fan removes its internal-core edges.
Every exterior vertex has all `k` incidences into the core, so the same
fan removes all its incidences into the core as well. The remaining edge
set is internal to the independent exterior and therefore empty. This
contradicts minimal noncolorability. This argument needs only `2*a < k`,
and does not appeal to preservation of no-overfullness after arbitrary
matching deletion.

The uniform factorization then invokes
`OrdinaryFactorization.exists_uniform_factorization_any_core_parity`.
Its tolerance is shrunk to `min η (α/4)` and its core-order threshold to
`max m₁ 1`; regularity and core containment derive `0 ≤ a`, while the
density and small-error inequalities derive `2*a < k`. Finally,
`BoundedExterior.exists_oneFactorization_of_coloring` changes the coloring
to an exact perfect-matching partition.

Focused verification was genuinely recorded as
`development/independent-exterior-001/command.json` and `output.log`:

```text
lake build --wfail Overfull.NativeCore.IndependentExterior
```

It passed on its first recorded attempt, exit code 0, 3,338 jobs, with no
input changed during the command. The run's unchanged full audit remains
the authority for integration and total declaration counts.

## Completed prefix interface and remaining structural consequences

Let `H` be the `h`-regular host immediately before native external-class
completion, and let `F : Fin h → Finset E` be the constructed external
classes. Let `f : Fin s → Fin h` select their protected colors. Each
protected class is exactly its selected native reserve boundary `R_t`.
Let the `h-s` nonprotected classes be completed to perfect matchings, and
write `H*` for the actual copy residual after deleting those matchings.

`NativeCore.exists_two_core_boundary_prefix` is the relevant existing
completion interface. It constructs the actual perfect-matchings prefix,
keeps a supplied reserved set untouched, embeds both exact remaining
cores into the residual, proves residual degree `k-q`, preserves robust
expansion with its returned parameters, and gives core minimum degree at
least `k-q-a`. It additionally certifies that the added copies lie in the
two original old-core internal sets.

This run's integration theorem
`NativeCore.exists_uniform_native_unprotected_prefix` in
`NativeCore/NativePrefix.lean` performs this application with `q=h-s`.
It chooses its constants before graph data, establishes both packing
horizons, invokes the constructed external palette and old-core parity
certificates, and reindexes the nonprotected colors. It returns the actual
prefix, both retained robust cores, exact final degree `r/2`, core degree
lower bounds `r/2-a`, and the external-copy remainder identity. Its
focused command receipts and the final full audit determine the
integration verification status; this review does not infer success from
the source statement alone.

The copy-accounting ingredients in `NativeCore/PrefixSelection.lean` are
`unprotectedEquiv`, `unprotectedClasses`,
`palette_union_selected_reserve`, `completed_prefix_external_remainder`,
and `completed_prefix_surviving_external`. The last two prove that the
external remainder is precisely the original selected reserve union,
both as a subtraction of original copy sets and inside the actual
residual-copy subtype. Thus the exact external remainder should not be
assumed again as a new unproved input to the next stage.

The next structural lemmas must derive the corresponding **geometric**
description of `H*`: every copy either has both endpoints in one original
old core or is one of the selected reserve copies; the latter split into
assigned-exception stars, an optional exceptional-pair component, and
zero or one old-core crossing copy per selected boundary. These are
consequences of the new exact remainder identity and the old boundary
geometry. Their uniform factorization composition is not supplied by the
independent-exterior module.

This step must retain all parallel copies. In particular, exceptional
pair copies and old-core crossing copies cannot be identified just by
their unordered endpoint pair.

## Assigned shores and terminal pieces

Use the original fixed assignment from the reserve representative:

```text
A₀ = AssignedParts.corePart G M Z U₀
A₁ = AssignedParts.corePart G M Z U₁
B  = AssignedParts.pairPart G M Z
```

The old cores `U_i` are contained in the assigned shores `A_i`.
The fixed signature makes the same assignment valid for every selected
reserve parent. Useful proved interfaces include
`AssignedParts.assignedLabel_fibers`,
`AssignedParts.corePart_cutOn_eq_core_crossings`,
`AssignedParts.coreParts_cutOn_eq`,
`AssignedParts.corePart_card_parity`, and
`AssignedParts.assignedLabel_parity_eq_core_crossing`.
The reserve-specific `NativeReserve.BoundaryPacking.assignedLabel` and
`crossing_card` expose this agreement for the actual compressed boundaries.

`AssignedParts.compressedBoundary` retains every exceptional incidence and
uses `paritySelection` on the original old-core crossing copies.
`paritySelection_card` says that this selection has exactly the original
crossing parity, hence zero or one copy. Thus every selected boundary has
the same crossing count `p ∈ {0,1}`, and the intended residual assigned
shore cut contains exactly `s*p` distinct original copies.

| Signature and shore parity | Intended terminal geometry | One-core host order and exterior |
| --- | --- | --- |
| Unpaired signature; both assigned shores even | No residual edge between `A₀` and `A₁`; factor their actual induced multigraphs separately. | The host on `A_i` has even order. Its robust core is the original `U_i`; its at most two assigned exceptions are an independent exterior. |
| Unpaired signature; both assigned shores odd | Exactly `s` residual crossing copies between old cores. Keep all vertices of `A_i`, collapse its complement to one apex, and retain copies incident with `A_i`. | `|A_i|+1` is even. The old robust core is still `U_i`; exterior consists of its assigned exceptions and the new apex, at most three vertices, with no edges among them. |
| Paired signature | The two original exceptions form a separate component containing precisely `s` parallel copies between them. Here `A_i=U_i`. | Factor that two-vertex component by a bijection from copies to `Fin s`. The old-core pieces use the same even-shore or odd-shore construction, with zero or one exterior vertex. |

The assigned shore parities agree because the host order and `|B|` are
even; the existing exact cut parity theorem also proves their equality.
The parity relevant to choosing contraction is the parity of `A_i`, not
necessarily the parity of `U_i`. The factorization engine already handles
either parity of the smaller robust old core.

Exterior independence in the unpaired case has substantive content:
all selected exceptional incidences go from an assigned exception to its
assigned old core; there are no selected exceptional-pair copies. The
only retained inter-shore copies have both endpoints in old cores. After
contracting the opposite assigned shore, the new apex therefore has no
edge to an assigned exception. These facts must be transported through
the final residual equality before invoking the independent-exterior
theorem.

## Existing contraction and palette transport

The graph-level contraction is already implemented in
`Overfull/BoundaryExtension/Contraction.lean`:

- `BoundaryExtension.contract G A` keeps every original copy incident
  with the chosen vertex set `A`, maps `A` injectively into `A ⊕ Unit`,
  and sends every outside endpoint to the apex.
- `degree_inl` preserves every retained vertex degree exactly.
- `degree_apex` and `degree_apex_eq_cutSize` identify apex degree with the
  actual cut-copy count.
- `contract_regular` gives regularity from the retained vertex degrees
  and exact cut size.
- `even_contracted_order` gives even host order when `A` is odd.
- `boundaryApexEquiv` identifies each original boundary copy with its
  apex incidence.

For `A=A_i`, this directly supplies the intended regular graph once the
exact `s`-copy cut is proved. However, `contractCore` currently embeds a
core whose vertex set is the whole contracted retained set. The robust
core needed here is the smaller `U_i ⊆ A_i`. One must construct its image
as a finset of vertices in `A_i ⊕ Unit`, transport the old core graph
through that vertex equivalence, and map its actual edge copies to the
retained-edge subtype. The existing `contractCore` construction provides
a model; `RobustRealization.comap_equiv_degree` and
`robust_comap_equiv` preserve the old degree and expansion exactly.
The even-shore branch similarly needs a finite vertex-restricted host
and an exact embedded old core; retaining all original vertices would
leave irrelevant isolated vertices and fail regularity.

No new abstract palette-permutation theorem is needed.
`BoundaryExtension.exists_singleton_boundary_extension` takes an actual
coloring of the contraction, an exact cut size, and any injective labels
on the actual boundary copies. It produces a coloring of the retained
original graph agreeing on each boundary copy and using only those
labels. It is built from `restoreSingletonLabels`,
`pullbackContractColoring`, and the saturated-vertex palette equivalence
in `BoundaryExtension/Palette.lean`.

In the odd-shore case, give the common `s` crossing copies any bijection
to `Fin s` (or to the original protected palette). Apply this transport
on both sides with the same labels, then glue along their common copy
set. Properness at a vertex on one shore follows from that shore's
retained coloring. The shared crossing copies must be represented once
in the final original-copy coloring. In the even-shore case, gluing is
disjoint and arbitrary common color indexing suffices. The paired
two-vertex component is another disjoint component.

These transport theorems do not by themselves produce the required
contracted coloring. That is the point where the established terminal
factorization or the new independent-exterior specialization is used.

## Quantitative composition and final reassembly still open

The final factorization requires its own parameter hierarchy. It must
prove that the terminal degree `s` is a positive fixed fraction of each
old-core order, that the old-core error is below the tolerance returned
by the one-core theorem, and that each core exceeds its returned order
threshold. The robustness parameters returned by prefix completion must
be selected or weakened to satisfy the one-core theorem's parameter
inequalities. The original host density alone does not immediately give
these claims for `s=r/2`; the reserve lower bound and rounding estimates
must be used explicitly.

Once the original-copy residual coloring is constructed, its classes can
be converted to `s` perfect matchings using
`BoundedExterior.exists_oneFactorization_of_coloring`. Their union with
the `h-s` completed prefix matchings must then be transported through the
residual subtype, shown pairwise disjoint, and shown to cover every copy
of the preceding host. Any earlier removed prefixes in the full theorem
need the same exact final reassembly.

This route preserves the selected reserve **copies** during prefix
completion, but its final one-core factorizations may recolor exceptional
star incidences. Singleton crossing labels can be restored; it does not
prove that every originally prescribed whole reserve boundary remains
monochromatic after terminal factorization. The Corollary 4.6
factorization conclusion does not require that stronger precoloring
extension. A theorem that explicitly asks to extend all original reserve
color classes would need further work.

The next narrow implementation target is therefore the geometric
consequences of the exact protected remainder and the two actual shore
hosts with their embedded old cores. After those, apply the already proved one-core
factorization and singleton-boundary label transport, prove the explicit
copy-level gluing, and close the uniform parameter/reassembly wrapper.
The full fixed-pattern Lemma 4.4, two-core Corollary 4.6, five-exception
obligations, and the main theorem remain outside the results asserted
here.
