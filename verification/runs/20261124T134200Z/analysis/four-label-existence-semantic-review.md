# Semantic review: unrestricted four-label compatible circuits

This review covers the ten new modules owned by the cycle/strict/induction
workstream. All source files are under `Overfull/CompatibleCircuits/`. It
records mathematical scope and exact interfaces; the run's genuine command
receipts and final frozen whole-project audit determine verification status.
No numbered manuscript assertion is promoted by this note alone.

## Final public criterion

`Multigraph.exists_compatibleCircuitPartition_of_four_label` constructs a
partition on `Fin 4` from precisely the original admissibility inequalities
and even selected degrees. The ambient edge type need not be finite. The
selected copy set is an arbitrary `Finset E`; parallel copies remain distinct.

`Multigraph.exists_compatibleCircuitPartition_of_card_le_four` gives the same
result on every finite vertex type of cardinality at most four. It embeds
vertices injectively into `Fin 4`, adds only isolated labels, uses the existing
`Option`-valued class embedding, and pulls the exact same parts back. It does
not assume that the original class type is inhabited.

`compatibleCircuitPartition_iff_admissible_and_even_of_card_le_four` combines
that sufficiency with both necessary conditions. Evenness is proved by the
sum of the degrees of the pairwise disjoint actual circuit parts. The existing
`CompatibleCircuitPartition.admissibleOn` provides necessity of all half-cut
inequalities. The concrete `Fin 4` specialization is
`fourLabel_compatibleCircuitPartition_iff_admissible_and_even`.

The final result assumes neither regularity, a degree bound, a copy-count
bound, a pre-existing circuit partition, a safe selector, strict nonlocal
inequalities, connectedness, nor positive minimum degree. Looplessness is part
of the existing `Multigraph` type. Every cut is tested in `AdmissibleOn`, with
the tested original incidence class at every vertex.

## Complete proof dependency structure

The proof uses strong induction on the number of selected original copies.
The empty selected set receives the existing empty partition.

If every nonlocal class-cut inequality is strict, a simultaneous local
tight-class coarsening preserves both admissibility and strictness. The
nonempty strict input then has an actual compatible pair or triangle. Every
coarse-compatible selected pair meets every original tight local class, so
the exact deletion criterion proves original admissibility after deletion.
The circuit has even degrees and at least one copy; the residual therefore
has even degrees and strictly fewer copies. Induction supplies the residual
partition, and `insertCircuit` restores the selected original copies.

Residual strictness is not asserted or needed. The next induction step may
take the tight-shore branch.

If strictness fails, original admissibility makes a genuinely nonlocal
inequality tight. `FourNonlocalReduction` normalizes the shore, by taking its
complement when necessary, to a nonempty set of at most two labels excluding
the class vertex. This includes zero cuts. The complete tight-shore endpoint
in `FourTightShoreCompletion` constructs the partition by the inside and
outside three-label graphs and exact block restoration. This is a direct
construction, not an invocation of the four-label induction hypothesis.

The tight-shore construction uses a finite whole edge type. The restriction
module replaces an arbitrary residual `C` by the finite subtype of its actual
copies, proves every degree/cut/class-cut identity, invokes the construction
on `univ`, and maps the resulting parts back bijectively to `C`.

## The strict support argument

The strict selector does not bound multiplicity. It uses the underlying
simple support only to classify which unordered endpoint pairs occur.
Every subsequent selection and all counts concern the original copies.

Strict nonlocal singleton inequalities force positive degree at every label.
In the absence of a compatible parallel pair, every nonempty bundle is
monochromatic at at least one endpoint. The original half-cut inequalities
then rule out a support vertex with only one neighbor. The loopless support
therefore has minimum degree at least two.

`FourSupport.classify_min_degree_two` exhausts finite subsets of the ten
unordered pairs on four labels, excludes loops, and returns a square, a
diamond, or the complete support, with explicit finite permutation lists.
The proof uses Lean's kernel `decide`; there is no external computation or
native decision axiom. This finite classification places no bound on the
number of copies in any present bundle.

At a vertex with two support neighbors, strictness and the original local
half bound force equal bundle sizes and constant, distinct classes at the
corner. In a square these facts at two neighboring corners make one bundle
monochromatic at the opposite endpoint while its size is half the adjacent
degree. Its strict singleton inequality would say `2m < 2m`. Thus the square
support under strict nonlocal inequalities already has a compatible parallel
pair. This strengthens the earlier proposed proof route, which had only
constructed a terminal square partition.

The diamond and complete support alternatives use the separately verified
`FourStrictDiamond` and `FourStrictComplete` endpoints. They force a pair or
triangle from the original admissibility and strictness inequalities.
Relabeling preserves strictness, all exact copy sets, compatibility, and
circuits, so the canonical support theorems apply to each labeled support.

The resulting theorem
`exists_short_compatible_circuit_of_four_strictNonlocal` assumes only
nonemptiness, original admissibility, and strict nonlocal inequalities. It
does not need even degrees. Evenness enters only in the later safe-deletion
theorem. Only pairs and triangles are deleted in the strict branch; no
unjustified arbitrary four-cycle deletion is used.

## Exact original-copy restoration checks

The uniform template construction is independent of the strictness argument.
For an injectively indexed simple circuit template whose bundles all have
the same size, finite bijections enumerate each actual bundle. Each index
selects one copy from each template edge. The copy embedding proves that
these are genuine circuits. Cross-bundle incidence-class separation proves
compatibility. Joint injectivity proves disjointness, and bundle surjectivity
proves exact cover. The C4 specialization permits arbitrary multiplicity.

`FourTightShorePieceGeometry` verifies the key exterior identities used by
the full tight-shore assembly. For a retained outside-contraction copy `e`
belonging to an inside piece `D`, it proves:

1. `e` is the unique complementary boundary copy of `D`. A retained copy
   touching the shore cannot originally be incident with the anchor.
2. For every exterior vertex, the original degree in `D` is exactly the
   incidence indicator of `e` in the outside graph.
3. Every original exterior incidence in `D` has exactly the class prescribed
   by `e` at that exterior vertex, including the new anchor incidence.

The proofs use the actual boundary equality `delta(D) = {a,e}` and the
singleton prescribed class `{a}`. They do not replace original copies by
unlabeled multiplicities or assume the desired partwise restoration.

## Per-module proof map

| Module | Main proved contribution |
| --- | --- |
| `FourUniformCycle.lean` | Generic uniform simple-template partition; arbitrary-multiplicity C4 partition. |
| `FourStrictCycle.lean` | Corner incidence identities and C4 partition constructed from strict singleton hypotheses and absence of compatible pairs. |
| `FourSupportClassification.lean` | Kernel support classification; positive degrees and support minimum degree two from actual graph hypotheses. |
| `FourSupportReduction.lean` | Strictness/partition transport under vertex equivalences; exact support pullback; relabeled square endpoint. |
| `FourStrictSelection.lean` | Strict square implies a pair; every nonempty strict four-label input has a compatible circuit with at most three copies. |
| `FourStrictSafeSelection.lean` | Coarsening and exact deletion give a safe short circuit, even residual degrees, and strict copy-count decrease. |
| `FourTightShorePieceGeometry.lean` | Complementary-boundary membership, exact outside degree, and exact outside class restoration for each piece. |
| `FourTightShoreRestriction.lean` | Copy-embedding class cuts; finite selected-copy restriction identities and exact partition lift. |
| `FourExistence.lean` | Full tight/strict induction and arbitrary vertex types of cardinality at most four. |
| `FourCharacterization.lean` | Necessary evenness and the full necessary-and-sufficient half-cut/parity criterion. |

These modules add 55 public source declarations, including definitions and
supporting theorems. The generated audit may count additional private or
compiler-generated declarations; its declaration map is authoritative for
that larger count.

## Verification evidence and boundaries

The full existence source passed its first strict dependency build,
`four-existence-build-01`, with 3,193 build jobs and unchanged input hashes.
The preceding strict selector and tight piece geometry each have their own
successful focused checks and dependency builds. All failed development
attempts are retained by the shared recorder with exact source snapshots,
commands, exit status, and output hashes.

These successful module builds do not replace the final frozen root build,
transitive axiom audit, old-source/declaration preservation checks, or public
branch/tree readback. The broader Overfull manuscript theorem and numbered
assertion coverage are separate project claims to be assessed by the root
verification inventory.
