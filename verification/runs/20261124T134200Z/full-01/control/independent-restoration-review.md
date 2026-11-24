# Independent review of strict selection and tight-shore restoration

## Scope and conclusion

This review inspected the new strict-selection chain, the complete tight-shore
integration, and the final selected-copy induction in `FourExistence.lean`.
No missing original-copy case, assumed target partition, or unproved
connectedness claim was found. The final four-label theorem has the original
half-cut inequalities and even selected degrees as its only mathematical
hypotheses beyond the loopless multigraph structure. It imposes no degree,
parallel-multiplicity, connectivity, or positive-cut restriction.

The reviewer implemented the inside contraction, inside pieces, pairing,
blocks, and block-assembly modules. The strict branch and final integration
were reviewed independently of their implementation; this is not a claim
that every constituent module received a second review by a different author.
This source review is separate from the root agent's frozen full build and
axiom audit. It does not change any numbered-assertion record.

The verified remote baseline for this continuation was
`3991bb7eee091a329046073e0366daa84a603e5d`. All development attempts are retained
in this run's `development/` directory, including unsuccessful attempts.
The following actual recorder receipts were inspected:

| Receipt | Command result | Inputs changed during command |
| --- | --- | --- |
| `tight-assembly-02/command.json` | `lake -KwarningAsError=true build Overfull.CompatibleCircuits.FourTightShoreAssembly`: exit 0, passed | None |
| `tight-completion-03/command.json` | `lake -KwarningAsError=true build Overfull.CompatibleCircuits.FourTightShoreCompletion`: exit 0, passed | None |
| `four-existence-build-01/command.json` | `lake -KwarningAsError=true build Overfull.CompatibleCircuits.FourExistence`: exit 0, passed | None |

These are development receipts, not substitutes for the forthcoming frozen
verification receipt. The later strict verifier determines the final audited
source identity and permitted axiom closure.

## 1. Strict branch: hypotheses and descent match

`NonlocalShore v X` requires that each side of the cut contain a vertex
different from the tested incidence-class vertex `v`. `StrictNonlocalOn`
requires the strict half-cut inequality for every such shore, including
zero cuts. This is deliberate: under original admissibility it is equivalent
to the absence of **any** tight nonlocal class cut. A disconnected zero cut
therefore enters the tight branch, rather than disappearing from the case
split.

`FourStrictCoarsening.lean` preserves both original weak inequalities and
strict nonlocal inequalities when a locally tight class is replaced by its
two complementary classes. The complement-class argument uses the exact
toggled-shore identity. A circuit compatible for these coarsened classes
remains compatible for the original classes and meets every original
locally tight class at a visited vertex. The final selector obtains a
`Nonempty K` instance from an actual selected copy, so there is no extra
inhabited-class assumption in the public theorem.

The strict support argument first either selects an actual compatible
parallel pair or deduces endpoint monochromaticity of each nonempty parallel
bundle. Original local bounds and strict singleton-shore bounds rule out
support degree zero or one. The finite classification on four vertices then
gives a square, diamond, or complete support. It is checked with Lean's
`decide`; it is not a `native_decide` certificate or a custom decision axiom.

For the square, the no-compatible-pair alternative contradicts the strict
singleton bound at a neighboring vertex. For triangles, absence of a
compatible actual-copy triangle supplies a monochromatic blocked corner.
The diamond and complete-support arguments turn these corner assignments
into contradictory incidence inequalities. The complete-support case uses
finite corner choices and arithmetic; no edge multiplicity or maximum
degree is bounded. The separate arbitrary-multiplicity cycle construction
is valid support material, but the final strict selector only needs a pair
or triangle of at most three copies.

`exists_safe_short_circuit_of_four_strictNonlocal` supplies:

- An actual nonempty circuit `D` contained in the original selected set `C`.
- Compatibility in the original incidence classes and `D.card ≤ 3`.
- Admissibility and even degrees on the exact residual `C \ D`.
- Strict decrease of the number of selected original copies.

It does **not** assert residual strictness. `FourExistence.lean` correctly
runs the strict/tight case split afresh in the induction hypothesis for the
residual. This is essential: deleting a safe circuit can create a tight
nonlocal inequality.

`FourNonlocalReduction.lean` normalizes any tight nonlocal shore by
complementing it if necessary. The normalized shore is nonempty, avoids the
class vertex, and has at most two vertices. The proof uses nonlocality on
both sides and the four-vertex cardinality; it also applies to zero cuts.

## 2. Inside construction preserves copy identity and original classes

The inside quotient has vertex type `Option X`: each vertex of `X` remains
distinct and every other original vertex becomes the apex. Its edge type is
the subtype of the **original** edge copies with at least one endpoint in
`X`. Parallel copies remain distinct. No new copy is substituted for an
original edge.

At an incidence, the temporary class records both the original endpoint
and its original class. Hence quotient class cuts are exact images of the
appropriate original class cuts. Original admissibility implies quotient
admissibility. Original even degrees imply even quotient degrees by cut
parity. The chosen tight class at the original anchor becomes a locally
tight tagged class at the apex; its coarsening into chosen/complementary
classes is proved admissible.

Because `X.card ≤ 2`, the inside quotient has at most three vertices.
`exists_tightShoreInside_partition` invokes the previously proved
at-most-three existence theorem. It does not receive a partition, pairing,
or selector as a hypothesis.

The injective image back to original copies produces `TightShorePieces`.
Each part is nonempty and compatible in the original classes at **every**
original vertex, has even degrees inside `X`, and has boundary of one of
the following exact forms:

| Boundary type | Exact original-copy data |
| --- | --- |
| Empty | No selected edge crosses `X` |
| Two copies | Exactly one copy in the anchor's chosen class and exactly one in its complement |

The parts are pairwise disjoint and cover every original copy touching
`X`. `FourTightShorePairing.lean` strengthens the cardinalities to actual
distinct witnesses `a,b`, with `δ_D(X) = {a,b}`, chosen boundary `{a}`,
and complementary boundary `{b}`. No path connectedness or orientation is
assumed.

## 3. Outside quotient is derived from original admissibility

The outside quotient is the original graph under the map sending every
vertex of `X` to the anchor `w`, leaving all other vertices fixed. Its
surviving edge type is again a subtype of the original copies. Copies
internal to `X` and copies between `X` and `w` become loops and are omitted
from this quotient; the inside pieces retain all of them.

At `w`, redirected incidences share the chosen class `k`; original exterior
incidences retain their original class. At other surviving exterior vertices
the original class is unchanged. The outside admissibility theorem derives
all its bounds from the original graph. For the merged anchor class, the
proof uses the original inequality on the normalized shore together with
`X` and the tight equality for `X`. The supporting exact cut identity is
the usual union identity for disjoint shores:

`|δ(T ∪ X)| + 2 |E(T,X)| = |δ(T)| + |δ(X)|`.

Other classes are bounded directly by original class cuts. Quotient
evenness follows from original cut parity. Since `X` is nonempty, the
outside support has at most three vertices. Thus
`exists_tightShoreOutside_partition` constructs its actual partition from
the earlier at-most-three theorem; no outside partition is assumed by the
final tight-shore endpoint.

## 4. Restoration has no missing-copy or duplicated-copy branch

A surviving outside copy that touches `X` belongs to exactly one inside
piece. It is that piece's unique complementary boundary copy and its
exterior endpoint differs from `w`. Therefore no inside piece contains two
distinct surviving outside copies.

`outsideBlock` uses this unique piece for a redirected copy. An original
copy with both endpoints outside `X` receives a singleton block. The blocks
are pairwise disjoint on actual original copies. `closedParts` consists of
the inside pieces disjoint from the surviving outside-copy set.

The final exact cover can be checked one original copy at a time:

1. If the copy has no endpoint in `X`, looplessness shows that it survives
   the outside quotient and indexes a singleton block containing itself.
2. If the copy touches `X`, the inside cover puts it in one part `D`.
   If `D` has an outside survivor, that survivor indexes the whole `D`.
   Otherwise `D` belongs to `closedParts`.

This is the proof of `outsideBlock_union_closedParts_cover`. The companion
disjointness theorem proves that the expanded block union and the closed
part union share no original copy. This handles both internal copies and
pieces whose two boundary copies return to the anchor. Such returning
pieces must be saved even though both boundary copies vanish in the
outside quotient, and they are saved here.

For an open piece, exact exterior degree is the incidence indicator of its
outside copy: one at `w`, one at the other exterior endpoint, and zero at
every other exterior vertex. Both exterior class labels are exactly the
original labels on those incidences. The `common_class` property ensures
that every block meeting `X` has the same class at the outside anchor.
Consequently a compatible outside part can contain at most one such block.
This transfers original compatibility across different blocks, including
vertices inside `X`.

Block disjointness makes degrees add. Inside degrees are sums of even
degrees; exterior degrees equal the corresponding even degrees of the
outside part. Every expanded part is therefore globally compatible and
even. The earlier ordinary theorem
`exists_compatibleCircuitPartition_of_compatible` decomposes that part.
This theorem already assumes and uses whole-set compatibility, which has
just been proved, and it predates the general existence result under review.
There is no circular invocation of `FourExistence`.

For a saved closed piece, all exterior incidences lie at `w`. Its degree
there is zero or two according to its empty or two-copy boundary; every
other exterior degree is zero. Its interior degrees and global compatibility
were established inside. The same ordinary compatible-even decomposition
therefore partitions every closed piece. The finite partition refinement
and disjoint union in `FourTightShoreCompletion.lean` preserve exactly the
two unions in the cover identity above.

No statement that a restored block or expanded part is connected is needed.
Connected circuit pieces are obtained by the already proved ordinary
decomposition. An empty tight cut is covered without a special positivity
assumption: all its inside pieces are closed and the outside support still
has at most three vertices.

## 5. Final theorem and ambient-type generality

The final tight endpoint is
`Overfull.FourOdd.exists_compatibleCircuitPartition_of_tight_shore`. Its
assumptions are the original all-copy admissibility and even degrees, one
nonempty shore of size at most two, an anchor outside the shore, and the
original tight class-cut equality. Inside pieces, the outside partition,
the expansion data, and the saved-piece partitions are constructed in the
body.

`FourTightShoreRestriction.lean` applies this finite all-copy theorem to the
subtype of any finite selected set `C`. Exact degree and class-cut identities
transport the original hypotheses to that subtype. Its injective copy map
transports the resulting partition back to exactly `C`.

`exists_compatibleCircuitPartition_of_four_label` then uses strong induction
on `C.card`: empty case, safely removable short circuit in the strict case,
and direct tight-shore construction otherwise. The ambient edge type need
not be finite. Finally,
`exists_compatibleCircuitPartition_of_card_le_four` embeds any finite
vertex type of cardinality at most four into `Fin 4`, transfers the
incidence classes and inequalities, and restores the partition on the
unchanged original copy type.

Source inspection found no `sorry`, `admit`, custom `axiom`, `unsafe`, or
`native_decide` declaration in the new four-label proof chain. The frozen
axiom audit remains the authoritative check of transitive proof dependencies.

## 6. Source map for the new construction

All module names in this table are under `Overfull.CompatibleCircuits`.

| Modules | Mathematical role |
| --- | --- |
| `FourStrictCoarsening`, `FourNonlocalReduction` | Preserve strict bounds under local coarsening; normalize the complementary tight case, including zero cuts |
| `FourStrictSupport`, `FourStrictTriangles`, `FourStrictDiamond`, `FourStrictComplete` | Turn absence of actual compatible short circuits into contradictory bundle inequalities |
| `FourSupportClassification`, `FourSupportReduction`, `FourStrictSelection`, `FourStrictSafeSelection` | Exhaust support types, select an actual pair/triangle, and prove safe strict descent |
| `FourTightShoreContraction` | Original endpoint-and-class tagging, quotient admissibility/parity, tight apex coarsening |
| `FourTightShoreInside`, `FourTightShorePieces`, `FourTightShorePairing` | Construct the at-most-three inside partition and exact original-copy boundary pairs |
| `FourTightShoreOutside`, `FourTightShoreOutsideGeometry` | Construct the outside quotient, its admissibility/partition, and exact incidence geometry |
| `FourTightShorePieceGeometry`, `FourTightShoreBlocks`, `FourTightShoreAssembly` | Give each surviving outside copy its unique block and prove all expansion fields |
| `FourTightShoreExpansion` | Refine compatible even expanded blocks into circuits, without assuming connectedness |
| `FourTightShoreClosed`, `FourTightShoreCompletion` | Save omitted closed pieces; prove exact total cover and full tight-shore existence |
| `FourTightShoreRestriction`, `FourExistence` | Selected-copy transport, strong induction, and arbitrary at-most-four vertex types |
| `FourJoiningComplete` | Apply the result to original-host all-even and exactly-two-odd joining copies without boundary-size restrictions |

## 7. Read-only next-target assessment: terminal Proposition 4.16

The new `FourJoiningComplete.lean` removes the previous small-boundary
conditions from both original-host joining decompositions. For at most four
even fibers it gives disjoint original matchings of size at most four with
even fiber footprints. For exactly two odd fibers it gives exactly `h`
primary original matchings of size at most three, plus surplus matchings of
size at most four, with exact cover and the odd/even footprints.

These are complete circuit-stage outputs. Proposition 4.16 is still not a
formalized consequence of the current terminal modules. The shortest next
concrete target is a bounded grouping theorem for pieces of size at most
four. `ResidualPalette/PaletteGrouping.lean` has a generic finite greedy
extension theorem, but its graph specialization assumes piece size at most
three, giving conflict bound `6D` and whole-group support bound `6L`.
The four-copy version can use `8D` and `8L`, with the corresponding capacity
`N ≤ L(r-8D)`. The parity and exact-copy union proofs already apply.

After that helper, there are two distinct terminal obligations:

1. **Four even cores.** Group all joining pieces into the short prefix;
   complete these matchings with the existing arbitrary-index
   `exists_prefix_completion`; then apply the existing arbitrary-index
   `exists_uniform_closed_core_factorization` to the four now-closed even
   cores. The current `PrefixPalette` records `6L` support, so either a
   width-parameterized or a separate four-copy prefix interface and numerical
   parameter proof are needed. The robust completion itself already accepts
   arbitrary core indices.
2. **Exactly two odd cores.** Select a short primary prefix, absorb every
   surplus piece into it, and retain the other `h-r` primary pieces with
   their full parity profile. Contract the two odd cores to apices while
   retaining both even robust cores and all surviving original copies.
   Establish regularity and no-overfullness of this two-core/two-apex host,
   apply the already proved `two_core_two_exception_factorization`, then
   align the odd-shore singleton boundary colors and glue all original
   copies back. The completed prefix is restored last.

The second obligation is not merely a change from `Fin 3` to `Fin 4`.
`Terminal/PartLabels.lean` uses the three-label identity that all joining
copies are the union of the two odd-fiber cuts. That identity is false on
four labels: a primary path can have shape odd--even--even--odd, and its
middle copy belongs to neither odd cut. The residual transcript must retain
this even--even copy and both even cores. Existing `Terminal/OddFactorization`
keeps only one even central core, so it does not supply this case directly.

A concrete route to the new central no-overfull lemma is available from
`SmallCuts.small_cut_lemma`, which bounds the **sum** of the core minorities
by one. The residual primary family has odd footprint at the two apices
and even footprint at each even core. An odd test shore with zero minority
contains exactly one apex, so every primary contributes a crossing. With
one minority vertex, the union of full majority cores and selected apices
has even parity; moving that one vertex makes every primary incident there
contribute a crossing. The remaining degree at that vertex is supplied by
internal core edges. This is a prospective proof obligation, not a theorem
claimed in this run.

Once those two cases and their uniform-parameter composition are proved,
they can be combined with the existing three-core theorem and
`four_odd_terminal_one_factorization`. The latter already has the actual
forest-pair supply hypotheses required by its all-four-odd branch. A final
source comparison must check the complete Proposition 4.16 statement,
including its supplied data and quantifier order, against pinned statement
hash `1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c`.
This is a plausible next route to a 50th completed numbered assertion,
subject to completing those constructions and the frozen audit. The present
run's general four-label theorem alone does not justify promotion from
49/69 or a claim of terminal one-factorization.
