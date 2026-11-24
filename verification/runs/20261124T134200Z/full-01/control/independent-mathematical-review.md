# Independent mathematical review: unrestricted four-label compatible circuits

## Conclusion and exact scope

The current source completes the unrestricted compatible-circuit existence
problem on at most four labels. The principal declarations are
`Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label` and
`Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_four` in
`Overfull/CompatibleCircuits/FourExistence.lean`.

For a loopless multigraph `G`, arbitrary incidence classes `classOf`, and a
finite selected set `C` of actual edge copies, the hypotheses are exactly:

1. Every original class-cut count is at most half its original cut count:
   `G.AdmissibleOn classOf C`.
2. Every selected original degree is even.
3. For the general vertex-type endpoint, the finite vertex type has
   cardinality at most four.

The conclusion is `Nonempty (G.CompatibleCircuitPartition classOf C)`. Its
structure requires genuine nonempty connected 2-regular parts, compatibility
in the original incidence classes, pairwise disjointness of the actual copy
sets, and an exact union equal to `C`.

No compatible selector, partition, strictness, regularity, positive minimum
degree, bound on degree or multiplicity, or finiteness of the ambient edge
type is an assumption of the final theorem. Thus the previous unbounded
four-label obstruction is removed at this theorem interface. This is a
specific combinatorial existence theorem; it is not an assertion that the
whole Overfull Conjecture manuscript or all four-core factorization results
are now verified.

The genuine command record
`development/four-existence-build-01/command.json` reports exit code 0,
3193 successful build jobs, and no input changes during that command. Its
output records successful construction of `FourTightShoreRestriction` and
`FourExistence`. This focused receipt is separate from the complete frozen
project audit and publication readbacks, which were not yet complete when
this review was written.

## Review method and boundaries

I read the root's strict coarsening, safe-deletion, nonlocal normalization,
outside-graph, block-expansion, completion, selected-subtype restriction,
and final-existence source, together with the support classification,
relabeling, strict selector and uniform-cycle modules. I compared the
actual theorem statements and supplied hypotheses at the interfaces. I also
read the inside contraction/pieces, boundary pairing, block selection and
block assembly on which the final tight branch depends.

The reviewer authored the strict support/triangle/diamond/complete-support
lemmas and two geometry/closed-piece modules in this run. Consequently the
independent portion of this review is the root and sibling implementation,
its assembly, and its statement-level composition; it is not described as an
independent reimplementation of those authored lemmas.

A source scan of the new strict, support, normalization, uniform-cycle and
tight-shore modules found no `sorry`, admitted proof, new `axiom`,
`native_decide`, or `unsafe` proof path. This scan is an additional source
check, not a substitute for the project's transitive declaration audit.
Finite classification uses ordinary `decide` proof terms checked by Lean's
kernel. The final whole-project audit must still establish the actual
transitive axiom sets for the frozen source snapshot.

## Strict nonlocal branch

`NonlocalShore v X` says that each side of the cut contains a vertex other
than the tested class vertex `v`. `StrictNonlocalOn` requires a strict
inequality on every such shore, including a zero cut. This is intentionally
strong enough to be the exact complement of the existence of a tight
nonlocal class-cut, once weak admissibility is assumed. Zero cuts therefore
fall into the tight branch rather than being lost under a connectivity
assumption.

The local coarsening retains a tight local class and merges its complement.
Its weak global validity was already established. The new strictness proof
uses the exact toggled-shore count identities: the complementary class's
slack at `X` equals the designated tight class's slack on the shore obtained
by toggling `v`. `NonlocalShore` is invariant under that toggle. Consequently
all strict nonlocal bounds transfer. The auxiliary `Nonempty K` requirement
for unused coarse class values is supplied from an actual selected copy in
the safe selector. It does not leak into the final theorem.

The actual short-circuit selector covers all simple support shapes. A
nonempty strict input forces positive degree at every label. If a vertex
has only one support neighbor, absence of a compatible pair contradicts a
local or nonlocal singleton half bound. The remaining loopless support is
therefore a relabeled square, a relabeled diamond, or the complete graph.
The finite classification returns exact endpoint-support equalities and
explicit vertex permutations. Relabeling preserves all selected actual
copies and pulls original incidence classes back through the permutation.

The square branch is stronger than the previous proposed proof route:
under strict nonlocal bounds a square cannot have no compatible pair. The
two-neighbor structure gives equal adjacent bundle sizes and a constant
class on a full bundle at its opposite endpoint, violating the strict
singleton inequality. Thus the strict selector always returns an actual
pair or triangle; it does not require a terminal four-cycle partition.
The separate arbitrary-multiplicity uniform-cycle theorem remains valid
as its own exact-copy construction.

The safe-deletion proof distinguishes circuit existence from deletion
safety. A coarse-compatible circuit meets every tight original local class
at each vertex it uses. If a tight cut is crossed, strictness implies that
it is local, so it is a singleton at the tested vertex or that singleton's
complement. The original exact small-circuit deletion criterion then proves
residual admissibility. Even degrees survive deleting a circuit. Its
nonempty actual copy set gives a strict decrease of the selected copy count.
The source correctly does **not** claim that residual strictness survives.

## Normalizing the tight branch

Failure of strictness, together with weak admissibility, supplies an actual
tight nonlocal class-cut. Complementation preserves both the original cut
and class-cut counts. Choose the side not containing its class vertex.
Nonlocality makes that side nonempty and leaves at least two distinct
vertices on the other side: the class vertex and one other vertex. On four
labels the selected shore therefore has cardinality at most two.

This supplies exactly the nonempty shore, cardinality bound, exterior class
vertex and tight equality required by the tight-shore construction. It also
covers disconnected inputs and tight cuts of size zero.

## First finite construction: inside graph

The inside graph collapses all exterior vertices to an apex and retains
every actual copy touching the shore. The original endpoint and class are
recorded together, so a quotient incidence class has precisely the
corresponding original class-cut count. Original admissibility therefore
transfers before coarsening. The specified original tight class becomes a
tight local apex class, permitting a two-class apex coarsening.

There are at most three labels (`Option X`). Even original degrees give even
quotient degrees by the exact cut-degree identity. The previously verified
three-label theorem constructs the inside partition. No inside path pairing
or partition is assumed.

Pulling its parts back to original copies gives a disjoint, exact cover of
all copies touching the shore. Every part is originally compatible, has even
interior degrees, and has either no boundary or precisely one designated
class boundary copy and one complementary boundary copy. These are proved
properties of the constructed pieces.

## Second finite construction: outside graph

The outside graph contracts the shore into the chosen exterior class
vertex. It retains all copies with distinct contracted endpoints. Exterior
copies remain unchanged; retained boundary copies keep their other original
endpoint and original class there, and receive the designated class at the
anchor.

For a quotient shore excluding the anchor, its original label preimage is
disjoint from the contracted shore. The exact disjoint-shore cut identity,
the designated tight equality, and admissibility on the union of those two
shores bound all redirected anchor incidences. Other class-cut counts are
bounded by their original class-cut counts. Complementation handles quotient
shores containing the anchor. No arbitrary incidence splitting is used.

The quotient has even degrees and support contained in the complement of a
nonempty original shore, hence at most three active labels. The verified
support-at-most-three theorem constructs its partition. Again the outside
partition is a conclusion, not an assumption of the tight-shore endpoint.

## Exact restoration and coverage

A surviving outside copy touching the shore cannot originally touch the
anchor: otherwise both contracted endpoints would coincide. It is therefore
a complementary boundary copy of its unique inside piece. Each inside
piece has only one complementary boundary copy, so two distinct surviving
copies select disjoint pieces. An exterior surviving copy selects its exact
original singleton.

The `CompatibleBlockExpansion` interface is populated by these constructed
blocks. At every exterior vertex a block has degree one exactly when its
outside copy is incident; its original class agrees with that copy's class.
All interior block degrees are even. Every block meeting the shore has the
same designated class at the outside anchor. Therefore a compatible outside
part uses at most one such block, preventing any new interior class
conflict. Exterior conflicts transfer by the exact class identities.
Pairwise disjoint blocks allow the degree-sum identity to transfer evenness.
The expanded set need not be connected: the already verified ordinary
four-label decomposition refines an originally compatible even set into
genuine compatible circuits.

Inside pieces with no surviving outside copy are retained as `closedParts`.
Every exterior incidence in such a piece is at the anchor. Its degree there
is its boundary cardinality, zero or two, and its other exterior degrees
are zero. Thus these pieces are originally compatible and even and also
receive genuine circuit partitions.

Completion proves both exact cover and disjointness of the expanded outside
blocks and the saved pieces. A copy touching the shore belongs to its unique
inside piece; either that piece contains a surviving outside copy and is
selected as its block, or it is saved. A copy avoiding the shore survives
as an exterior singleton. These cases include the copies whose contraction
would become loops. The two constructed partitions are combined only after
proving disjointness, giving the entire original edge set exactly once.

## Selected-copy restriction and final induction

The tight-shore construction uses a finite whole edge type, while the final
theorem allows arbitrary `E` and a finite selected set `C`. The restriction
module changes the edge type to the subtype `C`, proves exact degree, cut
and class-cut cardinality identities, transfers the tight equality and
admissibility, and maps the resulting partition back through the injective
subtype embedding. The conclusion covers precisely `C`, not all ambient
copies and not merely its simple support.

`FourExistence` then performs strong induction on `C.card`. The empty input
has its explicit empty partition. In the strict branch the checked safe
short circuit is removed and the induction hypothesis is used only on the
strictly smaller residual with its proved admissibility and evenness. The
residual is permitted to have a tight nonlocal cut. In the other branch the
normalized tight-shore construction directly partitions the entire selected
input. The old `insertCircuit` interface gives exact disjoint reassembly.
Finally, injective padding into `Fin 4` transfers the result to every finite
label type of cardinality at most four, including smaller or empty types.

## Joining wrappers and the exact criterion

I also inspected `FourJoiningComplete.lean` and the existing decomposition
structures and quotient bridges it invokes. Each wrapper constructs its
quotient partition by the new unrestricted theorem, then applies the
unchanged injective original-copy transport.

- `exists_fourJoining_decomposition_of_even_fibers` assumes at most four
  labels, original `h`-regularity, absence of original `h`-overfull sets,
  and even cardinality of every label fiber. It has no small-boundary or
  joining-degree assumption. Its `FourJoiningDecomposition` conclusion
  supplies nonempty disjoint original matchings of size at most four,
  covering exactly the original joining copies, with each matching's
  boundary at each fiber equal to zero or two.
- `exists_fourJoining_decomposition_of_even_degree_bound` allows arbitrary
  fiber parity. It explicitly retains even regular degree and a uniform
  original joining-degree bound `D` with `2 * D ≤ h`, as well as the
  regular/non-overfull hypotheses. The wording must retain this per-vertex
  bound; the unrestricted statement here concerns quotient size and the
  former small-fiber-boundary restriction.
- `exists_fourTwoOddJoining_decomposition` assumes exactly two specified
  distinct odd fibers and even cardinality of all remaining fibers, at
  most four labels, original regularity, and absence of original overfull
  sets. Its augmented quotient uses exactly `h` virtual copies without a
  small-boundary or virtual-multiplicity hypothesis. The existing
  `FourTwoOddJoiningDecomposition` structure gives exactly `h` distinct
  nonempty primary original matching pieces of size at most three. Each
  has boundary one at both odd fibers and odd boundary exactly at those
  fibers. Surplus pieces have size at most four and even boundaries
  everywhere. The families are disjoint and cover every original joining
  copy exactly once.

The genuine `development/four-joining-complete-01` receipt has exit zero,
3204 successful build jobs and no input changes. Its command used Lake's
package-option syntax; this focused receipt is not described as an
independent warning-as-error gate. The final verifier uses `lake build
--wfail` and remains the warning-sensitive project gate.

`FourCharacterization.lean` adds the converse parity condition for arbitrary
vertex types: disjoint circuit degrees sum to the original selected degree,
so all selected degrees are even. Together with the existing necessary
half-cut theorem and new existence result, this proves the exact
necessary-and-sufficient criterion on at most four finite labels, including
the specialized `Fin 4` criterion. No stronger hypothesis is introduced.
The first focused characterization build genuinely failed and is preserved;
`development/four-characterization-build-02` passed with 3194 jobs, exit zero
and unchanged inputs.

These wrappers complete the stated joining circuit-stage outputs. They do
not construct the subsequent four-core reserve, grouping, palette, robust
completion or final uniform factorization. The distinction from full
Proposition 4.16 and Theorem 4.17 is preserved in the source and documentation.

## Completed and remaining status

Completed in the reviewed source and focused build: unrestricted four-label
compatible-circuit existence, its selected-copy tight-shore construction,
the cardinality-at-most-four extension, its exact converse criterion, and
the three original-host joining wrappers reviewed above. I found no additional
mathematical hypothesis in the proof interfaces that weakens those stated
conclusions.

This review does not itself change any numbered manuscript assertion or
source identity. The reviewed original-host joining outputs are circuit-stage
results. Terminal factorization and global Overfull assertions must be
checked against their own full interfaces before any numbered-coverage promotion. The complete frozen build, declaration
mapping, transitive axiom audit, preservation audit, source/output hashes,
and public branch readbacks remain distinct verification/publication gates.

## Reviewed source SHA-256 values

The following hashes fix the implementation read for this review. Later
source changes require checking the affected conclusions again.

| Source module | SHA-256 |
| --- | --- |
| `FourStrictCoarsening.lean` | `321806b885cd897d19343938ba02fd1e92ce46ebca80f2217fd4e3a2604420ef` |
| `FourStrictSafeSelection.lean` | `f6a8a9841e2e00d44a57cfa20b8a1102845ba62625b88bf2569d5be1a67d8960` |
| `FourNonlocalReduction.lean` | `f7d06e58f836e3cd3155d6f8917681b70f2aa5e29bafabc2a85e49bfd80aea96` |
| `FourTightShoreContraction.lean` | `bc7c56c21f411f457d21e2df7e30583743bd5959e23ae179cafda0e3899e53b4` |
| `FourTightShoreInside.lean` | `2e08ca1609e6307ebe2cf45523b237486e1d8e08adec4ac1a7bdac67f954a384` |
| `FourTightShoreOutside.lean` | `f9efe2600330d277462848d8661aef6f3ddc21d47d7376acb3956ee93ba890a5` |
| `FourTightShoreExpansion.lean` | `08650aa52d59801a1dd460c0b41da849cf9b66b7c975934ced2b7d89d580507b` |
| `FourTightShorePieces.lean` | `ebeedf26c1d0bb7224ec95b7621b0c209245d0ed0a4d5baaa885908565738803` |
| `FourTightShorePairing.lean` | `b44b8b05eb4365597a1f7c234335a0cd54a61207dcef22de6f7ba9e739e19684` |
| `FourTightShoreBlocks.lean` | `4ca81d126902b3891067ed916bbf7173dfae0b1a08cbbbd317d9fe250466ae1c` |
| `FourTightShorePieceGeometry.lean` | `a594c11090936420a789e6d0985062c8baa6eead6b060ed4673d069c97c9bb06` |
| `FourTightShoreAssembly.lean` | `4da0de1bfb78e9a88c4b8a4089439ba1e5580c0f66e12a4902342a9d5f2395e2` |
| `FourTightShoreCompletion.lean` | `10f4abd9d729b6a79992fb33347a5c3978d0208b20090a07e1b3b9b3eec239ed` |
| `FourTightShoreRestriction.lean` | `23a43eec041bcf984a50f76080d6344018b3c4097bfb50378057694cdcad3e81` |
| `FourUniformCycle.lean` | `e6a0ceac0b05a583ccf888e08bec4f7091029a1f9d550476bf360d6b345b23b9` |
| `FourStrictCycle.lean` | `9cf3434078dbd203922d0ee9347beff7660ed889c4d8d8b96a4ecd3836f0b605` |
| `FourSupportClassification.lean` | `27b7a34db9d5803af55c90a7779309e86ba1046b4597cb675ae56455227efc99` |
| `FourSupportReduction.lean` | `796fb64d76b8d23e4c5a88abb16a4f77e2e2871292d8cd857b8bc3982125f6e1` |
| `FourStrictSelection.lean` | `351c956aae1298546204474bbe12b1fb0876f3cb109520266a6033e3b796f5f4` |
| `FourExistence.lean` | `e03d30e032bbc00f212529405c8d3aad5804578d4fe49fb0c18e014d22cad028` |
| `FourJoiningComplete.lean` | `a7733333226233c4f8f6aecd459ee1358873b85120a91e59243065207b0a280c` |
| `FourCharacterization.lean` | `6a832b965756a005e5a1df9ab93f8c221ecc830b82b5dbcc12dfb17220724636` |
