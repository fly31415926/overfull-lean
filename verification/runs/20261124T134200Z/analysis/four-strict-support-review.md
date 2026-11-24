# Four-label strict support and triangle reductions: semantic review

This review covers the new modules `FourStrictSupport`, `FourStrictTriangles`,
`FourStrictComplete`, and `FourStrictDiamond`. All statements use the actual
selected edge-copy set `C`, the original endpoint graph, and original
incidence classes. No module assumes the compatible partition it is intended
to help construct. None imposes a bound on edge multiplicities or degrees.

## Support with one or two neighbors

`bundle_monochromatic_of_no_compatible_pair` translates the elementary
two-coordinate selection result into actual two-edge circuits. Two copies
with distinct class values at both ends are distinct copies, have equal
unordered endpoints, and satisfy `IsCircuit` and `Compatible`. Their finite
set has exactly two members and is contained in `C`.

`no_single_bundle_incidence_of_no_compatible_pair` needs only admissibility
and absence of a compatible pair. If the sole positive bundle at a vertex is
monochromatic there, its local class bound is impossible. If it is
monochromatic at its neighbor, the nonlocal singleton class bound is equally
impossible. Thus a nonisolated vertex cannot have just one support neighbor.

`two_neighbor_bundle_structure` additionally uses strict nonlocal singleton
bounds at the common vertex. A largest bundle cannot be monochromatic at its
other endpoint: strictness would make its size less than half the common
vertex's degree. It is therefore monochromatic at the common vertex, where
the weak local bound forces equality of the two bundle sizes. Applying the
same argument to the other bundle makes it monochromatic too. The two
constant class values must differ, since otherwise the whole positive
incidence set would violate a local half-degree bound. This proves equality
of cardinalities and compatibility of every cross-bundle pair, retaining all
original copies.

## Actual triangles and common corners

`isCircuit_triangle_of_distinct_vertices` and
`compatible_triangle_of_endpoint_classes` operate on any ambient vertex
type. They require three distinct vertices and one copy on each of their
three endpoint pairs. The circuit proof explicitly verifies degrees,
support and all nonempty proper cuts. Thus extra ambient vertices are not
silently deleted.

`triangle_common_corner_of_no_short_circuit` combines actual pair
construction, the existing elementary three-bundle selector, and the actual
triangle construction. If no compatible circuit of at most three copies
exists, every nonempty triangle support has a whole corner in one incidence
class. `common_corner_local_bound` and `common_corner_strict_cut_bound` bound
the union of its two disjoint actual bundles by one original class. The
strict cut lemma requires an explicit nonlocal shore containing both
neighbors and excluding the corner vertex.

## Complete four-vertex support

`exists_short_compatible_circuit_of_four_complete_support` requires original
admissibility, `StrictNonlocalOn`, and nonemptiness of the six actual bundles.
It concludes the existence of an actual compatible circuit contained in `C`
with at most three copies. Even degrees are not required for this selector.

The exact degree and opposite-shore cut sizes are proved by summing over the
six unordered endpoint bundles. Each of the four triangles supplies a
monochromatic blocker if no short circuit exists. For each blocker, the
local bound says that the two corner bundles total at most the remaining
incident bundle; the strict opposite-shore bound says that they total less
than the two bundles from the opposite vertex. All 81 choices of one blocker
per triangle are discharged by checked natural-number linear arithmetic.
This is finite classification of blocker assignments, not enumeration of
bounded multiplicities.

In the opposite-pair blocker configuration, the two corners tested on the
same two-versus-two cut give directly `A < B` and `B < A`. This avoids the
longer monochromatic-edge argument in the preceding checkpoint's proposed
route.

## Diamond support

`exists_short_compatible_circuit_of_four_diamond_support` has the same
conclusion when exactly bundle `2--3` is empty and each of the other five
bundles is nonempty. The missing bundle gives exact two-bundle incidence
identities at vertices 2 and 3. The two-neighbor theorem gives equal sizes
`m02 = m12` and `m03 = m13`. A blocker at either support-degree-two vertex is
impossible by its local bound. The two triangles must therefore be blocked
at vertices 0 or 1. Any assignment contradicts those equalities, the local
bounds, and positivity of the common bundle `0--1`.

## Scope

These modules settle the diamond and complete-support selector branches and
supply the support restrictions needed by the separate uniform-cycle and
support-classification modules. They do not, in isolation, prove an
unrestricted four-label compatible-circuit partition theorem, a full
manuscript assertion, or a terminal factorization. Strictness can be lost
after a deletion, so a complete induction also needs the nonlocal tight-shore
branch. Genuine development commands, failed attempts, successful checks and
source snapshots are retained under the same run's `development/` directory.

## Additional reviewed tight-shore modules

`FourTightShoreOutsideGeometry` proves exact incidence and class identities
for the explicit outside graph `shoreIntoLabel X w`. Retention means the two
contracted labels are distinct. Consequently a retained copy touching `X`
crosses `X` and was not originally incident with `w`; otherwise it would
become a loop. At every original outside incidence its class is retained.
At the added anchor incidence its class is exactly the designated `k`.
A copy avoiding `X` keeps its exact unordered pair of endpoints. The optional
endpoint theorem identifies the unique original exterior endpoint, proves
that it differs from `w`, and states both original and contracted endpoint
pairs. These results have no admissibility, evenness, or bounded-degree
assumptions: they are identities of the explicit contraction.

`FourTightShoreClosed` treats original inside pieces disjoint from all
surviving outside copies. Any boundary copy absent from that contraction
has equal contracted endpoint labels, so its original exterior endpoint is
`w`. Therefore every exterior incidence in a saved piece occurs at `w`.
Its degree at `w` equals its boundary cardinality, which the inside-piece
construction proves to be zero or two; every other exterior degree is zero.
Interior degrees were already proved even. Combining this evenness with the
original compatibility of the piece gives a genuine circuit partition
without requiring the piece to be connected. Finally the pairwise disjoint
saved pieces are refined into a partition of their exact original-copy
union.

A direct review of the separate `CompatibleBlockExpansion` and
`outsideExpansion` interfaces confirms the intended restoration logic:
original interior conflicts are prevented because every block meeting `X`
has the same class at `w`, so an outside compatible part can contain at most
one such block. Original exterior conflicts transfer by exact class
identities. The exact outer degree identity and pairwise block disjointness
transfer evenness to the expanded copy set. The expansion can then be
partitioned into circuits by the previously verified ordinary four-label
circuit theorem. This reasoning does not require an expanded set itself to
be connected and does not merge distinct original parallel copies.
