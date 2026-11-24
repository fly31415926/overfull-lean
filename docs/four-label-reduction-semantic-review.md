# Four-label low-degree reduction: semantic review

## Exact scope

The source endpoint is
`Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_small_degree`.
It takes a loopless multigraph on `Fin 4`, a finite set of selected actual edge
copies, arbitrary incidence classes, all original half-cut inequalities, even
degree at every label, and the existence of a label of degree at most two.
It constructs a compatible circuit partition of precisely the original copies.
There is no supplied circuit, partition, safe selector, or bound on the other
three degrees.

The statement is a supporting result. The unrestricted four-label existence
theorem, full Proposition 4.16, full Theorem 4.17, and the main theorem remain
incomplete. All 69 numbered assertion records and their statement hashes remain
unchanged; the complete count remains 49.

Source inspection is distinct from kernel verification. The immutable terminal
receipts for `verification/runs/20261124T120200Z/` determine which actual build,
audit, and preservation commands passed. This note alone does not certify them.

## Support restriction

The selected support graph uses the subtype of selected copies and the subtype
of their actual incident vertices. Its graph map back to the ambient vertex
type is injective, as is the copy projection. Cut, degree and class-cut
identities transfer admissibility and parity to this graph. Applying the
previous complete three-label theorem and transporting its output back gives
the support-at-most-three result, with no ambient vertex-count assumption.

In particular, an isolated label in a four-label problem leaves at most three
active labels. Padding and removing isolated labels never change any selected
edge copy.

## Parallel degree-two incidences

Let `v` have exactly two incident selected copies `e,f`, both joining its
neighbor `a`. Original admissibility forces their classes at `v` to differ.
The class-cut inequality on the singleton shore `{v}`, tested at `a`, forces
their classes at `a` to differ too. They therefore form a compatible
two-edge circuit.

After removing the pair, test any residual shore by placing `v` on the same
side as `a`. Both removed copies disappear from that original cut, and every
remaining copy has the same crossing status and class. The residual is thus
admissible. Its degrees remain even and `v` is isolated. The three-label
theorem supplies the residual partition; inserting the pair restores exactly
the original copy set.

## Distinct-neighbor degree-two suppression

Write the two selected incidences at `v` as `e=av` and `f=vb`, with `a!=b`.
Keep the original copy type, change only the endpoints of `e` to `ab`, and
erase `f` from the selected finite set. The class of the changed incidence at
`b` is inherited from `f`; all other relevant classes are unchanged.

For a tested shore, placing `v` on `b`'s side gives exact equality of the
suppressed cut and the corresponding original cut. This also gives exact
class-cut equality for a class vertex different from `v,b`. At `b`, put `v`
on `a`'s side instead. Swapping the two copy names `e,f` identifies these
cuts and class cuts, so their cardinalities agree. At `v`, the new class-cut
is empty. These identities prove every original half-cut inequality for the
suppressed graph. They do not rely only on the local half-degree inequalities.

All degrees except the degree of `v` are unchanged; `v` becomes isolated.
The complete three-label theorem therefore constructs a partition of the
suppressed selected set.

## Exact restoration and compatibility

Precisely one suppressed part contains `e`. Expand that part by restoring
`f`. At `v`, its two restored incidences have different classes by original
admissibility. At `a,b`, compatibility follows from the suppressed part and
the inherited class at `b`. All other relevant incidences are unchanged.
The entire expanded set is therefore compatible and has even degrees.

The existing four-label ordinary circuit theorem for an already compatible
set partitions this expanded set into genuine compatible circuits. No
unproved connectivity claim is needed. The remaining suppressed parts contain
neither changed copy and transfer unchanged. Their copy sets are disjoint
from the expanded set, so the disjoint-union construction covers exactly the
original finite set. Neither parallel copies nor distinct parts are merged.

This avoids the obstruction recorded in the preceding run: expanding a path
at an arbitrary high-degree vertex can fail compatibility. Here the restored
vertex has exactly the two specified selected incidences.

## Bounded consequences

If all four degrees are at most four, either a label has degree zero or two,
or every label has degree four. The first case uses the new reduction; the
second uses the previous exact four-regular theorem. Connectedness is not
assumed.

If there are at most eight selected copies and no degree is at most two,
evenness forces all four degrees to be at least four. The handshake identity
then forces all four degrees to equal four. Thus every admissible Eulerian
four-label instance with at most eight copies is covered, even if a
different instance in that size range has unequal degrees larger than four.

Consequently any counterexample to unrestricted four-label existence would
have all four degrees at least four, one degree at least six, and at least
nine copies. This necessary description does not assert a counterexample
exists. Finite vertex types of cardinality at most four are handled by
injective labeling and exact copy transport.

## Exact four-copy deletion criterion

For a candidate circuit `D` of at most four copies, every cut has size zero,
two or four in `D`. Compatibility bounds each selected class-cut by one copy.
The exact residual inequality is

`2*classCut(C) + cut(D) <= cut(C) + 2*classCut(D)`.

For an admissible even-degree original set this is equivalent to two explicit
conditions: on a tight cut, the candidate crosses at most twice and meets the
tight class whenever it crosses; on a cut of slack two, four crossings require
a copy from that class. Cuts of larger slack impose no extra condition.
For a pair or triangle, only meeting the tight classes is required. These
are exact equivalences, not an existence assertion for a passing candidate.

## Global admissibility after local coarsening

At a vertex with an incidence class of size exactly half its degree, merge
all other incidence classes into the complementary class. For an arbitrary
shore, let `s` be its cut size, `t` the number of cut copies incident with
the vertex, and `p` the number of those in the original tight class. If the
vertex has degree `d`, toggling it changes the cut size to `s+d-2*t` and
changes the tight-class cut size to `d/2-p`. The original admissibility
inequality on the toggled shore is therefore exactly
`2*(t-p) <= s`, the required inequality for the complementary class.

The formal proof uses natural-number addition identities, so no division,
truncated subtraction, or positivity assumptions are hidden. It applies to
arbitrary vertex types and degrees, without an Eulerian hypothesis. Local
coarsenings may be chosen independently at every vertex and remain globally
admissible. Compatibility for the coarse classes implies compatibility for
the original classes, and the same circuit partition transports unchanged.
The existing local-coarsening structure also ensures that every coarse
compatible pair meets every original tight local class.

This supplies a globally valid preprocessing step. It does not construct a
circuit partition for the unrestricted four-label problem.

## Elementary triangle-bundle selection

For a nonempty finite bundle, absence of a pair with different classes at
both endpoints forces the whole bundle to be monochromatic at one endpoint.
For three nonempty bundles with this property, a compatible choice of one
copy from each exists unless one corner's two entire bundles have one
common class. The proof chooses a monochromatic endpoint for each bundle,
handles the cyclic and transitive orientations, and explicitly covers all
eight endpoint choices. It does not bound the class type or identify copies.

These are statements about finite sets and incidence maps. Their use in a
graph requires the actual endpoint bundles, whose disjointness and geometry
are separate. The graph support classification, safe selector for every
remaining instance, and complete four-label induction are still open.

## Original-host applications

For a regular multigraph with no overfull set, the earlier original-host cut
identities supply admissibility and parity of the joining quotient.

With at most four even fibers, the new theorem constructs exact joining
matching pieces whenever some fiber boundary has at most two copies. The
other boundaries are unrestricted. A second result handles boundaries all
of size at most four. Each output part is nonempty, contains at most four
original copies, and meets every fiber zero or twice. Distinct parts are
disjoint and their union is exactly the original joining-copy set.

With exactly two odd fibers, add the original regular degree `h` virtual
parallel copies between their labels. If an even fiber has boundary at most
two, its augmented degree is still at most two. The new circuit theorem
therefore applies even when `h` and the odd-fiber degrees are arbitrarily
large. Removing the virtual copies and projecting back gives exactly `h`
distinct primary matching pieces of size at most three, plus surplus
matching pieces of size at most four. Primary pieces meet each odd fiber
once; surplus footprints are even everywhere. All original copies are
covered exactly once.

These hypotheses do not cover arbitrary four-core terminal instances.
The separate tight-shore research note in this run is a mathematical plan;
it is not included in the verified theorem inventory.
