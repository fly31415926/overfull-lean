# Checked components of the four-odd-parts argument

Recovered from published main commit `54db7b826be05fbba9845f4140aaba0a7db5ba04`. The current combined inventory remains **44 of 69**: the recovered circuit results are supporting components, and the alternate frequent-pattern proof establishes the already-counted Lemma 4.13. Recovered pattern declarations use `Overfull.CircuitPatterns` and `Overfull.CircuitPatternRealization`; `Overfull/Patterns/Compression.lean` is shared with the continuation. Current verification evidence is generated from the combined source tree; no old verification hashes or success reports are reused.


This checkpoint proves the matching-pairing, parity-forest, and actual
surplus-circuit construction used at the end of Lemma 4.15. It also
constructs the virtual-edge multigraph and proves the local classification
of its compatible circuits. Every edge set contains actual edge copies,
so parallel copies and original endpoints retain their identities.

**Lemma 4.15 is not yet a complete checked assertion.** The general
compatible-circuit existence step, its application to the reserved
augmented quotient, and the final assembly from the manuscript's original
hypotheses remain unfinished. The manuscript coverage therefore remains
**44 of 69**, and the main theorem remains unverified.

The strict build and full transitive axiom audit are recorded in
`verification/results.json`. A component is not counted as a complete
numbered assertion merely because its source compiles.

## Actual circuits and incidence classes

`Multigraph.IsCircuit C` means that `C` is nonempty, every incident vertex
has degree two in `C`, and every nonempty proper subset of its incident
vertex set has an edge crossing to the rest. This is the connected
2-regular condition and permits two distinct parallel copies.

`Multigraph.Compatible classOf C` says that two selected copies incident
with the same vertex and belonging to the same incidence class must be
the same copy. Values of `classOf` at nonincident pairs are irrelevant.

`CompatibleCircuitPartition` contains an actual finite family of circuits,
compatibility of every part, pairwise edge disjointness, and the exact
union identity. It is a structure describing an output, not an assumption
that such an output always exists.

The handshake identity proves that a circuit has equally many copies and
incident vertices. On four labels it therefore has at most four copies.
Cut counting proves that every compatible circuit partition satisfies
the necessary half-cut inequalities

```text
2 * classCutOn(classOf, C, v, k, X).card <= cutOn(C, X).card.
```

The converse is not yet formalized here for arbitrary incidence classes.

## Quotient copies lift to original matchings

`G.labelQuotient label hjoin` retains the original edge type and maps
each endpoint to its core label. The hypothesis `hjoin` says that every
edge in this supplied host has distinct endpoint labels. The intended
application uses the host restricted to joining edges.

`G.endpointClass label` records the actual original endpoint at an
incident quotient label. The theorem
`Multigraph.compatible_endpointClass_iff` proves the exact equivalence

```text
quotient compatibility of C <-> G.IsMatching C.
```

This also applies to parallel quotient copies. A separate embedding
version allows additional virtual copies in the quotient while retaining
an injection from the original copies.

## Ordinary Eulerian decomposition on four labels

`Multigraph.exists_circuitPartition` constructs a circuit partition of
any finite even-degree edge-copy set on four labels. The proof repeatedly
removes two distinct parallel copies. When the remaining pair projection
is injective, a kernel-checked classification over the six unordered
label pairs shows that a nonempty simple even graph on four labels is a
triangle or a four-cycle.

`exists_compatibleCircuitPartition_of_compatible` additionally preserves
compatibility when the entire input edge set is already compatible.
That stronger input is available for the remainder of an actual
original-graph matching. It is not implied here by the half-cut
inequalities, and this theorem is not the restricted Fan--Zhang theorem.

## Hall pairing and retained forests

The support-counting theorem proves that a set of at most `b` vertices
meets at most `b * a` members of a family in which each vertex occurs at
most `a` times. For two equally large indexed families, Hall's condition
follows when their common order exceeds `2 * b * a`.

`CircuitPatterns.exists_six_endpoint_pairing` specializes this to the two path
families in the manuscript. Under support size at most six, vertex load
at most `a`, and `12 * a < u`, it constructs a permutation pairing
disjoint supports. Each paired union is proved to be an actual matching.

`Multigraph.family_support_load_le_degreeOn` derives each vertex's family
membership load from the degree in an actual edge pool containing
pairwise edge-disjoint family members. Together with
`edgeSupport_card_le`, this proves
`CircuitPatterns.exists_three_edge_pairing_of_degree_bound`: the support and
load conditions follow from at most three copies per member, edge
disjointness within each family, and degree at most `a` in their common
original edge pool. Global edge disjointness between the two input
families is needed separately when asserting a partition of their union.

`CircuitPatterns.exists_odd_matching_forest` takes an actual matching whose four
projected degrees are odd and constructs a subset with injective pair
projection and at most three edges. Its projection is one of the three
perfect matchings or one of the four three-edge stars. Every projected
degree of the actual set-difference remainder is even.

`CircuitPatterns.exists_odd_matching_forest_circuit_split` completes that local
construction: its `ForestCircuitSplit` output contains the retained
forest and an actual compatible circuit partition of exactly the
discarded copies. Every circuit lifts to an original matching with at
most four copies. The retained forest and circuits are disjoint and
cover the original matching exactly.

`CircuitPatterns.exists_paired_forest_circuit_splits` assembles Hall pairing
with this construction. Its explicit parity hypothesis requires the
projected degrees of every potential pair to sum to odd numbers. The
two virtual-edge path families are intended to supply this property.
Additional theorems preserve exact coverage and edge disjointness across
the whole indexed family when those properties hold for the input
families.

## Virtual-edge construction and classification

`Multigraph.virtualAugmentation Q h` has edge type
`E ⊕ (Bool × Fin h)`. It preserves every original edge and adds `h`
distinct copies of each pair `01` and `23`. The original classes embed
into `K ⊕ Unit`; all virtual incidences use the one new class. The degree
at each label is exactly its old degree plus `h`.

For a supplied compatible circuit, the following are proved.

| Virtual copies | Actual conclusion after their removal |
| --- | --- |
| Zero | The original copies themselves form a connected circuit in `Q`. |
| One | At most three original copies remain; their projected degrees are odd exactly at the endpoints of the unique virtual pair. |
| Two | Exactly two original copies remain, each label has original degree one, and there is one virtual copy from each family. |

A compatible set has at most one virtual copy from each family, hence at
most two altogether. The original part remains compatible with its
original classes. These statements classify supplied circuits and do not
construct the initial compatible decomposition.

`CompatibleCircuitPartition.oneVirtualParts_card_add_twoVirtualParts_card`
derives the exact family counts from an actual partition of the full
augmented edge set. If `r` parts have two virtual copies and `u_b` parts
have one copy from family `b`, then `u_b + r = h`. Thus the two one-virtual
families have the same size `u = h - r`, and `r + u = h`. The proof sums
actual virtual copies using the partition's cover and disjointness
identities. Part indices are retained as subsets of the circuit family,
so passing to original copies cannot collapse distinct circuit indices.

## Exact deletion accounting

`Multigraph.admissibleOn_sdiff_iff` proves that deleting `D ⊆ C`
preserves admissibility exactly when every class and shore satisfies

```text
2 * classCut(C).card + cut(D).card
    <= cut(C).card + 2 * classCut(D).card.
```

Thus compatibility of the deleted circuit alone does not justify safe
deletion. In an admissible even-degree graph, cut slack is even. Since a
four-label circuit removes at most four crossing copies, only cuts with
slack zero or two require additional checks. The theorem
`admissibleOn_sdiff_of_critical_cuts` proves this sufficient test. Finding
a compatible circuit that meets all those critical-cut tests remains an
existence problem.

## Small finite inputs and the remaining existence theorem

The small-kernel files contain explicit edge-copy templates for four
parallel edges, a doubled triangle, and the three connected four-vertex
4-regular multiplicity patterns `(3,1,0)`, `(2,2,0)`, and `(2,1,1)`.
Opposite pairs have equal multiplicities in the latter templates. At a
used vertex, a local choice selects one of the three partitions of its
four incidences into two forbidden pairs.

Stored partition witnesses are checked by Lean's kernel against explicit
endpoints, connectivity, degree, compatibility, coverage, and
disjointness. External search only proposes the finite witness data; it
is not trusted as a proof. The complete family has 279 distinct relevant
class assignments, and irrelevant choices at unused vertices do not
affect the graph.

These finite results do not prove that an arbitrary admissible quotient
reduces to one of the templates. In particular, no minimal-counterexample,
cut-vertex, degree-two-suppression, or general forbidden-class reduction
is asserted as proved by the finite tables.

`CompatibleCircuits.three_vertex_integer_flow` is a separate arithmetic
input for a possible one-forbidden-vertex reduction. Given zero total
integer demand and the three singleton capacity bounds on a triangle,
it supplies bounded integer signed flows by choosing a point in an
explicit interval. Selecting and orienting actual edge copies and
constructing the associated circuits are separate steps.

The external target is Fan and Zhang, *Circuit Decompositions of Eulerian
Graphs*, Journal of Combinatorial Theory, Series B 78 (2000), 1--23,
[doi:10.1006/jctb.1999.1923](https://doi.org/10.1006/jctb.1999.1923),
Theorem 1.1 ([author-hosted paper](https://www.math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2000-Compatible.pdf)).
The needed four-label consequence is still unproved here. The paper's
theorem is not imported as an axiom.

## Remaining work for Lemma 4.15

1. Construct the reserved `s` actual forest matchings from the original
   pair supplies and prove the required endpoint-conflict bounds.
2. Prove every original and virtual class-cut inequality in the precise
   augmented quotient after those reserved deletions.
3. Construct a compatible circuit partition of that quotient from its
   Eulerian and admissibility hypotheses, with no decomposition premise.
4. Reinsert the reserved circuits, derive the family-size reserve and
   original endpoint loads, and apply the checked pairing and
   forest/circuit-splitting results.
5. Assemble the exact partition into `h` primary matchings and all surplus
   circuit matchings from the manuscript's original hypotheses.

The separate factorization input for Lemma 4.14 and the later terminal
factorization are also unresolved in this published proof chain.
