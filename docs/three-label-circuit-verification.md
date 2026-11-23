# Complete compatible circuit decomposition on at most three vertices

## Exact result and scope

Let `G : Multigraph V E` be a loopless multigraph, let `C : Finset E` be
the selected actual edge copies, and let `classOf : V → E → K` assign
incidence classes. Values at nonincident vertex/copy pairs are irrelevant.
Assume that `V` is finite with at most three vertices, every degree in `C`
is even, and for every vertex `v`, class `k`, and vertex shore `X`,

```text
2 * (G.classCutOn classOf C v k X).card ≤ (G.cutOn C X).card.
```

The new theorem constructs `G.CompatibleCircuitPartition classOf C`.
Its parts are nonempty connected 2-regular actual-copy subgraphs, are
compatible in the original incidence classes, are pairwise disjoint, and
have union exactly `C`. Parallel copies remain distinct throughout.
Empty `C` and isolated vertices are included. Neither the entire copy type
`E` nor the class type `K` needs to be finite.

The main three-label declarations are:

- `Overfull.Multigraph.exists_threeLabel_safe_circuit`;
- `Overfull.Multigraph.exists_threeLabel_compatibleCircuitPartition`;
- `Overfull.Multigraph.threeLabel_compatibleCircuitPartition_iff_admissible`.

The first selects a safe circuit with exactly two or three copies from
every nonempty admissible even-degree residual. The second constructs the
complete partition without assuming a selector. The third proves that,
for even-degree graphs on three labels, admissibility is equivalent to
existence of that partition. `AtMostThree.lean` supplies the arbitrary
finite-vertex wrapper `exists_compatibleCircuitPartition_of_card_le_three`.

This is supporting progress. It does not complete the general four-label
compatible-circuit theorem, the joining construction for full Corollary
4.6, fixed-pattern Lemma 4.4, terminal Proposition 4.16, Section 6, or the
main theorem. The original numbered inventory remains **47 complete out
of 69**, with all original statement hashes retained.

## Proof chain

| Module | Checked contribution |
| --- | --- |
| `LocalCoarsening` | Two-coordinate selection; a coarser class map with half-size bounds whose distinct pairs meet every original tight local class. |
| `ThreeLabelBundles` | Exact actual-copy bundle cover, disjointness, incidence and degree identities, common parity, and reduction of all cut checks to singleton cuts. |
| `EqualBundleSelection` | Selects a compatible triangle from three equal bundles when one endpoint bundle is monochromatic; constructs the actual graph circuit. |
| `EqualBundleSafety` | Handles every ordered nonlocal tight class; proves its fiber fills its bundle and constructs a safely removable triangle. |
| `EqualBundlePair` | With no nonlocal tight constraint, constructs a compatible parallel pair meeting every local tight class and proves residual admissibility. |
| `UnequalBundleSelection` | Constructs a safe parallel pair when `|AB| > |BC|` and `|AC| ≥ |BC|`; derives every tight-class witness from original cut bounds. |
| `VertexRelabeling` | Sorts bundle sizes by actual vertex permutations while preserving all copy sets, circuits, classes, and admissibility. |
| `SafeSelectionInduction` | Constructs and removes actual partition parts, preserves disjointness and exact cover, and proves the strong-induction bridge. |
| `ThreeLabel` | Combines every equal/unequal case and discharges the selector hypothesis in the final partition theorem. |
| `VertexEmbedding` | Transfers actual-copy graph data through an injective vertex map, including unused labels. |
| `AtMostThree` | Applies the three-label result to arbitrary finite vertex types of cardinality at most three. |

### Why deletion is safe

A circuit on at most three vertices crosses each cut in zero or two
copies. In an even-degree graph, positive slack in a class-cut inequality
is at least two, so only tight inequalities can become false after a
compatible circuit is removed. The preserved original deletion theorem
reduces safety exactly to meeting the tight classes on the crossed cuts.
The new selection proofs derive these witnesses; they do not assume them.

At a vertex with a local tight class, its class and complement form a
binary coarsening. Any other local tight class must be that complement.
Distinct coarse classes therefore guarantee original compatibility and
meet every tight local class. The coarsening also records whether it is
the original map or a binary tight-class map, which is needed when a
bundle occupies exactly half the local incidences.

Unequal bundles admit a safe parallel pair in a dominant bundle. Equal
bundles split into two cases: an original nonlocal tight class yields a
safe triangle, while absence of such a class yields a safe parallel pair.
Vertex permutations exhaust all original bundle-size orderings. Deletion
strictly lowers the number of original copies; reinsertion yields the
exact final partition.

## Verification and provenance

The base checkpoint is
`b5afb03a0f0613eedd0cb3310e06706942afe2e7`. The new source inventory is
[`three-label-circuit-source.json`](three-label-circuit-source.json).
It records exact source hashes and every public theorem name. The
verification script checks those names against the complete fresh audit,
including their source modules, and writes the full declaration map to
`verification/three-label-circuit-declarations.json`.

Reproduce the verification with the pinned toolchain and dependencies:

```sh
python3 scripts/verify.py
```

This runs `lake build --wfail` and the unchanged `lake env lean Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The
fresh global counts, source hashes and input hashes appear in
`verification/results.json`; timestamped reports under `verification/runs/`
record preservation of the preceding checkpoint and actual run status.
Refreshing the source manifest alone does not verify a theorem.

The older Python selector experiment remains independent supporting
evidence. No finite experiment or historical verification log is used as
a substitute for the new Lean proofs. The original recovered source
files, previous proof modules, and reconstruction evidence are retained.
