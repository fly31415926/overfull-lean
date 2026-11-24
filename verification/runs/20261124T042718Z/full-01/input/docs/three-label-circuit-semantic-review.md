# Semantic review of the three-label compatible-circuit proof

## Reviewed conclusion and hypotheses

The composition in `Overfull/CompatibleCircuits/ThreeLabel.lean` proves
compatible circuit decomposition for a loopless multigraph on `Fin 3`.
The reviewed and strictly compiled extension in `AtMostThree.lean`
proves the same conclusion for any finite vertex type with cardinality
at most three, with arbitrary parallel multiplicities and incidence
classes. The general partition theorem assumes exactly:

- a vertex type `V` with `[Fintype V]` and `Fintype.card V ≤ 3`;
- a finite selected set `C` of actual edge copies;
- an incidence-class map `classOf : V → E → K`;
- the original `AdmissibleOn classOf C` condition: for every vertex,
  class, and shore, twice the class's crossing-copy count is at most the
  whole cut's crossing-copy count;
- even degree at every vertex within `C`.

The type `K` need not be finite. The type `E` need not be finite; the
selected set `C` supplies the required finiteness. Values of `classOf`
on nonincident vertex-copy pairs do not affect compatibility or the
class-cut inequalities. Looplessness is part of the existing
`Multigraph` structure, not a newly introduced assumption.

The general final declarations are:

| Declaration | Conclusion |
| --- | --- |
| `exists_safe_circuit_of_card_le_three` | Every nonempty admissible even-degree residual contains a compatible circuit of two or three actual copies whose deletion remains admissible. |
| `exists_compatibleCircuitPartition_of_card_le_three` | All original selected copies admit an exact compatible circuit partition. |
| `compatibleCircuitPartition_iff_admissible_of_card_le_three` | For even-degree selected graphs, the original half-cut inequalities are necessary and sufficient. |

Their `Fin 3` counterparts are `exists_threeLabel_safe_circuit`,
`exists_threeLabel_compatibleCircuitPartition`, and
`threeLabel_compatibleCircuitPartition_iff_admissible`.

Neither final existence theorem assumes a circuit selector, a compatible
partition, a compatible pair, or witnesses for tight constraints.
Nonemptiness is required only by the one-step selector. The partition
theorem includes the empty graph and graphs with isolated labels.

## Mathematical sufficiency of the construction

### Exact reduction to singleton cuts

`ThreeLabelBundles.lean` proves that every shore on at most three
vertices is empty, full, a singleton, or a singleton complement. Taking
a shore complement preserves the actual crossing copies and every
class-cut intersection. Thus the reduction to singleton cuts loses no
constraint, including nonlocal incidence classes.

The singleton safe-deletion equivalence is derived from the previously
checked three-label deletion criterion. Its use retains the original
even-degree hypothesis, the original admissibility condition, and the
fact that the deleted copies form a genuine circuit. Positive-slack
constraints are handled by that exact criterion; they are not assumed
away by the selector proofs.

### Coarsening and selection

`LocalCoarsening.lean` constructs either the original class map or the
binary map given by one locally tight class and its complement. Its
`identity_or_tight` field records this actual construction. This field
matters: a general coarsening with only half-size bounds would not
suffice to exclude a monochromatic bundle occupying exactly half a
vertex's incidences.

The constructed coarsening preserves the local half-size bounds.
Distinct coarse values imply distinct original class values, and any
pair with distinct coarse values meets every original locally tight
class. Two distinct tight fibers cover the whole incidence set because
they are disjoint and their sizes sum to its size. These statements
require no bound on the number of original classes.

The two-coordinate selector gives one pair differing in both endpoint
coordinates. It selects actual members of the common bundle, not merely
two class names or two independently chosen endpoint pairs.

### Unequal bundles

`UnequalBundleSelection.lean` constructs an actual safely removable
parallel pair when `|AB| > |BC|` and `|AC| ≥ |BC|`. The selected pair
meets all locally tight classes at both ends and every relevant nonlocal
tight class. The third vertex cannot contribute a tight obstruction on
either crossed cut: the original local half-bound and the smaller bundle
size give strict inequalities.

The proof covers both possibilities for the first endpoint's nonlocal
tight classes. If one exists, its membership is used as a binary
coordinate, and exact fiber-size arguments show that crossing it also
meets every other necessary tight class. If none exists, the constructed
local coarsening is nonconstant on the selected bundle. No selection
witness is added as a hypothesis of the graph-level theorem.

### Equal bundles

The equal-bundle construction splits on the existence of an original
nonlocal tight class. This split is exhaustive over all six ordered
pairs of distinct labels.

If a nonlocal tight class exists, its crossing copies fill the whole
corresponding bundle. `EqualBundleSafety.lean` uses the coarsened maps
and the counting selector from `EqualBundleSelection.lean` to select a
compatible triangle. The local coarsening makes the triangle meet all
local tight classes. One selected copy in each bundle also meets every
nonlocal tight class. Equal bundle sizes imply even degrees directly.

If no nonlocal tight class exists, `EqualBundlePair.lean` derives strict
original fiber bounds on both incident bundles at each relevant
endpoint. These bounds force the constructed coarsenings to be
nonconstant on the common bundle. The selected parallel pair meets
every local tight class, and the nonlocal cases are excluded by the
case hypothesis. The proof concludes residual admissibility through
the same exact singleton-cut criterion.

### Sorting and transfer back

`VertexRelabeling.lean` uses a vertex equivalence to sort the three
bundle sizes. The edge-copy type and every selected copy set stay
unchanged. The class map is pulled back by the inverse vertex
equivalence. The file proves both directions of admissibility and
compatibility preservation, together with circuit preservation and
exact cut and bundle identities.

`ThreeLabel.lean` applies the unequal or equal case to this renamed
graph and transfers the resulting circuit and residual admissibility
back to the original graph. Sorting introduces no hypothesis on the
original ordering of the bundle sizes. The equal case obtains its
positive common size from nonemptiness and the exact three-bundle
cover; no nonempty residual is discarded.

### Padding smaller vertex types

`VertexEmbedding.lean` embeds an arbitrary finite vertex type of size
at most three into `Fin 3`. It maps the two endpoints of each original
copy injectively and introduces only isolated additional vertices. The
copy type `E` and every selected finite set are unchanged.

The extended incidence map takes values in `Option K`: actual original
classes become `some k`, and `none` is used on isolated padding
vertices. This avoids an unjustified inhabitant assumption on `K`.
Injectivity of `some` preserves the distinction between original
classes. All added vertices have degree zero and empty class-cut
intersections, while cuts on image vertices are the pullbacks of
original cuts. The embedding theorems prove both directions of
admissibility and compatibility transfer.

The pullback of a circuit preserves its connectivity, two-regularity,
and selected copies. The pullback of a partition literally retains
its parts, pairwise-disjointness proof, and covering equation.
`AtMostThree.lean` therefore obtains the general theorem without
assuming that the original vertex type or class type is inhabited.
This extension also includes the zero-, one-, and two-vertex cases.

## Induction and original-copy accounting

`SafeSelectionInduction.lean` provides the generic strong-induction
bridge. Its selector hypothesis is explicit in that generic theorem.
The final three-label partition theorem supplies this hypothesis by
the unconditional selector just proved, for every admissible
even-degree residual.

Each selected circuit is a nonempty subset of the current residual.
Deleting it strictly decreases the finite copy count. The checked
even-degree deletion lemma preserves parity, while the selector
preserves admissibility. Reinserting the selected circuit into the
residual partition proves both pairwise disjointness and exact
`parts.biUnion id = C` coverage.

All these sets consist of elements of the original copy type `E`.
Parallel copies are never identified by an endpoint projection, no
copies are silently omitted, and no auxiliary copy enters the final
partition. Vertex relabeling changes neither `E` nor `C`.
The padding extension likewise preserves these exact original-copy
sets and pulls back the resulting partition without modifying its parts.

## Integration review and verification evidence

The reviewed modules contain no admitted proofs, new axioms, or
weakened definition of admissibility. The initially duplicated
specialized parallel-pair circuit helper was removed: the equal and
unequal branches both reuse the existing generic theorem from
`FourLabel.lean`. The inspected import graph has no circular dependency.

This document records the semantic review of the proof statements and
their composition. The strict build and complete project axiom-audit
results, exact source hashes, and declaration mappings are recorded
separately in `verification/`; this review does not stand in for those
checks or introduce an audit declaration count.

## Limits of the result

The three-label result does not prove the general four-label
compatible-circuit theorem. In particular, it does not supply the
four-label selector handling all tight and slack-two constraints.
The broader factorization statements and the main Overfull theorem
still require their other recorded inputs. Completion of numbered
manuscript assertions is tracked separately in `docs/coverage.json`.
