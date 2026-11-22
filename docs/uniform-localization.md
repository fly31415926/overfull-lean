# Uniform localization: actual palettes, blocks, and selected graphs

This continuation starts from published checkpoint `2eb61f5`, where
Theorem 2.23 brought complete numbered coverage to **44 of 69**. It proves
further parts of the Section 6 localization construction. These are
supporting results for Proposition 6.2 and Theorem 6.1. Neither full
factorization statement is claimed. The current complete numbered count
is **45 of 69**, with 24 remaining, after the subsequent
[complete proof of Lemma 4.15](four-odd-decomposition.md).

The principal change is that the graph-specific simultaneous-selection
theorems now choose their positive error tolerance and integer order
threshold before the graph. Their public hypotheses contain no probability
estimates and no assumption that a numerical failure budget is below one.
Actual integer palettes and actual compatible vertex blocks are constructed.

## Uniform simultaneous choices

| Construction | Principal source and theorem |
| --- | --- |
| Graph-specific palette and block failure budgets | [UniformBudgets.lean](../Overfull/BipartiteFactorization/UniformBudgets.lean) |
| Uniform actual disjoint palettes | [UniformSelection.lean](../Overfull/BipartiteFactorization/UniformSelection.lean), `UniformSelection.exists_uniform_palettes` |
| Uniform actual blocks with integer floor caps | [UniformSelection.lean](../Overfull/BipartiteFactorization/UniformSelection.lean), `UniformSelection.exists_uniform_blocks` |
| Positive even palette sizes and their capacity | [IntegerSizes.lean](../Overfull/BipartiteFactorization/IntegerSizes.lean) |
| Actual disjoint palettes with those even sizes | [RoundedPalettes.lean](../Overfull/BipartiteFactorization/RoundedPalettes.lean), `UniformSelection.exists_uniform_rounded_palettes` |
| Equal fine positions and exact coarse unions | [UniformPositions.lean](../Overfull/Probability/UniformPositions.lean) |
| Actual simultaneous fine and coarse vertex blocks | [FineCoarseSelection.lean](../Overfull/BipartiteFactorization/FineCoarseSelection.lean), `UniformSelection.exists_uniform_fine_coarse_blocks` |
| Preferred rows when no correction is needed | [PreferredBlocks.lean](../Overfull/BipartiteFactorization/PreferredBlocks.lean), `PreferredBlocks.exists_uniform_preferred_blocks` |

Fix positive lower bounds for the density, active-row threshold, palette
fractions, and block fractions, and fixed bounds on the numbers of labels,
large pools, and special vertices. The new theorems choose `ε > 0` and `m₀`
before the order, error, graph, coloring, or vertex partition. From
`α*m ≤ k`, `0 ≤ a ≤ ε*m`, the actual row bounds `c_x ≥ θ*k`, and actual
large-pool sizes at least `θ*k/65536`, they derive the probability budgets
used in the preceding continuation.

The per-color copy bound `2*m*a/k + 4` is bounded by `2*a/α + 4`.
This converts the palette budget into a fixed exponential term plus fixed
multiples of `a/m` and `1/m`. The block budget is treated in the same way.
The existing uniform scalar theorem then supplies the required constants.
All cardinalities and degrees refer to the actual graph and original
multigraph copies.

The palette theorem permits the indexed family of large pools to be empty.
Small pools have their colors excluded by the earlier allowed-color
construction. The score-based block theorem explicitly concerns a large
correction pool; it does not assert a positive score requirement for a
small pool whose palette demand has been excluded.

The separate preferred-row theorem constructs simultaneous ordinary and
special preferred rows with uniform constants even when no correction
pool is available. It requires no cap, no correction-score estimate, and
no two-selected-vertices condition. It retains the supplied position
relations. Thus the no-correction branch also has its own proved finite
sampling input.

## Actual integer choices

For a prescribed target fraction `λ > 0`, the constructed size is

```text
evenPaletteSize λ k = 2 * floor(λ*k/2).
```

The rounding loss is strictly below two. Once `λ*k ≥ 4`, the size is
positive and even, and its actual fraction lies between `λ/2` and `λ`.
A single threshold works for every member of a fixed finite family of
positive target fractions. The sum of the rounded sizes is bounded by the
sum of the targets times `k`. The uniform rounded-palette theorem composes
these facts with actual palette sampling. Its fixed targets satisfy
`target_j ≥ 2*λ_min > 0` and their total is at most `1/2`; the resulting
actual palette fraction is at least `λ_min`. No integer-size family or
palette-capacity conclusion is assumed.

For the vertex positions, take `c*t` fine labels indexed by
`Fin c × Fin t`, and `c` coarse labels indexed by `Fin c`.
If every original part has size divisible by `c*t`, its positions are
partitioned into `c*t` equal sets. The coarse set for label `j` is the
actual union of the `t` fine sets with first label `j`. Both levels cover
the whole population and are disjoint within their respective level.
Their exact fractions are `1/(c*t)` and `1/c`. A nonempty part of size
at least `2*c*t` contributes at least two vertices to every selected set.

Shared permutations carry these relations to actual vertex blocks.
Taking `c = 7` gives the seven coarse blocks in the manuscript. The
result contains exact partwise cardinalities, disjoint fine blocks,
disjoint coarse blocks, complete coverage at each level, and the exact
coarse-union relation.

The cluster-size arithmetic is also constructive. Under the specified
divisibility and initial size conditions, it chooses the adjusted old
cluster size and the exceptional population. The old cluster loses fewer
than `6q` vertices; the adjusted size is divisible by `3q`; and the
exceptional population is either empty or has size at least `2q` and is
divisible by `q`. This is a numerical adjustment theorem. Construction
of a suitable regularity partition remains separate work.

## Floor caps and actual deletion losses

[LocalizationBounds.lean](../Overfull/BipartiteFactorization/LocalizationBounds.lean)
proves the following exact estimates. If `λ*c_x ≥ 64`, the actual integer
cap satisfies

```text
(59/64)*λ*c_x ≤ floor((15/16)*λ*c_x) ≤ (15/16)*λ*c_x.
```

The sampled row lower bound makes this cap no larger than the actual
palette demand. The uniform block theorem derives the order threshold
needed for these inequalities internally. It also derives
`a ≤ p*c_x/4096` by making its error tolerance small enough.

The manuscript weights `ω₁ = 64λ/p` and `ω₂ = 64λ/p²` satisfy
`0 ≤ ω₁ ≤ ω₂ ≤ 1` under the palette-size bound. An arbitrary deletion
of at most `p²*M/512` copies from the relevant correction pool costs at
most `λ*M/8` in the weighted score. A sampled score of at least
`13λ*M/8` therefore leaves at least `3λ*M/2`, exceeding the correction
demand bound `5λ*M/4`.

For coarse selection, the initial boundary and the fine-family correction
cost each receive half this loss allowance. The exact fine-family cost
is bounded from the original fine palette counts before any fine copies
are selected. Only copies in the relevant local correction pool are
charged; unrelated deleted copies are not counted against that pool.

The boundary-copy set is the actual union of the incidence sets of its
vertices. At an exceptional vertex outside the boundary, its intersection
with a core row consists exactly of copies whose other endpoint lies in
the boundary. A representative row with distinct other endpoints loses
at most one copy per boundary vertex. Special rows use their actual
incidence-loss bound instead. These are deterministic statements and
allow the boundary to depend on earlier choices.

## Actual normalized boundary weights

[BoundaryWeight.lean](../Overfull/BipartiteFactorization/BoundaryWeight.lean)
defines the manuscript weight from actual restricted-edge degrees and
actual parallel-copy counts. Each indexed pool contributes at most two
to the total weight, and each indexed special row contributes at most
one. Empty pools and zero rows contribute zero. Consequently two pools
and at most `z` special rows give total weight at most `4+z`.

Among any nonempty family of `h` pairwise disjoint actual clusters
contained in the core, the theorem constructs a cluster of weight at
most `(4+z)/h`. Deleting vertices cannot increase its weight. For any
subsequently chosen boundary with total weight at most `δ`, the actual
lost copies from a positive pool are at most `δ` times that pool's size;
an active special row loses at most `δ*c_x`. These bounds do not require
independence of the boundary choice.

The result does not yet construct the final cluster copies or control
vertices inserted during the spanning regularity setup. Those later
changes must retain the required weight and cardinality bounds.

## From samples to selected graphs and colorings

[SampledSelection.lean](../Overfull/BipartiteFactorization/SampledSelection.lean)
separates the fixed palette geometry from the supply and capacity
conclusions. `reserved_palette_conditions_of_samples` derives every
preferred-row reserve and the exact correction-score condition from the
actual sampled row, pool, and floor-score inequalities, together with
the stated boundary and earlier-family loss bounds.

Ordinary and special preferred rows are both covered. For special rows,
the larger permitted boundary loss is removed first; the surviving copies
then meet the same supply interface used by ordinary representative rows.
Core-boundary deletion is proved disjoint from the inherited
exceptional-internal base.

When the two actual correction demands are equal, zero correction
weights give the selection conditions directly. The theorem
`exists_selected_palette_without_correction` constructs an actual
selected graph meeting neither correction pool, with no score or
large-pool hypothesis. This includes the branch where both pools have
their colors excluded.

The constructed conditions feed the existing original-copy selection
theorem. `exists_colored_sampled_palette` constructs the selected graph
and its actual balanced localized coloring. The strict palette and active
degree inequalities required by the fan argument are derived from the
active-row lower bound and small error. The residual degree reserve is
also derived from the small total selected-palette bound.

This completes explicit bridges between the sampling estimates and the
finite construction. It does not yet assemble all choices into the full
regularity and absorber construction of Proposition 6.2.

## Remaining obligations

The following distinctions remain part of the public scope:

- The target palette fractions must still be chosen compatibly with the
  absorber-specific identities and divisibilities. Arbitrary positive
  even palette sizes are not by themselves those absorber parameters.
- The uniform block construction uses an actual partition satisfying its
  divisibility and lower-size hypotheses. The spanning regularity setup
  and all of its neighborhood and superregularity conditions are not
  supplied by that finite position construction.
- Deterministic weight and loss estimates control a boundary once its
  graph and cluster hypotheses are established. The eventual boundary
  must also fit the special-path and absorber construction.
- The special path systems, robust absorber of Theorem 6.3, and final
  factorization remain unformalized. Consequently Lemma 4.2, Lemma 4.14,
  Theorem 6.1, Proposition 6.2, and the main theorem remain incomplete.

The companion [critical-partition continuation](critical-partition-consequences.md)
records a separate advance toward Proposition 2.24. The verification
script checks the complete imported development, rejects unfinished
proof axioms, and records exact source and input hashes in
[verification/results.json](../verification/results.json).
