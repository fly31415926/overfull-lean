# Frequent boundary patterns: Lemma 4.13

The public theorem is `Overfull.frequent_boundary_patterns` in
[`Patterns/Frequent.lean`](../Overfull/Patterns/Frequent.lean). Its result is
`Patterns.FrequentPatternResult`, an actual matching-deletion history and
an actual partition into enlarged robust cores. The source statement is
`three:lem:pattern`, with recorded statement SHA256
`557d62e4c4ab7c00ac7cc29fa403d80601a2b9851e7c7eb62cdeb4caa1d40c3b`.

This result does not prove the terminal factorization, the compatible
circuit theorem, or the manuscript main theorem.

## Quantifier order and input

For an exceptional bound `t`, set

```text
B = patternBound t = 2^(t.choose 2) * 4^t * 2^6.
```

The theorem fixes `0 < α ≤ 1`, `0 < ν ≤ τ`, and
`τ ≤ α/(1000*B)`. It chooses a positive surviving robust parameter
`νout ≤ τ` before the requested final error `δ > 0`. Only then does it
choose a positive original error tolerance and an order threshold. All
these choices precede the finite vertex and core-label types, graph,
partition, exceptional set, degree, and actual core graphs.

The input is a simple `k`-regular graph with no `k`-overfull set, three or
four disjoint robust cores, and an exceptional set of size at most `t`.
The cores and exceptional set partition all vertices. The degree and
each original core order are at least `α*n`; each core graph is an actual
subgraph of the corresponding induced host graph and has minimum degree
at least `k-a`. The small-error condition is
`a + |Z| + 1 ≤ ε*n`, with `a ≥ 0`. For bounded `|Z|`, the additive terms
are absorbed by the uniform order threshold.

The bound on the robust range depends on `t`. In a later composition
with Proposition 4.12, its bound on the final exceptional set must be
known before applying this range condition. Range reduction is a
separate proved tool; this lemma does not silently assume that the
original range already satisfies every later value of `t`.

## Actual conclusion

`FrequentPatternResult` records the following data and proofs.

| Obligation | Actual result fields |
| --- | --- |
| Original-host perfect-matching deletions | `N`, `rounds`, `perfect`, `present` |
| Exact residual and its regular degree | `G`, `graph_eq`, `h`, `degree_eq`, `regular` |
| No overfull set, including every intermediate prefix | `safe_prefix`, `no_overfull` |
| Positive retained fraction of the initial degree | `degree_positive`, `reserve_positive`, `reserve_linear`, `reserve_le_degree`, `retained_degree` |
| Reserve within the requested relative error | `reserve_gap` |
| Full final partition, with no exceptional vertices remaining | `A`, `core_enlargement`, `core_subset`, `core_disjoint`, `cover` |
| Actual embedded robust cores and small degree error | `H`, `core_embed`, `core_degree`, `core_robust`, `error_nonneg`, `error_bound` |
| Fixed actual joining forest and enlarged-part parity | `code`, `forest`, `forest_valid`, `forest_card`, `forest_labels`, `part_parity` |
| At least `r` actual residual edges for every forest pair | `pair_supply` |
| Forest supply for every union of enlarged parts | `cut_supply` |
| Perfect matching or three-edge star in the four-odd-part case | `four_odd_shape` |

In particular,

```text
k/(3*B) ≤ r ≤ h,
h-r ≤ δ*h,
core_error ≤ δ*h.
```

Every final part contains its original core and is contained in that core
together with the original exceptional set. The forest has at most three
distinct unordered label pairs. Every used label represents an actual
core. When there are four cores, the embedding into `Fin 4` is surjective;
the four-odd conclusion is therefore about all four actual parts.

The pair supply counts actual `Sym2` host edges between enlarged parts.
The cut supply uses `graphCutCount` of the actual residual graph. These
are not assumed capacities of an abstract quotient.

## Proof construction

### A single finite pattern space

`exists_encoded_distribution` invokes the proved matching-polytope
distribution and compresses every support matching using one fixed core
embedding. `Pattern` records exceptional pairs, assignments of the
remaining exceptional vertices, and a simple joining forest. The exact
size of the ambient pattern type is
`2^(choose |Z| 2) * 4^|Z| * 2^6`, bounded by `B`.

The scaled weights are nonnegative and sum to `k`. Actual edge marginals
prove pair capacity and whole-cut capacity. A pattern containing an
exceptional pair has weight at most one, because that pair is one
specific simple host edge. Choosing a maximum-weight pattern gives
weight at least `k/B`. For `k ≥ 6*B`, the integer reserve
`r = floor(weight/2)` satisfies `r ≥ k/(3*B)`, and this pattern has no
internal exceptional pair.

### One proposal and one discard family

The proposal is

```text
m_proposed(p) = floor((1-η) * (weight(p)-r*indicator(p=p₀))).
```

All sparse-pair and protected-cut tests use this same proposal. The
formalization tests all quotient-label subsets as possible pair labels
and all quotient shores, which harmlessly overcounts the relevant
tests. It uses the explicit coefficient

```text
C_t = 2^(t+4) * (t+10)
```

in the discard bound `C_t*a/η`. This is larger than the sharper
manuscript count and has the required dependence only on `t`. It changes
neither the pattern bound `B` nor the retained fraction `1/(3*B)`.
The accepted multiplicities give

```text
r ≤ h ≤ r + η*k + B + C_t*a/η.
```

### Actual realization and fixed completion

The finite copy type is the dependent sum `Σ p, Fin (m p)`. Greedy
selection uses disjoint actual edge pools and proves global injectivity
of the chosen edges and endpoint disjointness within each copy. For an
actively demanded pair, its original encoded witness and the core
degree bound prove `1 ≤ a`; this supplies the strict endpoint-conflict
slack. No global incidence bound is incorrectly imposed on unused
singleton pools containing internal core edges.

The resulting actual boundary matchings cover the exceptional set, have
no internal core edge, have exactly the prescribed boundary image, and
leave even uncovered order in each core. One finite enumeration produces
a natural-number schedule with exactly the accepted multiplicities.

`exists_boundary_completion` chooses one certified packing rule per
original core. Actual edge disjointness and the exterior-degree bound
prove every input's accumulated incidence budget. It completes each
prescribed boundary and establishes actual robust unused core graphs at
every prefix. Completion only adds internal core edges.

### Safety of every actual prefix

`completed_pattern_whole_cut` proves that internal completion does not
change the prescribed whole-union cut count. `prefix_cut_accounting`
subtracts all actually deleted crossing edges from the original cut.

For odd whole unions, every positive-weight pattern crosses at least
once, and the remaining numerical weights sum to the current degree.
For a protected small cut, every accepted crossing multiplicity is
zero, so the original cut-edge set and its boundary incidences remain
unchanged. Large proposed cuts remain at least `2*a`; a core-vertex
toggle uses its actual exterior-degree bound. Toggling an exceptional
vertex gives another whole union. The proved small-cut classification
then supplies all remaining odd shores.

The quantities `weight(p)-m(p)` are numerical accounting terms. They are
never asserted to be a fractional decomposition supported on the
greedily constructed residual graph.

### Absorption, parity, and supply

Actual pool accounting proves that every pair in the distinguished
pattern retains at least `r` edges. For an exceptional vertex these are
at least `r` distinct neighbors in its assigned original core.
`absorb_all_with_reserved_neighbors` adjoins all exceptional vertices and
constructs the actual enlarged core graphs. Their error is at most
`a+h-r`; the uniform scalar choices make this at most `δ*h`.

The compressed representative transfers its parity to the enlarged
parts. A kernel-checked finite argument classifies a forest on four
labels with all degrees odd as a perfect matching or a three-edge star.
For every union of assigned parts, exceptional assignment edges are
internal, so its distinguished pattern cut is exactly the forest cut.
The original weighted cut inequality and exact subtraction prove the
final forest supply. Original-core pair edges remain joining edges
between their enlarged parts.

## Main proof interfaces

| Stage | Declarations |
| --- | --- |
| Fixed encoding and actual distribution | `exists_compressed_encoding`, `exists_encoded_distribution`, `card_pattern_le` |
| Frequent reserve | `EncodedDistribution.exists_frequent_reserve` |
| Rounding and simultaneous discards | `EncodedDistribution.planned_residual_bounds`, `planned_pool_lower`, `planned_protected_zero`, `planned_pair_demand` |
| Actual finite copies | `EncodedDistribution.exists_planned_realization`, `realize_patterns` |
| Certified internal completion | `exists_boundary_completion` |
| Actual prefix safety | `EncodedDistribution.completed_prefix_safe` |
| Actual reserved pairs and cuts | `completed_pattern_pool_reserved`, `completed_pattern_cut_reserved` |
| Final absorption and full result | `assemble_frequent_pattern_result` |
| Uniform manuscript theorem | `Overfull.frequent_boundary_patterns` |

All supporting modules are imported transitively by `Overfull.lean`.
The verification script checks the strict project build, transitive
logical axioms, named declaration coverage, and exact source hashes.
