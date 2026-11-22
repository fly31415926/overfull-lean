# The deterministic critical-partition reduction

Theorem 2.23 is already proved. This continuation proves the deterministic
steps that turn a suitable average-degree estimate into all the
partition conclusions of Proposition 2.24. **Proposition 2.24 is not
counted as complete:** its asymptotic average-degree input for critical
graphs, cited from Cao–Chen in the manuscript, has not been formalized.
The complete numbered inventory remains **44 of 69**.

## Actual deletion and uniform choices

[LowDegree.lean](../Overfull/RobustPartition/LowDegree.lean) defines
the exact manuscript set

```text
Z_ζ = {v : Δ(G) - d_G(v) > ζ*n}
```

and the actual induced graph on its complement. From the actual
total-deficiency inequality

```text
sum_v (Δ(G) - d_G(v)) < ζ³*n²
```

it proves the strict bound `|Z_ζ| < ζ²*n`, the exact deleted-plus-retained
vertex count, and the degree bounds in the surviving induced graph.
These are graph statements, not inequalities about an unrelated list
of putative degrees.

`exists_uniform_small_deficiency_partition` chooses an arbitrarily small
positive `ζ` and a positive near-regularity tolerance before the graph.
The minimum degree of the surviving graph is at least `Δ-(ζ+ζ²)n`,
and its maximum degree is at most `Δ`. The constants are chosen so that
the already proved robust-partition theorem applies. Its error function
is capped by `(θ/100)³`, producing the required bound on `ρ` while
retaining the original prescribed error-function condition.

`exists_uniform_partition_of_average_degree` provides the corresponding
average-degree interface. It derives the deficiency condition from the
normalized degree-sum lower bound `(1-ζ³/2)Δ ≤ (sum_v d_G(v))/n`, then constructs the actual
deleted graph and its partition. The formal statement retains that
degree-sum hypothesis; it does not assume that every critical graph
satisfies it.

## Actual part sizes and degree exceptions

[CriticalConsequences.lean](../Overfull/RobustPartition/CriticalConsequences.lean)
derives the graph consequences from `PartitionConclusion` and the actual
degree transfer to the original maximum degree.

For an ordinary part, the exceptional-set bound and the square-root
part-size bound ensure the existence of an actual good vertex. Since
its induced graph is simple, the internal degree of that vertex is
strictly below the part order. This gives the manuscript's `+1` in
the ordinary part-size lower bound.

For an ordered bipartite part, actual incidence counting bounds the
number of edges that fail to go to the opposite side. An internal
same-side edge contributes two such incidences; an edge leaving the
whole part contributes one. The proof constructs the actual exceptional
vertex set for opposite-side degree and obtains the original bounds:

```text
|V_i| ≥ Δ - 2ρn + 1,
|A_j|, |B_j| ≥ Δ - 3√ρ n,
ordinary degree exceptions ≤ ρn,
bipartite degree exceptions ≤ 2√ρ n.
```

Outside the indicated exceptions, the internal or opposite-side degrees
meet `Δ-2ρn` and `Δ-2√ρ n`, respectively. All orders and errors in
these conclusions are measured against the original graph order.

## The five alternatives

The exact weighted floor bound from Theorem 2.23, the density
`Δ ≥ (1/4+θ)n`, and `ρ ≤ (θ/100)³` imply that the weighted number
of parts is strictly below four. Positivity and coverage rule out zero
parts. Consequently the actual component counts satisfy

```text
(q, ℓ) ∈ {(1,0), (2,0), (0,1), (3,0), (1,1)}.
```

When `q+2ℓ=3`, the three actual disjoint shores exhaust the surviving
vertex set. The lower bounds on the other two shores give, for every
shore `X`,

```text
Δ - 3√ρ n ≤ |X| ≤ n - 2Δ + 6√ρ n.
```

The argument uses the actual shore partition and its cardinality
identity. It does not infer these conclusions from a merely assumed
five-case classification.

## Precisely what is still missing

The remaining input for the full numbered proposition is the
criticality-to-average-degree theorem with the correct uniform degree
threshold. Once that is proved, its degree-sum estimate must be composed
with the already constructed parameters and induced graph. The current
theorems prove the deterministic reduction completely under their
explicit numerical degree-sum hypothesis. They do not remove that
hypothesis or claim a full proof of Proposition 2.24.

The full source and transitive-axiom audit are recorded in
[verification/results.json](../verification/results.json). The separate
[uniform localization continuation](uniform-localization.md) advances
the Section 6 factorization dependencies.
