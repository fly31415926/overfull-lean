# Semantic review: native reserve completion

This review concerns the mathematical scope and interfaces of the current
`Overfull/NativeReserve/` sources. It does not substitute for compilation.
The current run requires fresh strict Lean verification of these exact
sources and the unchanged transitive axiom audit.

## Reviewed invariants

- **Original copies:** all pool, boundary, reserve and deletion sets use
  the original host's edge-copy type. Parallel copies remain distinct.
  The internal exceptional-pair signature is permitted at arbitrary
  multiplicity; there is no simple-host weight-at-most-one shortcut.
- **One assignment:** the reserve's parent matchings share the actual
  representative's coarse signature. Accepted rounds realize their
  declared signature with exact native pool counts. The same original
  core partition and exception set are used throughout.
- **Actual protected reserve:** the forbidden reserve is the actual
  union of the packed compressed boundaries. Exact pool accounting gives
  the two-thirds initial remainder. This is not a claim about the pool
  sizes after all accepted rounds have been deleted.
- **A fixed proposal:** every protected even-cut test is computed from
  the original rounded proposal. Sparse-pool and cut discards do not
  change the tests. Their losses are bounded by a union bound.
- **Realized, disjoint boundaries:** each selected sigma slot receives
  an actual host copy. Injectivity gives round cardinality and disjoint
  copies, while the greedy endpoint avoidance gives the matching property.
  Exact counts imply the declared signature and uncovered-core parity.
- **Valid core completion:** a boundary footprint consists of its actual
  core endpoints. Cardinality at most six, even uncovered order, and load
  at most the original core-complement error satisfy the general robust
  packing hypotheses. Added copies are genuinely embedded core copies.
- **The actual residual:** exact copy membership identifies the retained
  embedded core with the packing's unused graph. Perfectness and
  disjointness imply degree `h=k-q`. Robustness and minimum degree come
  from the original-core packing, not an assumption about a new host.
- **All odd cuts:** weighted accounting first proves whole-shore bounds.
  Internal completions preserve those cut-copy sets exactly. Even shores
  have either a `2a` cut bound or untouched original cut copies. Together
  with core-incidence bounds and the robust classification, this proves
  the no-overfull condition for the entire actual residual.
- **Uniform parameters:** `ε,θ,m₀`, then `η,ξ,nSetup`, then the final
  minimum error bound and maximum order threshold are chosen before the
  host. Initial admissibility is obtained before any boundary selection.
  The later packing horizons and `δn` margin use the derived count identity.

## Independent source-level checks

The numerical review checked the quantifier order, both packing horizons,
the conversion from `δk/2` to `δn`, and the initial/later budget split.
The residual-safety review checked both embedded-copy membership
equivalences, the transferred whole-cut sets, and the actual residual
regularity, robustness and no-overfull applications. Neither review found
a missing mathematical hypothesis at the reviewed source stage.

In particular the classifier uses density `α'=α/30`. Its requirements are
met by `σ≤α/300`, `a≤αn/300`, `h≥k/30≥αn/30`, and the uniform threshold
`n>3/(θ²c²)`. The estimate `k≤2n` is derived from an original simple core
and the initial error budget. No regularity or fractional decomposition of
the boundary-only residual is used.

## What is deliberately not concluded

The selected parent perfect matchings can overlap and need not survive.
The reserve's compressed boundaries need not themselves be perfect.
The optional reserved old-core crossing copy may be a joining copy of
the assigned partition; only the exceptional reserved incidences are
automatically internal to their assigned parts.

The next palette construction must retain the parity certificate for
every grouped joining piece, align prescribed reserve crossings when
needed, and prove the footprint and load bounds for the grouped family.
The size-three bound for an individual piece does not by itself bound
the size of a whole palette class. These are additional proof obligations.

The full two-core Corollary 4.6, the general five-exception statement,
remaining terminal factorization and the main theorem are not proved by
this continuation. The 69 numbered assertion records remain unchanged,
with 47 complete and 22 incomplete.
