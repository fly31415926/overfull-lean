> **Historical continuation notes.** Coverage and status statements below describe the earlier checkpoint documented here. The current inventory is **47 of 69**, including complete Lemmas **4.2**, **4.14**, and **4.15**. The one-core branch of 4.6 is complete; its two-core branch and the main theorem remain incomplete. See [the current scope](next-verification-target.md) and [reconstruction record](checkpoint-reconstruction.md).

# Semantic review: parameters and the final bipartite packing stage

**Review date: November 22, 2026. The completed numbered inventory remains
45 of 69.** This continuation proves numerical parameter constructions,
original-copy reservation accounting, and the final matching-packing stage
from an explicit reservation of the original regular host. It does not
prove the robust absorber, Theorem 6.1, Proposition 6.2, Lemma 4.2, or
Lemma 4.14. The main theorem remains unverified.

## Source identity and correspondence

The source inspected for this review is
`Four_Robust_Component_Cases_2026-11-21.tex`, SHA256
`ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.
The source locations below refer to that exact file.

The numbered assertion inventory remains pinned to the November 20 source
recorded in [manuscript-source.json](manuscript-source.json), SHA256
`4605bdf3ee5b241a7b52dd59d08537fa0a439335cd6f119394cddd4609efffc1`.
This continuation does not rebase that inventory or claim that the two full
manuscripts are identical.

| Reviewed source location | Lean implementation | Scope |
| --- | --- | --- |
| `old:fac:palette-sizes`, lines 4550–4560 | [AbsorberParameters.lean](../Overfull/BipartiteFactorization/AbsorberParameters.lean) | Actual palette fractions and the displayed numerical bounds, with the source constants retained |
| `old:fac:absorber-counts`, lines 5178–5184; integer conditions, lines 5185–5186 | AbsorberParameters | Coupled integer identities and exact divisions; no absorber construction |
| Parameter order and rounding, lines 5207–5251 | AbsorberParameters | Main ratio fixed before the cluster count, followed by the small ratio and uniform order bounds |
| `old:fac:range`, lines 5366–5395 | [ResidualPacking.lean](../Overfull/BipartiteFactorization/ResidualPacking.lean), using the previously proved [BipartiteRange.lean](../Overfull/BipartiteRange.lean) | Packing with an arbitrary fixed positive reserve after deriving the smaller robust range |
| `old:degree-accounting`, lines 5397–5437 | [ReservedCore.lean](../Overfull/BipartiteFactorization/ReservedCore.lean) and AbsorberParameters | Exact identities for an explicit reserved set of original copies; existence of that set remains separate |
| Completion and exact residual degree, lines 5439–5455 | [ComplementCompletion.lean](../Overfull/BipartiteFactorization/ComplementCompletion.lean), [CompletionTransport.lean](../Overfull/BipartiteFactorization/CompletionTransport.lean), [UniformRemainder.lean](../Overfull/BipartiteFactorization/UniformRemainder.lean), [ReservedRemainder.lean](../Overfull/BipartiteFactorization/ReservedRemainder.lean) | Actual completions preserving every supplied residual exterior color, with a simple residual of degree exactly `2*r`; the final wrapper derives the preparation conditions from an explicit original-copy reservation |
| Balanced orientation, lines 5455–5456 | [ResidualOrientation.lean](../Overfull/BipartiteFactorization/ResidualOrientation.lean) | An actual orientation with indegree and outdegree exactly `r`; uses a proved König-coloring construction |
| `old:fac:absorber`, lines 5168–5200; final restoration, lines 5458–5474 | Not completed by this continuation | Robust absorber, Hamilton decompositions, and replacement of auxiliary systems by exceptional matchings remain necessary |

The source uses `q` for the number of fine palettes. In
`UniformRemainder.lean`, `q` instead denotes the number `k-2*s` of remaining
exterior colors. These are local formal variables with different roles;
the review does not identify them.

## Coupled parameters and their quantifiers

`AbsorberParameters.make` constructs all eight integer parameters together.
It takes `r` to be a multiple of the fine-palette count, which is a permitted
stronger condition than the source's period `q/gcd(q,f*t)`. The proof derives
the latter divisibility and the exact quotient `r3 = r*f*t/q`.
`make_valid` proves that the natural subtraction defining `rdiamond` does
not truncate. In particular, all intended identities are equalities of
integers, not asymptotic or real-number replacements:

```text
r2 = 96*l*g^2*t*r
q*r3 = r*f*t
rdiamond + (q-1)*r3 = r1+r2+r
s = q*r3 + 7*rdiamond
k1 = 2*r3,    k2 = 2*rdiamond
q*k1 + 7*k2 = 2*s
r1+r2+r3+6*rdiamond = s-r.
```

The construction also proves positivity, `r*t^2 ≤ m_cl`, the small budget
`100*(r2+r+q*r3) ≤ r1`, and explicit lower and upper bounds on
`rdiamond/r1`. Both palettes are positive and even. The six derived
structural divisibilities in `spanning_divisibilities`, together with its
premise `f ∣ q`, supply the seven integer conditions displayed in the source.
`exists_cluster_order` also derives an actual equal cluster order and its
refinement divisibility from the prescribed divisibility of the side order.
It does not construct the clusters or assert their regularity.

The source order of choices is preserved by `exists_uniform_parameters`:
the positive main ratio `rho` is an input before the lower cluster-count
threshold; after an admissible count `t` is fixed, the positive smaller ratio
`xi`, a positive lower palette fraction, and the cluster-order threshold
are chosen before the actual cluster order and ambient degree. The
finite-family wrapper takes a finite nonempty list of admissible counts
and constructs one positive palette lower bound and one order threshold
for the entire list. This supplies the stated bounded-count uniformity.

The integer construction does not assert the full regularity/absorber
hierarchy involving `eps_set`, `d0`, `l`, and `g`. Nor does it construct a
bi-setup or special factors. Those are additional geometric obligations.
The displayed palette bounds are consequences of explicit positive target
bounds and the stated degree bounds; they are not assumed properties of
unrelated preselected palette sizes.

## Reservation and preservation of original copies

`ReservedCore` starts with an explicit reserved set `T` of original ambient
edge copies. The surviving host is exactly `G.restrictEdges Tᶜ`.
Its simple core retains an embedded edge if and only if that edge's
specified original copy is not reserved. This definition distinguishes
parallel edges with the same endpoints.

The complementary graph consists precisely of the surviving copies from
the old core complement. The embedding `exteriorOriginal` is injective,
preserves endpoints, and includes every unreserved original complementary
copy. All ambient vertices remain in the fixed vertex type, including
vertices that become isolated, and every unreserved exceptional incidence
is retained. `exteriorColoring` restricts the supplied old
coloring with its existing palette; it does **not** assert compression
from `k` colors to `k-2*s` colors.

From actual reserved degrees `2*(s-r)` on core vertices and `2*s` on
exterior vertices, the module derives the exact remaining ambient degrees
and the core-plus-exterior incidence identity. The rewritten form
`(k-2*s)+2*r` has the explicit arithmetic hypotheses `r ≤ s` and
`2*s ≤ k`, so natural-number subtraction cannot hide a loss of degree.
Existence of a reserved set satisfying these conditions is not proved by
these accounting results.

`exterior_degree_le_original` proves that reservation cannot increase the
complementary degree. `core_degree_bounds` and `core_almost_regular` retain
the original error `a` on the actual surviving core. The two
`bipartite_robust_of_*` theorems prove robust expansion with parameter
`nu-mu` when the degree of the reserved copies is at most `mu*m`.
Their conclusion is positive when the later application chooses `mu<nu`;
no such choice is silently inferred from a nonnegative budget alone.

## Uniform packing and actual completion

`pack_fixed_bipartite_forbidden_sets` fixes its positive error, retained
robust parameter, smaller range, and order threshold before every graph,
nominal degree, packing length, and forbidden-set family. It assumes
`0<alpha<1`, `0<gamma<1`, and `0<nu≤tau<alpha/16`. The minimum degree
needed for range reduction is derived from the actual degree error,
after capping that error at `alpha/2`.

For any `q ≤ floor(d-gamma*m)`, the theorem constructs actual pairwise
edge-disjoint matchings perfect outside the specified balanced footprints.
It pads the future inputs by empty sets, proves the exact incidence count
is unchanged, applies the proved adaptive bipartite packing theorem, and
restricts to the requested `q` rounds. Robustness is retained for the
actual unused graph after every subfamily. No matching family or residual
graph is supplied as an existence premise.

The exact identity is

```text
remaining.degree v + q = G.degree v + number_of_forbidden_footprints_containing_v.
```

`CompletionTransport` identifies these footprints with the vertices covered
by the actual exterior color classes. Their total load equals the actual
complementary degree, and the side equivalence preserves the matching
adjacencies and the complete unused graph exactly.

`ComplementCompletion` combines each internal matching with its original
exterior color class. Core vertices are covered by exactly one of those
two pieces. Exterior vertices are covered because their actual degree is
`q` in a proper `q`-coloring. The resulting classes are genuine pairwise
disjoint perfect matchings of the prepared ambient graph. All exterior
copies retain their supplied labels and are used. Every surviving ambient
copy belongs to the remaining embedded simple core; hence a parallel,
same-side, or exterior copy cannot survive unnoticed.

`exists_uniform_oriented_remainder` composes these results for a prepared
host of degree `q+2*r` on the core and `q` outside. It explicitly takes a
proper coloring of the actual core complement, balanced footprints, and
the manuscript footprint bound `2*m*a/q+4`. It derives the packing degree
error and the total footprint load from the actual core-degree bound.
It does not assume a coloring of the whole prepared host or any absorber.

The order threshold is at least one. Consequently `q≥alpha*m` gives
`q>0`, making the footprint divisions valid. With the constructed input
error at most `epsilon_pack*alpha/8` and
`epsilon_pack*m≥8`, the whole footprint-size bound is below the packing
tolerance. The hypothesis `gamma*m≤2*r` proves the required packing
horizon. All such constants precede the graph and the actual integers
`q,r`.

`exists_uniform_reserved_remainder` now composes the reservation and packing
stages. Its input is the original `k`-regular host, its original robust core,
an explicit original-copy set `T`, and the balanced remaining exterior
coloring in `k-2*s` colors. It assumes `r≤s`, `4*s≤k`, the source's exact
reserved degrees, and the budget `2*(s-r)≤(nu/2)*m`. It derives robustness
`(nu/2,tau)` of the surviving core, its unchanged error `a`, and all actual
remaining ambient degrees. The density `k-2*s≥alpha*m/2` is derived from
`4*s≤k`; the range hypothesis `tau<alpha/32` is exactly what the packing
wrapper needs at density `alpha/2`. All positive constants and thresholds
precede the original host and `T`.

Consequently, this last wrapper does not ask for an unrelated already
regular residual or assume the post-reservation robustness and degree
identities. It still explicitly requires the reserved set and the balanced
compressed exterior coloring. It does not construct those two inputs from
the original hypotheses of Theorem 6.1.

## Orientation and endpoint cases

The exact residual simple core has degree `2*r`. The proved König theorem
colors this bipartite graph in `2*r` colors. Two complementary palettes of
size `r` give disjoint spanning `r`-regular subgraphs. Their edges are
oriented in opposite bipartite directions. The explicit arc relation is
asymmetric, contains one direction of every original edge, introduces no
nonedge, and has actual indegree and outdegree `r` at every vertex.
This is a valid alternative to the source's Eulerian-component orientation.
No directed robust-expansion assertion is inferred from it.

The fixed-family packing and exact accounting include `q=0`; the family
and used union are then empty. A supplied zero-color complement coloring
can exist only when that complement has no copies. The uniform positive-
density wrapper excludes `q=0` through its derived positive-order and
density bounds. The orientation theorem separately includes `r=0`, giving
the empty orientation of the zero-degree residual. The absorber parameter
construction deliberately chooses positive `r,r1,r3,rdiamond` and a
positive cluster-order threshold.

## What has been removed from the remaining work

The final packing stage no longer needs a separate existence theorem for
the internal completions, an unexplained small-reserve application, an
assumed exact residual degree, or an assumed balanced orientation. The
coupled integer choices and the stated palette budgets are constructed.
The original-copy reservation identities are proved on actual graphs.

The following inputs still have to be constructed and composed from the
original hypotheses of Theorem 6.1 and Proposition 6.2:

1. The full spanning bi-setup, its regularity and superregularity conditions,
   compatible refinements, and final boundary after insertions and equalization.
2. The source-compatible selected families and the balanced compressed
   coloring of their precise remaining exterior, including all global
   boundary and copy-accounting requirements.
3. The special path systems and special factors retaining every prescribed
   exceptional matching and all required endpoint/label conditions.
4. The robust absorber of Theorem 6.3, or a proved sufficient replacement,
   supplying an actual reserved graph with the requisite degree,
   disjointness, and Hamilton-decomposition properties.
5. The final replacement of each auxiliary edge system by its original
   augmented exceptional matchings, with a partition of every original
   edge copy into the prescribed number of perfect matchings.

The original-copy reservation, loss bounds, and packing theorem are now
composed by `exists_uniform_reserved_remainder`. A further theorem must
still choose their common constants across the bounded possible cluster
counts and construct the reserved set, compressed exterior coloring, and
geometric inputs from the original robust-core hypotheses. That further
construction is not asserted by the present stage interfaces.

König's theorem is applied only to the final simple bipartite core. Its
additional matchings do not cover the exterior vertices. They therefore
cannot replace the special-factor/absorber reconstruction of the original
regular host. The new results justify no increment to the completed
numbered-assertion count.

This document records mathematical scope and statement correspondence.
The strict build, full transitive axiom audit, and exact source hashes are
recorded separately in [verification/results.json](../verification/results.json).
