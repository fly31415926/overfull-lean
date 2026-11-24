# Independent review of terminal shore transport and coloring

Reviewer: the agent responsible for native reserve geometry, reviewing the
separately authored shore transport, pair coloring, and coloring assembly.
Run: `20261124T021500Z`. Baseline: `f557ae03355f14a0441b37283f35186a95aca2d7`.

## Finding and scope

No mathematical or graph-modeling gap was found in the reviewed transport and
terminal-coloring composition. The low-level glue theorems legitimately accept
local colorings; the complete terminal theorem constructs those colorings from
the robust-core and geometric hypotheses. It does not accept the terminal
coloring as an assumption. Every multigraph edge remains an individual original
copy. The two assigned-shore parity cases and the optional exceptional pair are
covered, including empty retained edge types.

This review covers `ShoreHost`, `ShoreCore`, `ShoreFactorization`,
`ColoringGlue`, `PairColoring`, and `Factorization`. It also checks the use of
those results by `NativeFactorization`. It is not an independent reproving of
all the established one-core factorization dependencies, and it is not a
complete audit of the original manuscript. A focused compile verifies only its
recorded source/dependency build. The final frozen verifier and unchanged full
axiom audit remain authoritative for the complete continuation and any numbered
assertion promotion.

## Actual induced and contracted hosts

`inducedHost G A` uses the finite vertex subtype `A` and the edge subtype
`G.internalEdges A`. This is a genuine vertex restriction. It does not retain
isolated vertices outside `A`, and it does not collapse parallel copies by their
endpoint pair. `inducedHost_incident` and `inducedHost_edge_map` show exact
original incidence and endpoint transport.

For an empty shore cut, `internal_of_incident_of_cut_empty` proves that every
copy incident with a shore vertex is internal. The explicit
`inducedIncidenceEquiv` gives a bijection of incidence-copy types. Consequently
`inducedHost_degree_of_cut_empty` preserves each degree exactly and
`inducedHost_regular` supplies regularity of the actual finite host.
`retainedInternalEquiv` is an original-copy equivalence, allowing an induced
coloring to be pulled back to the original-vertex retained graph. Properness is
checked at the actual original vertex common to two candidate edges.

The odd-shore construction uses the established `BoundaryExtension.contract`.
It retains only edges incident with `A`; it discards edges with both endpoints
outside `A` before contracting. Therefore no outside edge is turned into a loop.
The old results `degree_inl`, `degree_apex`, `contract_regular`, and
`even_contracted_order` give regularity and even order precisely when the
original shore is odd and its cut has size equal to the terminal degree.

## The smaller old core is retained correctly

A terminal shore may strictly contain its old core. `inducedCoreEquiv` and
`contractedCoreEquiv` are explicit bijections from the original core vertex
subtype `U` to its actual image in the larger shore host. `inducedCoreEdgeMap`
and `contractedCoreEdgeMap` retain the original embedded simple-core copies;
their injectivity is inherited from the original `SmallCuts.Core.edgeMap`.
The map-edge obligations are proved, so no replacement simple graph with
unrelated edges is introduced.

Both new core graphs are the old graph relabeled by a vertex equivalence.
`inducedCore_degree` and `contractedCore_degree` preserve every degree;
`inducedCore_robust` and `contractedCore_robust` use the established equivalence
transport of robust expansion, with the same parameters. The core order remains
exactly `U.card`. There is no assumption that the old core equals its assigned
shore, and no assumption about the old core's parity.

For the induced host, the outside-core vertex count is exactly `(A \ U).card`.
For the contracted host it is exactly `(A \ U).card + 1`; the new apex is
explicitly outside the core. Thus the bound used by the one-core theorem is
correct in both cases.

## Exterior independence and crossing incidences

`shore_geometry_of_star_incidence` uses the native condition

```text
for z in A \ U and every copy e incident with z, otherEnd(z,e) belongs to U.
```

This implies that no edge has both endpoints in `A \ U`. It also implies that
a crossing copy incident with a vertex of `A` must have that endpoint in `U`:
otherwise the star condition puts the other endpoint in `U ⊆ A`, contradicting
that the edge crosses the shore cut. These are the exact two structural facts
needed after contraction.

`contractedHost_independent_exterior` covers both possibilities for a retained
edge. If both original endpoints are in `A`, an edge outside the transported
core would be internal to `A \ U`, which is excluded. If exactly one endpoint
is in `A`, an edge outside the transported core would join an assigned exception
to the apex, excluded by the crossing condition. Edges between two exterior
original vertices are not retained. This checks the substantive independence
condition, including the potential apex-to-exception case.

## Uniform one-core applications

`exists_uniform_shore_coloring` obtains one positive tolerance and one order
threshold from `NativeCore.exists_uniform_independent_exterior_factorization`
with exterior bound `s+1`, before any graph data. The even-shore branch can use
this bound because its actual exterior has size at most `s`; the odd branch has
size at most `s+1`. The input terminal density is relative to the old core order,
whose transported order is unchanged. All regularity, parity, robustness,
minimum-degree and error conditions are supplied explicitly.

The resulting even-shore coloring is on its actual induced finite host and is
then transported to `retainedGraph G A`. The odd-shore coloring is on the actual
contraction. The old core may be odd or even in either branch. The relevant
parity is the assigned shore's order, exactly as required by the native reserve
construction. The specialization `exists_uniform_shore_coloring_of_star_incidence`
derives its structural premises rather than accepting them additionally.

## Optional closed pair

`retained_pair_colorable` requires a closed vertex set of order at most two and
an actual degree bound at each of its vertices. If a retained edge exists, its
two distinct endpoints form a two-element subset of the pair set; hence they
are the whole pair set. Therefore every retained edge is incident with the
same chosen vertex, and its total copy count is bounded by that vertex's actual
degree. An injection into `Fin k` assigns distinct colors to all such copies.
Every parallel edge is counted separately. The empty retained-edge type is
handled directly; sets of order zero or one therefore cause no exception.
The theorem does not assume the pair has exactly `k` copies. In the final
regular host that fact follows from regularity when the pair is nonempty, but
the weaker degree condition is sufficient for coloring.

## Agreement and original-copy gluing

`exists_glued_retained_coloring` defines a global color for each original copy
using one shore containing its first endpoint. Its agreement hypothesis ensures
that this label equals the local label in every other shore retaining that
copy. To prove global properness, it chooses a shore containing the actual
common vertex of two candidate copies. Both copies are retained there, their
local colors agree, and local properness identifies them. This avoids the
invalid shortcut of checking properness only at a chosen endpoint.

For disjoint shores, `boundary_of_two_retained` proves that every overlap copy
crosses both cuts. A closed pair has no overlap with either other shore.
`exists_glued_three_shore_coloring` consequently needs agreement only between
the two large shores, and checks all nine choices of shore pair. The even case
has no overlap at all because its first shore is closed.

For odd shores, the common original crossing set has exactly `k` copies. A
bijection of that edge-copy subtype with `Fin k` gives common injective labels.
The equality of the two actual cut sets transfers these labels without changing
which original edge receives each label. The existing
`exists_singleton_boundary_extension` restores these labels separately on both
contracted colorings. The two resulting retained colorings then agree pointwise
on every common original crossing copy and can be glued. No assumption that the
two independently constructed colorings initially agree is made.

## Case coverage in the terminal theorem

`exists_uniform_two_shore_factorization` assumes disjoint assigned shores
`A₀,A₁` and closed pair `B`, covering the actual vertex type, with robust cores
contained in their respective assigned shores. It constructs the pair coloring
and both one-core colorings. Its even case colors both closed induced components;
its odd case contracts each opposite side, aligns their common cut, and glues.
There is no unused parity alternative that is needed by the native application:
`NativeFactorization` derives equality of the assigned shore parities from the
original perfect-matching cut identities, then splits their remainder modulo
two into zero and one.

The native input supplies exactly `k` selected, disjoint reserve boundaries.
`residual_geometry` derives both actual shore cut sizes
`k * (Aᵢ.card % 2)`, equality of the actual cut sets, closure of `B`, and the
strong star-incidence conditions. `twiceResidual_external_image` derives the
needed copy-image hypothesis from the actual last remainder identity returned
by `NativePrefix`, rather than adding a new terminal geometric assumption.
The resulting `exists_uniform_native_residual_factorization` constructs a
coloring of the actual twice-residual graph.

The terminal proof is free to recolor selected exceptional-star incidences.
Only the common old-core crossing labels are restored. It does not assert that
each originally selected full reserve boundary remains monochromatic. The
one-factorization conclusion requires preservation of copies and properness,
which the construction supplies; it does not require this stronger precoloring
property.

## Quantitative composition and evidence boundary

The reviewed original-host `TwoCore` draft uses
`exists_uniform_native_reserve_completion_with_small_joining`, whose retained
robustness is fixed before the requested small error. This avoids the apparent
parameter cycle that would arise from using only the older completion theorem
with robustness returned after a requested error. The original host composition
is separately owned and verified by the integration lead.

The observed command receipt
`development/native-completion-001/command.json` records the genuine command
`lake build --wfail Overfull.NativeTerminal.NativeCompletion`, exit code zero,
and no changed inputs. Its output records 3,494 jobs. It includes the reviewed
shore modules, both generic and native factorization modules, and the concrete
prefix-completion wrapper. Earlier failed commands and warnings remain retained;
their statuses are not rewritten. This focused result does not establish a new
whole-project declaration count or a numbered assertion count. Those claims
must use the final frozen full build, audit and preservation report.

## Reviewed source hashes

| Source | SHA256 |
| --- | --- |
| `Overfull/NativeTerminal/ShoreHost.lean` | `7166fce2560f38c4f1dc556d96aa88d6e40a976d5130bbc4213ccd5c0fb5279b` |
| `Overfull/NativeTerminal/ShoreCore.lean` | `ea772797df6982976c25e0e7ea315fb15c30421afc4424ecb06efe183c5fd8b4` |
| `Overfull/NativeTerminal/ShoreFactorization.lean` | `349ad511138f99647bee467e4601e569f3941637e241e14b3a8593b210a2dc06` |
| `Overfull/NativeTerminal/ColoringGlue.lean` | `9e1630206ec0b3b91ba9f80bdf558786d5cd83237b1fa30d4ee89db2a21e0437` |
| `Overfull/NativeTerminal/PairColoring.lean` | `6f16b5a28677e04d86f2cc7c100b9a92f303095600916c315b91ca645578d52f` |
| `Overfull/NativeTerminal/Factorization.lean` | `ad4e6d1a9480e81b5555b29952f07f3c98e40ea475977b33bbb00abdc88fa2d0` |
| `Overfull/NativeTerminal/NativeFactorization.lean` | `fe133211b48696c8fc940e36e421e42d42f0c41d6c5fc61d67a03dca120f8583` |
