# Semantic review of the full boundary extension

## Review state and source identity

This review concerns the complete proof of Lemma **4.14**, label
`three:lem:boundary`, with public theorem `Overfull.boundary_extension` in
`Overfull/BoundaryExtension/Full.lean`. The full theorem and its dependencies
passed `lake build --wfail Overfull.BoundaryExtension.Full` with 3,344 jobs
and no warnings. Two independent semantic reviews found no missing
factorization premise, quantifier reversal, or loss of original edge-copy
identities. The accompanying source manifest records the finished proof
file hashes.

The targeted build and this mathematical review are distinct from the
repository-wide verification. The full build, transitive axiom audit,
declaration inventory, and completed-assertion count are recorded separately
in `verification/results.json`; this document does not infer those global
results from a targeted module build.

The canonical numbered inventory remains pinned to
`Four_Robust_Component_Cases_2026-11-20.tex`, SHA256
`4605bdf3ee5b241a7b52dd59d08537fa0a439335cd6f119394cddd4609efffc1`.
Its Lemma 4.14 statement occupies lines 3119–3128 and has SHA256
`67baedd4ae2e0451a8842fd27ea0976f50db94c9054eacd2f5dd40ce2cfa21e3`.

The source inspected for this continuation is
`Four_Robust_Component_Cases_2026-11-21.tex`, SHA256
`ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.
The statement is at lines 3267–3276. Hashing its complete statement
environment, without a trailing newline, gives the same statement SHA256.
The numbered inventory has therefore not been rebased or matched merely by
the theorem's title. Its mathematical statement is byte-identical to the
pinned statement. The following proof is at lines 3277–3292.

## What the final theorem says

Fix a positive lower degree fraction `α ≤ 1`, a positive singleton-color
reserve `γ`, and ordinary robust parameters `0 < ν ≤ τ ≤ α/8`. The theorem
chooses a positive error tolerance and an order threshold before the host,
core, degree, or prescribed coloring is supplied.

The input is an actual loopless multigraph with finitely many edge copies,
an odd finite vertex set `U`, and an embedded simple robust core on `U`.
Each core vertex has ambient degree exactly `d`; the embedded core has
degree at least `d-a`, with `a` at most the chosen small fraction of
`|U|`; and `d ≥ α|U|`. The original cut of `U` has a proper coloring by
`Fin d`, every class has size one or three, and at least `γ|U|` classes
have size one.

The output colors every original edge copy having an endpoint in `U`.
For each original boundary copy, its output label equals its prescribed
input label. The ambient vertex type need not be finite: the theorem uses
the finite core and the finite edge-copy type, and the contraction itself
has finite vertex type `U ⊕ Unit`.

This realizes the original assertion with explicit sufficient parameter
conditions. The low-error and large-order requirements are existential
choices before the graph, as required by the source. It does not require
the original graph to be regular outside `U`, simple as a whole, or already
colored inside `U`.

## The dependency that is replaced

The manuscript first completes the boundary classes of size three and
contracts the exterior of the remaining graph to one apex. It then invokes
Corollary 4.6 to factor that one-core graph, permutes the remaining labels,
and restores the completed classes.

The new route proves the needed one-apex coloring directly. It does not
assume the full statement of Corollary 4.6, Theorem 6.1, a spanning setup,
special path systems, or a robust absorber. Those broader assertions do not
become complete merely because this particular one-apex application is
resolved. The previous adaptive packing, prescribed-pair cut, first group
of completed colors, residual-core, fan-coloring, and bipartite coloring
theorems remain actual proved dependencies.

## The direct one-apex construction

An odd core with one exterior apex is converted to an even core by moving
one of its own vertices outside. The old apex and the moved vertex are the
two exterior vertices. The already proved `even_core_complement` theorem
constructs a proper coloring of this actual new core complement; it also
proves the new error and robust-expansion bounds. The whole host's original
edge copies and regularity are retained.

The moved vertex must retain many incidences toward both shores of the
later bipartite cut. The new construction makes that guarantee explicit:

1. `MovedNeighbors.lean` identifies the moved vertex's original simple
   neighbors with surviving core vertices and injects them into the actual
   original host-copy incidence sets.
2. `NeighborPairing.lean` chooses an even subset containing all but at most
   one of those neighbors, pairs that subset internally, and pairs the
   remaining population. Every cut meeting each prescribed pair contains
   at least half the neighbor set, rounded down. This includes empty sets
   and all parity endpoint cases.
3. `ApexPalette.lean` chooses the first labels from the two proper-color
   rows in balanced numbers. Properness makes incident copies correspond
   injectively to their colors. The labels are chosen from the actual
   coloring and actual rows, not from assumed independent color counts.
4. `ApexChoices.lean` proves that the exact row counts survive the completed
   internal matchings. Core matchings cannot remove an additional exterior
   incidence. The selected-label accounting therefore gives a positive
   linear supply on both shores in the actual residual graph.

The modified first-half and residual wrappers accept those chosen pairs
and labels and return the proved geometric and coloring data with the
choice preserved. The new one-core reduction combines these facts with
range reduction, the one-vertex core deletion, and uniform thresholds.

`ResidualShores.lean` identifies the residual core pulled back to the sum
of its two side subtypes with the exact cut-sides graph carrying the
proved expansion estimate. Its left and right shore images are the same
ambient vertex sets used in the retained-incidence estimates. This
transport does not replace the residual graph by an unrelated isomorphic
copy or change which original apex incidences are counted.

`Factorization.lean` fixes the parameter order explicitly. The one-core
reduction first supplies positive `ν₁,τ₁,ξ`, with `τ₁ ≤ α/512`. Set
`νB = min (ξ/2) (4*τ₁)` and `τB = 4*τ₁`. The two-apex theorem is then
instantiated with density fraction `α/4` and apex-supply fraction `α/100`.
These choices satisfy `τB < (α/4)/16` and
`α/100 ≤ (α/4)/4`. The resulting two-apex error tolerance is supplied to
the first-half reduction before its packing parameters are chosen; the
resulting two-apex order threshold is supplied before the final original
order threshold is chosen. No tolerance is selected after seeing the
input graph or a residual coloring.

## Selecting and completing the two-apex colors

`TwoApexFactorization/Selection.lean` constructs a subset of the original
exceptional edge copies. It contains every exceptional internal-core copy
and every apex incidence on the forbidden same side of a chosen augmented
bipartition. It selects enough other apex incidences and apex-to-apex copies
to make the selected degree exactly `q` at both apices. The equality of the
two original apex-to-core incidence counts is derived from regularity.
Parallel copies between the apices are counted separately.

`Theorem.lean` constructs the selected palette size as well. If `λ*m` is
the supplied lower bound on each of the moved apex's two shore rows, it
sets `d = ceil (λ*m/4)` and `q = k-d`. The uniform order threshold gives
`λ*m > 4`, hence `λ*m/4 ≤ d ≤ λ*m/2`. The density condition and
`λ ≤ α/4` imply `q ≥ α*m/2` and `k ≤ 2*q`. Both rows of the supplied
apex have size at most `q`; at least one row of the other apex has size
at most `q`. The proof swaps the two apex assignments when necessary,
so the required same-side row caps are derived from actual counts.

The chosen error tolerance is at most `λ/8`. It yields both
`2*a < q` and `2*a < min q b`, where `b` is the actual common
apex-to-core incidence count. Those strict inequalities discharge the
fan-coloring criterion. The large-order and positive-density hypotheses
force `q > 0`; there is no division by an unhandled zero palette.

The complementary original-copy graph is proved bipartite on the actual
augmented shores. Its internal copies are exactly the embedded simple core
copies; no additional internal copies disappear from the accounting.

`Balance.lean` constructs a `q`-coloring of the selected graph using the
proved multigraph fan criterion. Its initial colored residue consists only
of copies between the two apices and is colored by the proved bipartite
edge-coloring theorem. The linear active-incidence supply dominates the
small selected core degree, satisfying the fan criterion. Thus the selected
coloring is a conclusion of the construction, not an input to the final
two-apex theorem.

Equal degree sums on the two core shores follow from regularity and the
actual bipartite unselected graph, after removing the two equally saturated
apex contributions. The proved balancing procedure then makes every
selected class's core footprint balanced and bounds its size by
`2*m*a/q + 4`, where `m` is one shore's order.

`Packing.lean` applies the actual robust bipartite packing theorem to these
footprints. It derives each selected vertex load from its actual selected
degree, and bounds that degree by `a` through inclusion in the original
core complement. Its error tolerance is at most
`min ε₀ (ε₀*β/8)`, where `q ≥ β*m`, and its order threshold ensures
`ε₀*m ≥ 8`. These choices absorb both the footprint's ratio term and its
additive constant. The horizon `q ≤ k-γ*m` leaves a positive reserve.

`Completion.lean` joins the actual packed core matchings to their selected
color classes. Each completed class is a perfect matching of the host:
core footprints are covered by their original selected edges, every other
core vertex by its packed matching, and both apices by saturation in every
selected color. Distinct completed classes are disjoint on original copy
identities. Exactly `q` incidences are removed at every vertex.

All surviving copies form a subgraph of the already proved bipartite
unselected host, with degree `k-q`. König's theorem colors that actual
remainder. Disjoint palettes for the completed and surviving copies give
an actual `k`-coloring of the whole host. No coloring of the final remainder
is assumed.

## Returning to the prescribed boundary labels

`boundary_extension_reduction` already constructs the completed triple
classes, their actual deletion, and the precise contracted residual. Its
remaining degree is the number of singleton classes and is at least
`γ|U|`. The contracted core has the same order as `U`, retains its error
bound, and has proved robust parameters `θ,σ` with
`0 < θ ≤ σ ≤ min γ 1 / 20`.

`Full.lean` takes `β = min γ 1`. The inequality `σ ≤ β/8` therefore permits
the new one-apex theorem. Its final error is the minimum of the reduction
and factorization errors, and its final order threshold is their maximum.
All these constants are chosen before the original input graph. Contraction
transports the embedded core, its degrees, its exact odd order, and its
one-vertex exterior by proved equivalences.

Finally, `BoundaryReduction.extend` transports the obtained coloring back
to the retained original copies, permutes the singleton labels to their
prescribed values, and restores the triple classes with their original
labels. The final equality is pointwise on every original boundary edge
copy. Merely obtaining an unlabeled coloring would not satisfy this result;
the theorem includes the required label-preservation equation.

## Scope and validation boundary

The final proof chain has no residual-factorization, selected-coloring,
absorber, or full Corollary 4.6 hypothesis. The explicit selected coloring
and bipartite remainder hypotheses in the intermediate packing wrapper are
discharged by the surrounding two-apex construction.

The separately developed `Probability/BernoulliDifferences.lean` proves
actual finite Bernoulli bounded-difference concentration. It is useful
support for another approach but is not used to discharge Lemma 4.14's
one-apex factorization step.

The 17 modules in `boundary-extension-full-source.json` are bound to their
finished source hashes. Their complete declaration map is
`verification/boundary-extension-full-declarations.json`. The source mapping
also records the separate Bernoulli concentration module, which does not
contribute an additional completed manuscript assertion. The strict module
build and both semantic reviews have passed. Repository-wide build and axiom
evidence is checked separately through `verification/results.json` before
the global completed inventory is reported. Existing completed assertions
and their source identities remain separate preservation obligations.
