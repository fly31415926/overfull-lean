# Adaptive bipartite packing: Theorem 2.16

`Overfull.adaptive_bipartite_packing` proves the full adaptive packing
statement in the manuscript. The final theorem is in
[`BipartitePacking.lean`](../Overfull/BipartitePacking.lean), and the direct
sequence corollaries are in
[`BipartitePackingCorollaries.lean`](../Overfull/BipartitePackingCorollaries.lean).
This supporting theorem does not prove the manuscript's main overfull theorem.

## Statement and quantifiers

Fix real parameters satisfying

```text
0 < α < 1,   0 < γ < 1,   0 < p < γ/8,
0 < ν ≤ τ < pα/100.
```

The theorem first chooses `ε > 0` and a natural order threshold `m₀`. Let
`G` be a bipartite robust `(ν, τ)`-expander with two sides of common order
`m ≥ m₀`. Suppose that `Δ ≥ αm` and every vertex degree differs from `Δ`
by at most `εm`. The formal parameter `Δ` may be real, which includes the
integer-valued choice in graph applications.

There is one fixed rule which works for every admissible adaptive sequence
of forbidden sets. In each of

```text
q = max(0, floor(Δ − γm))
```

rounds, the next set is balanced between the sides and has size at most
`εm`. Every vertex has occurred in at most `εm` previous sets. The rule
receives only those earlier sets and matchings and the current set. It
constructs an actual matching of `G` whose vertex set is exactly the
complement of the current forbidden set. The resulting matchings are
pairwise edge-disjoint. After every prefix, deleting their edges leaves
a bipartite robust `(pν/4, τ)`-expander.

The quantifier order is essential: `ε` and `m₀` precede the graph; the rule
precedes the adaptive choices. The rule's type contains no future sets.
`BipartitePackingOnline.history` constructs the actual execution recursively,
and its prefix lemmas show that later choices do not alter earlier rounds.
Lean's `Nat.floor` truncates negative values to zero, so the empty packing
is included without an additional assumption on `Δ−γm`.

## Proof components

| Step | Lean module | What is proved |
| --- | --- | --- |
| Constants and initial reserve | `BipartitePackingParameters`, `BipartitePackingInitial` | Uniform small constants and order threshold; an actual contained reserve with expansion, degree control, and minimum degree |
| Degree accounting | `BipartitePackingAccounting`, `BipartitePackingDeletion` | Exact degrees after deleting the reserve, used edges, and forbidden vertices; transport to the actual remaining sides |
| Initial matching in a round | `BipartitePackingWorking` | An actual matching avoiding all unavailable edges and vertices, covering saturated vertices, with equal and bounded uncovered-side counts |
| Disjoint paths and completion | `BipartitePathPacking`, `BipartitePathFamily`, `BipartiteMatchingCompletion` | Construction of disjoint alternating paths, simultaneous switching, exact covered set, and bounds on actual new reserve use |
| Capacity and total load | `BipartitePackingBounds`, `BipartitePackingRound`, `BipartitePackingHistory` | Preservation of each vertex's integer capacity and the total-load recurrence under an actual appended matching |
| Adaptive iteration | `BipartitePackingOnline`, `BipartitePackingStrategy` | One fixed rule, actual histories, invariant propagation, and robust expansion of every remaining graph |
| Final assembly | `BipartitePacking`, `BipartitePackingCorollaries` | The manuscript's full adaptive theorem and its direct prescribed-set and perfect-matching forms |

The reserve load at a vertex is the degree of the intersection of the
original reserve with the actual used-edge union. The total load is the sum
of those degrees. For each valid history, the one-round construction
supplies a next matching whose actual totals `t` before and `t′` after the
round satisfy

```text
t′ ≤ (1 + 4ℓ/(γm)) t + 32ℓεm/γ.
```

Here `ℓ` is the fixed path-length bound. Starting with total zero, this
one-round estimate proves preservation of the geometric invariant

```text
tₛ ≤ 8εm² ((1 + 4ℓ/(γm))^s − 1).
```

The fixed rule chooses a matching preserving that invariant. In particular,
throughout the permitted number of rounds it maintains

```text
tₛ ≤ c₀ εm²,   where c₀ = 8(exp(8ℓ/γ) − 1).
```

The rule's specification requires the invariant, rather than the affine
recurrence between the actual totals of successive outputs. The recurrence
is the checked existence argument for a permissible next choice.

The saturation threshold is `floor(μm)`. The proof checks its positivity and
rounding bounds, estimates the actual saturated set, and prevents each
matching completion from adding reserve edges at saturated vertices.
The remaining reserve therefore retains enough expansion for the next
round and for the final `(pν/4, τ)` conclusion. No existence of a completed
matching or packing sequence is assumed by the final theorem.

## Correspondence with the manuscript

The manuscript bounds each vertex's total number of occurrences in all
forbidden sets. The adaptive Lean theorem requires only the corresponding
bound on occurrences before the current round. The manuscript's condition
implies this condition at every round. Thus the difference weakens the
formal hypothesis; it does not omit a requirement needed for the proof.

`Overfull.bipartite_matching_packing` gives a direct sequence statement with
the manuscript's balance, size, and total-incidence hypotheses. It derives
the adaptive admissibility condition from those hypotheses and returns
actual matching subgraphs indexed by `Fin q`.

`Overfull.bipartite_perfect_matching_packing` takes every forbidden set to
be empty and proves that every returned matching is perfect. Both sequence
statements prove robust expansion after deleting any subfamily. This
follows from the expansion of the graph remaining after all matchings are
removed and monotonicity under adding edges.

## Verification and scope

All mathematical modules are imported through `Overfull.lean`. The project
verifier checks a strict build, records exact source hashes, and audits the
transitive axioms of all project theorems. The accepted logical axioms are
`propext`, `Classical.choice`, and `Quot.sound`. No unproved packing axiom is
introduced. The full report is in
[`verification/results.json`](../verification/results.json).

The remaining main-theorem dependencies are listed in
[`main-theorem.md`](main-theorem.md), and the numbered assertion inventory
is in [`coverage.json`](coverage.json).
