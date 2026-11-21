# Frequent boundary patterns and complete absorption

The public declaration is `Overfull.frequent_boundary_pattern` in
[`Overfull/Patterns/Frequent.lean`](../Overfull/Patterns/Frequent.lean).
Its output is the actual graph-level record
`Overfull.Patterns.FrequentPatternResult` in
[`Overfull/Patterns/Result.lean`](../Overfull/Patterns/Result.lean).
This document describes that declaration and its construction. The strict
build, transitive axiom audit, exact source hashes, and counted manuscript
coverage are recorded by `scripts/verify.py` in `verification/results.json`;
this documentation is not a substitute for those checks.

**The manuscript main theorem remains unverified.** This reduction does
not assert a one-factorization of its final graph. Boundary extension,
bounded exceptional multigraph factorization, compatible circuits, and
the terminal factorization still require their own proofs.

## Manuscript correspondence

The numbered source remains the pinned
`Four_Robust_Component_Cases_2026-11-20.tex`, identified in
[`manuscript-source.json`](manuscript-source.json). The relevant assertion
is **Lemma 4.13**, label `three:lem:pattern`, with statement SHA256

```text
557d62e4c4ab7c00ac7cc29fa403d80601a2b9851e7c7eb62cdeb4caa1d40c3b
```

The complete statement environment was compared with
`Four_Robust_Component_Cases_2026-11-21.tex`; its SHA256 is identical.
This comparison concerns that statement, not an assertion that the two
complete manuscripts are identical.

## Public hypotheses and quantifier order

Write `B = patternBound t = 2^(t.choose 2) * 4^t * 2^6`.
The theorem fixes `t`, the density lower bound `α`, and ordinary robust
parameters `ν, τ`, with

```text
0 < α ≤ 1,   0 < ν ≤ τ ≤ α / (1000 * B).
```

It then chooses a positive `νout` **before** every requested final error
`δ > 0`. After `δ` it chooses one positive initial error tolerance `ε`
and one order threshold `n₀`. Only then are the finite vertex and core
label types, graph, partition, embedded cores, regular degree, and actual
error supplied.

The input is a simple `k`-regular graph of order `n ≥ n₀`, with no
`k`-overfull vertex set, three or four disjoint cores and an exceptional
set `Z` of at most `t` vertices. The cores and `Z` cover every vertex.
Both `k` and every original core order are at least `αn`. Each embedded
simple core graph is a robust `(ν, τ)`-expander and has minimum degree
at least `k-a`, where `0 ≤ a ≤ εn`. Its upper degree bound follows from
embedding into the regular host.

The output robust range is the original `τ`, and the positive output
neighborhood parameter is independent of `δ`. Internally, packing retains
range `τ/2`, and absorption restores range `τ` with the fixed weaker
neighborhood parameter. The theorem constructs all subsequent objects;
it takes no realization oracle, safe residual, prescribed matching family,
final assignment, or terminal factorization as an additional hypothesis.

## What the result contains

| Result fields | Actual conclusion |
| --- | --- |
| `N`, `rounds`, `perfect`, `present` | Original-host perfect matchings, each present when it is deleted |
| `G`, `h`, `graph_eq`, `degree_eq`, `regular` | The exact residual graph and its exact degree `h = k-rounds` |
| `safe_prefixes`, `no_overfull` | No overfull set at the current degree after every prefix, including the final graph |
| `degree_positive`, `retained_degree` | Positive degree and `h ≥ k/(3B)` |
| `U`, `H`, `core_enlargement`, `core_disjoint`, `cover`, `core_embed` | Disjoint enlarged parts containing the old cores and covering every vertex, with actual embedded core graphs |
| `error`, `error_nonneg`, `error_bound`, `core_degree`, `core_robust` | A common nonnegative error at most `δh`, minimum core degree at least `h-error`, and fixed positive robust expansion |
| `reserve`, `reserve_le`, `reserve_error` | An integer `r₀ ≤ h` with `h-r₀ ≤ δh` |
| `code`, `forest`, `forest_isForest`, `forest_shape` | One common core-label embedding and an actual label forest; when all four enlarged parts are odd, it is an explicit perfect matching or three-edge star |
| `pair_supply`, `cut_supply` | At least `r₀` actual joining edges on every forest pair, and at least `r₀` times the forest crossing count on every union of enlarged parts |

The error field is a real upper bound on actual missing core degree. The
ambient regularity and core embedding also give the corresponding upper
degree bound. No exceptional vertex remains outside the enlarged parts.

## Construction and module map

| Stage | Modules | Main content |
| --- | --- | --- |
| Fixed encoding | `Compression`, `Encoding`, `Boundary` | Compress every support matching using one fixed embedding into four labels; encode exceptional pairs, assignments and the joining forest; prove the finite pattern count and exact boundary image |
| Actual weighted distribution | `Weights`, `Distribution`, `WholeUnions` | Scale the proved perfect-matching distribution to total weight `k`; derive actual pair and cut capacities; prove every positive-weight pattern has the correct whole-cut parity |
| Rounding and selection | `Rounding`, `Selection`, `Multiplicity` | Choose a maximum-weight pattern, reserve half its weight, apply one common set of sparse-pair and small-even-cut tests, and enumerate every accepted copy exactly once |
| Actual boundary realization | `Realization`, `BoundaryRealization`, `Pools`, `RealizedFamily` | Select fresh actual host edges while avoiding occupied endpoints; prove matching, exceptional coverage, exact pattern image, parity, footprint and pairwise edge disjointness |
| Fixed-rule completion | `Completion`, `SelectedCompletion` | Derive every core input's admissibility and complete the exact boundary family using one certified rule per core; construct ambient perfect matchings and exact robust residual cores |
| Residual safety | `Cuts`, `Safety`, `SelectedSafety` | Subtract actual crossing counts at every prefix; prove odd whole cuts and all required one-vertex toggles; apply the proved small-cut classification |
| Retained edges and absorption | `ReservedEdges`, `AbsorptionParity`, `Forest` | Prove exact surviving pool counts, actual assigned neighbors, parity of enlarged parts, forest classification and actual pair/cut supply |
| Uniform assembly | `Parameters`, `Result`, `Frequent` | Choose all scalar bounds before the graph, enlarge every assigned core, and produce the complete public result |

All module names in this table are relative to `Overfull/Patterns/`.
Core enlargement reuses the proved actual graph constructions and
robustness lemmas from `Overfull/Absorption/`.

## Numerical reserve and exact graph accounting

For aggregated weights `λΠ`, choose a maximum-weight `Π₀` and put
`r₀ = floor(λΠ₀/2)`. The large-degree threshold gives
`r₀ ≥ k/(3B)`. Simplicity implies that a pattern containing a particular
internal exceptional pair has weight at most one. Consequently `Π₀`
contains no such pair, and no positively selected copy contains one.
Every exceptional vertex is therefore assigned to an actual core.

The proposal is

```text
mΠ = floor((1-η) * (λΠ-r₀*indicator(Π=Π₀))).
```

All exclusions are tested against this same proposal. With

```text
Cₜ = (4t+6)*(t+8) + 2^(t+5),
a₁ = ηk + B + Cₜ*a/η,
```

the selected family leaves `r₀ ≤ h ≤ r₀+a₁`. The stronger pair-demand
inequality reserves `r₀` actual edges on every pair used by `Π₀`.
The endpoint-conflict estimates count actual outside incidences and
establish realizability from candidate counts, including the zero-demand
case. They do not assume that a second collection of copies of the
original support matchings is available.

The numbers `λΠ - processedΠ` are **numerical accounting weights**.
They are not asserted to be a fractional perfect-matching decomposition
of the actual residual after greedy realization. The proof instead uses
original weighted capacities and exact subtraction of actual realized
pattern counts. Odd whole unions have residual cut at least the current
degree. For an even whole union, either its cut remains at least `2a`, or
no accepted pattern crosses it and its original cut edges and incidences
are all retained. Core-vertex cut incidences are at most `a`; exceptional
vertex toggles are other whole unions. These facts prove all-prefix
safety through the small-cut classification.

Finally, every exceptional vertex has at least `r₀` distinct surviving
neighbors in its assigned old core. Adding those vertices and edges gives
core error at most `a+a₁`. The uniform scalar choice makes this at most
`δh`. Assigned exceptional incidences cancel in the part-order parity,
leaving the joining-forest degrees. The classification of odd forests on
four labels uses kernel-checked finite decisions, not `native_decide`.
Actual reserved pair-edge sets then supply every asserted forest cut.
