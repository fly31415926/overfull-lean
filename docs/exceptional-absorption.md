# Bounded exceptional-set absorption

The public declaration for manuscript Proposition 4.12 (`three:prop:band`)
is `Overfull.bounded_exceptional_absorption` in
[`Bounded.lean`](../Overfull/Absorption/Bounded.lean). Its result records an
actual perfect-matching deletion sequence, the exact residual graph, two
actual core enlargements, and the final exceptional set. The main theorem
of the manuscript remains unverified.

## Statement and parameter order

Fix a positive density `α ≤ 1`, positive robust parameters `ν ≤ τ`,
`τ ≤ α/1000`, and a nonnegative foreign-incidence constant `c`.
The theorem first chooses a positive output robust parameter. For every
positive function `f : ℕ → ℝ`, it then chooses a finite exceptional bound
`T`, a positive original error tolerance, and an order threshold. All
these choices precede the graph.

The input is a sufficiently large simple regular graph of degree
`h ≥ αn`, with no overfull set at degree `h`. Its vertex set is partitioned
into an exceptional set and at most four disjoint cores, each of order at
least `αn`. Each distinguished core graph is an actual subgraph, is robust
`(ν,τ)`, and has minimum degree at least `h-a`. The smallness hypothesis is
`a + |Z| + 1 ≤ εn`. An assignment of exceptional vertices to cores is
supplied. Their actual foreign-neighbor counts have total at most `ch`.
Because the cores and exceptional set are disjoint, this sum counts every
exceptional-to-nonassigned-core edge once; the equality with the edge-count
form is already proved in `ForeignEdges/FinalCount.lean`.

The result has:

- A sequence of actual perfect matchings in the original host, each
  present when it is deleted, and hence pairwise edge-disjoint.
- Exactly the graph left by those deletions, regular of degree at least
  `3h/4`, with no overfull set at its retained degree.
- Enlarged disjoint cores containing their original labelled cores and
  covering every vertex outside the final exceptional set.
- At most `T` exceptional vertices, all drawn from the original set.
- Actual core graphs embedded in the residual ambient graph, retaining a
  fixed positive robust parameter and range `2τ`.
- A common nonnegative core error bounded by
  `f(|Z_final|) * h_final`.

The last clause uses the actual final cardinality. No monotonicity of `f`
is assumed. This is supplied by applying the threshold construction to
the positive finite lower envelope of `f`.

## Threshold bands

[`Thresholds.lean`](../Overfull/Absorption/Thresholds.lean) freezes the
entry graph, its degree, and each exceptional vertex's foreign-neighbor
count. The bands are exactly

```text
rho(i+1) * h ≤ q(z) < rho(i) * h.
```

Their pairwise disjointness gives a band of total weight at most `h/8`
when the number of bands exceeds `8c`. At any positive threshold `rho`,
the actual high set has at most `ceil(c/rho)` vertices. The module also
proves the exact exceptional-set identity after the two absorptions.

[`ThresholdsSchedule.lean`](../Overfull/Absorption/ThresholdsSchedule.lean)
constructs the decreasing positive thresholds recursively. The next
threshold is chosen after the current bound `t(i)=ceil(c/rho(i))` is
known. Finite minima and maxima produce one error tolerance and one order
threshold working for every possible selected band. Its final-error
theorem absorbs the finite star threshold into the requested error at the
actual final cardinality.

[`PhaseParameters.lean`](../Overfull/Absorption/PhaseParameters.lean)
fixes the initial threshold control before the eventual exceptional
bound. After that bound is known, it proves all scalar bounds needed by
the forcing phase: the strict quarter-degree budget, the residual density,
the packing horizon, the footprint tolerance, the small-cut order bound,
and both vertex-addition bounds.

## Actual vertex addition

[`CoreRobust.lean`](../Overfull/Absorption/CoreRobust.lean) proves robust
stability under addition directly. An embedded robust `(ν,τ)` graph on
`m` vertices remains robust `(ν/4,2τ)` after at most `νm/4` vertices are
added, provided `0 ≤ ν ≤ τ ≤ 1/4` and its old edges are retained.
The proof restricts an actual tested set to the old vertices and compares
the old and enlarged neighbor counts and orders. A separate corollary
uses the actual enlarged minimum degree to restore any permitted smaller
robust range.

[`Core.lean`](../Overfull/Absorption/Core.lean) constructs the enlarged
graph. It retains precisely the old core edges between old vertices and
adds every ambient edge incident with an absorbed vertex. It proves
ambient embedding, the exact restriction to the old labels, and old/new
vertex degree bounds.

[`CoreFamily.lean`](../Overfull/Absorption/CoreFamily.lean) applies that
constructor to the assignment fibers of the absorbed set. It proves the
actual partition, covering, disjointness, order, degree, and robustness
properties. Absorption changes the distinguished core graphs and the
partition; the ambient graph is unchanged.

After the first absorption the common error is

```text
A = a + rho(i+1) * h + |Z|.
```

## Safe repeated forcing with fixed rules

[`ForceMatching/Adaptive.lean`](../Overfull/ForceMatching/Adaptive.lean)
separates the sampled compressed matching from its eventual internal
completion. The partial matching meets the requested exceptional-centered
star, covers the exceptional set, has the required core parities and
bounded footprints, and has no internal core edges. Its safety clause
applies to every compatible completion with the stated actual robust
residual cores.

[`Potential.lean`](../Overfull/Absorption/Potential.lean) counts every
current neighbor outside each selected vertex's assigned enlarged core.
This includes neighbors that remain exceptional. Its exact outside-star
cardinality equals that outside degree. Meeting such a star strictly
decreases the actual summed potential. The initial potential is at most

```text
h/8 + T * |Z|.
```

The original smallness condition makes this strictly less than `h/4`.

[`ForcingProcess.lean`](../Overfull/Absorption/ForcingProcess.lean)
chooses one certified packing rule for each first-enlarged core. The
existing `ForeignEpoch.Transcript` records the actual original-host
matchings and the exact local rule outputs. At each round the current
partial matching's input is proved admissible from its actual exterior
incidences before its completion is constructed. The completed matching
is rehosted into the original graph and appended to the transcript.

Strong induction on the natural potential gives termination with

```text
rounds + current potential ≤ initial potential.
```

All residual cores retain the same certified robust parameter throughout
the phase, including at a zero-round termination. No per-round completion
or admissibility oracle is assumed. In this uniform formulation the star
bound is `11 * 2^(T+4)`, where `T` bounds every exceptional cardinality in
the fixed schedule. This larger common bound simplifies the uniform order
choice without affecting the asymptotic conclusion.

## Second absorption and the actual result

At termination every selected vertex has at most `11 * 2^(T+4)` neighbors
outside its assigned first-enlarged core.
[`SecondAbsorption.lean`](../Overfull/Absorption/SecondAbsorption.lean)
therefore obtains final error

```text
a + rho(i+1) * h + |Z| + 11 * 2^(T+4).
```

There is no second exceptional-order term: the terminal outside degree
already counts every edge outside the assigned core. The degree-budget
lemma includes natural-number rounding and yields the `3h/4` reserve.

[`Result.lean`](../Overfull/Absorption/Result.lean) records the actual
residual graph, original-host matching sequence, enlarged partition, and
all degree, error, and robustness conclusions. The public theorem
constructs this result from the graph-independent parameter choices and
the actual selected band.

## Verification boundary

The strict project build and transitive axiom audit are recorded in
`verification/results.json`. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Compilation of a conditional helper
is not used as evidence that the complete manuscript is proved.

The subsequent Lemma 4.13, the frequent-pattern reduction, is now proved
with actual pattern selection, rounding, realization, all-prefix safety,
complete absorption, and retained forest supply; see
[`frequent-pattern.md`](frequent-pattern.md).
[`next-verification-target.md`](next-verification-target.md) records the
boundary-extension target of Lemma 4.14, its unresolved bounded-input
factorization dependency, and the later terminal-factorization work.
