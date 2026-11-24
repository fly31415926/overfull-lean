# Independent semantic review: complete one-core coloring lemma

Reviewer: four-label proof agent, independently of the one-core implementation agent.
This note records a source comparison and mathematical interface review after the
clean focused Lean build. The root's complete verifier and axiom audit remain the
release gate; this note does not replace them or certify publication.

## Source identity

The project inventory pins the 2026-11-20 manuscript. For this review, the exact
Lemma 3.1 bytes were recovered from the later inspected manuscript
`/workspace/scratch/f234ea3483b7/overfull_revision/baseline/Four_Robust_Component_Cases_2026-11-21.tex`,
whose full SHA-256 is `ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.
The recovered block, label `single:lem:coloring`, has SHA-256
`e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe`, identical to the
pinned assertion identity in `docs/coverage.json`. This establishes identity of
the inspected assertion bytes, not identity of the two whole manuscripts. The
assertion's source statement has not been altered to match the implementation.

## Scope comparison

The final declaration is `Overfull.single_core_coloring` in
`Overfull/AuxiliarySimple/SingleCore.lean`.

| Pinned source requirement | Formal public statement or derivation |
| --- | --- |
| Fixed ordinary robust parameters with sufficiently small range | Inputs `0 < ν`, `ν ≤ τ`, and explicit sufficient bound `τ ≤ 1/4096000` |
| Positive tolerance and order threshold before the graph | `∃ ε > 0, ∃ n₀ > 0, ∀ V, G, U, Z, H, a, ...` |
| Simple host of maximum degree at least one quarter of its order | `G : SimpleGraph V` and `card V / 4 ≤ G.maxDegree` |
| No maximum-degree-overfull set | Quantification over every `X : Finset V` with palette `G.maxDegree` |
| Cover by U and Z, possibly overlapping | Public cover is `∀ v, v ∈ U ∨ v ∈ Z`; the proof replaces Z by `Z \ U` |
| Core order at least one quarter of host order | Public bound `card V / 4 ≤ U.card` |
| A spanning robust graph in G[U] | `H : SimpleGraph U`, `H ≤ G.induce U`, and `IsRobustExpander H ν τ` |
| Minimum core degree at least Δ-a | Public lower bound at every vertex of H |
| Combined error `a+|Z|+1 ≤ εn` | Same public error budget; removing overlap can only decrease it |
| Δ-edge-coloring of original G | `Nonempty (Overfull.EdgeColoring G G.maxDegree)` |

No regularity, even host order, disjoint-cover, or nonnegative-error assumption
has been added. The proof derives `a ≥ 0` from a core vertex: the positive order
threshold and core-size bound make U nonempty, and `d_H(v) ≤ d_G(v) ≤ Δ` combines
with the source lower bound. Simplicity and positive host order supply `Δ < n`.
No completion graph, matching schedule, circuit partition, residual coloring,
or final coloring is supplied as a public hypothesis.

## Dependency and constant order

The one-core theorem constructs an auxiliary completion and calls the new
nonregular two-core theorem. That theorem constructs another auxiliary core
and calls the completed three-core regular factorization theorem. In each
completion, the auxiliary robustness parameter is chosen first, the old and
new core parameters are reduced to a common positive value, and downstream
tolerances and order thresholds are chosen before the host graph. The doubled
host order accounts for the halved density. Original colorings are recovered
by the proved copy-preserving restriction from the actual simple completion.

The two completion budget calculations use `a ≥ 0` when passing from
`a+2|Z|+2` to `2(a+|Z|+1)`. The missing `ha` in an early tactic invocation was
reported during this independent review and is included in the final proofs.

The three-core regular composition chooses the entire tolerance function
`f(t) = min(1/4, εB(t)/2)` before bounded absorption chooses T. It then takes a
finite maximum of the order thresholds for t≤T. Thus no tolerance or threshold
is chosen after observing an unknown exceptional set or host. Its foreign,
absorption, and frequent-pattern prefixes are restored on original copies.

The explicit range bound is a sufficient bound obtained by composition; this
review makes no optimality claim. The result closes the full pinned Lemma 3.1.
It does not close the full four-core terminal proposition, the general
four-label compatible-circuit theorem, or the main Overfull Conjecture theorem.

## Observed focused verification

`development/auxiliary-simple-single-05/command.json` records the actual
`lake build --wfail Overfull.AuxiliarySimple.SingleCore` command with exit 0,
3,614 jobs, no warnings, and no inputs changed during the command. The whole
project audit and preservation checks must still pass before numbered coverage
is promoted in a released checkpoint.

## Reviewed source hashes

| Source | SHA-256 |
| --- | --- |
| `Overfull/AuxiliarySimple/SingleCore.lean` | `bb8ddfb7f84de7f9dcbcdb5c54c1996be9967e4df6d95b237ed72778cabf76cd` |
| `Overfull/AuxiliarySimple/OrdinaryOne.lean` | `18a3145ef747a8b09fa524c65aa8e7edd98d56022e43dd4cb86f78b6d60e30f7` |
| `Overfull/AuxiliarySimple/OrdinaryTwo.lean` | `e921f8e66c4241adcf08bf1bee8073a25ebf13c76ac6d5a1ec182952f20043a0` |
| `Overfull/AuxiliarySimple/Deficiency.lean` | `92971ee36ca5d2ab15888c6ff8c19e92f3524bf5c172db2119f0be076ca82c43` |
| `Overfull/ThreeCoreReduction/Regular.lean` | `2e08a839f27ed961c929ff41d63a46c9d30d6f084249a50558a24ed3af3f9db6` |
| `Overfull/ThreeCoreReduction/Bounded.lean` | `b3e386b59b907a69ed2598e28a0eaa8ce27416614e658349b62772efb904a6a3` |
