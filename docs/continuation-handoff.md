# Continuation handoff: complete bounded-input factorization

## Completed assertion and exact baseline

This continuation completes **Corollary 4.6**, with both its one-core and
two-core alternatives, and increases numbered coverage from 47/69 to **48/69**.
Its original statement hash remains
`86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26`.
All 69 source statement hashes and all other 68 assertion records are unchanged.
The main theorem and 20 other numbered assertions remain incomplete.

The verified local predecessor is `f557ae03355f14a0441b37283f35186a95aca2d7`,
exact tree `efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d`, containing 4,321 files,
13,170 audited declarations, 2,176 completed-result mappings and 696 frozen
source/input hashes. This worktree is
`/workspace/scratch/7dae4c9bb5a1/overfull-lean`; the run is
`verification/runs/20261124T021500Z/`.

Before the new proof verification, the exact preceding local chain
`af8dca2 → d2e7b12 → f557ae0` was recovered as identical public Git trees at
`a4b34a84f14deaff118d34d0f0bd8a46be40fdcc →
498d7378c6b5a2fe126f7dd2e20c3c5798248d20 →
0f168ca9f2f8a82b6c00e1a7633ec035985b7209`.
Both `main` and `verified-bipartite-continuation-2026-11-21` were advanced
without force and independently read back at the last public commit. The
genuine receipts are `baseline-publication-success.json`. Historical
automatic-review rejections remain preserved; they are not a current blocker.
New publication must separately record its exact tree and branch readbacks.

## Completed construction

`Overfull.NativeTerminal.exists_uniform_native_remaining_factorization`
constructs the entire native residual coloring. It applies the existing
nonprotected-prefix construction, factors the actual protected residual from
its exact selected-reserve image, and restores the removed perfect matchings.

`Overfull.two_core_two_exception_factorization` constructs the reserve and
first prefix from the original regular non-overfull host and its two robust
embedded cores. The uniform reserve theorem fixes the surviving expansion
parameter before the requested surplus tolerance. It then applies the native
remaining factorization and restores the first prefix. Its companion
`Overfull.two_core_two_exception_one_factorization` produces exactly the
degree number of disjoint perfect matchings covering every original copy.

`Overfull.bounded_input_factorization` and
`Overfull.bounded_input_one_factorization` combine the existing one-core and
new two-core branches under one error tolerance and order threshold. They
match the two alternatives in the source: one core with at most three exterior
vertices, or two cores with at most two other vertices. No input coloring,
reserve, perfect-matching representative, or residual factorization occurs
in the public theorem's hypotheses.

The exact residual external-copy image gives a terminal shore cut of size
zero for even assigned shores and of size equal to the residual degree for
odd assigned shores. Both shores see the same crossing copies. Assigned
exceptions meet their own old core only. The optional exceptional pair is a
closed component of order zero or two.

Even shores use actual vertex-and-edge restrictions. Odd shores contract the
opposite shore to an apex. The smaller old core is embedded exactly, preserving
degree and robustness. The independent-exterior theorem constructs each shore
coloring. A common bijection on original crossing copies aligns both odd-shore
palettes. Gluing proves properness at original vertices. Parallel copies are
never identified.

The final factorization preserves every removed prefix class exactly, but may
recolor selected reserve stars. It does not assert that each originally
protected full boundary retains its old color. Corollary 4.6 does not require
that stronger extension.

## Uniform numerical hierarchy

The outer reserve range is `α/960`, below its `α/300` bound and the next
prefix's `α/240` bound. Terminal range is `α/3840`; the prefix's returned
expansion parameter is reduced to its minimum with that range. Density is
`α/120`. The actual natural quotient `r/2` meets this density by the reserve
bound `r≥αn/30` and `n≥120/α`. Shrinking host error below
`ε_terminal*β` converts it to both core-order bounds; explicit ceiling
thresholds make both cores sufficiently large. All choices precede the host.

The original-host proof derives `a≥0` from regularity and a nonempty embedded
core, then uses `a+1` as the positive reserve deficit. The combined statement
sets `γ=min α (min β 1)`, allows arbitrary positive fixed density bounds,
and requires the explicit sufficiently small range `τ≤γ/16`.

## Verification and publication

Read `verification/results.json`, this run's `verification-command.json`,
`preservation.json` and `final-report.md` for actual full-verification counts.
A focused build alone is not a whole-project audit. Every genuine failed and
successful development command remains preserved.

The stock `Audit.lean`, all old nonroot proof sources, old declaration names,
owners and axiom sets, prior completed mappings, and historical evidence are
preserved. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The verifier registers the new maps and promotes only 4.6: count 48, an explicit
positive theorem-and-statement-hash gate replacing its old incompleteness
guard, with every other guard retained. The checker preserves all 69 statement
identities and all 68 other assertion records. The manuscript-source metadata
changes only its top-level completed count. Exact permitted deltas are recorded.

Use Lean 4.24.0 at
`/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`
with mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Focused commands use `record-command.py UNIQUE-NAME lake build --wfail MODULE`.
Run the complete verifier attached through
`python3 -u verification/runs/20261124T021500Z/supervise-verifier.py full-01`;
await its actual exit, then run `record-preservation.py` and local-only
`package-verified.py`. Do not alter frozen inputs during a full run.
Uploaded objects or a local commit do not establish branch publication.

## Next mathematical work

Corollary 4.6 is no longer unfinished. The broader fixed-pattern Lemma 4.4 and
its five-exception Corollary 4.5 still need their full construction; the present
native reserve geometry assumes at most two exceptions. General four-label
compatible-circuit selection, terminal Proposition 4.16, remaining dense and
bipartite factorization constructions, the critical average-degree input and
the main theorem remain open in the formalization.

The next continuation should inspect the latest remote handoff and coverage,
then target a concrete missing assertion. Reuse the completed bounded-input
theorem in the three-core terminal argument where its actual hypotheses can
be derived. Never count a composition that supplies an unproved target input.
