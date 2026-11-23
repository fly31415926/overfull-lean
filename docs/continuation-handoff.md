# Continuation handoff: native reserve completion

## Authoritative state and recovery

Read the current remote heads of `main` and
`verified-bipartite-continuation-2026-11-21` in
`fly31415926/overfull-lean` before continuing. This run began from
`98c6b228a997fead863d05041f12799c93fac18b`, tree
`1a3d5f43124a34de81c46a260d6c399fcecb5c96`, with 1027 tracked files.
The published baseline audited 12055 declarations and completed 47 of 69
numbered assertions. A later verified commit supersedes this baseline.

Current run: `20261123T201422Z`, started 2026-11-23T20:14:22.720770Z.
Recovery source checkpoints are on `recovery/native-reserve-20261123`.
The first preserves the exact recovered `AcceptedRealization.lean` at
`2eccf2a00df03c9a3c07f14fdbecd38087c8028d`; the next, `40ee472`,
preserves 21 draft/recovered modules and actual setup evidence.
Source-only checkpoints are not full verification claims.

The earlier run `20261123T125102Z` was observed to complete a build/audit,
but its complete publication was interrupted and its scratch artifacts
became unavailable. Only the recovered source identified above has an
exact original-byte recovery claim. Other sources in this run were
reconstructed and require fresh verification. Missing old logs are not
recreated. See this run's `recovery-provenance.md` and actual command records.

## Current completed construction interface

The final interface is
`Overfull.NativeReserve.exists_native_reserve_completion_parameters`.
The exact source manifest, proof map and semantic review are in
`docs/native-reserve-source.json`, `docs/native-reserve-verification.md`,
and `docs/native-reserve-semantic-review.md`. Actual full verifier records
for the exact current source hashes determine checked status.

The theorem chooses positive error/robustness constants and an order
threshold before the host. From original regularity, absence of overfull
sets, two disjoint large robust embedded cores, at most two exceptions,
and a sufficiently small original core degree error, it constructs:

- An actual linear reserve of disjoint compressed boundaries sharing one
  actual matching's native assignment signature.
- A disjoint perfect matching family avoiding every reserved copy.
- Integers satisfying `k/30≤r≤h`, `h+q=k`, and `h-r≤δn`.
- The actual `h`-regular residual with no `h`-overfull vertex set.
- Actual retained robust cores on both old core vertex sets, each with
  minimum degree at least `h-a`.

Every object uses original multigraph edge copies, including arbitrary
parallel copies in an exceptional pair. The original representative need
not be a perfect matching of the residual. Its assignment remains the
one used in the next joining stage. The exact original-assignment
`assignedLabel_joining_decomposition_in_host` interface is already
available in the preserved baseline.

## Next proof obligation: grouping and residual factorization

Apply the existing assigned-part/joining decomposition to the actual
residual constructed above, then prove the palette grouping and final
factorization. The following points are proposals to prove, not checked
new conclusions of the reserve theorem.

1. Derive joining-copy degree bounds in the actual assigned residual:
   at an old-core vertex, use the retained core-complement error `a`;
   at an exception, use the `r` surviving reserved incidences internal
   to its assigned part, giving the proposed bound `h-r`.
2. Develop a finite palette assignment preserving the parity of every
   joining piece. For the two-odd case, precolor the `h` primary pieces
   injectively, then add surplus pieces using endpoint conflicts and
   bounded class loads. A candidate greedy condition is `6D<h`, where
   `D=max(a,h-r)`; its hypotheses must be derived from uniform constants.
3. Retain individual parity certificates in the all-even case. The
   existing wrapper that forgets these certificates is not sufficient
   by itself for grouping; use the underlying compatible-circuit data.
4. Align reserved old-core crossing copies with the necessary primary
   palette structure. A reserved crossing copy may be a joining copy;
   it is not automatically internal to an assigned part or aligned to
   an arbitrary circuit decomposition. Only the exceptional reserved
   incidences are automatically internal to the assigned parts.
5. Prove group footprint size, parity and vertex-load bounds. A piece
   with at most three edges can produce a much larger grouped palette
   class, so the individual-piece size bound does not justify the
   required robust extension input for the whole group.
6. Treat a two-vertex exceptional pair fiber with its actual parallel
   copies. Exact equal free palettes and regularity should supply the
   required pair-copy assignment; this still needs a Lean construction.
7. Combine completed residual color classes with the already removed
   perfect matchings using disjoint palettes, then invoke the available
   coloring-to-one-factorization bridge. This requires an actual residual
   coloring and is not supplied by a conditional reconstruction lemma.

The new reserve theorem solves the reserve/actual-safe-residual stage;
do not repeat it or silently assume the next palette conclusions.
Full Corollary 4.5 still permits five exceptions; this construction's
`|Z|≤2` hypothesis must not replace that manuscript condition.

**Coverage remains 47/69; full two-core Corollary 4.6 and the main theorem
remain incomplete.** General four-label circuits, the remaining terminal
factorization, structural/critical-average-degree and Section 6 obligations
remain distinct gaps. The 69 original assertion records are unchanged.

## Verification, preservation and publication

Use Lean 4.24.0 and the existing dependency manifest, with mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Do not run `lake update`.
The current runtime is `/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`.
Temporary workspaces may disappear; reachable GitHub checkpoints and their
real run records are the durable authority.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_native_reserve_manifest.py
python3 verification/runs/20261123T201422Z/run-verifier.py full-01
python3 verification/runs/20261123T201422Z/record-final.py
```

Use a new attempt directory if a full check must be rerun. Keep all real
success, failure and interrupted logs. `Audit.lean` is byte-identical and
retains only `propext`, `Classical.choice`, and `Quot.sound`. The verifier
has exactly four additive source-map checks for this continuation. Every
prior proof, declaration mapping, numbered assertion record and historical
verification artifact must be preserved.

The first dependency-cache attempt hit HTTP 429; a lower-concurrency retry
restored 3106 cache files successfully. Duplicate initial dependency builds
were explicitly interrupted with observed exit 130 and retained records;
a single baseline build then completed before targeted native checks.
These interruptions do not constitute failed mathematical proofs or passes.

After a fresh complete strict build, full transitive audit, exact mapping
validation and preservation check pass, publish all sources, documentation,
mappings and genuine run logs to both authorized verified branches. Read
back both branch heads and the exact commit/tree. The user has already
authorized autonomous recovery, continuation and this publication; do not
ask again. Do not label a source-only checkpoint as verified.
