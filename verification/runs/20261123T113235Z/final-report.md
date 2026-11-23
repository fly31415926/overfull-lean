# Native matching patterns: final verification and preservation

**The complete frozen candidate passed strict Lean verification and the unchanged full axiom audit.**
This run began at `2026-11-23T11:32:35.097528+00:00`. The preservation report was written at
`2026-11-23T12:31:39.211058+00:00` against authoritative baseline `ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6`.

## Checked mathematical progress

Native actual-copy matching-distribution capacities, at most five two-core assignment signatures and a heavy actual representative, forced copy pools, and boundary compression retaining every exceptional matching copy and crossing parity. Supporting progress toward Corollary 4.6 only. Does not construct simultaneous reserves or a safe residual, prove robust completion or palette grouping, or complete a numbered manuscript assertion.

The native distribution keeps every parallel edge copy distinct. With at most two
exceptions, at most five assignment signatures suffice; a positive-weight actual
representative has signature weight at least `k/5`. Equal signatures retain the
actual assigned parts and old-core crossing parity. The internal-pair signature
has weight exactly the original internal-copy multiplicity. The corresponding
exceptional-to-core pool cardinality is exactly the aggregate weight of all
signatures assigning that exception to that core. Individual heavy signatures
therefore give the proved pool lower bounds; odd crossing parity also forces
the cross-core pool lower bound.
Boundary compression retains all selected exceptional copies, uses at most
`|Z| + 1` original copies, and leaves an even uncovered order in each core.
Its zero-or-one retained crossing count is constant on each signature, with
the original representative and assigned parts retained throughout.

| New module | Public theorem proofs |
| --- | ---: |
| `Overfull.AssignedParts.NativeWeights` | 11 |
| `Overfull.AssignedParts.Signatures` | 15 |
| `Overfull.AssignedParts.SignaturePools` | 7 |
| `Overfull.AssignedParts.HeavySignature` | 9 |
| `Overfull.AssignedParts.ExactPoolWeights` | 5 |
| `Overfull.AssignedParts.BoundaryCompression` | 21 |
| `Overfull.AssignedParts.CompressionCuts` | 11 |
| `Overfull.AssignedParts.NativePatternConstruction` | 4 |

The native manifest has **83 public theorem proofs**
in **8 modules**, covering
**128 audited declarations** including generated
and private support proofs. This is supporting progress toward Corollary 4.6.
**No numbered manuscript assertion is newly complete: coverage remains 47/69,
with 22 assertions, including the main theorem, incomplete.**

## Actual verification evidence

| Check | Result |
| --- | --- |
| Complete `python3 scripts/verify.py` | Exit 0; frozen inputs unchanged |
| Strict `lake build --wfail` | 3,683 jobs passed |
| Stock complete `Audit.lean` | 12,055 declarations passed |
| Prior declaration names, modules and axiom sets | All 11,927 preserved |
| Newly audited declarations | 128 |
| Prior nonroot proof files, including `Audit.lean` | 503 byte-identical |
| Previous declaration maps | All 8 byte-identical |
| Previous completed-result mappings | All 1,538 retained |
| Numbered assertion records and statement hashes | All 69 unchanged; all 47 complete records preserved |
| Current proof source paths and SHA256 values | 512 files; exact match |
| Other current verification-input paths and SHA256 values | 79 files; exact match |
| Frozen source/input inventory | 591 paths; exact match at verification and recording |

The permitted logical axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
The preserved Lean pin is `leanprover/lean4:v4.24.0`; mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, with all other dependency source
revisions unchanged. The actual axiom-log declarations were compared with every
declaration in the fresh result. Removing the declared new root import reproduces
the old root bytes. The verifier differs by precisely the four checked native
manifest/mapping extensions; every previous gate is preserved.

The [`final/`](final/) directory contains byte-for-byte copies of the actual
fresh build, complete axiom log, result report, native declaration map, Lean
version log and Vizing-source log. The full console remains in
[`verification-console.log`](verification-console.log). No old verification log
was replayed or rewritten as a fresh compiler result. Exact copies, source
snapshots and evidence hashes are recorded in [`preservation.json`](preservation.json).

## Retained development and setup failures

The run retains 11 successful, 8 failed and
0 incomplete command records. These are separate from the completed
full verification above. Every recorded source snapshot was checked against its
recorded SHA256; every command has its actual output log. Failed intermediate
commands remain marked failed, including setup/download errors and intermediate
Lean diagnostics. No failure is relabeled as a successful check.

| Failed command record | Exit code | Actual output |
| --- | ---: | --- |
| `verification/runs/20261123T113235Z/compression-01/command.json` | 1 | `verification/runs/20261123T113235Z/compression-01/output.log` |
| `verification/runs/20261123T113235Z/compression-cuts-01/command.json` | 1 | `verification/runs/20261123T113235Z/compression-cuts-01/output.log` |
| `verification/runs/20261123T113235Z/exact-pool-weights-01/command.json` | 1 | `verification/runs/20261123T113235Z/exact-pool-weights-01/output.log` |
| `verification/runs/20261123T113235Z/native-construction-01/command.json` | 1 | `verification/runs/20261123T113235Z/native-construction-01/output.log` |
| `verification/runs/20261123T113235Z/setup-cache-retry/command.json` | 1 | `verification/runs/20261123T113235Z/setup-cache-retry/output.log` |
| `verification/runs/20261123T113235Z/setup-proofwidgets/command.json` | 1 | `verification/runs/20261123T113235Z/setup-proofwidgets/output.log` |
| `verification/runs/20261123T113235Z/signatures/attempt-01/command.json` | 1 | `verification/runs/20261123T113235Z/signatures/attempt-01/output.log` |
| `verification/runs/20261123T113235Z/setup-commands.json` entry 1 | 1 | `verification/runs/20261123T113235Z/setup-cache.log` |

## Remaining proof work and publication

Actual copy capacities do not by themselves provide simultaneous disjoint
reserves, enough distinct neighbors, or a residual graph with no overfull set.
Reserve selection, residual safety, palette grouping, robust completion and
the full factorization in Corollary 4.6 remain separate obligations. The exact
same representative must be used when connecting these new results to them.
The finalized [`next-native-reserve-target.md`](next-native-reserve-target.md)
specifies proposed next-stage work; it is research planning and contributes no
additional checked theorem or declaration to the counts above.

This report is generated before publication to the verified branches and does
not claim that publication has succeeded. The containing checkpoint must be
published to both `main` and `verified-bipartite-continuation-2026-11-21`, preserving
concurrent work, followed by an actual read-back of both remote heads and the
published commit/tree.
