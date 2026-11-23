# Native reserve completion: fresh verification and preservation

**The exact frozen candidate passed strict Lean verification and the unchanged full axiom audit.**
Run `20261123T201422Z` began at `2026-11-23T20:14:22.720770+00:00`. This preservation report
was recorded at `2026-11-23T21:14:00.091618+00:00` against published baseline `98c6b228a997fead863d05041f12799c93fac18b`.

## Mathematical scope

Uniform original-host native two-core reserve completion: actual disjoint compressed reserves, rounded and protected native multiplicities, original-copy boundary realization, robust core completions, and an actual regular non-overfull residual retaining robust embedded cores. The surviving linear reserve and h-r margin are derived from original-host assumptions. Supporting progress toward Corollary 4.6; palette grouping, the full two-core factorization, and the main theorem remain incomplete.

The final uniform theorem chooses all error and order parameters before the
host. From its original regularity, no-overfull condition and two robust
embedded cores with at most two exceptions, it constructs an actual linear
boundary reserve and disjoint perfect completions avoiding it. The actual
residual is regular, has no overfull set, and retains robust embedded cores.
Its degrees satisfy `h+q=k`, `k/30≤r≤h`, and `h-r≤δn`.

The proof retains actual parallel copies, a single original weighted proposal,
exact reserved-pool accounting, exact completed cut-copy identities, and the
actual unused core graphs. It assumes no residual fractional decomposition.
The parent perfect matchings of the reserve need not survive or be disjoint.

The full two-core Corollary 4.6, palette grouping, and main theorem remain
incomplete. **No numbered assertion is added: coverage remains 47/69.**
See the proof map and semantic review for the exact hypotheses and limits.

| New module | Public theorem proofs |
| --- | ---: |
| `Overfull.NativeReserve.AcceptedRealization` | 1 |
| `Overfull.NativeReserve.BoundaryProperties` | 6 |
| `Overfull.NativeReserve.CompletionConstruction` | 1 |
| `Overfull.NativeReserve.CompletionCuts` | 3 |
| `Overfull.NativeReserve.CompletionFootprints` | 9 |
| `Overfull.NativeReserve.CompletionGlue` | 12 |
| `Overfull.NativeReserve.CompletionParameters` | 6 |
| `Overfull.NativeReserve.Construction` | 2 |
| `Overfull.NativeReserve.CorePacking` | 1 |
| `Overfull.NativeReserve.CutSafety` | 10 |
| `Overfull.NativeReserve.DenseSelection` | 6 |
| `Overfull.NativeReserve.Greedy` | 5 |
| `Overfull.NativeReserve.NativeCutWeights` | 17 |
| `Overfull.NativeReserve.PackingConstruction` | 11 |
| `Overfull.NativeReserve.ProtectedPacking` | 6 |
| `Overfull.NativeReserve.ProtectedSelection` | 6 |
| `Overfull.NativeReserve.Realization` | 6 |
| `Overfull.NativeReserve.Residual` | 11 |
| `Overfull.NativeReserve.RetainedCore` | 7 |
| `Overfull.NativeReserve.RoundedPools` | 12 |
| `Overfull.NativeReserve.Rounding` | 10 |
| `Overfull.NativeReserve.Schedule` | 4 |
| `Overfull.NativeReserve.WeightedPacking` | 2 |
| `Overfull.NativeReserve.WeightedSafety` | 9 |

The 24 modules contain 163
mapped public theorem proofs and 336 audited
proof declarations including private and generated support.

## Fresh verification evidence

| Check | Observed result |
| --- | --- |
| Complete verifier | Exit 0; all frozen inputs unchanged |
| Strict `lake build --wfail` | 3,707 jobs passed |
| Unchanged full `Audit.lean` | 12,391 declarations passed |
| Prior declarations, modules and axiom sets | All 12,055 preserved |
| Newly audited declarations | 336 |
| Prior nonroot proof sources | 511 byte-identical |
| Previous declaration maps | All 9 byte-identical |
| Previous completed-result mappings | All 1,621 retained |
| Numbered assertion records | All 69 unchanged; all 47 completed records retained |
| Frozen sources and verification inputs | 619 exact SHA256 matches |

Logical axioms remain limited to `propext`, `Classical.choice`, and `Quot.sound`.
Lean remains 4.24.0, and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Every prior verification gate is
retained; the verifier has exactly four additive native-reserve mapping edits.
The root differs only by its declared new import.

The `final/` folder contains byte-for-byte copies of the actual fresh build,
complete axiom output, results, declaration map, and setup/version outputs.
The console and all evidence hashes are retained in this run. No historical
verification log was replayed or rewritten as a current result.

## Recovery and development evidence

Only `AcceptedRealization.lean` was recovered byte-for-byte from the earlier
interrupted publication. The other continuation sources were reconstructed
and checked afresh. The earlier observed successful run is historical context;
its lost logs were not recreated. See `recovery-provenance.md`.

This run retains 13 successful, 15 failed,
4 explicitly interrupted and 1 incomplete
command records. Interrupted duplicate dependency builds remain interrupted,
with their actual observed exit 130. Every command source snapshot has been
checked against its recorded hash. Intermediate errors remain visible.

| Failed command record | Exit code | Actual output |
| --- | ---: | --- |
| `verification/runs/20261123T201422Z/rebuild-numeric-02/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-numeric-02/output.log` |
| `verification/runs/20261123T201422Z/rebuild-numeric-03/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-numeric-03/output.log` |
| `verification/runs/20261123T201422Z/rebuild-numeric-04/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-numeric-04/output.log` |
| `verification/runs/20261123T201422Z/rebuild-realization-01/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-realization-01/output.log` |
| `verification/runs/20261123T201422Z/rebuild-realization-02/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-realization-02/output.log` |
| `verification/runs/20261123T201422Z/rebuild-realization-03/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-realization-03/output.log` |
| `verification/runs/20261123T201422Z/rebuild-realization-04/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-realization-04/output.log` |
| `verification/runs/20261123T201422Z/rebuild-realization-06/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-realization-06/output.log` |
| `verification/runs/20261123T201422Z/rebuild-root-02/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-root-02/output.log` |
| `verification/runs/20261123T201422Z/rebuild-root-04/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-root-04/output.log` |
| `verification/runs/20261123T201422Z/rebuild-root-05/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-root-05/output.log` |
| `verification/runs/20261123T201422Z/rebuild-safety-02/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-safety-02/output.log` |
| `verification/runs/20261123T201422Z/rebuild-safety-03/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-safety-03/output.log` |
| `verification/runs/20261123T201422Z/rebuild-safety-05/command.json` | 1 | `verification/runs/20261123T201422Z/rebuild-safety-05/output.log` |
| `verification/runs/20261123T201422Z/setup-commands.json` entry 1 | 1 | `verification/runs/20261123T201422Z/setup-cache.log` |

## Publication and next work

This report precedes verified-branch publication and makes no claim that the
branch updates have succeeded. Publish the exact checked sources and complete
real evidence to both authorized verified branches, preserving concurrent work,
and read back their actual commit/tree identifiers.

The next proof stage applies the existing assigned-part/joining decomposition
to this actual residual, then constructs compatible palette classes and the
remaining robust completions. Group parity, reserved crossing alignment,
group footprint bounds and final coloring reconstruction remain obligations.
