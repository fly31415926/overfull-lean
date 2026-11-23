# Native residual joining palettes: verification and preservation

**The exact frozen candidate passed the complete strict Lean verifier and the unchanged full axiom audit.**
The successful latest attempt is `full-04` in run `20261123T210325Z`.
This supplementary preservation report was recorded at `2026-11-23T21:48:10.053865+00:00`;
it does not replace the compiler or axiom audit.

## Exact comparison and provenance

| Reference | Commit |
| --- | --- |
| Actual preceding native-reserve verified commit, used for preservation | `b7be9966640e932ef7bbd030d3dae42f7bcb4638` |
| Earlier verified baseline retained in the source manifest | `98c6b228a997fead863d05041f12799c93fac18b` |
| Earlier native-reserve source-only checkpoint retained in the source manifest | `964027f1a74cd68149033dc74f87846cabdf2eae` |

The earlier source checkpoint and the actual preceding verified commit have
different roles. Every preservation comparison uses the actual preceding
verified commit supplied to this checker. The frozen source manifest keeps
its historical baseline and source-checkpoint fields unchanged.
Historical failure and probe metadata retain the native commit SHA actually
used at the time. Their recorded native commit must have the same complete
Git tree, prior verification results and root source bytes as the supplied
comparison commit; a later publication does not rewrite those historical IDs.

## Mathematical scope

Actual native residual joining-degree bounds; retained robustness chosen before requested surplus error; bounded matching palettes with exact original-copy coverage, per-class cut parity, whole-class footprint and vertex-load bounds; prescribed singleton primary joining copies and protected grouping. Supporting progress toward Corollary 4.6. Internal exceptional completion, final robust completion, full residual factorization and the main theorem remain incomplete.

The uniform parameter theorem chooses the surviving robustness `θ>0`, with
`θ≤σ`, before the requested surplus error `δ`. The actual residual joining
degree bounds use the original representative's assignment, preserve actual
parallel copies, and give the natural degree bound needed by the palette
construction. The prior completion theorem and all prior proof sources are
retained byte-for-byte.

The joining classes are actual matchings that are disjoint and cover all
joining copies exactly once. Their certificates retain per-class cut parity,
at most `3L` copies and `6L` support vertices per class, and at most `D`
classes meeting each vertex. The odd assigned-part case selects `⌊r/2⌋`
distinct surviving original reserve crossings. The composed protected-palette
theorem makes each selected crossing an entire singleton joining class under
its explicit margin `6D+⌊r/2⌋<h` and capacity
`nD≤2L(h-6D-⌊r/2⌋)`. Separate quantitative budget proofs supply positive
capacity and small whole-class footprints under their stated bounds.

These singleton joining classes are not yet complete reserved boundary color
classes. Internal exceptional incidences, the equal-free-palette construction
for an exceptional pair with arbitrary parallel copies, old-core uncovered
parity after that internal extension, robust perfect-matching completions,
and final factorization/reconstruction remain open. The full two-core
Corollary 4.6, full five-exception statement and main theorem remain incomplete.
**No numbered assertion is added: coverage remains 47/69, with 22 incomplete.**

| New module | Mapped public theorem proofs |
| --- | ---: |
| `Overfull.ResidualPalette.JoiningBounds` | 12 |
| `Overfull.ResidualPalette.JoiningGrouping` | 5 |
| `Overfull.ResidualPalette.NativeProtectedPalette` | 1 |
| `Overfull.ResidualPalette.NativeReservedCrossings` | 6 |
| `Overfull.ResidualPalette.PaletteBudget` | 8 |
| `Overfull.ResidualPalette.PaletteGrouping` | 20 |
| `Overfull.ResidualPalette.PaletteParity` | 5 |
| `Overfull.ResidualPalette.ProtectedBudget` | 5 |
| `Overfull.ResidualPalette.ProtectedGrouping` | 6 |
| `Overfull.ResidualPalette.ReservedPrimary` | 5 |
| `Overfull.ResidualPalette.UniformCompletion` | 1 |
| `Overfull.ResidualPalette.UniformJoining` | 1 |

The 12 new modules contain 75
mapped public theorem proofs and 168 audited
proof declarations including private and generated support. The full audit,
source manifest and declaration map agree on all of them.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Exit 0; all frozen inputs unchanged |
| Strict `lake build --wfail` | 3,719 jobs passed |
| Unchanged full `Audit.lean` | 12,559 declarations passed |
| Prior declarations, modules and axiom sets | All 12,391 preserved |
| Newly audited declarations | 168 |
| Prior nonroot Lean proof sources | 535 byte-identical |
| Previous declaration maps and metadata | All 10 unchanged |
| Previous source/provenance manifests and other preserved inputs | 80 byte-identical |
| Previous completed-result mappings | All 1,784 retained |
| Numbered assertion records | All 69 unchanged; all 47 completed records retained |
| Frozen sources and verification inputs | 635 exact SHA256 matches |
| Archived development files | All 163 exact SHA256 matches |
| Earlier full-03 observed snapshot | All 32 archived files retained exactly |
| Targeted import-order probe | All five generated declaration module labels restored |
| Earlier supplementary preservation failure | Original checker, command, output and five-label comparison retained |
| Historical verification/recovery paths | All 1232 byte-identical |

The stock audit is unchanged. The verifier differs only by the four recorded
additive residual-palette manifest and mapping edits; the proof root differs
only by five declared imports following the complete original import prefix.
Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Logical axioms remain limited
to `propext`, `Classical.choice`, and `Quot.sound`.
All previous verification inputs are byte-identical except the explicitly
updated README, continuation handoff and verifier; the latter is restricted
to its exact four additive edits. All prior source/provenance manifest JSON
files and earlier proof maps remain unchanged.

The actual raw axiom records and imported-module lists agree with the fresh
results. The latest console is exactly the concatenation of the four actual
stage logs and the final verifier summary. The `final/` directory contains
byte-for-byte copies of those logs, all latest declaration maps, results,
the frozen inputs, latest command/console and new source manifest. No earlier
verification output was replayed as a current result.

## Retained failures and development evidence

| Complete-verifier attempt | Recorded status | Exit code | Actual output |
| --- | --- | ---: | --- |
| `full-01` | failed | 1 | `verification/runs/20261123T210325Z/full-01/output.log` |
| `full-02` | failed | 1 | `verification/runs/20261123T210325Z/full-02/output.log` |
| `full-03` | passed | 0 | `verification/runs/20261123T210325Z/full-03/output.log` |
| `full-04` | passed | 0 | `verification/runs/20261123T210325Z/full-04/output.log` |

| Supplementary preservation attempt | Full verifier checked | Recorded status | Exit code | Actual output |
| --- | --- | --- | ---: | --- |
| `preservation-check-01` | `full-03` | failed | 1 | `verification/runs/20261123T210325Z/preservation-check-01/output.log` |

`full-01` genuinely failed because the source manifest had not been generated.
The initial manifest scanner confused a named Lean section with a namespace;
its exact failed script and observed error remain archived. `full-02`
genuinely failed because new root imports followed a non-import command.
Both attempts retain their original command metadata, frozen inputs, source
snapshots and failure logs; their inspected hashes are pinned by this checker.
The setup-path failure and successful targeted initial integration observation
also remain intact. The latter preserves its raw tool output without inventing
an unrecorded start time.

`full-03` passed the strict compiler build (3,719 jobs) and the full axiom audit
(12,559 declarations), with all 635 frozen inputs unchanged. Its subsequent
`preservation-check-01` failed because prepending the five new root imports
changed the recorded source-module labels of five generated declarations.
Every old declaration name and axiom set was retained, but the stronger
name/module/axiom preservation requirement was not satisfied. That requirement
is unchanged. The original failed checker, command metadata, actual error and
independently recomputed five-label difference are preserved alongside the
32-file snapshot of the observed full-03 state. This successful compiler and
axiom audit is recorded as historical evidence, not as the final preserved result.

The correction moves the five new imports after the original import prefix.
Removing them restores the exact original root bytes. A separately archived
strict targeted probe restored all five expected native module labels. Its
proposed root places one existing blank line differently from the actual
corrected root; their import sequences agree, and both reduce byte-for-byte
to the original root when the five additions are removed. The probe checks
module ownership only and does not replace the full audit. A later complete
verifier is required after that probe; `full-04` was the next planned attempt,
and the actual successful latest attempt used by this report is `full-04`.

There are 53 distinct retained full-verifier, development, targeted
probe and read-only historical-helper diagnostic command records: 31
successful, 22 failed, 0 interrupted,
and 0 incomplete. Separately, there are
1 retained supplementary preservation command records,
all failed, for 54 retained command records
in total. The supplementary failure is not mislabeled as a failed Lean audit.
The 1 read-only historical-helper diagnostics validate the
history-reading code; they do not execute the final checker or the full verifier
and supply no current full-verification claim.
Development commands establish
only their recorded targeted results; the latest full attempt supplies the
complete verification claim. Source snapshots and recorded output hashes
were checked. Recorded dependency hashes are retained as provenance; no
missing dependency snapshots or missing timing metadata are reconstructed.

## Publication and remaining work

Publication of this continuation to the authorized verified branches is
pending. This report makes no claim that those branch updates succeeded.
Publish the exact checked sources and genuine evidence, preserve concurrent
work, and record the actual resulting commit/tree identifiers after readback.

The continuation handoff identifies the next internal exceptional completion
and robust completion obligations. The protected joining palette is a proved
intermediate result under its explicit hypotheses, not a final factorization.
