# Three-core terminal continuation: verification and preservation

**The exact frozen candidate passed the complete strict verifier and the unchanged full axiom audit.**
The latest full attempt is `full-01` in run `20261124T032118Z`. Its
attached supervisor observed the actual runner exit zero. This supplementary
report was recorded at `2026-11-24T03:56:33.830246+00:00` and checks consistency and
preservation; it does not replace the Lean build or the full audit.

## Exact baseline and mathematical scope

The preceding published verified commit is `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`, tree
`5d031253d02d0d0878422f8fbc367f04b812450c`, with 5,478 files. Its committed result
contains 13,366 audited declarations and 2,272
completed-result mappings. All their names, modules, axiom sets and mappings
are preserved. The baseline public heads recorded at run creation were
`0cf1c68c4daaeec9b879a03f1871eb64a0fa9640` for `main` and
`0cf1c68c4daaeec9b879a03f1871eb64a0fa9640` for the continuation branch.

Uniform terminal factorization for a simple regular graph of even order with no overfull set and exactly three disjoint covering robust core parts. Fixed positive ambient degree and part-order densities and robust parameters precede a common positive core-error tolerance and order threshold. Joining palettes, completed perfect-matching prefixes, residual cores, the simultaneous contraction of the two odd parts, and compatible leaf colorings are constructed from the original host hypotheses. The conclusion is a coloring and an exact partition of all original edge copies into the degree number of perfect matchings. This proves only the three-core subcase of Proposition 4.16; the four-core cases, full Proposition 4.16, and the main theorem remain unproved. Numbered coverage stays 48 of 69.

**Numbered coverage remains 48 of 69, with 21 assertions incomplete. All 69
original assertion records, including all 48 completed records, are unchanged.
This run proves the exactly-three-core subcase; full Proposition 4.16, its
four-core cases, and the main theorem remain unverified.**

| New module | Mapped public theorem proofs |
| --- | ---: |
| `Overfull.Terminal.CentralCuts` | 5 |
| `Overfull.Terminal.CentralFactorization` | 1 |
| `Overfull.Terminal.CentralMatchings` | 6 |
| `Overfull.Terminal.ClosedCores` | 3 |
| `Overfull.Terminal.CompletedFactorization` | 1 |
| `Overfull.Terminal.Contraction` | 29 |
| `Overfull.Terminal.CoreBridge` | 4 |
| `Overfull.Terminal.OddFactorization` | 1 |
| `Overfull.Terminal.OddGluing` | 1 |
| `Overfull.Terminal.Palette` | 6 |
| `Overfull.Terminal.Parameters` | 1 |
| `Overfull.Terminal.ParityCases` | 3 |
| `Overfull.Terminal.PartLabels` | 8 |
| `Overfull.Terminal.Prefix` | 1 |
| `Overfull.Terminal.PrefixCompletion` | 7 |
| `Overfull.Terminal.PrefixResult` | 1 |
| `Overfull.Terminal.Reassembly` | 8 |
| `Overfull.Terminal.RemainingProfile` | 3 |
| `Overfull.Terminal.ResidualPools` | 15 |
| `Overfull.Terminal.SimpleBridge` | 18 |
| `Overfull.Terminal.ThreeCore` | 2 |

The 21 new modules contain 124
mapped public theorem proofs and 309 audited
declarations including private and generated support. The source hashes,
recomputed public inventory, declaration map and full audit agree.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Actual exit 0; frozen sources and controls unchanged |
| Attached supervisor | Actual child exit 0 observed and retained |
| Strict `lake build --wfail` | 3,801 jobs passed |
| Unchanged full `Audit.lean` | 13,675 declarations passed |
| Prior declaration names, modules and axiom sets | All 13,366 preserved |
| Newly audited declarations | 309 |
| Prior nonroot mathematical sources, including audit | 608 byte-identical |
| Prior completed-result mappings | All 2,272 retained |
| Prior declaration maps and metadata | All 16 unchanged |
| Prior verification inputs outside the four allowed edited files | 103 byte-identical |
| Baseline files outside the explicit current-file allowance | 5,468 byte-identical |
| Historical verification/recovery files | 4,756 byte-identical |
| Original numbered assertion records | All 69 unchanged |
| Completed numbered assertion records | All 48 unchanged |
| `docs/manuscript-source.json` | Byte-identical |
| Frozen source/input hashes | 741 exact matches |
| Archived development files | 547 exact matches |

Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The only permitted logical axioms
are `propext`, `Classical.choice` and `Quot.sound`.

The proof root retains its complete original import prefix and adds only
the recorded contiguous new imports before the original documentation.
The verifier differs by exactly four reviewed additive substitutions:
new source/declaration registrations and an explicit scope gate for the
source-linked three-core subcase. Every preceding verifier guard and every
byte of the full stock `Audit.lean` remain unchanged.

Coverage permits only top-level scope prose and one appended
`three_core_terminal` supporting component. All earlier component catalog
entries and every numbered assertion record are identical. The original
Proposition 4.16 statement hash remains pinned, its full-assertion flag stays
false, and the manuscript-source manifest is byte-identical.

The actual raw axiom records and imported-module lists agree with current
results. The latest console equals the exact concatenation of its four
actual stage logs and final summary. The `final/` directory retains exact
copies of the current logs, results, declaration maps, frozen-input manifest,
command, console and new source manifest. Every full attempt also retains
all input bytes, control-script bytes, its actual outputs and exact contiguous
raw audit segments. Earlier failures remain genuine failed records.

## Retained actual diagnostics

| Full-verifier attempt | Recorded status | Exit code |
| --- | --- | ---: |
| `full-01` | passed | 0 |

The run retains 36 distinct full-verifier, development and
supplementary command records: 12 passed,
24 failed, 0 incomplete and
0 interrupted. Supervisor observations and runner
outputs are additionally retained for 1 attached invocations,
including any preflight failures. Missing original timings or source metadata
are identified as missing and are never reconstructed. Concurrent edits in
focused development are reported by their original receipts; only the final
frozen full verifier establishes the complete candidate result.

## Publication and remaining work

This report establishes local verification and exact preservation. Any later
publication has separate exact-tree and branch-readback receipts; it is not
inferred from a local result or an unreferenced upload. The remaining four-core
terminal obligations and their precise scope are recorded in
`docs/continuation-handoff.md` and the source-linked semantic review.
No numbered assertion is promoted in this run.
