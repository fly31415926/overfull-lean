# Native terminal continuation: verification and preservation

**The exact frozen candidate passed the complete strict verifier and the unchanged full axiom audit.**
The latest successful attempt is `full-01` in run `20261124T021500Z`.
This supplementary report was recorded at `2026-11-24T02:43:27.673899+00:00`. It checks
consistency and preservation; it does not replace the Lean build or audit.

## Exact baseline and mathematical scope

The preceding verified local commit is `f557ae03355f14a0441b37283f35186a95aca2d7`, with tree
`efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d` and 4,321 files. Its committed result
contains 13,170 audited declarations and 2,176
completed-result mappings, all checked again here for exact preservation.
The preceding verified local chain has separate publication receipts. The
public heads most recently observed when this run was created were `0f168ca9f2f8a82b6c00e1a7633ec035985b7209` for `main` and
`0f168ca9f2f8a82b6c00e1a7633ec035985b7209` for the continuation branch.
Later publication receipts are separate from this local verification and
preservation report.

Complete Corollary 4.6 for even regular multigraphs with no overfull set and either one robust core with at most three exceptional vertices or two robust cores with at most two exceptional vertices. Fixed positive degree and core-order densities and robust parameters precede one common positive core-error tolerance and order threshold. The conclusion constructs a coloring and an exact partition of all original edge copies into k perfect matchings. No representative matching, reserve, complementary coloring or residual factorization is assumed. Full fixed-pattern Lemma 4.4, five-exception Corollary 4.5, terminal Proposition 4.16 and the main theorem remain unproved.

**Corollary 4.6 is now completely verified under both source alternatives.
48 of 69 numbered assertions are complete; 21 remain incomplete. The main
theorem, stronger five-exception Corollary 4.5 and general terminal assertions
remain unproved.**

| New module | Mapped public theorem proofs |
| --- | ---: |
| `Overfull.NativeTerminal.BoundedInput` | 2 |
| `Overfull.NativeTerminal.ColoringGlue` | 6 |
| `Overfull.NativeTerminal.Factorization` | 1 |
| `Overfull.NativeTerminal.NativeCompletion` | 1 |
| `Overfull.NativeTerminal.NativeFactorization` | 2 |
| `Overfull.NativeTerminal.NativeGeometry` | 10 |
| `Overfull.NativeTerminal.PairColoring` | 1 |
| `Overfull.NativeTerminal.PrefixGeometry` | 3 |
| `Overfull.NativeTerminal.Reassembly` | 11 |
| `Overfull.NativeTerminal.ReserveGeometry` | 15 |
| `Overfull.NativeTerminal.ResidualGeometry` | 12 |
| `Overfull.NativeTerminal.ShoreCore` | 16 |
| `Overfull.NativeTerminal.ShoreFactorization` | 3 |
| `Overfull.NativeTerminal.ShoreHost` | 8 |
| `Overfull.NativeTerminal.TerminalParameters` | 3 |
| `Overfull.NativeTerminal.TwoCore` | 2 |

The 16 new modules contain 96
mapped public theorem proofs and 196 audited
declarations including private and generated support. The exact sources,
lexically recomputed public inventory, declaration map and full audit agree.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Exit 0; frozen inputs unchanged |
| Strict `lake build --wfail` | 3,780 jobs passed |
| Unchanged full `Audit.lean` | 13,366 declarations passed |
| Prior declaration names, modules and axiom sets | All 13,170 preserved |
| Newly audited declarations | 196 |
| Prior nonroot mathematical sources, including audit | 592 byte-identical |
| Prior completed-result mappings | All 2,176 retained |
| Prior declaration maps and metadata | All 15 unchanged |
| Prior verification inputs outside the five allowed edited files | 98 byte-identical |
| Baseline files outside the explicit current-file allowance | 4,310 byte-identical |
| Historical verification/recovery paths | 3,619 byte-identical |
| Original assertion statement identities and hashes | All 69 unchanged |
| Other numbered assertion records | All 68 unchanged |
| Corollary 4.6 | Exact reviewed completion; both source alternatives |
| Frozen source/input hashes | 716 exact matches |
| Archived development files | 302 exact matches |

Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The only permitted logical axioms
are `propext`, `Classical.choice` and `Quot.sound`.

The proof root retains the complete original import prefix and adds only
the recorded contiguous new imports before the original documentation.
The verifier differs by exactly seven reviewed substitutions: four terminal
source/declaration registrations, the completed count 48, removal of only 4.6
from the incomplete list, and a positive gate tying its exact pinned statement
hash and complete public theorem names to the fresh full audit. Every other
preceding guard and every byte of the full stock `Audit.lean` are unchanged.

The coverage comparison allows precisely the recorded 4.6 completion, one
appended complete-result component, the total 48 and top-level scope prose.
All 68 other assertion records and all 69 original statement identities and
hashes are identical. The source excerpt is independently rehashed. The only
change in `docs/manuscript-source.json` is its completed count from 47 to 48;
every other parsed field remains exact. Old/new bytes and permitted changes
are recorded in `preservation.json`.

The actual raw axiom records and imported-module lists agree with current
results. The latest console is exactly the concatenation of the actual
four stage logs and final verifier summary. The `final/` directory contains
byte-identical copies of the current logs, results, declaration maps, frozen
inputs, command/console and new source manifest. Historical verification
logs have not been replayed as current verification.

## Retained actual diagnostics

| Full-verifier attempt | Recorded status | Exit code |
| --- | --- | ---: |
| `full-01` | passed | 0 |

The run retains 27 distinct recorded commands: 12
passed, 15 failed, 0 incomplete and
0 interrupted. Individual records, exact outputs
and available source snapshots are listed in `preservation.json`. Source
hashes or timings absent from an original command record are identified as
absent; the checker does not invent them. A targeted compiler pass establishes
only its own result; the latest complete verifier establishes the full audit.

## Publication and remaining work

This report establishes local verification and exact preservation only.
Publication is a separately authorized action with exact public-tree and branch
readback receipts. No public commit, tree availability or branch promotion is
inferred from a local check or unreferenced upload.
Any later publication must have its own exact tree and branch readback receipts.

The remaining native factorization obligations and the precise scope of the
new supporting constructions are recorded in `docs/continuation-handoff.md`
and the source-linked semantic review. The completed-numbered-assertion count
increases by exactly one, for the source-authenticated Corollary 4.6.
