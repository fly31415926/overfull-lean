# Proof map: three-core terminal continuation

The exact source hashes and public theorem inventories are generated in
`three-core-terminal-source.json`. The full verifier writes
`verification/three-core-terminal-declarations.json` from the actual unchanged
axiom audit, including every private and generated proof in the new modules.
The semantic scope is described in `three-core-terminal-semantic-review.md`.

## Public conclusions

| Declaration | Conclusion |
| --- | --- |
| `Overfull.three_core_terminal_factorization` | Original-host edge-coloring with the degree palette, under uniform three-core terminal hypotheses |
| `Overfull.three_core_terminal_one_factorization` | Exactly the degree number of disjoint perfect matchings covering all original edge copies |

Both declarations choose the error tolerance and order threshold before the
host, the core parts and graphs, the degree and the core error. Neither assumes
any final or residual coloring. This proves a subcase of Proposition 4.16;
**numbered coverage remains 48/69 and the main theorem remains unproved**.

## Source modules and proof roles

| Module under `Overfull.Terminal` | Proof obligation |
| --- | --- |
| `PartLabels` | Actual labels for the three covering parts; parity and exact joining-cut identity |
| `ParityCases` | Explicit even and odd indices and preserved cover after reordering |
| `Palette` | Even and selected two-odd palettes with exact original-copy coverage |
| `Parameters` | Uniform numerical capacity, footprint, horizon and error bounds |
| `PrefixCompletion` | Actual perfect-matching completion and exact joining copies removed |
| `PrefixResult` | Constructed prefix record and original-copy survival |
| `Prefix` | Uniform prefix from the original host, with robustness fixed before requested residual tolerance |
| `SimpleBridge` | Surviving-copy equivalence and exact simple deletion identities |
| `ResidualPools` | Matching, disjointness, cut counts, supports and unions transported to actual residual copies |
| `CoreBridge` | Embedded residual cores with robustness and correctly cast degree bounds |
| `RemainingProfile` | Empty joining set or exactly the residual degree number of singleton-cut primary matchings |
| `ClosedCores` | Uniform original-copy coloring of closed even components |
| `Contraction` | Exact simultaneous two-apex graph, incidence, degree and robust-core transport |
| `CentralCuts` | No-overfullness from robust small-cut classification and actual exterior matchings |
| `CentralFactorization` | Uniform application of complete bounded-input Corollary 4.6 |
| `CentralMatchings` | Primary matching preservation, central coverage and original-copy boundary labels |
| `OddGluing` | Both leaf boundary extensions and compatible three-shore gluing |
| `OddFactorization` | Uniform construction of the full two-odd residual coloring |
| `Reassembly` | Exact prefix and residual color classes and restoration to original copies |
| `CompletedFactorization` | Both residual parity cases and restoration under one common tolerance |
| `ThreeCore` | Public original-host coloring and one-factorization theorems |

## Verification and preservation

The run directory is `verification/runs/20261124T032118Z/`. Each focused
command retains its genuine exit status, output, source snapshots, dependency
hashes and any observed concurrent source changes. Failed development attempts
remain in the archive. A focused pass is not a substitute for the full audit.

After sources and documentation stabilize, the full runner freezes every
mathematical source and verifier input, retains every input byte, invokes
`python3 scripts/verify.py`, and records the actual process exit. The attached
supervisor records live observations and a terminal receipt. The runner checks
that the frozen candidate did not change during execution and preserves the
complete actual logs, output maps and raw audit segments.

The supplementary preservation checker compares the result with published
baseline `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`. Its successful report can
be written only after the actual complete verifier succeeds. All 69 assertion
records and statement identities, the 48-complete assertion list, and the
manuscript source metadata must be identical to that baseline. The only coverage
addition is a source-linked supporting component for the three-core subcase.
Publication requires separate exact Git-tree and branch readbacks.
