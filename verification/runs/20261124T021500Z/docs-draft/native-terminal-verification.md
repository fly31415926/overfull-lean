# Native terminal construction: exact proof map and verification scope

This complete Corollary 4.6 continuation adds 16 source modules and
96 explicitly named public theorem/lemma proofs.
The exact manifest is `docs/native-terminal-source.json`. Its source hashes,
names and lines describe the candidate source; they do not certify a full run.

The unchanged full `Audit.lean` enumerates every proof declaration actually
imported, including private and generated support proofs. Its successful run
produces `verification/native-terminal-declarations.json`, which ties every
audited new declaration to the exact source path and hash. The current run's
genuine command receipt, full raw logs and `preservation.json` establish the full
verification and preservation state. No audited declaration count is inferred
from this lexical source map or from a focused compiler pass.

## Exact baseline and mathematical scope

The local verified baseline is `f557ae03355f14a0441b37283f35186a95aca2d7`, exact tree `efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d`: 4,321 committed
files, 13,170 audited declarations, 2,176 completed-result mappings and 696 frozen
source/input hashes. Every prior nonroot mathematical source, declaration
name/owner/axiom set and old declaration map are preserved. All 69 original
statement identities and hashes and all 68 other assertion records are exact.
The only promoted assertion is 4.6; one complete-result component is appended.
Root imports are appended after the full original prefix. The verifier permits
exactly seven reviewed substitutions, including a positive 4.6 identity/audit
gate and the completed count 48. All other guards and the full audit are unchanged.
The successful predecessor publication has separate exact tree and branch
readback receipts under this run.

Complete Corollary 4.6 for even regular multigraphs with no overfull set and either one robust core with at most three exceptional vertices or two robust cores with at most two exceptional vertices. Fixed positive degree and core-order densities and robust parameters precede one common positive core-error tolerance and order threshold. The conclusion constructs a coloring and an exact partition of all original edge copies into k perfect matchings. No representative matching, reserve, complementary coloring or residual factorization is assumed. Full fixed-pattern Lemma 4.4, five-exception Corollary 4.5, terminal Proposition 4.16 and the main theorem remain unproved.

**The candidate completes Corollary 4.6, with coverage 48/69. The main theorem
and 20 other numbered assertions remain incomplete.** The semantic review records
the precise conclusions and hypotheses rather than inferring mathematical scope
from a passing compiler command.

## Source modules

| Module | Mapped public theorem proofs |
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

## Complete explicit public proof inventory

### `Overfull.NativeTerminal.BoundedInput`

Source: `Overfull/NativeTerminal/BoundedInput.lean`. SHA-256: `feb995a3d83bcf5862502d1dafae2509368064a46b74a1d3a7895e147d7fbc20`.

- `Overfull.bounded_input_factorization` (source line 20).
- `Overfull.bounded_input_one_factorization` (source line 74).

### `Overfull.NativeTerminal.ColoringGlue`

Source: `Overfull/NativeTerminal/ColoringGlue.lean`. SHA-256: `9e1630206ec0b3b91ba9f80bdf558786d5cd83237b1fa30d4ee89db2a21e0437`.

- `Overfull.NativeTerminal.exists_glued_retained_coloring` (source line 21).
- `Overfull.NativeTerminal.boundary_of_two_retained` (source line 51).
- `Overfull.NativeTerminal.no_overlap_of_closed_shore` (source line 66).
- `Overfull.NativeTerminal.exists_glued_three_shore_coloring` (source line 76).
- `Overfull.NativeTerminal.exists_glued_closed_shores_coloring` (source line 123).
- `Overfull.NativeTerminal.exists_glued_contracted_shores_coloring` (source line 142).

### `Overfull.NativeTerminal.Factorization`

Source: `Overfull/NativeTerminal/Factorization.lean`. SHA-256: `ad4e6d1a9480e81b5555b29952f07f3c98e40ea475977b33bbb00abdc88fa2d0`.

- `Overfull.NativeTerminal.exists_uniform_two_shore_factorization` (source line 23).

### `Overfull.NativeTerminal.NativeCompletion`

Source: `Overfull/NativeTerminal/NativeCompletion.lean`. SHA-256: `e31750cc22797674da98987585df87e6cf11ea5eb561ea908a3a7b85f451d5c5`.

- `Overfull.NativeTerminal.exists_uniform_native_remaining_factorization` (source line 24).

### `Overfull.NativeTerminal.NativeFactorization`

Source: `Overfull/NativeTerminal/NativeFactorization.lean`. SHA-256: `fe133211b48696c8fc940e36e421e42d42f0c41d6c5fc61d67a03dca120f8583`.

- `Overfull.NativeTerminal.exists_uniform_native_image_factorization` (source line 20).
- `Overfull.NativeTerminal.exists_uniform_native_residual_factorization` (source line 76).

### `Overfull.NativeTerminal.NativeGeometry`

Source: `Overfull/NativeTerminal/NativeGeometry.lean`. SHA-256: `84fbd28c5ed999ec4679488760d64feff1e9861543dad4d98255bad82d3862d7`.

- `Overfull.NativeTerminal.first_assigned_cut_subset_external` (source line 28).
- `Overfull.NativeTerminal.second_assigned_cut_subset_external` (source line 36).
- `Overfull.NativeTerminal.pair_assigned_cut_subset_external` (source line 45).
- `Overfull.NativeTerminal.residual_first_cutSize` (source line 59).
- `Overfull.NativeTerminal.residual_shore_cuts_eq` (source line 66).
- `Overfull.NativeTerminal.residual_second_cutSize` (source line 76).
- `Overfull.NativeTerminal.residual_pair_cut_empty` (source line 87).
- `Overfull.NativeTerminal.residual_assigned_star_incidence` (source line 94).
- `Overfull.NativeTerminal.residual_assigned_exterior_independent` (source line 110).
- `Overfull.NativeTerminal.residual_geometry` (source line 122).

### `Overfull.NativeTerminal.PairColoring`

Source: `Overfull/NativeTerminal/PairColoring.lean`. SHA-256: `6f16b5a28677e04d86f2cc7c100b9a92f303095600916c315b91ca645578d52f`.

- `Overfull.NativeTerminal.retained_pair_colorable` (source line 21).

### `Overfull.NativeTerminal.PrefixGeometry`

Source: `Overfull/NativeTerminal/PrefixGeometry.lean`. SHA-256: `022233b05fa156d5acea17a23f43d595d435f34ca03cc821018df440afaa8149`.

- `Overfull.NativeTerminal.externalCopies_eq_joining_exceptional` (source line 23).
- `Overfull.NativeTerminal.externalCopies_residual` (source line 64).
- `Overfull.NativeTerminal.twiceResidual_external_image` (source line 85).

### `Overfull.NativeTerminal.Reassembly`

Source: `Overfull/NativeTerminal/Reassembly.lean`. SHA-256: `5bcfbdcb465a8c8af0756fa5d61421821464a17e2a800edd7f84406821be5250`.

- `Overfull.NativeTerminal.prefixLabel_injective` (source line 27).
- `Overfull.NativeTerminal.residualLabel_injective` (source line 32).
- `Overfull.NativeTerminal.prefixLabel_ne_residualLabel` (source line 39).
- `Overfull.NativeTerminal.prefixIndex_mem` (source line 51).
- `Overfull.NativeTerminal.prefixIndex_eq` (source line 55).
- `Overfull.NativeTerminal.reassembledColoring_prefix` (source line 94).
- `Overfull.NativeTerminal.reassembledColoring_residual` (source line 105).
- `Overfull.NativeTerminal.reassembledColorClass_prefix` (source line 115).
- `Overfull.NativeTerminal.reassembledColorClass_residual` (source line 136).
- `Overfull.NativeTerminal.exists_reassembled_coloring` (source line 158).
- `Overfull.NativeTerminal.exists_reassembled_one_factorization` (source line 176).

### `Overfull.NativeTerminal.ReserveGeometry`

Source: `Overfull/NativeTerminal/ReserveGeometry.lean`. SHA-256: `78a74c4ce651d4920cfbd107f900b9de408c5c347b04edf3a1144b971f8d8954`.

- `Overfull.NativeTerminal.corePart_sdiff_subset_exceptions` (source line 24).
- `Overfull.NativeTerminal.corePart_sdiff_card_le` (source line 33).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_assigned_parts` (source line 48).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_first_cut` (source line 58).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_shore_cuts_eq` (source line 66).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_pair_cut` (source line 74).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_first_cut_card` (source line 80).
- `Overfull.NativeTerminal.BoundaryPacking.boundary_otherEnd_mem_core` (source line 88).
- `Overfull.NativeTerminal.BoundaryPacking.mem_selectedUnion` (source line 109).
- `Overfull.NativeTerminal.BoundaryPacking.selectedUnion_cut` (source line 114).
- `Overfull.NativeTerminal.BoundaryPacking.selected_cuts_disjoint` (source line 127).
- `Overfull.NativeTerminal.BoundaryPacking.selectedUnion_first_cut_card` (source line 139).
- `Overfull.NativeTerminal.BoundaryPacking.selectedUnion_shore_cuts_eq` (source line 150).
- `Overfull.NativeTerminal.BoundaryPacking.selectedUnion_pair_cut` (source line 157).
- `Overfull.NativeTerminal.BoundaryPacking.selectedUnion_otherEnd_mem_core` (source line 167).

### `Overfull.NativeTerminal.ResidualGeometry`

Source: `Overfull/NativeTerminal/ResidualGeometry.lean`. SHA-256: `5c2ec18f8955d78ab8c4136ab7fd6350f62ff331a1a4e299c24d5600bb5b78e9`.

- `Overfull.NativeTerminal.CopyEmbedding.firstEnd` (source line 29).
- `Overfull.NativeTerminal.CopyEmbedding.secondEnd` (source line 33).
- `Overfull.NativeTerminal.CopyEmbedding.otherEnd` (source line 37).
- `Overfull.NativeTerminal.CopyEmbedding.incident` (source line 40).
- `Overfull.NativeTerminal.mem_externalCopies` (source line 52).
- `Overfull.NativeTerminal.CopyEmbedding.mem_cut_iff` (source line 61).
- `Overfull.NativeTerminal.CopyEmbedding.mem_external_iff` (source line 65).
- `Overfull.NativeTerminal.CopyEmbedding.cut_image_of_external_image` (source line 70).
- `Overfull.NativeTerminal.CopyEmbedding.cutSize_of_external_image` (source line 91).
- `Overfull.NativeTerminal.CopyEmbedding.cut_empty_of_external_image` (source line 100).
- `Overfull.NativeTerminal.whole_shore_cut_subset_external` (source line 111).
- `Overfull.NativeTerminal.external_of_incident_outside` (source line 129).

### `Overfull.NativeTerminal.ShoreCore`

Source: `Overfull/NativeTerminal/ShoreCore.lean`. SHA-256: `ea772797df6982976c25e0e7ea315fb15c30421afc4424ecb06efe183c5fd8b4`.

- `Overfull.NativeTerminal.inducedCoreEquiv_val` (source line 26).
- `Overfull.NativeTerminal.inducedCoreEquiv_symm_val` (source line 29).
- `Overfull.NativeTerminal.inducedCoreEdgeMap_val` (source line 44).
- `Overfull.NativeTerminal.inducedCore_degree` (source line 62).
- `Overfull.NativeTerminal.inducedCore_robust` (source line 68).
- `Overfull.NativeTerminal.inl_mem_contractedCoreVertices` (source line 77).
- `Overfull.NativeTerminal.apex_not_mem_contractedCoreVertices` (source line 81).
- `Overfull.NativeTerminal.vertexMap_mem_contractedCoreVertices` (source line 85).
- `Overfull.NativeTerminal.contractedCoreVertices_card` (source line 89).
- `Overfull.NativeTerminal.contractedCoreVertices_compl_card` (source line 94).
- `Overfull.NativeTerminal.contractedCoreEquiv_apply_val` (source line 114).
- `Overfull.NativeTerminal.contractedCoreEquiv_symm_map` (source line 117).
- `Overfull.NativeTerminal.contractedCoreEdgeMap_val` (source line 134).
- `Overfull.NativeTerminal.contractedCore_degree` (source line 153).
- `Overfull.NativeTerminal.contractedCore_robust` (source line 160).
- `Overfull.NativeTerminal.contractedHost_independent_exterior` (source line 167).

### `Overfull.NativeTerminal.ShoreFactorization`

Source: `Overfull/NativeTerminal/ShoreFactorization.lean`. SHA-256: `349ad511138f99647bee467e4601e569f3941637e241e14b3a8593b210a2dc06`.

- `Overfull.NativeTerminal.shore_geometry_of_star_incidence` (source line 27).
- `Overfull.NativeTerminal.exists_uniform_shore_coloring` (source line 53).
- `Overfull.NativeTerminal.exists_uniform_shore_coloring_of_star_incidence` (source line 119).

### `Overfull.NativeTerminal.ShoreHost`

Source: `Overfull/NativeTerminal/ShoreHost.lean`. SHA-256: `7166fce2560f38c4f1dc556d96aa88d6e40a976d5130bbc4213ccd5c0fb5279b`.

- `Overfull.NativeTerminal.inducedHost_incident` (source line 30).
- `Overfull.NativeTerminal.inducedHost_edge_map` (source line 37).
- `Overfull.NativeTerminal.internal_of_incident_of_cut_empty` (source line 42).
- `Overfull.NativeTerminal.inducedHost_degree_of_cut_empty` (source line 65).
- `Overfull.NativeTerminal.inducedHost_regular` (source line 71).
- `Overfull.NativeTerminal.inducedCoreVertices_card` (source line 117).
- `Overfull.NativeTerminal.inducedCoreVertices_compl_card` (source line 121).
- `Overfull.NativeTerminal.inducedHost_independent_exterior` (source line 124).

### `Overfull.NativeTerminal.TerminalParameters`

Source: `Overfull/NativeTerminal/TerminalParameters.lean`. SHA-256: `9566212de0baa3de831709cc1579cdbb679eceb8a4d933b157a15bb38c8896bb`.

- `Overfull.NativeTerminal.terminal_robust_range` (source line 17).
- `Overfull.NativeTerminal.terminal_core_error` (source line 26).
- `Overfull.NativeTerminal.exists_uniform_terminal_parameters` (source line 35).

### `Overfull.NativeTerminal.TwoCore`

Source: `Overfull/NativeTerminal/TwoCore.lean`. SHA-256: `a07e1b9d6e4a9107db7d75ad369199021bd957c07b05722faa1ddb1d5e77e12a`.

- `Overfull.two_core_two_exception_factorization` (source line 23).
- `Overfull.two_core_two_exception_one_factorization` (source line 89).

## Required complete verification

The full command is `python3 scripts/verify.py`, running strict
`lake build --wfail` and the unchanged complete `lake env lean Audit.lean`
under Lean 4.24.0 and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted logical axioms.

Every genuine focused attempt retains its command, actual exit, source hashes,
available input snapshots and complete log. Each complete attempt is immutable,
with all frozen input bytes, fresh output copies and exact raw audit segments.
The attached supervisor observes its real child process through terminal exit.
The separate preservation checker rechecks all old evidence, sources, mappings,
assertion records and new source-to-declaration maps before emitting success.
