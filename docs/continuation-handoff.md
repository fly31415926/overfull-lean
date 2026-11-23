# Continuation handoff: actual residual joining palettes

## Authoritative state

Fetch and inspect `main` and
`verified-bipartite-continuation-2026-11-21` in
`fly31415926/overfull-lean` before editing. Their newest verified commits
and actual run reports are authoritative. Both verified branches began this
continuation at `98c6b228a997fead863d05041f12799c93fac18b`. Newer native
reserve sources were saved at recovery checkpoint
`964027f1a74cd68149033dc74f87846cabdf2eae`; all 24 native module blobs matched
the observed local sources.

The interrupted native-reserve full audit was resumed as
`verification/runs/20261123T201422Z/full-04`. Its final actual records and
preservation report determine status. This palette continuation was developed
in a separate worktree, leaving those frozen source inputs unchanged.

New run: `20261123T210325Z`. Its folder contains genuine development
diagnostics, frozen full-check inputs, complete audit, preservation report
and publication evidence. A targeted compiler pass or source-only recovery
checkpoint is not a complete verification claim.

## Completed construction interfaces

The new sources are under `Overfull/ResidualPalette/`. All preceding nonroot
proof sources are preserved, including the native reserve modules.

- `exists_uniform_native_reserve_completion_parameters` fixes retained
  robustness `θ>0`, with `θ≤σ`, before every requested surplus error `δ>0`.
- `native_residual_joining_degree_bounds` gives joining degree at most
  `a` on old-core vertices and `h-r` on exceptions in the actual residual.
- `exists_uniform_native_reserve_completion_with_small_joining` constructs
  the original reserve and safe regular residual with retained robust cores,
  and natural `D=⌊max(a,h-r)⌋₊` satisfying the degree bound and `6D<h`.
- `AssignedParts.exists_assigned_joiningPalette_in_host` constructs actual
  matching classes covering every residual joining copy. It retains the
  original representative's assignment and proves exact coverage,
  disjointness, cut parity, whole-class size and vertex-load bounds.
- `assigned_joiningPalette_uncovered_even` gives even uncovered order in
  every assigned fiber for every whole palette class.
- `BoundaryPacking.exists_half_residual_crossing_reserve` selects exactly
  `r/2` surviving original reserve crossings when the assigned parts are odd.
- `exists_twoOddJoining_decomposition_with_reserved_primary` forces
  prescribed actual crossings into singleton primary pieces.
- `TwoOddJoiningDecomposition.exists_protected_palette` keeps those
  primaries as whole classes by excluding surplus pieces from their colors.
- `exists_native_protected_joiningPalette` composes the actual native
  reserve, forced primaries and protected grouping. It retains original
  reserve membership and gives an injective map from the selected `r/2`
  crossings to distinct singleton palette classes.

The original representative and reserve parent matchings need not survive
as perfect residual matchings. Parallel copies remain distinct. Selected
crossings may share vertices and receive different colors. Their singleton
classes are joining classes, not yet complete compressed reserve boundaries.

## Uniform whole-class budgets

For unprotected grouping the margin is `h-6D`; with `s` protected colors it
is `h-6D-s`. Choose the common natural capacity `L=(nD/2)/gap+1`. This
directly proves the input `nD≤2L*gap` for both parity cases.

`uniform_palette_budget` proves `6L≤εn` from `h≥αn/30`, `D≤δn`,
`δ≤α/360`, `δ≤εα/360`, and `n≥12/ε`.
`uniform_protected_palette_budget` supplies the protected counterpart for
`s≤h/2`, using `δ≤α/720` and `δ≤εα/720`. It proves the positive protected
gap; `6D<h` alone does not imply that gap. Robustness being chosen first
permits taking these errors from later packing tolerances. For a core of
order at least `cn`, use error `c ε_core` for a core-relative tolerance.

## Next obligations

1. Insert internal exceptional incidences into the palette classes. A
   selected protected color in the odd case contains just its reserved
   crossing, so the remaining copies of that actual compressed reserve
   boundary are a possible prescribed extension. Prove this extension,
   distinctness, and exact remaining-copy accounting.
2. In the all-even case, preserve sufficiently many empty joining colors
   for the crossing-free reserve boundaries. The current all-even palette
   theorem does not assert that extra protected-empty-color property.
3. For a two-vertex exceptional pair fiber, construct the exact equal-free-
   palette bijection and color its actual parallel copies. Whole-class
   parity supplies simultaneous covered/uncovered behavior of the pair,
   but it does not itself supply this coloring.
4. For exceptions assigned to old cores, assign every remaining internal
   incident copy to its required free color while avoiding existing core
   endpoint conflicts and respecting prescribed reserve classes.
5. After all assigned exceptions are covered in each color, derive even
   uncovered order on the old cores and the actual extended-boundary
   footprint/load bounds. Assigned-fiber parity alone is insufficient.
6. Apply the checked robust boundary/completion interfaces with all their
   hypotheses, construct the remaining perfect color classes, and restore
   the previously removed perfect matchings using disjoint palettes. A
   conditional implication assuming a residual coloring is not this step.

The selected half-reserve crossing alignment is now constructed. Do not
restart it or describe it as wholly unproved. Internal exceptional coverage
and final factorization remain distinct proof obligations.

**Coverage remains 47/69.** Full two-core Corollary 4.6 and the main theorem
remain incomplete. Full five-exception Corollary 4.5, general four-label
circuits, remaining terminal and Section 6 obligations, and structural or
critical-average-degree inputs remain separate. All 69 original assertion
records and statement hashes are unchanged.

## Verification and publication

Use Lean 4.24.0 and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Do not run `lake update`. Runtime:
`/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`.
Palette worktree: `/workspace/scratch/96ddfd820f7d/overfull-next`.
Scratch paths may disappear; published GitHub sources and genuine records
are the durable authority.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_residual_palette_manifest.py
python3 verification/runs/20261123T210325Z/run-verifier.py full-01
```

Use a new attempt directory for every rerun. `Audit.lean` stays byte-identical
and permits only `propext`, `Classical.choice`, and `Quot.sound`. The verifier
has four additive residual-palette source-map extensions and retains every
prior gate. Compare every prior declaration, module, axiom set, completed
mapping, assertion record, proof source and historical artifact against the
actual preceding verified checkpoint before publishing.

Every actual intermediate failure remains archived. Direct Lean checks use
`-DwarningAsError=true`; `--wfail` is a Lake build flag. Unsupported-option
and scratch module-path diagnostics are retained. The initial isolated
setup's missing local runner path is recorded and was corrected by copying
the existing runner from its observed absolute location.

Standing user authorization covers autonomous continuation/recovery and
publication of all project sources, documentation, mappings and genuine
logs. After the strict build, full unchanged audit, mappings and preservation
pass, publish the exact checked sources and evidence to both verified
branches, preserving concurrent work and using expected-head updates.
Read back both heads and the exact commit/tree. No repeat confirmation is
required. Failed or unfinished work belongs on a clearly identified attempt
branch with actual diagnostics and must not be promoted as verified.
