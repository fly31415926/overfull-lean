# Continuation handoff: native two-core assignment patterns

## Resume from the authoritative remote

Fetch and inspect both `main` and
`verified-bipartite-continuation-2026-11-21` in `fly31415926/overfull-lean`
before editing. At this run's start both branches pointed to
`ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6`, tree
`8e59576eb2b94c02b6b1072c4afaf29543540db6`, with 751 tracked files.
The newest remote heads and their current run reports supersede this
baseline; do not restart from the earlier reconstruction checkpoints.

Current run: `20261123T113235Z`, started 2026-11-23 11:32:35 UTC.
The early source-only checkpoint is
`95be6df3e3d4a43fca9393210942b912f4252b58` on
`continuation-attempt/20261123T113235Z`. It predates the complete new
construction and fresh full verification. Later commits on that branch
and the verified branches take precedence. Exact command records, source
snapshots, final preservation checks and reports are in this run folder.
Only a successful complete verifier for the exact current source/input
hashes permits a new source checkpoint on the two verified branches.

No source reconstruction was required for this run. The original
`cb05ef5` reconstruction and later lost-draft records remain historical.
The current work starts from the exact published `ec25857` sources.

## Completed native interfaces

The eight new modules under `Overfull/AssignedParts/` are:

| Module | Role |
| --- | --- |
| `NativeWeights` | Native scaled marginals, exact pool expectations, selected-copy capacities and weighted pigeonhole. |
| `Signatures` | An actual matching signature in `Option (↥Z → Fin 2)`, constant assigned parts and crossing parity, at most five codes. |
| `SignaturePools` | Actual-copy usage of the internal pair, exceptional-to-core and old-core crossing pools. |
| `HeavySignature` | A heavy actual representative with weight at least `k/5` and linear forced pool supplies; exact internal-pair weight. |
| `ExactPoolWeights` | Exact total signature weight for an exceptional-to-core assignment equals its original copy-pool cardinality. |
| `BoundaryCompression` | Retains all exceptional matching copies and zero or one actual crossing copy, with size and assignment preservation. |
| `CompressionCuts` | Exact original/compressed cut splits, preserved cut parity and even uncovered order in both old cores. |
| `NativePatternConstruction` | Composition retaining one representative and exact alignment of the compressed crossing statistic. |

Key declarations in `Overfull.AssignedParts`:

```lean
coarseSignature
assignedParts_eq_of_signature_eq
card_assignmentSignature_le_five
exists_heavy_signature_with_pools
signatureWeight_none_eq_internalPool
signature_assignment_weight_eq_pool
compressedBoundary
compressedBoundary_internalOn
compressedBoundary_assignedLabel
compressedBoundary_uncovered_even
compressedBoundary_coarseSignature
compressedBoundary_coreCrossing_card
compressedBoundary_crossing_card_eq_of_signature_eq
exists_compressed_assignment_with_linear_pools
```

The finite host result assumes positive regular degree, no overfull set,
a disjoint covering pair of old cores and at most two exceptional vertices.
It constructs an actual perfect matching and its actual compressed boundary.
The compression has at most `|Z|+1` copies, retains every exceptional copy,
keeps the selected internal exceptional pair exactly, leaves even uncovered
order in each old core, and preserves the representative's assignment.
The retained old-core crossing count is exactly its original crossing
parity and is constant for a fixed signature.

The paired code is retained even with arbitrary parallel multiplicity.
Its weight equals the number of original internal exceptional copies.
For each exception and either original core, the sum of weights of the
signatures assigning it there equals the corresponding copy-pool size.
Each pool forced by a heavy signature has size at least `k/5`.
These are original-host copy counts, not distinct-neighbor bounds or
surviving reserve guarantees.

The compression itself permits any exceptional-set size. The five-code
bound and the identification of `none` with one pair require `|Z|≤2`.
Full Corollary 4.5 still permits five exceptions; do not silently replace
that source condition. The separate general simple-host `Encodes` relation
has not been identified with this native code.

See `docs/native-pattern-verification.md`, its semantic review and source
manifest. Actual compiler and stock-audit records determine verification;
a source manifest or semantic review alone does not.

## Exact next obligation

Proceed to **native reserve realization and residual safety** for the
original two-core branch of Corollary 4.6. The previous handoff's native
weight, coarse-signature, pool-usage and small boundary bridge has now been
implemented. Do not repeat that bridge or reapply the simple-host shortcut
that an exceptional endpoint pair has weight at most one.

1. Choose numerical multiplicities for the native signatures, retaining
   the heavy signature's reserve and its possible internal exceptional
   pair. The graph-independent rounding identities in
   `CircuitPatterns/Rounding.lean` are available; its simple-host selection
   structure and no-internal-pair fields are not directly applicable.
2. Realize those multiplicities by pairwise disjoint actual boundary
   matchings with the required incidence and reserve budgets. The new
   exact pool weight identities supply counts, but do not by themselves
   guarantee simultaneously compatible choices.
3. Complete the selected boundaries in the actual robust cores, accounting
   for earlier deletions and preserving the prescribed copies and labels.
   The original uniform error and order parameters must precede the host.
4. Prove regularity and absence of overfull sets for the actual residual.
   Native `SmallCuts` and exact selected/residual cut formulas are already
   available. Regularity after perfect-matching deletion alone does not
   imply odd-cut safety.
5. Apply the existing assigned-part and joining decomposition to that
   verified residual, then construct palette grouping, regular auxiliary
   graphs, robust completions and the final factorization reconstruction.

The previously checked
`assignedLabel_joining_decomposition_in_host` uses the original
representative's assignment in another host on the same vertices. It does
not require the representative to survive deletion. Its residual regularity
and no-overfull hypotheses still need to be proved at the reserve stage.

**47/69 numbered assertions remain complete; full Corollary 4.6 and the
main theorem remain unproved.** The general fixed-pattern and five-exception
statements, remaining terminal factorization, Section 6 setup/absorber,
general four-label circuits and structural/critical-average-degree inputs
remain separate obligations. Original authorized source excerpts remain
in `verification/runs/20261122T235931Z/`.

## Reproduce, preserve and publish

Use the pinned Lean 4.24.0 and dependency manifest, with mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Do not run `lake update`.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_native_pattern_manifest.py
python3 scripts/verify.py
```

The stock `Audit.lean` remains byte-identical and audits every imported
project declaration, including generated and private proofs. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. The verifier
retains every prior gate and adds exact hash/public-name/module checks
for the native-pattern manifest. Preserve every old proof source,
all 69 assertion records, all prior completed results and genuine logs.

This run used an isolated checkout at
`/workspace/scratch/d5dce0496f02/overfull-lean` and Lean at
`/workspace/scratch/4ffd54dab476/lean-runtime/lean-4.24.0-linux/bin`.
Temporary workspaces can disappear; recover from GitHub when necessary.
The restored ProofWidgets checkout initially lacked upstream release tags;
fetching them preserved its pinned revision and allowed the normal cache
setup. A cache download hit HTTP 429; retrying with three concurrent
transfers succeeded. All setup failures and genuine proof attempts are
preserved. No dependency source or verifier gate was weakened.

Native git fetch works; push had no transport credential in this environment.
The connected GitHub Git Data API can publish source blobs, exact trees and
commits. Compare every published tree with the local tree, fetch fresh
branch heads before updating, preserve concurrent work, and use expected
heads when advancing both verified branches. Read back the final commit,
tree and both heads. Exclude caches, binaries, credentials and unrelated
files. Existing user authorization covers publishing all project sources,
documentation, mappings and genuine verification logs; no repeat approval
is required.
