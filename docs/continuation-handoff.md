# Continuation handoff: exceptional pair and reserve palette extensions

## Authoritative state and publication

Fetch and inspect `main` and `verified-bipartite-continuation-2026-11-21`
in `fly31415926/overfull-lean` before editing. At the start of this run
both still pointed to `98c6b228a997fead863d05041f12799c93fac18b`.

The preceding complete local verified candidate is
`1b5663a8fb472e42e698f4e09fcfc55497393815`, tree
`ab2dd45502da57ea7dfb1db046a9efc9ab0cf067`, with 2,196 files. Its parent
is the native-reserve verified checkpoint
`b7be9966640e932ef7bbd030d3dae42f7bcb4638`, tree
`7b7c84d18ee0f7826e87829de5d175fd6eea7ff6`. The public source-only recovery
checkpoint `964027f1a74cd68149033dc74f87846cabdf2eae` omits the later full
evidence and must not be promoted as the completed result.

This run independently checked the previous candidate's 635 frozen hashes,
all 2,196 file blobs, complete 12,559-declaration audit, and preservation of
12,391 preceding declarations. The connected GitHub integration uploaded
some objects but automatic approval review blocked the historical-evidence
batch. Neither verified branch advanced. An uploaded object is not a
published checkpoint. See this run's `publication-blocked.json`.

The user has repeatedly authorized publication of all sources,
documentation, mappings and genuine logs to this public repository. The
first rejected manifest was retried only after recovering explicit prior
authorization and verifying its source hashes against already-public
sources; that retry succeeded. A subsequent historical-evidence batch
was rejected again, so that operation was stopped. Do not bypass an
approval rejection or claim branch advancement without readback.

New local run: `20261123T221916Z`. It starts from the exact complete local
candidate above in a separate worktree. Its actual full command, frozen
inputs, logs and preservation report determine current local status.
Preserve this work and any concurrent remote changes when resuming.

## New constructions

Sources are under `Overfull/ExceptionalPalette/`. The exact source manifest
lists all public proof names and module hashes. The full axiom audit also
includes private and generated support. Every preceding nonroot proof
source remains byte-identical.

- **All-even reserve colors:** construct joining classes using the
  complement of any prescribed palette set Q, leaving those labels empty.
  Exact original-copy coverage, matching, disjointness, parity, size and
  vertex load are retained. The margin is `6D+|Q|<h`, with capacity
  `nD<=2L(h-6D-|Q|)`. Uniform wrappers give whole-class support at most
  epsilon times the host order, using the existing protected budget.
- **Actual exceptional pair:** derive equal free palettes from whole-class
  even cut parity and derive the exact number of internal parallel copies
  from degree h and joining coverage. Extend an injective prescription to
  all actual pair copies. Both exceptional vertices are covered in every
  color; fiber cuts and other vertex supports are unchanged. Each class
  gains at most one copy and two support vertices. The actual assigned-pair
  wrapper identifies the source fiber before applying the construction.
- **Full reserve boundaries:** transport original reserved copies into the
  actual residual subtype and retain their original indices. Replace
  protected joining classes by the full boundaries with those exact
  joining portions. Prove matching, disjointness, joining portion and cut
  identities, exact additional-copy accounting, whole-class bounds, and
  the actual vertex-load equation. Native odd/even wrappers establish
  source-level survival, alignment, exceptional coverage and even
  uncovered old-core orders in the protected colors.

The preceding native selection, reserve completion, residual no-overfull
safety, uniform retained robustness, joining grouping and half-reserve
crossing alignment are already proved. Do not restart those stages.

## Next mathematical obligations

The optional pair fiber and exceptional vertices assigned into old cores
are different cases. For the latter, construct a proper assignment of
all internal incident copies to remaining free colors while retaining
selected reserve prescriptions. Keep every parallel copy distinct.
Unweighted footprint/load estimates alone do not establish all required
color availability: multiplying whole-class support by the largest
parallel multiplicity can exceed the available palette. Derive adequate
weighted compatibility or prove a valid recoloring construction.

Compose coverage of assigned exceptions with assigned-fiber parity to
obtain even uncovered order on each old core in every remaining color.
Retain actual whole-class footprint and core-vertex-load bounds after
these additions. Then apply the proved robust completion interfaces with
all hypotheses established, construct the remaining perfect color classes,
and restore the removed perfect matchings using disjoint palettes.
A conditional statement assuming a residual coloring is insufficient.

Where both pair coloring and reserve insertion apply, compose their exact
prescription interfaces explicitly; separate existence statements do not
by themselves assert a full global factorization.

**Coverage remains 47/69.** Full two-core Corollary 4.6, full five-exception
Corollary 4.5, general four-label circuit obligations, remaining terminal
and Section 6 obligations, structural/critical-average-degree inputs, and
the main theorem remain open. All 69 statement records and hashes are
unchanged. Only the top-level coverage summary is corrected to describe
later supporting constructions accurately.

## Verification

Use Lean 4.24.0 and mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; do not run `lake update`.
Runtime: `/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`.
Worktree: `/workspace/scratch/0f64d20031b0/overfull-next`.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_exceptional_palette_manifest.py
python3 verification/runs/20261123T221916Z/run-verifier.py full-NN
python3 verification/runs/20261123T221916Z/record-final.py
```

Use a fresh attempt name. `Audit.lean` remains unchanged and allows only
`propext`, `Classical.choice`, and `Quot.sound`. The verifier adds exactly
four exceptional-palette source-map extensions and preserves all previous
gates. Append new root imports after the complete old import prefix, before
the first non-import command, to preserve generated-declaration ownership.

The supplementary checker compares preceding declaration names, modules,
axiom sets, completed-result mappings, nonroot sources, source/provenance
manifests, old proof maps and historical evidence with the actual preceding
verified local commit. It also checks raw audit records, source maps,
frozen hashes, command statuses, actual logs and development archives.
Do not replay historical output as a current check. Keep every genuine
failed or unfinished attempt with its actual status and diagnostics.

Publication is separate from local verification. When an authorized upload
is accepted, preserve the exact checked sources and complete evidence,
use expected-head branch updates, and read back both branch heads and the
uploaded commit/tree. Do not promote an incomplete attempt as verified.
