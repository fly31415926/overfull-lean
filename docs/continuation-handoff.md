# Continuation handoff: original-host joining decompositions

## Authoritative state and scope

Fetch the newest remote `main` and
`verified-bipartite-continuation-2026-11-21` in `fly31415926/overfull-lean`
before editing. Verified publications keep both branches at the same
commit. This round began from `5f46a36d87f9ca1cee382f46687d9d155b9b5bc2`,
tree `6f951398782cb08956a07765f1fbf168ddc3a3de`, with 603 tracked files.
That base adds the user-authorized source excerpts to the previous fully
verified three-label proof checkpoint `51c17b4936cf450fa86aa40e646328c8f01771f8`.
Neither is the unavailable original `cb05ef5` tree.

Run ID: `20261123T010829Z`, started 2026-11-23 01:08:29 UTC.
Read `verification/runs/20261123T010829Z/` for actual command records,
targeted failures and snapshots, setup recovery, complete-verifier status
and preservation evidence. `verification/results.json` is valid only for
its exact recorded source and input hashes. A pending or failed run is not
a verified checkpoint. The interim recovery branch, when published, is
`continuation-attempt/20261123T010829Z`; its role and exact commit are
recorded in this run's report.

**47/69 numbered assertions are complete; 22 and the main theorem remain
unfinished.** This round adds a supporting joining stage, not full 4.6.

## New checked interfaces

All five new modules are under `Overfull/CompatibleCircuits/`:

| Module | Result |
| --- | --- |
| `QuotientCuts.lean` | Exact original-copy cut/class/degree transport, fiber parity, host half-cut bounds and singleton-fiber obstruction. |
| `PairAugmentation.lean` | A generic family of `h` virtual copies between two distinct labels; admissibility, parity repair, restrictions, disjoint coverage and exactly `h` virtual-containing parts. |
| `JoiningPartitions.lean` | Injective whole-partition lift to host matchings and complete all-even-fiber decomposition. |
| `TwoOddQuotient.lean` | Original host implies all augmented half-cut inequalities and even degrees; internally constructs a compatible circuit partition. |
| `TwoOddDecomposition.lean` | Exact primary/surplus families on original copies with counts, sizes, disjointness, coverage and fiber-cut footprints. |

Main interfaces are in `Overfull.FourOdd` (the historical namespace does
not impose four labels):

```lean
exists_joining_matching_partition_of_even_fibers
twoOddJoiningQuotient_admissible
twoOddJoiningQuotient_even_degrees
exists_twoOddJoining_circuitPartition
exists_twoOddJoining_decomposition
```

For finite `G : Multigraph V E`, `label : V → I`, `Fintype.card I ≤ 3`,
regular degree `h` and no `h`-overfull set:

- All fibers even: every joining copy is covered exactly by pairwise
  disjoint nonempty host matchings of size at most three.
- Exactly two odd fibers `a,b`, with `a ≠ b`: exactly `h` primary matchings
  of size at most two and surplus matchings of size at most three. Every
  primary has one crossing copy at each odd fiber and odd cut footprint
  exactly there. Every surplus has even fiber-cut footprint everywhere.

`TwoOddJoiningDecomposition G label a b h` records the actual families.
No bound on individual joining degrees is assumed in these two results.
The separate even-degree/`2 * D ≤ h` wrapper has a stronger explicit
sufficient assumption and is not the original corollary. See
`docs/joining-circuit-verification.md`, its independent semantic review,
and `docs/joining-circuit-source.json` for the full proof map.

## Next concrete obligation

Continue the **two-core, at-most-two-exception branch of Corollary 4.6**.
The original statements and inspected assigned-part construction are in
`verification/runs/20261122T235931Z/authorized-manuscript-recovery.md`,
with assessment in `authorized-next-target-assessment.md` beside it.
These two documents were explicitly approved and published; the old
restriction records are historical evidence only.

Construct the actual label map and preceding reserves from the original
heavy-boundary pattern: assign unpaired exceptional vertices to a core
part and keep each internal exceptional pair as one extra part. Prove
the part-count and parity alternatives, then apply the new joining
interfaces. Derive subsequent palette grouping, incidence supply, robust
perfect-matching completion, regular auxiliary graphs and final host
factorization. These have not been supplied by the new decomposition and
must not be hidden in stronger hypotheses.

Reuse `Overfull/FewExceptions/`, `Overfull/OrdinaryFactorization/`,
`Overfull/TerminalComplement/` and actual fixed-pattern/reserve interfaces
located by source search. Original 4.5 permits five exceptions despite
its `two-four-exceptions` label. Keep the numbered inventory unchanged.

General four-label circuits, full 4.4/4.5, remaining 4.16 parity cases,
Section 6 setup/absorber, critical average-degree input and main theorem
remain open. For four labels both tight and slack-two cuts matter.

## Details and failed approaches to preserve

- Keep actual copies: subtype-value lifting is injective, and nonempty
  original restrictions prevent distinct parts from collapsing.
- Compatibility permits at most one virtual copy per circuit; exactly
  `h` virtual-containing parts follows from exact partition coverage.
- A zero-virtual restriction remains a circuit in the joining quotient;
  its host projection is a matching. The one-virtual result proves size
  and degree/parity profile, not a separate connected-path object.
- Quotient `P.cover` rewrites may fail due to equal decidability instances.
  Normalize with `convert P.cover using 1`, `congr`, and
  `Subsingleton.elim _ _` before transporting the equality.
- Lean may omit section hypotheses unused syntactically in a statement.
  The final two-odd existence theorem explicitly includes `hab : a ≠ b`.
- A singleton quotient fiber is not harmless: the checked obstruction
  says endpoint-class admissibility there forces vertex degree zero.

## Reproduce, verify and publish

Use Lean `leanprover/lean4:v4.24.0` and the committed manifest, including
mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Do not run `lake update`.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_joining_manifest.py
python3 scripts/verify.py
```

The verifier checks exact new source hashes and public names against the
fresh complete audit, in addition to every previous gate. Stock
`Audit.lean` remains unchanged; only `propext`, `Classical.choice` and
`Quot.sound` are allowed. Refreshing manifests is not verification. Do
not edit source or hashed documentation during the complete audit.

The temporary checkout is
`/workspace/scratch/4ffd54dab476/overfull-lean-round2`; runtime binaries
are under `/workspace/scratch/4ffd54dab476/lean-runtime/lean-4.24.0-linux/bin`.
These may disappear. Recover from GitHub and the pinned dependencies.
Setup logs record a missing ProofWidgets release-tag lookup and mathlib
HTTP 429, resolved without changing dependency revisions.

The user authorizes autonomous continuation and publication after every
run. Publish sources, mappings, docs and genuine logs; exclude caches,
compiled binaries and credentials. Refresh remote heads before updates,
preserve concurrent work, and verify published commit/tree and both heads.
Use an attempt branch for unfinished or unverified sources, keeping the
verified branches at the last complete passing source checkpoint.
No supported new-conversation control is exposed here; do not claim to
open one. Resume from this handoff without chat history, and do not
duplicate or alter the existing hourly automation.
