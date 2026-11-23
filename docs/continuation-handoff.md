# Continuation handoff: actual assigned parts and residual-host joining

## Recover the authoritative state

Fetch and inspect both `main` and
`verified-bipartite-continuation-2026-11-21` in `fly31415926/overfull-lean`
before editing. Both verified branches pointed to
`5f46a36d87f9ca1cee382f46687d9d155b9b5bc2` at this run's start.
The previous source work was preserved at recovery commit
`28edc7b555d459b93a00d15258ca374abf5f0bb0`; all five joining module hashes
were recovered exactly. A later observed full check finished on
2026-11-23 at 01:47:29 UTC, but the workspace was replaced before final
publication, so its final raw outputs were not available from that commit.
This run repeats verification rather than treating the old observation
as fresh evidence.

Current run: `20261123T042619Z`, started 2026-11-23 04:26:19 UTC.
An early source recovery checkpoint is
`b6356191c948cac240f77ca3560c1910de42112e` on
`continuation-attempt/20261123T042619Z`. It predates fresh compiler checks
and the separate-host refinement. Later run reports and the exact latest
remote heads take precedence. Read `verification/runs/20261123T042619Z/`.
Only a successful complete verifier for the exact current source/input
hashes permits a new source checkpoint on the two verified branches.

The five assigned-part drafts were lost with the transient workspace and
recreated in this run. No byte identity with those lost drafts is claimed,
and their missing historical logs have not been fabricated. The original
`cb05ef5` recovery record remains historical and unchanged.

## Completed mathematical interfaces

The recovered modules under `Overfull/CompatibleCircuits/` are
`QuotientCuts`, `PairAugmentation`, `JoiningPartitions`, `TwoOddQuotient`
and `TwoOddDecomposition`. They derive every quotient cut condition and
degree parity from a regular non-overfull host and supplied all-even or
two-odd fibers on at most three labels. They construct exact original-copy
joining matching decompositions; the two-odd case has exactly `h` primary
parts and surplus parts with checked cut footprints.

The new modules under `Overfull/AssignedParts/` are:

| Module | Main role |
| --- | --- |
| `PairFiberParity.lean` | Exact fiber sum and exhaustive parity alternatives. |
| `ThreePartLabels.lean` | An explicit label map with exact fibers for a disjoint covering triple. |
| `Basic.lean` | Actual matching-based core assignment, optional pair support, disjoint coverage and derived fiber parity. |
| `MatchedCuts.lean` | Exact original selected matching cuts and crossing-count parity. |
| `JoiningConstruction.lean` | Composition in the original host or another host on the same vertices. |

Key declarations in `Overfull.AssignedParts`:

```lean
assignedLabel
assignedLabel_fibers
exists_two_core_assigned_labels
corePart_cutOn_eq_core_crossings
assignedLabel_parity_eq_core_crossing
assignedLabel_joining_decomposition
assignedLabel_joining_decomposition_in_host
```

The supplied perfect-matching representative `M` is retained. The label
fibers are the two old cores enlarged by their matched unpaired exceptions
and the support of actual matching copies internal to `Z`. With `|Z|≤2`,
that third fiber has size zero or two and there is at most one internal
copy. Both assigned core cuts of `M` equal
`G.cutOn M U₀ ∩ G.cutOn M U₁`; the pair-part selected cut is empty.
Fiber parity is derived from the actual matching.

The generic construction can aggregate multiple internal pairs. A source
interpretation as one optional pair requires the displayed `|Z|≤2` result.
In the separate-host theorem, `M` belongs to the original graph `G`, while
the joining parts use actual copies of another graph `H` on the same
vertices. `H` regularity and absence of overfull sets remain explicit
inputs; the theorem does not prove reserve deletion preserves them.

See `docs/assigned-part-verification.md`, its semantic review and source
manifest. `verification/results.json`, the generated declaration maps and
this run's actual command records determine the completed verification
status; a source manifest alone is not a proof check.

## Exact next obligation and pitfalls

Continue the original two-core branch of Corollary 4.6 through native
multigraph boundary-pattern compression and reserve selection. Read
`verification/runs/20261123T042619Z/next-reserve-target.md` for the exact
existing APIs and proposed smallest next theorem. Native actual-copy
perfect-matching distributions and `SmallCuts` results are available;
graph-independent pattern-weight aggregation and rounding may be reusable.

Existing `Patterns`/`CircuitPatterns` distribution and reserve wrappers
use `SimpleGraph`. Their internal-pair weight-at-most-one argument cannot
be applied to several parallel copies. Retain the internal pair and prove
native copy marginals/capacities. Do not substitute an unrelated matching
for the chosen heavy-pattern representative. Prove source-statistic
alignment rather than simply identifying it with the new crossing count.

Reserve degree estimates, residual non-overfull safety, palette grouping,
robust perfect-matching completion, regular auxiliary graphs and final
factorization remain unfinished. Generic joining data are matchings; no
separate connected-path object was added for one-virtual parts.

Lean-specific lessons: normalize equal decidability instances before
rewriting partition coverage; retain distinct-label hypotheses explicitly
when section-variable inference would omit them; use small propositional
helpers instead of broad `tauto` in a large graph context. Fresh failures
and exact source snapshots belong in the run record.

**47/69 numbered assertions remain complete; full 4.6 and the main theorem
are not proved.** Full 4.4/4.5, general four-label circuits, remaining 4.16,
Section 6 setup/absorber and structural/critical-average-degree inputs are
also incomplete. Original 4.5 allows five exceptions. The already-approved
source excerpts remain under `verification/runs/20261122T235931Z/`;
old restriction records are historical only.

## Reproduce and publish

Use Lean 4.24.0, the committed dependency manifest and mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Do not run `lake update`.

```sh
python3 scripts/setup_vizing.py
python3 scripts/update_joining_manifest.py
python3 scripts/update_assigned_manifest.py
python3 scripts/verify.py
```

The unchanged stock `Audit.lean` must audit every project module and
permit only `propext`, `Classical.choice` and `Quot.sound`. The verifier
retains every prior gate and checks exact source hashes, public names and
modules for both new source maps. Preserve all historical proof sources,
69 statement hashes, completed assertion records and actual logs.

Temporary checkout:
`/workspace/scratch/4ffd54dab476/overfull-lean-current`.
Temporary runtime:
`/workspace/scratch/4ffd54dab476/lean-runtime/lean-4.24.0-linux/bin`.
These can disappear; recover from GitHub. Never depend on an unpublished
local-only checkpoint. Publish early attempt branches and genuine logs,
then update both verified branches only after the full exact candidate
passes. Fetch fresh heads, preserve concurrent work, and read back the
published commit/tree and both branch heads. Exclude caches, binaries,
credentials and unrelated private files.

The existing hourly automation was found paused and re-enabled at the
user's request during this run; no duplicate task or unrelated schedule
was changed. A scheduled run is not proof that verification or publication
succeeded. No supported fresh-conversation operation is exposed here;
resume from this durable handoff without claiming to open a new chat.
