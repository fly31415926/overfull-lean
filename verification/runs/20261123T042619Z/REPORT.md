# Recovery and continuation: actual assigned parts and joining proofs

**Fresh complete verification passed for the exact frozen candidate.**
The run began at `2026-11-23T04:26:19+00:00`; this record was generated at
`2026-11-23T05:00:02.264177+00:00`. The verified baseline is `5f46a36d87f9ca1cee382f46687d9d155b9b5bc2`.
The early recovery snapshot is `b6356191c948cac240f77ca3560c1910de42112e`. A later frozen-candidate recovery commit is `2fe5003409369512a53e309de9af9a45f57d737b`.

## What was recovered and what was proved now

Five joining modules, with 75 public theorems,
were recovered byte-for-byte from published attempt `28edc7b555d459b93a00d15258ca374abf5f0bb0`. They prove
the original-host joining decomposition for a supplied assignment to at most
three labels. All-even fibers yield exact matching partitions; exactly two
odd fibers yield exactly `h` primary matchings plus surplus matchings, retaining
all original joining copies and their cut footprints.

The unpublished assigned-part drafts were lost when the workspace was
replaced. The 5 current assigned-part modules were
recreated and freshly checked; byte identity with those lost drafts is not
claimed. Their 43 public theorems construct
actual labels from a specified perfect matching, prove the exact assigned
fibers and selected cuts, derive their parity, and compose the construction
with joining decomposition. With at most two exceptions, the optional pair
fiber has zero or two vertices and contains at most one selected internal copy.

The new `assignedLabel_joining_decomposition_in_host` refinement uses the
representative in one graph `G` to construct labels for another host `H` on
the same vertices. The representative need not survive in `H`; the output
retains `H`'s own actual edge copies. Regularity and absence of overfull sets
for `H` remain explicit residual-stage hypotheses, not consequences falsely
attributed to reserve removal.

The supplied perfect-matching representative is preserved. Generic interfaces
can aggregate multiple internal pairs into one even fiber; the source-specific
single optional pair interpretation uses the explicit two-exception bound.
The native multigraph proofs do not assume the original host is simple.

## Actual verification and preservation

| Check | Result |
| --- | --- |
| Fresh `python3 scripts/verify.py` | Exit 0; recorder status passed |
| Strict `lake build --wfail` | 3,675 jobs passed |
| Unchanged complete `Audit.lean` | 11,927 declarations passed |
| Prior declaration names/modules/axiom sets | All 11,727 preserved |
| New audited declarations relative to verified baseline | 200 |
| Prior nonroot Lean files | 493 byte-identical, including stock audit |
| Prior declaration maps | All 6 byte-identical |
| Recovered joining public/audited declarations | 75 / 131 |
| Recreated and new assigned public/audited declarations | 43 / 69 |
| Exact Lean source path/hash inventory | 504 files |
| Exact other verification-input path/hash inventory | 75 files |
| Frozen source/input inventory | 579 paths; unchanged through checking and recording |
| Numbered manuscript assertions | 47/69 complete; 22 remain |

The only allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Lean remains pinned to `leanprover/lean4:v4.24.0`, with mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; all dependency source revisions
match the verified baseline. The actual complete audit log is compared to
every declaration record in the fresh results. Removing the two new imports
reproduces the baseline root file exactly. All 69 original statement hashes
and all 47 previously complete assertion records are unchanged.

`run.json` records exact evidence hashes, complete group mappings, the frozen
input identity and genuine current command results. Full logs are in
`verification/build.log`, `verification/axioms.log` and this run's
`verification-console.log`. Source and declaration maps separately identify
the recovered joining group and the recreated/new assigned group.

## Recovery and diagnostic honesty

The earlier conversation reported a complete joining audit, but its final
raw outputs were not preserved in the referenced recovery commit. They are
not fabricated, replayed or used as current verification evidence here.
This report relies on the new complete verifier run. The published prior
targeted diagnostics and historical recovery evidence remain byte-identical.
The two manuscript documents already authorized and published in the
baseline remain preserved; no new source-release restriction is introduced.

Current retained targeted records contain 4 successes and
2 failures. A failed check remains a failed check. Actual logs
and captured source snapshots are retained, including heartbeat or warning
failures where they occurred during recreation.

| Current command record | Exit code | Actual result |
| --- | ---: | --- |
| `assigned-basic-01.json` | 0 | passed |
| `joining-construction-01.json` | 0 | passed |
| `matched-cuts-01.json` | 1 | failed |
| `matched-cuts-02.json` | 1 | failed |
| `matched-cuts-03.json` | 0 | passed |
| `public-name-check.json` | 0 | passed |

The earlier `cb05ef5` reconstruction evidence remains historical. Neither
this run nor the recovered joining attempt is described as that unavailable
original commit/tree.

## Remaining proof target

The assigned parts, exact selected cuts and joining-stage composition are
now checked supporting results. The native multigraph heavy-pattern and
reserve construction, reserve-degree estimates, residual safety, palette
grouping, robust completions, auxiliary graphs and original-host factorization
remain unfinished. Existing simple-graph pattern/reserve APIs do not supply
those multigraph steps. The exact old-core crossing count has not silently
been identified with an unrelated pattern-code statistic.

Full 4.4/4.5/4.6, the remaining 4.16 branches, general Section 6, structural
inputs and the main theorem remain incomplete. No numbered assertion is
newly counted complete. Continue from `docs/continuation-handoff.md`,
`docs/next-verification-target.md` and the source/proof maps.

## Publication boundary

This report was generated before the verified branch updates. It does not
claim those updates have happened. Publication must preserve concurrent
work, update both verified branches to the same checked source checkpoint,
and confirm the commit/tree and both remote heads afterward.
