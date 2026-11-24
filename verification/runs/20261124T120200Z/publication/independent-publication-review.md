# Independent verification of the public proof commit

Reviewer: `/root/verification_infrastructure`.

The focused read-only checks passed at **2026-11-24 13:26:59.910121 UTC**.
The fetched public proof commit contains the exact saved verified tree, with
no source, declaration-map or verification-evidence loss.

## Exact public and local objects

| Item | Checked value |
| --- | --- |
| Public proof commit | `33941c5eebe9fb470f7b0f2c4350b787bf04b5fe` |
| Local proof checkpoint | `da6c2be9170823d3f7f04913863910b1661f739a` |
| Identical tree in both commits | `63b623f73fcb4333d38f46d8e845a2c3f4ff6f23` |
| Parent of both commits | `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` |
| Exact file-leaf count | 10,490 |

The public commit was available through native Git after the recorded fetch.
Its raw commit bytes hash to the stated public commit ID. Its actual tree and
parent match the saved local checkpoint, and the complete recursive Git leaf
listings of the two commits are byte-identical. Selected principal evidence
blobs were also read from the fetched public tree and compared with the live
files, including the full results, build and axiom logs, new declaration map,
source inventory, stock audit, preservation result, full terminal receipt,
raw full-run output and run report.

## Original verification evidence remains intact

The original full-run command and terminal receipts are identical and retain
SHA-256 `02c16881a3f0b32cc3f80304451e599fbc11c838dfbb6eee73a6aa8e23ce815b`.
They record verifier and wrapper exit zero, unchanged inputs and controls,
no missing principal output, and no wrapper error. All **794 current inputs**
and **16 controls** match the frozen inventories and archived copies. All
**24 recorded outputs** match their live and archived bytes and recorded sizes.

The preservation report retains SHA-256
`0c48080a95476e87cf439ee2372fe6cc032d81f1e6dcfd3368c92219cb27bfe3` and its
successful original baseline-anchored result. The raw full-run output retains
SHA-256 `a0ae96d437ca48999098f4fde42f316df5c21407acc80276eef21b7a04292271`.
The complete strict build reported **3,846 jobs**, and the stock axiom audit
checked **14,260 declarations**, including **205 new declarations** in the
11-module continuation. The new inventory has **73 public proof declarations**,
and the completed-result map contains **2,609 entries**.

The original preservation result retains all 14,055 prior declarations,
2,536 prior result mappings, old source/declaration maps, and all 69 numbered
assertion records. Current coverage checks still give **49 of 69** completed
assertions and an unverified main theorem. The development index and its
334 evidence files also pass their unchanged-byte checks: 10 attempts passed,
13 failed, and 3 were interrupted, with their original distinctions retained.
No Lean build or axiom audit was rerun as part of this publication review.

## Tree discrepancy and actual recovery

The earlier large `approved-final-tree-0001` request returned API 422 with a
timeout. Its expected intermediate tree was
`5d4d05f18d7b5b70ec83eb99665465072501fba3`. The following readback contains a
self-consistent nonrecursive root-tree response: 17 entries, the expected
SHA, and `truncated: false`. Re-encoding those exact entries as a raw Git tree
reproduces that SHA. The subsequent `approved-final-tree-0002` create request
nevertheless returned API 422, stating that this base tree was invalid.

The cause of that read/write discrepancy is **unestablished**. The positive
root readback did not establish that the write endpoint could use the object
and its descendants. Both failed create receipts and the readback remain
preserved; neither failed create is counted as a successful update.

Recovery started from the genuinely successful tree
`b3363366151d79de46e15e1c055a4fe06621138d`. The remaining 701 upserts were
submitted in **eight requests: seven of 100 entries and one of one entry**.
For every recovery request, this review checked the payload hash, entry count,
base-tree chain, and actual tool response. Every response has `isError: false`
and returns exactly its independently reconstructed expected tree SHA.
Concatenating the recovery entries reproduces the original remaining upserts
without loss or reordering. The last successful response returns the exact
verified target tree `63b623f73fcb4333d38f46d8e845a2c3f4ff6f23`.

## Commit and both-branch readbacks

The successful commit-creation receipt names the exact verified tree and the
baseline parent, and returns the fetched public proof commit above. Both
branch-update receipts request `force: false`, require the expected old
baseline commit, and record success. The stored API branch responses were
parsed and checked for branch name, public commit, exact tree, and parent.
Both resolve to the public proof commit:

- `main`
- `verified-bipartite-continuation-2026-11-21`

The native Git receipt independently records a successful fetch of the exact
public commit and a successful `git ls-remote` observation of both branch
heads at that commit. The fetched commit is present in `FETCH_HEAD`. Fetching
by commit SHA did not refresh local `origin/*` tracking refs; those stale local
refs were not used as evidence of the published branch heads.

This record concerns the completed proof-publication checkpoint. The later
publication receipts, including this review, are retained for the separate
receipt follow-up commit. The reviewer performed no remote mutation, staging,
commit or ref update, changed no frozen source or control, and will make no
further repository writes after adding this single review file.
