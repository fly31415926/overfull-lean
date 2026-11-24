# Published verified snapshot and publication receipts

The complete verified proof snapshot is public in
[fly31415926/overfull-lean](https://github.com/fly31415926/overfull-lean) as commit
[33941c5eebe9fb470f7b0f2c4350b787bf04b5fe](https://github.com/fly31415926/overfull-lean/commit/33941c5eebe9fb470f7b0f2c4350b787bf04b5fe).
Its exact tree is `63b623f73fcb4333d38f46d8e845a2c3f4ff6f23`, containing
10,490 files. This tree is identical to verified local proof checkpoint
`da6c2be9170823d3f7f04913863910b1661f739a`.

This publication-only follow-up archives the complete transport and proof-publication
receipts. It changes no verified source, frozen input, verification control, declaration
map, archived verifier output, or nonpublication run evidence. The containing Git commit
identifies the receipt snapshot; its own future publication is not represented as a
pre-existing receipt.

The strict full verifier and independent preservation gate passed. Coverage remains
**49 of 69 numbered assertions fully verified**, and the main theorem remains
**unverified**. See the [completed verification report](../REPORT.md).

## Published contents and verification

The proof tree contains all sources, complete public/private/generated declaration maps,
794 frozen inputs, 16 frozen controls, 24 archived outputs, successful, failed and
interrupted development evidence, genuine full build and audit logs, and recorded
environment metadata. Nothing was replaced with a synthetic successful log.

| Check | Observed result |
| --- | --- |
| Strict complete build | `lake build --wfail Overfull`; 3,846 jobs; exit 0 |
| Stock unchanged kernel audit | `lake env lean Audit.lean`; 14,260 declarations |
| New modules | 11 |
| New public proof declarations | 73 |
| New audited declarations, including private/generated | 205 |
| Completed-result mappings | 2,609 |
| Allowed axioms | `Classical.choice`, `Quot.sound`, `propext` |
| Frozen inputs / controls | 794 / 16; all unchanged |
| Archived verifier outputs | 24; exact live/archive byte matches |
| Published nonpublication run files | 1,304; exact local evidence matches |
| Explicit published digest comparisons | 1,668 |
| Prior declarations / result mappings retained | 14,055 / 2,536 |
| Numbered assertion coverage | 49/69; no promotion |

The fetched public commit has parent
`e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` and exactly the expected proof tree.
The [published-byte integrity receipt](receipts/published-proof-integrity.json)
checks both live and archived inputs, controls and outputs against the immutable
full-run hashes. It also compares every nonpublication run file with retained
evidence. The [independent publication review](independent-publication-review.md)
provides a separate check.

## Actual branch updates and readbacks

Both existing branches were advanced without force, with the expected old head
explicitly supplied:

| Branch | Expected old head | Observed published proof head |
| --- | --- | --- |
| `main` | `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` | `33941c5eebe9fb470f7b0f2c4350b787bf04b5fe` |
| `verified-bipartite-continuation-2026-11-21` | `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` | `33941c5eebe9fb470f7b0f2c4350b787bf04b5fe` |

These are historical proof-publication observations, before the receipt follow-up.
The raw [API branch readbacks](receipts/proof-branch-readbacks.json) and independent
[native Git fetch and branch readback](receipts/native-proof-git-readback.json) agree.
The actual [commit creation](receipts/proof-commit-create.json) and
[commit/tree/parent readback](receipts/proof-commit-readback.json) are retained.
The receipt follow-up is a child of this proof commit, with changes restricted to
this publication directory.

## Preserved authorization and transport history

The first attempt stopped when automatic approval review rejected content batch 33.
The original [rejection](receipts/automatic-review-rejection.json),
[blocked status](blocked-status.json), and [blocked README](blocked-publication-README.md)
are preserved. The user then explicitly authorized publication of the complete
snapshot, source and declaration maps, private/generated declarations, frozen
inputs and outputs, genuine logs, environment metadata, receipts, and both branch
updates. The [exact authorization record](receipts/explicit-publication-approval.json)
is retained. Resumed uploads use new receipt filenames; no rejection was overwritten
as a success.

All 36 content batches and all five large blobs received the expected object hashes.
The first bulk final-tree update succeeded. The second returned an API 422 timeout.
A subsequent GET returned self-consistent root-tree metadata, but the next write
rejected that intermediate tree as an invalid base. The receipts do not establish
the cause of that read/write discrepancy.

Recovery restarted from the last successful write response, tree
`b3363366151d79de46e15e1c055a4fe06621138d`. The remaining 701 upserts were split
into seven batches of 100 entries and a final batch of one entry. All eight
create-tree responses matched independently computed expected hashes, ending at the
exact verified tree. The [recovery requests and hash plan](transport/recovery-small-batches/index.json)
and every actual response are retained. A precommit tree GET also returned 404;
that failure is preserved. Publication was confirmed by the later actual commit
readback, successful native fetch, both branch readbacks, and checks of the fetched
commit's bytes, rather than by interpreting failed reads as successes.

## Evidence index and reproduction

The [receipt-archive transport index](receipt-archive-transport/index.json) also preserves
the 11 actual responses for uploading the receipt archive itself: four content batches,
six large blobs, and the successful archive-tree update. Each returned object hash
matched its independently prepared expected value. The containing commit finalizes
these records; it cannot contain receipts for its own future commit and ref updates.


- [Machine-readable publication status](status.json)
- [Complete proof transport manifest](transport/manifest.json)
- [Every verified target path, mode and Git object](transport/target-tree-inventory.json)
- [Changed-file inventory](transport/file-changes.json)
- [Expected upload tree hashes](transport/upload-index.json)
- [All raw publication receipts](receipts/)
- [Receipt SHA-256 index](receipt-index.json)
- [Independent resumption review](independent-resumption-review.md)
- [Read-only transport exporter](prepare.py)
- [Transport inclusion and hash checker](prepare-upload-index.py)
- [Fetched-byte verification program](verify-published-snapshot.py)

The transport inclusion check covers 2,070 required source and setup/development/full-run
evidence paths. Reconstruct the raw payload/chunk cache in a fresh directory outside
the repository, using the exact proof tree and baseline tree:

~~~sh
python3 verification/runs/20261124T120200Z/publication/prepare.py \
  --repo /path/to/overfull-lean \
  --target-tree 63b623f73fcb4333d38f46d8e845a2c3f4ff6f23 \
  --baseline-tree 9013f6d5c07676ba130d4bb794062d700bab6136 \
  --output-dir /path/to/fresh-transport-directory \
  --chunk-bytes 60000
python3 verification/runs/20261124T120200Z/publication/prepare-upload-index.py \
  /path/to/fresh-transport-directory
~~~

To repeat the published-byte check, fetch the proof commit and select a fresh output
path. The checker refuses to overwrite an existing receipt.

~~~sh
git fetch --no-tags origin 33941c5eebe9fb470f7b0f2c4350b787bf04b5fe
python3 verification/runs/20261124T120200Z/publication/verify-published-snapshot.py \
  --commit 33941c5eebe9fb470f7b0f2c4350b787bf04b5fe \
  --tree 63b623f73fcb4333d38f46d8e845a2c3f4ff6f23 \
  --parent e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8 \
  --output fresh-publication-integrity.json
~~~

The original full-run preservation wrapper is anchored to the prepublication baseline
HEAD. Its successful immutable receipt remains the preservation evidence; the fetched-byte
checker is the appropriate publication-integrity check after commits have advanced.
