# Publication status: blocked by automatic approval review

The complete Lean verification and baseline-preservation gate passed. The
verified local proof commit is
`da6c2be9170823d3f7f04913863910b1661f739a`, with exact tree
`63b623f73fcb4333d38f46d8e845a2c3f4ff6f23` containing 10,490 files.
The full result remains 49/69 numbered assertions, with the main theorem
unverified. See the completed [verification report](../REPORT.md).

Automatic approval review rejected content batch `content-0033.json` after
33 earlier content batches were successfully uploaded and hash-checked.
Its stated reason was that the current request to continue Lean verification
did not explicitly authorize public publication of the complete repository
snapshot, including sources, frozen inputs, detailed logs, and environment
metadata. The raw rejection is preserved in
[automatic-review-rejection.json](receipts/automatic-review-rejection.json).
No rejected upload was retried or routed through another publication mechanism.

No new public commit was created and no branch update was attempted. Fresh
GitHub and native Git readbacks show both `main` and
`verified-bipartite-continuation-2026-11-21` still at
`e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8`. The successful remote content
objects do not constitute publication of the verified snapshot on either
branch. All 794 frozen inputs and 16 controls were checked again after the
block and remain unchanged.

## Exact pending action

The pending approval covers public publication of the complete verified
snapshot and its publication receipts to `fly31415926/overfull-lean`,
including all source files, complete public/private/generated declaration
maps, frozen verification inputs and outputs, genuine successful, failed and
interrupted development logs, and environment metadata. It also covers
advancing both existing branches after exact-tree and branch-head checks.

The remaining transport comprises three content batches, five large UTF-8
blobs, three final-tree updates, commit creation, and both non-forced branch
updates. Any subsequent attempt must first receive the explicit authorization
required by automatic review. It must inspect fresh remote branch heads and
retain the actual new call responses. The original rejection receipt must
not be overwritten as a success receipt.

## Evidence and reproducible continuation

- [Publication status and branch readbacks](status.json)
- [Native branch readback](receipts/blocked-native-branches-final.json)
- [Post-block frozen-input integrity check](receipts/post-block-integrity.json)
- [Complete transport manifest](transport/manifest.json)
- [Every target file, mode, and Git object](transport/target-tree-inventory.json)
- [Exact changed-file inventory](transport/file-changes.json)
- [Expected content and final-tree hashes](transport/upload-index.json)
- [Read-only transport helper](prepare.py)
- [Upload hash and inclusion checker](prepare-upload-index.py)

All 2,070 required frozen source and setup/development/full-verification
evidence files were checked for exact byte inclusion in the target tree.
The raw blob and chunk cache is reproducible from the local proof commit.
Recreate it in a fresh directory outside the repository, using the exact
target tree above, then rerun `prepare-upload-index.py` on that directory.
The successful receipts for `upload-content-0000.json` through
`upload-content-0032.json` identify already confirmed object trees. A newly
authorized retry of batch 33 must use a new receipt filename.

## Original preparation reference

This directory initially contains preparation code and an early file-encoding
scan. It does **not** assert that a new commit or tree has been published.
The root agent owns all commit creation, uploads and branch updates.

The baseline is public commit
`e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8`, tree
`9013f6d5c07676ba130d4bb794062d700bab6136`, in
`fly31415926/overfull-lean`. Both `main` and
`verified-bipartite-continuation-2026-11-21` were read back at this commit
before the work. The full preservation check remains anchored to this local
HEAD until it passes.

## Required order

1. Finish focused proof work, manifest generation, exact imports, reviews and
   the development index. Run the complete frozen verifier and preservation
   check. Their genuine successful receipts determine release eligibility.
2. Retain the actual final report and all successful, failed and interrupted
   development evidence. Stage and inspect the concrete complete publication
   snapshot only after the full preservation gate passes.
3. Supply that snapshot's full immutable tree SHA to `prepare.py`, with an
   explicit fresh output directory outside the repository. The helper reads
   existing Git objects and writes transport files; it performs no Git, index,
   commit, worktree, ref or remote mutation.
4. Upload unique content blobs and verify every returned Git blob SHA. Apply
   the final tree batches on the exact baseline tree in the recorded order.
   The reconstructed remote tree must equal the local target tree exactly
   before any commit or branch update.
5. Create the commit with the actual remote parent, then update both branches
   with their observed expected heads and without a forced rewrite. Retain
   genuine commit, exact-tree and both-branch readbacks. Publication receipt
   commits are distinct from the frozen proof snapshot and do not change its
   verified source bytes.

The invocation, with the exact tree supplied by the root agent, has the form:

```sh
python verification/runs/20261124T120200Z/publication/prepare.py \
  --repo /workspace/scratch/77adbfc63087/overfull-lean \
  --target-tree FULL_TARGET_TREE_SHA \
  --baseline-tree 9013f6d5c07676ba130d4bb794062d700bab6136 \
  --output-dir /workspace/scratch/77adbfc63087/publication-prepared \
  --chunk-bytes 60000
```

Do not reuse an existing output directory. The explicit outside-repository
output path is required with this preserved helper. Raw blob and request-chunk
caches are reproducible transport material; the actual project bytes, commands,
source snapshots and output receipts remain the evidence that must be retained.

## Encoding and exact transport checks

The early scan is `initial-transport-scan.json`. At its recorded time, all 250
current setup/development files were valid UTF-8; none required binary/base64
transport. The retained HTTP-429 download log was about 498 kB and is a large
UTF-8 blob. Later full verifier results and audit logs will also need their
actual sizes assessed by the final export. The early scan is intentionally
not treated as a final file inventory.

`prepare.py` is the preceding checkpoint's read-only transport helper with only
the repository and baseline constants updated. It retains independent complete
Git tree reconstruction, exact path/mode/object inventories, raw Git blob SHA
verification, UTF-8 or base64 chunk round trips, duplicate-content reuse, and
final-tree-plan reconstruction. Each final target leaf is included, including
all genuine evidence and private/generated declaration maps. The helper's
provenance record documents this limited adaptation.

Coverage remains 49/69; no numbered manuscript assertion is promoted by these
supporting reductions. The main theorem remains unproved.
