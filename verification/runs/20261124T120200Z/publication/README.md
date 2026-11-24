# Publication preparation for four-label reductions

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
