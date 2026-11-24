# Verified snapshot publication receipts

The complete 9,064-file verified snapshot was published as commit
`db8d538df6fad430dd022154613145947f7a55b3`, with exact Git tree
`4310ca34b44916d161624653b4925910e9bef570`. Both `main` and
`verified-bipartite-continuation-2026-11-21` were independently read back at
that commit. Native Git fetch and branch readback also passed, and all 779
frozen source/verifier inputs match the published commit byte for byte.

This follow-up contains publication evidence only. The main theorem remains
unproved; numbered coverage is 49/69. The complete warning-failing build has
3,835 jobs, and the unchanged transitive axiom audit checked 14,055 declarations.
The proof snapshot's full verifier and preservation receipts remain authoritative.

## Evidence

- [Publication status](status.json)
- [Explicit user approval](receipts/explicit-publication-approval.json)
- [Public commit creation](receipts/proof-commit-create.json)
- [Public commit readback](receipts/proof-commit-readback.json)
- [Both branch readbacks](receipts/proof-branches-readback.json)
- [Native Git verification](receipts/proof-native-readback.json)
- [Native fetch output](receipts/proof-native-fetch.log)
- [Native branch readback](receipts/proof-native-refs.log)
- [Complete transport manifest](transport/manifest.json)
- [Complete target path/object inventory](transport/target-tree-inventory.json)
- [Complete baseline path/object inventory](transport/baseline-tree-inventory.json)
- [All file changes](transport/file-changes.json)
- [Final tree entries](transport/final-tree-elements.json)
- [Expected content trees](transport/expected-content-trees.json)
- [Receipt file hash index](receipt-files.json)

## Interruptions and recovery

The earlier automatic-review interruption is preserved as reported. The tool
exposed only a generic abort result; no detailed rejection rationale was
returned. The explicit later user approval authorizes public publication of
the complete snapshot and publication receipts and advancement of both branches.
No approval or security policy was changed.

One interrupted orchestration cell did not retain all original upload-call
responses. Its observed progress and interruption are recorded. For content
trees already created by that cell, this bundle retains genuine subsequent
GitHub readbacks, not invented original success receipts. Missing-object 404
readbacks are also preserved. Subsequent uploads retain their actual responses.
All 61 representative content trees and eight separately uploaded large blobs
match their expected hashes. Four final tree updates reproduce the exact
approved snapshot tree before commit creation and non-forced branch updates.

## Reproducing the transport inventory

The complete source and evidence bytes are already in the proof commit.
Regenerable raw-blob and request-chunk caches are not a separate source of
verification evidence. Recreate them outside the worktree with the preserved
read-only helper:

```sh
python verification/runs/20261124T042718Z/publication/prepare.py \
  --repo . \
  --target-tree 4310ca34b44916d161624653b4925910e9bef570 \
  --baseline-tree c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767 \
  --output-dir /tmp/overfull-publication-replay \
  --chunk-bytes 60000
```

The helper independently reconstructs the full Git trees and verifies every
exported blob. Manifest paths identify every original object and destination;
no proof source, declaration map, frozen input/output or genuine development
log is omitted from the published snapshot.
