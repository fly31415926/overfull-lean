# Publication status: verified locally, blocked by approval review

The complete frozen verifier and preservation gate passed. The independent
final review passed 335 checks. The local proof has 14,627 audited declarations,
including 367 new declarations across 28 new modules. Numbered coverage remains
49/69, and the main theorem remains incomplete.

Public publication is not complete. Automatic approval review rejected two
content uploads because it could not establish current user-authored permission
for public egress of this new snapshot's source, logs, and metadata. The exact
responses are preserved in `proof-transport/content-0004.json` and
`proof-transport/content-0007.json`.

The first four content batches succeeded. The next four were launched
concurrently: batches 5 and 6 succeeded, and batches 4 and 7 were rejected.
All four completed responses were collected and preserved before stopping.
No further upload was attempted, no final repository tree was assembled,
no public commit was created, and neither branch was advanced. Fresh API
readbacks confirm both branches remain at `3991bb7eee091a329046073e0366daa84a603e5d`.

The earlier project approvals were retrieved through Personal Context. The
latest explicit approval referred to the preceding snapshot; no explicit
standing authorization for future snapshots was found. The frozen run-level
authorization note preserves the pre-rejection understanding and is not fresh
authorization. See `authorization-check.json` for the later correction.
The rejection was not bypassed through another tool, endpoint, or recipient.

## Concrete verified snapshot

The initially prepared proof tree is
`c691dabf252b6fe72005963c61ce4128962d7e66`, with 12,787 tracked paths.
Its exporter and upload-index checks passed. The staged local checkpoint
subsequently adds only publication records, including these actual rejection
receipts and the blocked-status documentation. Its immutable mathematical
inputs, controls, source maps, results, and full-run evidence are unchanged.

The transport metadata records exact content hashes and the expected tree
after every batch. Successful temporary content trees already materialize
some Git blobs; they do not constitute a published branch checkpoint.
The external transport cache can be regenerated with the included helpers.

## Resumption after explicit authorization

Refresh both remote heads. Prepare an export from the approved local commit's
actual tree, preserving every source and evidence file. Retain the original
rejections and successful responses. Do not overwrite original receipt files
or represent a rejected upload as successful. Reuse already materialized blob
objects when their expected hashes are confirmed.

Require the complete returned tree to equal the approved local tree before
creating a public commit. Advance both branches with the inspected expected
head and without force, then independently fetch and check the published
objects and both branch references. Archive publication receipts separately
without modifying the frozen mathematical verification inputs.

