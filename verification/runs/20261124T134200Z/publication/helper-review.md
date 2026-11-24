# Independent read-only review of publication helpers

## Finding and scope

The reviewer inspected `prepare.py`, `prepare-upload-index.py`, and
`verify-published-snapshot.py`, including the final optional transport-baseline
change. No concrete blocking runtime or publication-integrity issue was found
for the intended continuation publication workflow.

This was a read-only source review with Python syntax parsing. It did not
execute exports, create publication receipts, create Git objects, update
references, or contact the remote repository. End-to-end publication success
must be established by the actual transport responses, exact returned tree
hashes, fetched commit checks, and both branch readbacks. This review does
not substitute for the full verifier or the separate preservation gate.

## Exact content transport

`prepare.py` reads immutable Git tree and blob objects. It reconstructs both
baseline and target tree hashes independently from exact paths, modes, and
object identifiers, then simulates the entire deletion/upsert plan and
requires the reconstructed final tree to equal the target. Extracted blobs
are checked against their Git object hashes, and chunked content is checked
by exact reconstruction before transport metadata is written.

Final-tree requests are limited to at most 100 entries as well as the stated
serialized-byte limit. The upload-index helper independently simulates those
batches and records their expected intermediate tree hashes. It rejects
deletions and non-blob updates for this continuation's intended additive
publication workflow. Remote responses must still be checked against the
expected object and tree hashes during execution.

The preparation command requires an explicit external `--output-dir` in
practice: its implicit default lies inside the repository and is rejected
by its own outside-repository check. The intended root workflow already
supplies an external directory, so this is not a blocker for that workflow.

## Verified evidence and readback

The upload-index helper requires the completed full-run command and terminal
receipts to agree, requires a successful verifier and wrapper with unchanged
inputs and controls, and checks the 826 frozen inputs. Control and output
inventories are taken from the actual frozen manifests and terminal receipt;
their counts are not replaced by a fixed historical inventory. It checks
live/frozen source and control bytes, exact live/archived output bytes, the
principal outputs, and the complete archived-output inventory.

The required source and nonpublication run evidence must appear in the target
tree with exact blob hashes. Publication helper sources are included as well.
The publication subdirectory is intentionally excluded from the later
nonpublication evidence comparison, allowing subsequent publication receipts
without changing the verified mathematical inputs or frozen controls.

`verify-published-snapshot.py` checks the explicitly requested commit, tree,
and sole parent. It reads fetched Git blobs, checks their object hashes,
compares all frozen sources and controls and their snapshots, verifies the
recorded output/archive bytes, and checks the entire nonpublication run-file
inventory against local evidence. A successful helper result concerns those
fetched immutable bytes; both live remote branch references require their
separate readbacks.

## Alternate transport baseline

The optional `--transport-baseline-tree` accepts an explicit full 40-hex tree
identifier and defaults to `6424bf81123aa75b2254aea7eceff6260611f397`.
The selected transport baseline is compared to the preparation manifest and
independently reconstructed from its tree inventory. It governs the starting
state for final-tree batch simulation.

The proof baseline remains separately pinned to commit
`3991bb7eee091a329046073e0366daa84a603e5d` and tree
`6424bf81123aa75b2254aea7eceff6260611f397`. An alternate transport baseline
does not relax the successful full-run receipt or change its baseline,
frozen-input requirement, control checks, or output checks. The default
transport requires the pinned baseline commit reference; a nondefault
transport requires that reference to be null, preventing it from being
misidentified as the continuation's proof baseline. The output index records
transport and continuation baselines separately.

This permits a later receipt-only transfer to begin from the already
published proof snapshot while preserving the original mathematical
verification identity.

## Reviewed final helper SHA-256 values

These are the final hashes observed and reported at completion of the review.
No additional verification was performed when this review artifact was saved.

| Helper | SHA-256 |
| --- | --- |
| `prepare.py` | `e07f7f9c0925f06958cca83082975e94b3e8e23b79885c1aa1c54ab91a68e55e` |
| `prepare-upload-index.py` | `3911df635167cfad654fea1cf013cc60d688a927587e8eb38ab283fe422d2329` |
| `verify-published-snapshot.py` | `cbc2d26143a4ecbf6bb27696dbc8013f49228c026ee47f12223cbf159f79173e` |
