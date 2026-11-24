# Independent review of the published-snapshot verifier

Reviewer: reconstruction agent responsible for the shared grouping and all-even modules. The reviewer did not author the original `verify-published-snapshot.py` or its verification predicates. After the read-only source review, the reviewer applied the explicitly authorized reporting-only correction described below. No final published proof snapshot existed at review time, and no successful final publication check is claimed here. The finalized review and staging helper are copied into `publication/`, outside all frozen input and control inventories; the original staging preparations remain unchanged.

## Reviewed identity

- Reviewed source: `verification/runs/20261124T213000Z/publication/verify-published-snapshot.py`
- Reviewed source SHA-256: `cd197d99f6287468ecb053bbe6dd6a68eb754b42191988965bf82e78926739f1`
- Staging helper SHA-256: `28c4071bbbd37cba9f90d428fe0dd3ef073cedd6d12aa51811f71a92af366143`
- Exact pre-audit tree: `9aaf99be730815a01ac32c6a6089787451d7c9f0`
- Pre-audit staging manifest SHA-256: `62e3a1cb3e2b6ccf34d49c81e0a0aa7e8147b84b79b9a7202f888a5af08a934f`

## Result

No substantive integrity defect was identified in the publication verifier for its stated role: compare an exact already-fetched commit against the genuine local frozen full-run evidence. It requires the exact requested commit, tree, and sole parent. Blob reads check Git SHA-1; proof inputs and controls are checked against frozen SHA-256 manifests at their live and archived locations. The input path set is reconstructed from the fetched tree without executing fetched code and must exactly match the frozen inventory.

The verifier requires the genuine `full-01` command and terminal receipts to agree, the full wrapper and verifier to have passed with zero exit codes, no changed inputs or controls, no missing principal outputs, and no wrapper errors. It checks the actual output log digest and the complete recorded output archive. The preservation receipt must refer to the exact terminal bytes and certify the pinned baseline, all previous declarations and mappings, all 69 statement identities, exactly the 4.16 and 4.17 promotions from 49 to 51, and `main_theorem_verified = false`. Every nonpublication file in the current run must have exactly the same path and bytes as the local evidence. The final report must agree with the frozen proof and preservation report.

## Required surrounding evidence

The script intentionally performs no remote read and therefore cannot itself establish that a local commit has been published. Its `fetched_public_commit_integrity` receipt must be paired with the separate authenticated/public readback and native-fetch receipts establishing that exact public commit and both requested branch heads. This is the planned publication procedure, not an additional proof assumption. The expected tree and parent must come from the concrete prepared snapshot and publication plan. An output path must remain in `publication/` or outside the repository so creation of the receipt does not modify the frozen nonpublication evidence.

The script is specifically bound to successful attempt `full-01`; it must not be represented as verifying a different attempt. The minor reporting issue identified in the original review is now corrected: `unique_blobs_checked` is `len(cache)`, and `unique_blob_bytes_checked` is `sum(len(v) for v in cache.values())`. This changes only two result fields, with no change to any verification predicate. The source before this reporting correction had SHA-256 `d4897d2578d11b1e8bfa7f4d130a08034ddca7b3d95ea285d55f5cc883b73852`. Before the edit, the verifier, review, and staging-helper publication paths were explicitly checked to be absent from both frozen manifests (855 inputs and 24 controls). The frozen manifests remain byte-identical, and no frozen source or control was edited. No new tests were run for this reporting correction.

## Staging validation

The staging helper completed against the exact pre-audit tree, independently rebuilding every directory tree and checking Git SHA-1, SHA-256, and length for all 3,163 unique blobs at 13,661 leaf paths. Relative to already-fetched public commit `1008c182a29dd6a86c1672236845ab357c2ceb7c`, it staged 163 needed blobs totaling 4,926,555 bytes in four batches of 50, 50, 50, and 13 files. The helper accepts both exact tree and commit object identities, performs no remote operations, invokes no mutating Git commands, and does not change the worktree, index, or refs.

A supplemental known-commit validation checked commit `1008c182a29dd6a86c1672236845ab357c2ceb7c`, exact tree `fec02f947b26a5abed7a78bfd9cd242ce681081b`. Relative to the original baseline, it correctly contains 35 additional blobs totaling 661,227 bytes because its parent already contains 34 recovery blobs. A separate postcheck initially assumed one nonbaseline blob and failed; that mistaken expectation was corrected and documented in `browser-helper-validation-1008/known-commit-validation.json`. The helper itself succeeded. A native parent-relative diff confirms that the ordinary browser upload added exactly one 138,825-byte log, blob `7a58ba65f8896c10c3761de961cfb303e6340e88`, with SHA-256 `b3e65bced70526a7962313cede31cf77e9d3c859d847200c7ddd1b42557b558b`.
