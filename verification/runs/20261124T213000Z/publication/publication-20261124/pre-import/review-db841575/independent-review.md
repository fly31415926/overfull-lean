# Independent review of the proposed exact-object publisher

Reviewed by the parent agent after the publisher was prepared by a separate agent.

## Exact reviewed bytes

- Helper SHA-256: `d3cbf3ef67e5020483dcb28fb57ae58d97bc2f1389d8ca51f79b8bf8a025b7c6`.
- Inert workflow text SHA-256: `2b3d5bb04e9af2b086e06221a9687ae5323ab9306d40cb01f163db98a9945d7f`.
- Exact proof commit: `db841575ca2c427e230387c1c95fa74bedb463d6`.
- Exact proof tree: `a7e59e8303f670fab6c95348cd100acd1aaa5899`.

## Findings

The helper fixes the repository, proof commit and tree, sole baseline parent, archive prefix, manifest digest, decoded bundle length and digest, and sole destination proof branch in its source. It verifies all part identities, canonical base64, actual Git bundle metadata, exact committed terminal and preservation receipts, and the recorded mathematical scope before a possible push.

The default path performs local verification only. It disables network protocols, Git object replacement, repository hooks, tag following, and submodule recursion for the relevant commands. The separately gated publication path enables HTTPS only, requires the exact GitHub Actions repository/branch/event context, checks the checkout against the event commit, rejects multiple or unexpected origin push URLs, and performs an ordinary nonforce push of the fixed proof commit to the fixed proof ref. It rejects a pre-existing different proof ref. It reads the two source publication refs before and after and verifies that this job did not change them.

The proposed workflow grants `contents: write` only to its one publication job, checks the helper's exact digest before running it, uses a pinned checkout action, and has a ten-minute limit. Its write permission remains repository-wide at the token level; the narrower destination is enforced by the reviewed code. Explicit approval is therefore still required. This review grants no approval and does not activate anything.

The review found no blocking discrepancy between the exact proposed helper and the stated scope. The helper reads committed proof evidence as data and does not execute the Lean sources or scripts from the bundled proof. The preparer's one default-mode local run is recorded separately. This review did not repeat that run or execute the publish path.

The public archive was independently restored after publication, yielding the same proof commit/tree and all 14,692 paths. Its actual public-only restoration receipts are separate evidence, not an execution of this proposed workflow.
