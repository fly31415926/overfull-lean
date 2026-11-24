# Concrete request: bounded retries of the reviewed publication procedure

Status: awaiting explicit approval for additional attempts. The first approved job has finished and its active workflow has been removed.

## Requested authorization

Approve up to **three additional attempts** of the same reviewed GitHub Actions publication procedure, with job-scoped repository `contents: write`, to recover from the observed GitHub `Internal Server Error`.

An attempt would rerun the failed publication job from its original immutable workflow definition. If GitHub requires a fresh activation instead, an attempt may reinstall the identical reviewed temporary workflow on the recovery branch, run it, and remove it after the observed outcome. The procedure stops after the first confirmed successful publication or after three additional attempts.

Every attempt retains the same fixed identities and restrictions:

| Item | Exact value |
| --- | --- |
| Repository | `fly31415926/overfull-lean` |
| Proof commit | `db841575ca2c427e230387c1c95fa74bedb463d6` |
| Proof tree | `a7e59e8303f670fab6c95348cd100acd1aaa5899` |
| Helper SHA-256 | `d3cbf3ef67e5020483dcb28fb57ae58d97bc2f1389d8ca51f79b8bf8a025b7c6` |
| Workflow SHA-256 | `2b3d5bb04e9af2b086e06221a9687ae5323ab9306d40cb01f163db98a9945d7f` |
| Bundle SHA-256 | `b28ad8fdf21678b583458683c58d04ce7cb823c9dc08b7932b988f22aa54d57e` |
| Sole pushed ref | `refs/heads/publication-four-core-proof-2026-11-24-2130` |
| Job timeout | Ten minutes per attempt |

The job verifies the exact archive and evidence before its ordinary nonforce proof push. It rejects a different existing proof ref and skips the push if that ref already has the exact proof commit. Its before/after checks require that this job leave `main` and the verified continuation ref unchanged. The active publishing workflow will be removed after each observed run; its historical review text and actual receipts will remain as ordinary data.

After successful proof-object publication and independent readback, the already authorized ordinary connector updates will advance both requested branches and publish their resulting receipt commit. No mathematical source or frozen verification data changes are proposed.

## Why this request is necessary

The automatic reviewer rejected an additional execution even though the first run failed at GitHub's remote push. Its stated reason was that the previous approval covered one run and did not clearly authorize a retry. The exact rejection is preserved in `control/same-job-retry-response.json`.

Suggested explicit approval: “I approve up to three additional attempts of the reviewed publication procedure with contents: write, including any necessary temporary installation and removal.”
