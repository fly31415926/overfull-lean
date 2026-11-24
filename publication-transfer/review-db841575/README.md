# Exact verified proof publication: inert review packet

**Approval is pending.** These files are proposed code and review evidence. They do not install or activate a GitHub Actions workflow. The helper's `--publish` path has not been executed. The proposed workflow is stored as `publish-verified-db841575.yml.txt` outside `.github/workflows/`.

## Actual approval boundary

The earlier attempt to add a write-capable workflow was rejected by automatic approval review. Its exact returned JSON is preserved in `actual-auto-review-denial.json`. The rejection stated:

> The tree would persistently add a GitHub Actions workflow with `contents: write` that executes repository code and pushes a proof branch, creating a durable privileged automation path; the user authorized publication of the proof data but did not explicitly authorize installing this persistent write-capable workflow or its security scope.

This packet does not bypass that rejection. No new authorization has been granted for a write-capable workflow. Publication of the archive and this inert packet remains ordinary data publication. Activating the proposed workflow requires a separate, explicit approval of its installation and repository-write scope after the archive and readbacks are complete.

## Exact proposal

The proposed job is restricted to a push in `fly31415926/overfull-lean`, on `reconstruction-four-core-2026-11-24-2130`, that changes `.github/workflows/publish-verified-db841575.yml`. It has a ten-minute timeout. Top-level token permissions are empty; only the publication job receives `contents: write`. The checkout action remains pinned to `11d5960a326750d5838078e36cf38b85af677262`, the pin used by the earlier proposal.

Repository `contents: write` is a repository-write permission. This would be a persistent workflow until removed or changed. The reviewed implementation constrains its actual write to one ordinary nonforce push of one hardcoded commit to the fresh proof branch. It rejects an already existing proof ref at a different commit and verifies the remote result. It does not run the Lean source or other repository scripts.

The helper path is `publication-transfer/review-db841575/publish_bundle.py`. Before executing it with `--publish`, the proposed workflow verifies this exact SHA-256:

`d3cbf3ef67e5020483dcb28fb57ae58d97bc2f1389d8ca51f79b8bf8a025b7c6`

The inert workflow text's SHA-256 is:

`2b3d5bb04e9af2b086e06221a9687ae5323ab9306d40cb01f163db98a9945d7f`

The approved activation, if later granted, would copy exactly the reviewed workflow text to `.github/workflows/publish-verified-db841575.yml` on the recovery branch. Its path-filtered push would then run the job. A normal activation commit is necessary; a CI-skip directive would suppress the proposed run. Merely publishing this packet or the archive does not match that active workflow path.

## Fixed object identities

| Item | Exact identity |
| --- | --- |
| Proof commit | `db841575ca2c427e230387c1c95fa74bedb463d6` |
| Proof tree | `a7e59e8303f670fab6c95348cd100acd1aaa5899` |
| Sole parent / prerequisite | `1c9404a454c99fe5c11ba8d774cb9c259f291f20` |
| Baseline tree | `087e26b5f004af1f9423a6f2b137d805f5991f1a` |
| Archive prefix | `publication-transfer/verified-db841575/` |
| Manifest SHA-256 | `7fac099d28d334ae8cb104dfd52a2e95533d40c515db310fbadb3cdc5949ec61` |
| Decoded bundle SHA-256 | `b28ad8fdf21678b583458683c58d04ce7cb823c9dc08b7932b988f22aa54d57e` |
| Decoded bundle length | 2,101,917 bytes |
| Part count | 63 |
| Only pushed ref | `refs/heads/publication-four-core-proof-2026-11-24-2130` |

Every part is checked for its exact name, number, byte length, SHA-256, and Git blob SHA-1. The helper requires canonical base64, the fixed decoded bundle hash, Git bundle verification, its sole exact advertised head, and the fixed proof tree and parent. The helper uses the finalized manifest's actual `commit`, `tree`, `parent`, nested `bundle`, and nested `verification` schema.

The exact committed terminal receipt, preservation report, results, actual full-run output, and frozen manifests are checked against the pinned manifest. The terminal must report the real `full-01` verification with exit 0, unchanged inputs and controls, and no wrapper errors. The preserved numbered-assertion scope must remain 51 of 69, with only 4.16 and 4.17 promoted and the main-theorem flag false.

## Separate source-branch publication

The helper does not advance `refs/heads/main` or `refs/heads/verified-bipartite-continuation-2026-11-21`. It reads both before and after the proof push and requires that their values remain unchanged during the job. Its receipt records those snapshots and lists these refs as later ordinary connector publication targets.

After the proof object is successfully published and independently read back, the already requested source-branch updates remain separate ordinary GitHub connector actions. They are not included in the workflow's push command.

## Preparation and verification already performed

The helper passed one default-mode run in a disposable local Git repository containing the exact prerequisite baseline. That run used the real 63 parts and finalized manifest, imported the local bundle, checked the committed proof objects and receipts, and exited 0. It made no network calls, did not use `--publish`, and did not publish a ref. The fixture's HEAD and refs remained unchanged, and it created neither an index nor FETCH_HEAD. The source project's HEAD, index hash, and ref hash were identical before and after this check.

The actual records are `offline-check-terminal.json`, `offline-verification-receipt.json`, `offline-verification.stdout.log`, and `offline-verification.stderr.log`. These are preparation records, not evidence of a public workflow execution.

Compared with the earlier proposal, this helper pins the manifest/proof/tree/bundle identities, uses the actual finalized archive schema and names, has an explicit publish flag and a guarded main entry point, disables network protocols during local verification, disables Git object replacement, rejects multiple push URLs, and suppresses automatic tag following on its only push.

## Receipts from a future authorized run

The helper would write `publication-transfer/publication-receipt-db841575.json` in the runner checkout and print its complete JSON in the run log, headed `OVERFULL_PUBLICATION_RECEIPT=`. It also writes the outcome to the GitHub step summary. The receipt contains actual subprocess exits and output hashes, evidence hashes, publication flags, and remote ref snapshots. It is not committed by this helper. A failure at any verification or publication gate returns a nonzero process exit.

`review-packet.json` records these exact identities, paths, scope, and pending authorization status in machine-readable form.
