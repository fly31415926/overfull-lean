# Independent review of the proposed Git-bundle publication transport

Reviewer: infrastructure/recovery agent, distinct from the original publication-helper author. Reviewed on 2026-11-24T21:45:49.347878+00:00.

## Authorization state

Automatic approval review rejected installing the persistent repository workflow with `contents: write`. This review does not authorize installation or execution. The proposed helper and workflow remain local review material. No remote workflow write or alternative execution path was attempted by this reviewer. Ordinary data publication and the mathematical verification remain separately authorized.

## Purpose and publication boundary

The proposed job reconstructs the exact native Git bundle from bounded text chunks, validates its SHA256 and each part's SHA256 and length, verifies the bundle prerequisites, and fetches only the advertised `HEAD`. The bundle must therefore be created with `HEAD` advertised, for example `git bundle create proof.bundle HEAD ^<baseline>`.

The helper validates the fixed repository, transfer branch, proof branch, baseline commit, exact fetched proof commit, exact tree, and single parent. It does not check out or execute the transported proof commit. It pushes only the separate `publication-four-core-proof-2026-11-24-2130` branch with a normal non-force push and verifies that ref afterward. It does not advance either requested publication branch. Root must independently fetch and verify the published bytes before the separately authorized lease-checked updates of `main` and `verified-bipartite-continuation-2026-11-21`.

The workflow has a fixed transfer-branch and manifest-path trigger, so installing only the helper and workflow without the manifest would not intentionally start this publication job. The proposed transfer-only Lean workflow limits its push trigger to the two requested publication branches; it is not part of the final mathematical proof tree. The stock workflow inside the proof snapshot remains unchanged and is frozen as a verifier input.

## Concrete validation issue found and corrected locally

The initial helper required the preservation report to equal the manifest's embedded report but did not independently require that report's verdict to be passed. Equality alone could accept an accidentally selected failed report. The local helper now explicitly checks the successful preservation status, actual full-verifier exit, exact baseline, exact full-run attempt, matching terminal-receipt hash, preservation of all prior declarations/mappings/maps, 51 of 69 coverage, only 4.16/4.17 promoted, every statement identity unchanged, and main-theorem status false.

The local terminal gate also now requires the exact verifier command, attempt, baseline/tree, actual launch and successful preflight, zero child and wrapper exits, unchanged inputs and controls with empty change lists, no wrapper errors, and no missing principal outputs. It compares terminal and command bytes and independently hashes the raw full-run output. These checks supplement the exact bundle/commit/tree hashes and do not manufacture an execution verdict.

## Independent fetched-commit verifier

The new `verify-published-snapshot.py` reads immutable fetched Git objects without executing source code from the commit. It checks exact commit/tree/single parent, regular blob modes and Git object hashes, every frozen live input and its archived copy, every frozen control and its archived copy, every generated output and its archive, the complete verifier-input path set, the exact full-run terminal and preservation relationship, and the entire non-publication run inventory against preserved local evidence. It also compares the full verifier's input map and audited count to the frozen manifests and preservation report.

Publication receipts are appendable and are excluded from the immutable non-publication run comparison. The checker requires a fresh output path so an existing success report is not overwritten. Use it only after an actual public fetch; the fetch and remote-ref readbacks must have their own genuine receipts.

## Validation performed and remaining boundary

Both Python files parsed successfully. The workflow and helper were reviewed statically. No live workflow, privileged job, synthetic verification receipt, remote push, or remote branch change was used to test this proposal. Final binding to the actual successfully verified commit/tree and actual bundle/receipt hashes must be reviewed when those values exist. A concrete approval is still required for the previously rejected workflow installation and execution scope. This review does not certify that GitHub Actions permissions or repository policy will allow that execution.

## Reviewed file hashes

| File | Bytes | SHA256 |
|---|---:|---|
| `publish_bundle.py` | 9431 | `fd9fbe137dd79c48f902055a0f97d730eb44624c06f2943e88e85611de01ace9` |
| `publish-checkpoint.yml` | 513 | `a35ebcc7b92ded28535fd3281cacc08250fbf898c30c32314761014263039a16` |
| `lean.yml` | 1327 | `21d00d077e3ec11fe608bf9a5f4ed9f8e2e3279b8e27dfcb36578c6dc3fc09a0` |
| `verify-published-snapshot.py` | 11557 | `d4897d2578d11b1e8bfa7f4d130a08034ddca7b3d95ea285d55f5cc883b73852` |
