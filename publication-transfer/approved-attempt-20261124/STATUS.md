# Approved publication attempt: verified payload, remote push failure, cleanup completed

The explicitly approved temporary publication workflow ran from recovery commit `020bbd8d1ef2ccc17c933680cfdc5f25ad443a1b`. Its checkout, exact helper digest check, complete bundle verification, and committed proof-evidence checks passed. The fixed proof-ref push failed because GitHub returned `Internal Server Error`.

- Publication run: https://github.com/fly31415926/overfull-lean/actions/runs/45506039249
- Publication job: `138841412903`.
- Fixed proof: `db841575ca2c427e230387c1c95fa74bedb463d6`.
- Fixed proof tree: `a7e59e8303f670fab6c95348cd100acd1aaa5899`.
- The actual publisher receipt reports `archive_verified: true`, `proof_ref_push_attempted: true`, `proof_ref_push_completed: false`, and `proof_ref_published: false`.

The active workflow was then removed by cleanup commit `bdbdb217bf3e1fb0724712fa141546e4c2ae00ff`. Its tree is exactly the preactivation recovery tree `5a480bf90e7da01eca2a6e7e0f3ecf8438a6b967`. The original approved helper and workflow text remain preserved as inert review data.

Readbacks after cleanup found the proof branch absent and the proof commit/tree unavailable through GitHub's Git data API. A bounded data-only tree construction also reported that the new results blob `05dcb9fa57b9acddcbfcb76f516926cf12386dcb` was unavailable, so the failed push did not leave the missing raw objects usable for ordinary API publication.

The proof remains completely recoverable from the already public bundle archive. Its prior strict Lean verification, 14,820-declaration audit, preservation check, and independent public restoration remain successful. The main theorem remains unverified; numbered assertion coverage of the reconstructed proof is 51/69.

The separate Lean workflow on the recovery activation tree failed its source inventory check for 23 excluded modules. That recovery-tree job is distinct from the successful frozen `full-01` proof audit and from the approved object-publication job. Both actual job logs are preserved here with their scope identified.

## Retry boundary

A single retry of the exact failed publication job was requested after the GitHub server error. Automatic approval review rejected the retry, treating the user's prior authorization as covering one run and requiring explicit permission for another privileged execution. No additional publication job was executed by that rejected call.

Both `main` and `verified-bipartite-continuation-2026-11-21` remain at `1c9404a454c99fe5c11ba8d774cb9c259f291f20` at the recorded readbacks. The reviewed procedure can continue after explicit retry approval; see `RETRY_APPROVAL.md`.
