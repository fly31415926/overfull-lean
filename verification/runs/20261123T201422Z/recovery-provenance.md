# Native reserve recovery and fresh verification

This run continues the Overfull Conjecture Lean development from published
commit `98c6b228a997fead863d05041f12799c93fac18b` (tree
`1a3d5f43124a34de81c46a260d6c399fcecb5c96`). The original pinned Lean and
mathlib versions remain unchanged.

## Interrupted publication and available evidence

The preceding session actually observed a strict build of 3707 jobs and an
audit of 12424 declarations for run `20261123T125102Z`. Its publication was
interrupted before a complete commit or tree became reachable. The old
scratch sources and full command logs subsequently became unavailable.
Those observations are historical context, not verification evidence for
the reconstructed bytes in this run. Missing logs have not been recreated.

One exact original source was recovered from GitHub's blob store:

- `Overfull/NativeReserve/AcceptedRealization.lean`
- Git blob `cc2a6cfe008ae27da616a55e75c664abc0d182cd`
- SHA256 `c566a01ed8c8fc1dcb61ba9082b2f9f44d3afe46503913bc05a5a5b36e8b805b`
- Reachable source-only recovery commit
  `2eccf2a00df03c9a3c07f14fdbecd38087c8028d`

The other continuation sources are being reconstructed from the recorded
mathematical interfaces and available project sources. They require fresh
Lean checking. Source-only commits on `recovery/native-reserve-20261123`
preserve progress and do not claim that a complete verifier has passed.

## Fresh evidence

`baseline.json` records the actual starting commit, tree, and tracked-file
hashes. The command recorder snapshots the available continuation sources
before each real command and preserves its output and exit status.
Interrupted or running records must not be interpreted as successful checks.

The runtime archive was restored from the pinned Lean 4.24.0 release and
its bytes were checked against the recorded SHA256. The first dependency
cache attempt failed with HTTP 429 responses; its real log and exit code
are preserved. A retry lowers curl concurrency without changing project
dependency pins or proof sources.

The final verified branches may advance only after a fresh strict full
build, transitive axiom audit, source-map validation, and baseline
preservation checks for the exact final sources. Numbered coverage remains
47 of 69; the full two-core Corollary 4.6 and main theorem remain incomplete.
