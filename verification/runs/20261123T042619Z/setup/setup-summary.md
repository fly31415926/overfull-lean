# Runtime, dependency and prerequisite setup

This setup belongs to the continuation resumed on 2026-11-23 UTC after the
previous transient workspace was replaced. The recorded commands and logs
are fresh; missing earlier raw verification outputs were not reconstructed
from claimed success messages.

## Pinned runtime and sources

The official Lean 4.24.0 Linux archive was downloaded, its exact 459,625,674
bytes and SHA256 checked, and it was extracted successfully. The archive
SHA256 is `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.
The compiler reports Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release. Runtime restoration
completed at 2026-11-23 04:28:07 UTC; its actual commands, timestamps and
exit codes are in `lean-runtime-setup.json` and the corresponding logs.

All nine Git dependencies were fetched at the committed manifest revisions.
Their actual HEADs and clean tracked source status were checked, including
mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The ProofWidgets release
`v0.0.74` tag was fetched without changing its pinned source commit. The
stock Vizing setup script prepared and verified its pinned compatibility
port at upstream commit `c4fc77be6af1a48a44351234120898ad3cf6b545`.
No `lake update` was used and no tracked dependency source was changed.

## Actual cache failure and successful retry

The cache roots were the 73 direct Mathlib modules imported by the project
and Vizing; the complete linked cache contains 3,130 archives. The first
cache request used four parallel transfers and exited 1 after 156.158
seconds: 2,858 archives downloaded and 272 reported HTTP 429. That failure
is retained in `mathlib-cache-command.json` and `mathlib-cache.log`.

A missing-only retry used two parallel transfers, an explicit request-rate
limit of five per second, and ten seconds of initial backoff. It used the
same official cache and unchanged source revisions. It downloaded all 272
missing archives and unpacked all 3,130. The actual retry exited 0 at
2026-11-23 04:32:44 UTC after 43.297 seconds, including backoff. Its command
metadata and actual output are in `mathlib-cache-retry-command.json` and
`mathlib-cache-retry.log`. The failed first attempt remains a failure.

## Prerequisite builds

The strict shared-prerequisite build of `Overfull.CriticalMultigraph`,
`Overfull.CompatibleCircuits.Counting` and `Overfull.FourOdd.OriginalGraph`
passed 3,145 jobs, exit 0, in 41.992 seconds at 04:33:42 UTC. All three
compiled module outputs were observed before proof development resumed.

The larger existing-source build used the 224 explicit import targets from
`git show 28edc7b555d459b93a00d15258ca374abf5f0bb0:Overfull.lean`, excluding
the mutable current root and the new AssignedParts targets. It passed all
3,668 jobs, exit 0, at 2026-11-23 04:42:56 UTC after 544.730 seconds.
Its exact command, timings and actual output are retained in
`existing-prerequisites-command.json` and `existing-prerequisites-build.log`.
Every target compiled module output was observed. All nine dependency
HEADs and their clean tracked-source status were checked again after the
build. `environment-readiness-final.json` records those final observations;
the earlier readiness snapshot remains unmodified as historical evidence.

Complete candidate verification remains a separate required step through
`python3 scripts/verify.py`, including strict whole-library build and the
unchanged stock `Audit.lean`. Runtime installation, cache restoration and
these prerequisite builds do not supply that final verification evidence.

The dependency cache, installed runtime binaries and downloaded archive
are excluded from the public project checkpoint. This directory contains
commands, setup scripts, provenance and genuine diagnostic logs only.
