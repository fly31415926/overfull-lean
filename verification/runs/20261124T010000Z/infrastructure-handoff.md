# Current-run verification infrastructure

These scripts were prepared without launching a full build, audit, input freeze,
commit or publication. The live mathematical sources, root imports, documentation
and source-manifest generator are owned by the integration lead.

## Candidate preparation

`prepare-docs.py` writes only this run's `docs-draft/` files and draft metadata.
Its manifest inventory is recomputed from all actual sources in `NativeWeighted`,
`NativeAssembly` and `NativeCore`; it is not a verification result. Its exact scope
is read from the live manifest generator. Rerun it after source scope stabilizes:

```sh
python3 verification/runs/20261124T010000Z/prepare-docs.py --archive-development
```

The additional flag records all genuine focused-command receipts, source snapshots
and full logs in `development-archive.json`, under the common build lock. No
attempt is discarded. It does not copy drafts into live docs, edit the root,
generate the live source manifest or invoke Lean. Finish those integration actions
separately. The checker expects the exact appended root import list in
`root-added-imports.json`, including newline characters, and the live manifest at
`docs/native-integration-source.json`.

## Attached full verification

Only after all source, documentation, root and manifest inputs are stable, run:

```sh
python3 -u verification/runs/20261124T010000Z/supervise-verifier.py full-01
```

Await this actual process through its terminal exit. The supervisor emits genuine
observations every 30 seconds. It neither detaches the child nor infers completion
from log presence. Each full attempt gets a new immutable directory; use `full-02`
if a later actual attempt is required. The full command remains exactly
`python3 scripts/verify.py`, under the pinned Lean 4.24.0 runtime. It retains the
unchanged strict build and full original audit gates.

Before starting, the wrapper checks the exact local baseline commit/tree, 2,752
tracked files, 12,951 audited declarations, 2,063 old completed mappings and all
670 original frozen input hashes against committed bytes. Only the five reviewed
source/input changes (root, README, handoff, verifier and coverage scope) are
allowed among those original inputs. The supplementary checker later verifies
the exact form and scope of every allowed edit.

Every frozen input is copied under `full-NN/input/` using its repository-relative
path. New Lean sources are also copied under `full-NN/source/`. The actual command
receipt records hashes, true timestamps and the observed child return code. Every
fresh verifier log/result/declaration map is retained under `full-NN/artifacts/`.
The complete audit log is additionally split into exact contiguous byte segments;
its manifest records offsets, lengths and hashes. The supplementary checker
reassembles these bytes and compares them to the complete raw log.

Do not edit frozen inputs during this full attempt. The wrapper records any
changed/missing/added input and will not report such a run as passed.

## Supplementary verification and local package

After the supervisor's actual successful terminal receipt:

```sh
python3 verification/runs/20261124T010000Z/record-preservation.py preservation-check-01
python3 verification/runs/20261124T010000Z/package-verified.py
```

The preservation recorder captures the actual checker output outside the run
while the checker hashes its evidence; only after it returns does the recorder
retain the command/output and their supplementary hash receipt. Failed checker
attempts are retained under separate names. Success is never reconstructed from
an old report. After a successful supplementary freeze, do not regenerate drafts,
rewrite run scripts or alter checked evidence before packaging.

The package script rechecks every frozen/evidence hash and the observed supervisor
and checker exits, then commits the exact local continuation and makes a full Git
bundle and ZIP. It verifies the bundle and every committed ZIP blob. It performs
no network call or branch publication. The exact tree and local checkpoint are
recorded in the release manifest. Public publication remains a separate operation
subject to the retained automatic-review decision and independent remote readback.
