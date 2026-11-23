# Independent review of the exceptional-palette preservation checker

Reviewed `verification/runs/20261123T221916Z/record-final.py`, its actual preceding checker, the four current additive changes to `scripts/verify.py`, the current manifest generator, the full-verifier runner, and the real development command schemas. This was a read-only review; the full checker and full verification were not run. No repository file was modified.

## Resolved correction: the baseline import prefix contains blank lines

`check_root_imports` initially used `re.match(rb"(?:import [^\n]+\n)+", original)`. The actual pinned baseline root has blank lines between import groups. That expression stops at byte 953, immediately before `\nimport Overfull.Multigraph...`, so its following documentation-layout check would reject the legitimate baseline.

Replace that expression by:

```python
re.match(rb"(?:import [^\n]+\n|\n)*import [^\n]+\n", original)
```

Keep the existing requirement that the remaining bytes start with `b"\n/-!"`, and keep the exact expected-byte reconstruction and comparison. The corrected expression reaches byte 9941, after the last original import and before the original blank line and documentation. It permits only import lines and blank lines, preserves the complete original prefix, and does not permit edits to existing imports or documentation. It fixes a false rejection without weakening preservation.

`root-added-imports.json` had not yet been written during the initial check. Root subsequently applied the precise correction above, preserved the initial checker under `checker-initial/record-final.py` with a setup observation, and independently ran the three read-only setup gates successfully: four exact root imports, four additive verifier edits, and 89 archived files containing 23 genuine commands. The import-prefix issue is resolved.

## Preservation and verification gates

No additional blocking issue was found.

- The baseline commit and tree are pinned exactly to `1b5663a8fb472e42e698f4e09fcfc55497393815` and `ab2dd45502da57ea7dfb1db046a9efc9ab0cf067`.
- Independently reading the baseline result confirmed 12,559 declarations, 1,859 completed-result mappings, 548 source hashes, and 87 verification-input hashes. The constants used by the new checker agree.
- The read-only `check_verifier_extension` check passed: the current verifier is exactly the baseline verifier with the four declared additive exceptional-palette substitutions. Earlier gates are byte-preserved.
- Prior declaration names, module labels, and complete axiom sets must all be identical. The current raw audit records must equal the complete current result, with exactly one matching success marker and matching imported-module inventories.
- Every baseline file is required byte-identical except explicitly identified current outputs, the root import addition, README/handoff/verifier, and the coverage scope string. This preserves all preceding verification histories and their older checkers, including failures and correction records.
- The coverage exception is narrowly checked: every parsed field other than the single top-level `scope` string must remain identical. All 69 assertion records and all 47 completed records remain unchanged. Neither supporting theorem counts nor generated-declaration counts can promote a numbered assertion.
- The current full command must be the actual `python3 scripts/verify.py` execution in the current root. The latest attempt is selected by its recorded start time and must have passed with unchanged frozen inputs. The command, console, and frozen-input aliases must match that exact attempt byte-for-byte.
- Current source bytes, verifier input bytes, result hashes, and the frozen candidate hashes must all agree. The console is compared byte-for-byte with the concatenated actual four stage logs and the exact final verifier summary. A successful build marker alone does not establish success.
- The complete new declaration map is reconstructed from actual audited module assignments and bound to exact current source paths/hashes. Every explicit public theorem name and source line is independently recomputed from current sources. New completed-result mappings must be exactly the sorted new public-theorem mapping used by the verifier.
- The new-source inventory must equal all current mathematical sources minus the preserved baseline sources. The imported project module inventory must equal old imports plus exactly the new modules.

## Source mapping and diagnostic schemas

The independent lexical inventory parsed all ten current exceptional-palette modules and found 79 public theorem proofs. Its per-module counts were: EvenBudget 2, EvenColors 2, EvenNative 1, PairAssigned 3, PairColoring 11, PairExtension 15, PairFree 10, ReserveCopies 18, ReserveInsertion 16, and ReserveNative 1. This is a source-inventory observation, not a full Lean verification result.

The current development record formats are handled faithfully:

- Reserve: eleven command records, `output.log`, ordinary UTC start/finish fields, actual exit code, no original source-hash field. Retained source snapshots are required, and the checker explicitly records that their hashes were not in the original command metadata.
- Pair: seven command records, separate `stdout.log` and `stderr.log`, `started_at`/`finished_at`, actual exit code, no original source-hash field. Both streams are retained and hashed.
- Even: five command records, `output.log`, UTC timestamps, explicit passed/failed status, actual exit code, a source SHA256 string, and output SHA256. The recorded source and output hashes are checked against the retained bytes.

The checker does not synthesize missing original timing/hash fields. Each archived development file is checked against its inventory hash and, when the original scratch source still exists, against that source too. Files not listed in the development archive cause rejection. All existing diagnostic metadata filenames matched the supported `command.json` layout.

The previous checker's specific native-parent/import-order correction observations are not rerun as new work: their entire historical files remain byte-preserved under the pinned baseline. The new run must provide its own fresh full verification and audit records.

## Review conclusion

The import-prefix correction has been applied and its exact-root gate passed. Root started the complete `full-01` verification at 22:25:07 UTC with source and input files frozen; the full verifier and supplementary checker still determine the final verification outcome. No other correctness or preservation-gate defect was identified in this review. Reserve source modules remain frozen and unchanged.
