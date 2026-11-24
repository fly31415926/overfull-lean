# Final independent audit review

**Result: passed; no blocker found.** The `full-01` build, kernel audit,
declaration preservation, source mapping, and frozen-byte evidence agree.
This review used independent read-only hash and record comparisons. It did
not rerun Lean, execute the preservation checker, or change frozen inputs.
The companion `final-audit-review.json` records 335 successful checks.

## Actual execution evidence

The inspected `full-01/terminal.json` and `command.json` are byte-identical.
They record the actual command `python3 scripts/verify.py`, verifier exit 0,
wrapper exit 0, passed preflight, no wrapper errors, and a finished timestamp
of `2026-11-24T14:20:27.043832+00:00`. The raw command-output hash matches the
receipt. Its contents include the archived build, axiom, Lean-version, and
Vizing-source logs.

The frozen verifier still executes `lake build --wfail` followed by
`lake env lean Audit.lean`. The build log reports successful completion of
**3,874 jobs**, with no warning/error diagnostic found. The raw audit contains
exactly **14,627 distinct theorem records** and one matching
`OVERFULL_AXIOM_AUDIT_OK 14627` marker. Parsing those raw records independently
produces exactly the names, owner modules, and axiom sets in `results.json`.

The stock `Audit.lean` is byte-identical to baseline. Its environment scan
rejects project axioms and checks transitive dependencies of every theorem
owned by the imported Overfull and Vizing modules. Every audited dependency
set is contained in `{propext, Classical.choice, Quot.sound}`.

## Independent preservation and coverage comparisons

The baseline was read directly from git commit
`3991bb7eee091a329046073e0366daa84a603e5d`, tree
`6424bf81123aa75b2254aea7eceff6260611f397`.

| Checked item | Independent result |
| --- | --- |
| Previous 14,260 audited declarations | Every name, owner module, and axiom set preserved |
| Previous 2,609 completed-result mappings | Every key and mapped declaration preserved |
| Previous 19 declaration maps | Metadata and complete map bytes preserved |
| Previous mathematical sources and stock audit | All unchanged; root differs only by the two recorded imports |
| Verifier | Exactly the four recorded additive registration edits |
| Numbered coverage and manuscript inventory | Byte-identical to baseline; all 69 records retained |
| Coverage claims | 49/69 complete; main theorem remains unverified |

The current completed-result table has 2,777 entries. Its 168 additional
entries map exactly to the new manifest's 168 public proof declarations.
No numbered assertion was promoted.

## New source and kernel-proof map completeness

The **28 new Lean modules** are exactly the mathematical source additions
relative to the baseline inventory. Their manifest paths, module names, and
SHA-256 values match the frozen files. All 168 public declarations have the
recorded source location, expected owner, and actual kernel-audit record.

The new declaration map equals the complete set of audited theorems owned
by those 28 modules, and also equals the complete difference between the
old and new audited-name sets: **367 declarations**. This verifies coverage
by module ownership rather than filtering names by public syntax. It
includes the 168 public proof declarations and **199 additional kernel
proof declarations**, including generated equations and support lemmas.
There are no new `_private.`-prefixed declarations in this particular run;
the complete ownership comparison would include them if present.

Every map entry has the correct frozen source path and source hash, and
every new module occurs in the map. The actual audit imports exactly the
**702 project modules** determined by the complete source inventory, plus
the recorded **25 external audited modules**.

## Frozen bytes and genuine development receipts

Independent SHA-256 recomputation confirms all of the following:

- **826 inputs**, comprising 703 Lean source/audit files and 123 other
  verification inputs, match both their live files and frozen archive.
  Their inventory equals the union of the two input tables in `results.json`.
- **17 controls** match their live files, archived copies, frozen-control
  manifest, and terminal receipt, with no missing or added control.
- **25 recorded outputs** match their live files, archived files, receipt
  hashes, and byte lengths. The output archive has exactly those files.
- The preservation report's receipt hash identifies the inspected genuine
  command receipt.
- All **1,252 development-evidence files** match their recorded hashes and
  sizes. All **81 command receipts** retain matching output and recorder
  hashes and source snapshots: **40 passed, 41 failed, none interrupted**.

Fourteen focused development attempts truthfully record source changes
during their execution. Those records remain visible and were not rewritten
as unchanged-input runs. They are historical development evidence; the
finished whole-project run independently verified the final 826-input
snapshot with no input or control changes.

## Receipt identities and scope

The command/terminal receipt SHA-256 is
`18f27dde12dd0388d9bdf2af4c34410ed20c625f50fcdc1fec022db543a56a0d`.
The inspected preservation report SHA-256 is
`adf1cb8b9acb301f8ddd0f52c1edc44ba3ec8d914e6d59172fb76e24fb554a5f`.

The evidence supports proceeding to the snapshot commit without another
Lean run. This review establishes the local frozen verification result;
publication and remote branch identity require their separate subsequent
receipts. Only this analysis document and its JSON companion were written
for the final audit review.
