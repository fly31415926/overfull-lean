# Independent verification and preservation review

Reviewed by the `three_core_composition` agent on 2026-11-24, independently of the root agent's verifier integration. This review covers the run-local recorder and preservation checker, and the exact diff of `scripts/verify.py` against published baseline `14978e4dec2bce94f63953df7b1bdd54f61c3e6c` (tree `c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767`). It does not replace the actual full build or kernel axiom audit.

## Baseline and stock-audit preservation

The read-only preflight reproduced the baseline counts of 13,675 audited declarations, 2,396 completed-result mappings, and 741 frozen inputs. Every previously frozen mathematical source and `Audit.lean` remains byte-identical. The root file adds only the three recorded imports. The new manifest covers all 34 new source modules.

The verifier diff contains exactly five reviewed modifications: the completed count changes from 48 to 49; the new source manifest is registered; its exact single-core closure identity is guarded; its declaration-map basename is registered; and its declaration-map evidence is included in the result. The original full `lake build --wfail` and `lake env lean Audit.lean` commands remain. The original imported-module inventory, prohibition on project axioms, and transitive kernel-axiom audit remain. The permitted axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

The final preservation checker still requires every old declaration to retain its name, owning module, and axiom set, every previous completed-result mapping to remain identical, and every previous source/declaration map to retain its metadata and bytes. It also requires all 69 numbered statement identities to remain unchanged, exactly the promotion of Lemma 3.1, all other 68 numbered records to remain identical, and `main_theorem_verified` to remain false. These are final-run acceptance conditions; this review does not assert that the full run has already satisfied them.

## Concrete gaps found and fixed

The initial checker validated archived outputs but then read live result and declaration-map files without binding those live files to the recorded successful command. It also did not require principal outputs, verify the raw command-output hash, compare terminal and command receipt bytes, or independently validate the complete control inventory. The initial recorder froze only Python scripts and could leave no terminal failure record if preflight or execution raised an exception.

Changes are confined to `run-verifier.py` and `check-preservation.py` in this run directory:

- Successful full execution must include `verification/results.json`, `verification/build.log`, `verification/axioms.log`, and `verification/global-factorization-declarations.json`. Every listed output, including additional logs and declaration maps, must match both its live and archived byte count and SHA-256 digest.
- The raw `output.log` must match the recorded digest, and `terminal.json` must be byte-identical to `command.json`.
- The receipt must record an actually launched verifier, successful preflight, actual child exit zero, wrapper exit zero, no wrapper exceptions, no missing principal outputs, and unchanged full input and control inventories. Input and control snapshots are checked against their recorded hashes and the current live files.
- Controls include the three recorder/checker Python files, the exact verifier-edit and root-import JSONs, the pinned Lemma 3.1 excerpt and metadata, the complete development index, all independent review notes, and the verifier diff. Added or removed matching control files invalidate the freeze.
- Preflight validates the development index's exact file inventory, every recorded byte count and digest, every attempt summary, and every source snapshot. The final preservation check repeats this preflight.
- The recorder creates an attempt receipt before preflight. Caught preflight, launch, execution, or evidence-collection exceptions produce a failed terminal receipt with the actual child exit when available and `null` when no child ran. Exception tracebacks are separate from the raw child output. Interrupted live child processes are stopped as a process group. A zero child exit cannot override missing outputs, changed inputs or controls, or recorder errors. This is best-effort exception recording, not a guarantee against power loss, hard process kill, or an unwritable filesystem.

## Honest development evidence

The exact development inventory contains 55 genuine attempts and 1,258 files, with 39 recorded failures and 16 exit-zero passes. Fifteen attempts recorded concurrent input changes; their exact changed-path lists remain in the original receipts and index. Two of those attempts exited zero: `auxiliary-simple-completion-04` and `four-odd-theorem-02`. Their original statuses are retained as subprocess results, not treated as acceptance of an unchanged final tree. The final full-run acceptance condition requires unchanged inputs and controls. The successful focused `auxiliary-simple-single-05` run records no changed inputs.

## Validation of the fixes

Python syntax checks passed for both run scripts and the unchanged-by-this-review `scripts/verify.py`. The actual repository's read-only preflight passed, including all baseline, coverage, source-manifest, root-import, and development-evidence checks.

Temporary fixtures outside the repository exercised the receipt checker. The unchanged fixture was accepted. Sixteen mutations were rejected: changed live principal output, changed archived principal output, changed live additional output, changed archived additional output, changed raw command output, differing terminal receipt, changed live control, changed archived control, added control, changed frozen-control index, changed source snapshot, changed live input, missing principal output, duplicate output path, a false controls-preserved flag, and a recorded wrapper exception.

Four temporary runner fixtures exercised real Python subprocess behavior without running Lean or the repository verifier. A preflight exception produced child exit `null`, wrapper exit 1, and a failed terminal. A child exiting 7 retained actual exit 7 and wrapper exit 7. A child exiting zero without the principal output set produced wrapper exit 1 and a failed terminal. A complete, unchanged fixture produced child and wrapper exit zero with identical terminal/command receipts and the correct raw-output hash. All fixture files were confined to temporary directories and removed afterward.

No full repository verifier or Lean build was launched during this verification-script review. The root agent must run the actual frozen full verifier and then the preservation checker before treating the continuation as release-verified.
