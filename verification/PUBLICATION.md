# Publication of verified checkpoint 75759f81b198

This publication preserves the mathematical sources, documentation, source and declaration mappings, and original axiom audit of local checkpoint `75759f81b1985413f494215f533e23642d5f7101`. Its original audited Git tree was `5afb50b64f0c361563d3a5d1ed39dc0e9efa1fcb`.

## Artifact identity

The original checkpoint contained 472 tracked files. The publication preserves 471 of those files byte-for-byte, including all 423 Lean source files and all 43 inputs hashed by the verifier. One original output, `verification/build.log`, was unavailable after the temporary working directory disappeared during upload. It is replaced with the complete build output from the GitHub verification run described below. The original short build timing log has not been reconstructed or represented as recovered.

The published tree therefore differs from the original audited tree. Four additional files record the publication and fresh verification: this note, `publication-recovery.json`, `github-actions.log`, and `github-actions-run.json`, all in `verification/`. The actual published tree is recorded in the publication commit message; it is not embedded in this file to avoid a self-referential hash.

| Artifact | Preservation and provenance |
| --- | --- |
| All mathematical sources, documentation, and verification inputs | Exact original Git blob identities. The complete 472-file original inventory in `publication-recovery.json` reconstructs the recorded original Git tree. |
| `docs/source-recovery.json` | Exact original provenance report, including source-file identities and 1,214 historical proof/declaration mappings. |
| `verification/axioms.log` | Exact original combined audit log; Git blob `7a211698812eaac1392c380869202f905087196e`. |
| `verification/results.json` | Exact original report recovered deterministically from the preserved audit, verifier, source data, and unchanged parent data. Accepted only after its byte size, Git blob hash, and SHA-256 matched the recorded original values. |
| `verification/build.log` | Complete, genuine build output extracted from the fresh GitHub run. This replaces the unavailable original 2,518-byte log, whose Git blob was `3a84f9d9b83715be66cbd59d79d8dfcb5f947edc`. |
| `verification/github-actions.log` | Complete decoded job log for the fresh GitHub run, preserving its timestamps and runner output. |
| `verification/github-actions-run.json` | Run and job identities, tested commit, completion status, extraction details, and log hashes. |

The recovered original report is 2,490,040 bytes. Its Git blob is `e640d9f3713c98e3b9a3a01729dde8cd91aa0772`, and its SHA-256 is `645d2b3e3b16aa7095994500958d1fce9b9e25eef4ab689dd56a31e75c85b5b3`.

## Verification

The original strict build completed 3,593 jobs. Its transitive audit checked 10,219 declarations across 422 imported project modules and 25 Vizing modules, accepting only `propext`, `Classical.choice`, and `Quot.sound`. It recorded 423 source hashes and 43 verification-input hashes. The pinned toolchain is Lean 4.24.0, and the mathlib revision is `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The fresh verification is [GitHub Actions run 45047705487](https://github.com/fly31415926/overfull-lean/actions/runs/45047705487), job `137285817164`, on recovery commit `b26c6b4bc5bd2f71500c11496d4b73f5c18316d4`. It runs the unchanged `scripts/verify.py`, including `lake build --wfail` and the complete transitive axiom audit. The final publication contains the same source and verification-input files as that tested commit. The additional publication files and verification outputs are outside the verifier's source/input hash inventory.

The fresh run completed successfully, including the strict build and complete transitive axiom audit. The committed original report and axiom log retain their original byte identities; the new build log and full GitHub transcript provide separately identified rerun evidence.

The wording in the original `docs/source-recovery.json` about not reusing old success reports describes the original combined verification relative to the two pre-merge parents. The committed `results.json` and `axioms.log` here are the exact artifacts of that combined verification. The fresh rerun is additional evidence, separately identified above.

## Formalization scope

The completed inventory remains **44 of 69 numbered assertions**. The main theorem remains **unverified**. The alternate proof of Lemma 4.13 is counted once, and the supporting components of Lemma 4.15 do not make that lemma complete. The criticality-to-average-degree input, complete spanning setup, absorber construction, and full factorization are still open.

Both prior public histories are retained: main commit `54db7b826be05fbba9845f4140aaba0a7db5ba04` and continuation commit `2eb61f588a26b3fe41edcf0bcec8610c9c343dd8`.
