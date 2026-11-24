# Verified reconstruction and publication evidence — 24 November 2026

The verified proof snapshot is commit `db841575ca2c427e230387c1c95fa74bedb463d6`, tree `a7e59e8303f670fab6c95348cd100acd1aaa5899`, with sole parent `1c9404a454c99fe5c11ba8d774cb9c259f291f20`.

This is the freshly verified reconstruction used for the requested continuation. The originally requested object `6e1c25d84920aacd6ac52e4b19032ad8c6a2ac7d` was unavailable. The reconstruction retains its own identity and genuine new verification records.

## Verification scope

The frozen full-01 verification completed successfully: 14,820 audited declarations, 193 newly audited declarations, and 51 of 69 numbered assertions complete. Assertions 4.16 and 4.17 were promoted. The main theorem remains unverified.

An independent fresh bare repository, initially without the proof object, fetched the exact public proof. The trusted snapshot validator passed all 855 frozen inputs, 24 controls, 26 archived outputs, and 1,563 nonpublication run files; it checked 1,810 explicit digests. All proof sources and frozen verification evidence remain identical in the publication descendants. Their additions are confined to this run's publication directory.

## Successful proof publication

The first run of the approved temporary workflow verified the archive but received GitHub's Internal Server Error on its proof push. The active workflow was removed. A subsequent retry was rejected by automatic approval review; that actual rejection is retained.

After the user explicitly approved up to three additional attempts, the first additional attempt succeeded. Workflow run 45506039249, attempt 2, job 138849283319 published the exact proof to `publication-four-core-proof-2026-11-24-2130`. Its genuine receipt records a successful push and exact proof-ref readback. No further retry was executed. Rerunning the historical job did not reinstall the active workflow on the current branch.

## Evidence directories

- `pre-import/` preserves all 213 historical transfer files, including the complete reconstructible proof bundle, earlier publication receipts, and the first failed run. Statements of pending, failed, denied, or proposed operations in those records describe their recorded stages.
- `approved-retries/` preserves the new explicit authorization, actual successful retry logs and receipts, and public API readbacks.
- `evidence-anchor-01/` preserves the actual publication and independent readback of the earlier 43-file failure-and-cleanup evidence commit.
- `public-proof-readback/` preserves the fresh public fetch and trusted snapshot validation. The complete large integrity report is retained losslessly with an explicit compressed archive manifest and restoration instructions.

Later branch-publication receipts record the actual checked commits and movements of `main` and `verified-bipartite-continuation-2026-11-21`. Each receipt identifies its observation time and exact commit rather than treating earlier historical statuses as current branch state.
