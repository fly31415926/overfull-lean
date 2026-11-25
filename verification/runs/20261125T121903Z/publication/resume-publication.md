# Resume publication of the verified protected-trace checkpoint

The mathematical work and full verification are complete. Public publication was blocked by automatic approval review; no blob upload succeeded and no branch was updated. `authorization-review.json` and the retained rejection contain the actual outcome. Explicit user authorization for this newly verified checkpoint is the remaining publication requirement.

## Exact identities

- Repository: `fly31415926/overfull-lean` (public).
- Public baseline on both branches at the final readback: `f2510d10c114bcf3d0003b5e2e4e35cb0400167d`.
- Baseline tree: `58fe77f4afaba4b0ab6cf77956afb1c23608cd35`.
- Local verified proof commit: `c59d4d740bd3a66937e71ee6538216444e63383e`.
- Exact verified proof tree: `6d5ccce3895e186caaf0b85018c30cf1ffe5028b`.
- Local branch: `continuation-protected-traces-20261125T121903Z`.
- Public destination branches: `main` and `verified-bipartite-continuation-2026-11-21`.
- Full successful run: `verification/runs/20261125T121903Z/full-01`.

The local receipt-only successor preserves publication preparation, the review rejection, the rechecked authorization scope, and final frozen-file integrity. It changes no verified source, input, control, or output.

## Verification outcome

The strict build passed 3,930 jobs. The complete audit passed 15,162 declarations, including 168 new declarations and all 14,994 previous ones. There are 75 new public theorem proofs in 16 new modules. All 742 previous nonroot mathematical sources, 2,926 prior completed-result mappings, 23 prior declaration maps, and 69 numbered records are preserved. Coverage remains 51/69; the main theorem remains unverified. All 900 frozen inputs, 75 controls, and 29 generated outputs were rechecked against their archives after the rejection.

## After explicit publication authorization

1. Read the actual user authorization and the retained rejection. Do not treat an assistant-authored scope inference as a new user grant, or use an alternate upload route to bypass automatic review.
2. Read both public heads again. Retain expected-head leases; never force-update over another change.
3. The ignored `upload-data-proof/` directory contains a checked immutable snapshot of the exact proof tree: 248 changed paths, 160 unique new blobs, 151 inline blobs and 9 individual uploads. Its complete object identities and transport plan are retained in this directory. No individual upload has succeeded yet.
4. Upload the exact prepared bodies, checking every returned blob SHA. Create the tree with the baseline tree and prepared entries, and require the returned SHA to equal `6d5ccce3895e186caaf0b85018c30cf1ffe5028b`.
5. Create the public proof commit with baseline parent `f2510d10c114bcf3d0003b5e2e4e35cb0400167d` and the exact tree. GitHub may assign different author/time metadata, so the public commit SHA may differ from the local one. Preserve both identities.
6. Update both requested branches with non-force expected-head leases and read back the public commit/tree and both branch heads. Record the actual results.
7. Publish a receipt-only successor containing the actual publication records, preserving all verified source, input, control and output bytes. Read back both final heads.

If transport snapshots were lost but the Git objects remain, regenerate them from the exact staged proof tree with the supplied preparation helpers. The successful full run does not need to be repeated merely for receipt-only changes; any mathematical or frozen-input change requires a fresh appropriate verification gate.
