# Verified reconstruction: public preservation and remaining publication step

The full reconstructed checkpoint is publicly preserved and independently recoverable. The requested `main` and `verified-bipartite-continuation-2026-11-21` updates remain pending explicit approval of the reviewed GitHub Actions publication workflow.

## Exact verified checkpoint

- Reconstructed proof commit: `db841575ca2c427e230387c1c95fa74bedb463d6`.
- Tree: `a7e59e8303f670fab6c95348cd100acd1aaa5899`.
- Sole parent: `1c9404a454c99fe5c11ba8d774cb9c259f291f20`.
- Original requested checkpoint `6e1c25d84920aacd6ac52e4b19032ad8c6a2ac7d` was unavailable. This is a fresh reconstruction with its own actual successful verification, not a claim to have recovered that original commit.

The strict build passed 3,899 jobs. The stock kernel/axiom audit checked 14,820 declarations, including 193 new declarations across 25 new modules and 63 public proofs. Proposition 4.16 and Theorem 4.17 are complete. Numbered coverage is 51/69; the main theorem remains unverified.

The preservation checker retained all 14,627 prior declarations and their owners/axioms, all 2,777 prior completed-result mappings, every prior complete source/declaration map, and all 69 statement identities. All 855 frozen inputs, 24 frozen controls, and 26 archived verifier outputs match their recorded hashes. Historical successful, failed, and interrupted evidence remains identified as such.

## Public archive and independent recovery

[Archive commit](https://github.com/fly31415926/overfull-lean/commit/c0c7c88e19a634f956027911beb11aa54e3d9674) contains the [complete Git bundle archive](https://github.com/fly31415926/overfull-lean/tree/c0c7c88e19a634f956027911beb11aa54e3d9674/publication-transfer/verified-db841575) and 114 additional raw proof/evidence objects. The bundle contains all committed sources, documentation, declaration maps, frozen data, logs, and recorded path/environment metadata.

An isolated repository, starting only from the public baseline and without local object alternates, fetched the public archive, verified all 85 archive files and 114 raw proof attachments, reconstructed the 2,101,917-byte bundle, and recovered the exact proof commit, tree, parent, and all 14,692 tracked paths. Full strict Git object integrity checking passed. The actual report is `status-db841575/public-restoration.json` beside this document.

## Remaining authorization boundary

The large direct-upload route did not complete. Automatic approval review rejected the fallback write-capable workflow because the existing data-publication instruction did not explicitly authorize persistent privileged automation or its repository-write scope. The exact denial, reviewed helper, inert workflow text, local preparation receipts, and concrete approval request are in [review-db841575](review-db841575/APPROVAL_REQUEST.md).

The requested additional scope is to install the exact reviewed workflow on the recovery branch, run its hash-pinned importer with job-scoped `contents: write`, and remove the active workflow after the observed run ends. It can push only the exact proof commit to the fixed proof branch. The already requested updates to `main` and the verified continuation branch would then use ordinary nonforce connector updates, followed by publication and readback of the resulting receipts.

No active publishing workflow has been installed, and its publish path has not been executed. The raw ref readbacks and machine-readable status are in `status-db841575/`.
