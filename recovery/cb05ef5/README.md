> **Historical recovery record.** The text below describes the partial recovery at commit `b31fc3219f6c764d173509912eb84a364edcdbef`. The current repository includes a later recreation and fresh verification; see [the reconstruction record](../../docs/checkpoint-reconstruction.md) and [current results](../../verification/results.json). The archive and inventory in this directory remain unchanged.

# Recovery of original cb05ef5 checkpoint files

This branch preserves original files recovered on 22 November 2026 after the working checkout and checkpoint archive became unavailable. **This is a partial recovery, not the complete cb05ef5 checkpoint.**

The requested checkpoint is `cb05ef5f5b7ef5ada4e535e9dcc652eecaddc43e`, with tree `e8a2de1dd1cf26d3454dd884ece6695a74a4780f`. Its original 566-file archive has not been recovered. The complete verified public baseline remains commit `a825b24b0dd0ad6edd336388c740530bcfb38d99` (46 of 69 numbered assertions).

## Recovered material

- All six new continuation Lean modules, each matching its recorded final SHA-256 hash.
- Three parent-checkpoint Lean modules and its root import file, each matching the recorded Git blob hash.
- The original assertion-47 checkpoint record and short verification logs, with their historical blob identities checked.
- The original continuation build and selector-check logs, recovered from complete raw file-read records.
- The complete recorded 50-file parent publication manifest and original README/verifier continuation patches.
- The recorded continuation source-map metadata and original supplied circuit note/checker. Their precise provenance qualifications appear in the inventory and evidence note.

The archive retains separate `checkpoint-c3dfd82` and `checkpoint-cb05ef5` directories so historical versions and evidence remain distinguishable. No missing proof or verification output has been invented or replaced with a claimed historical result.

## Remaining missing files

Eleven new parent-checkpoint Lean source modules remain unavailable. They are listed with their exact expected Git blob hashes and byte sizes in `recovery-inventory.json`. The complete final `verification/axioms.log`, `verification/results.json`, and other final checkpoint records also remain unavailable. Consequently, this recovered subset cannot establish or reproduce the complete cb05ef5 build.

The historical evidence describes earlier verification runs. No new Lean verification run is claimed by this recovery publication. The project source and verification files at the repository root remain those of the public baseline; recovery records are contained in this directory and archive.

## Files

- [Recovered original files](recovered-original-files.tar.gz)
- [Recovery inventory and missing-file identities](recovery-inventory.json)

The original archive identity, for future recovery, is `overfull-lean-cb05ef5.tar.gz`, 2,076,473 bytes, SHA-256 `67946e43d77fcbe67e0b3ea33c5771cfe425f78574c3ebe650290522f2e79da5`.
