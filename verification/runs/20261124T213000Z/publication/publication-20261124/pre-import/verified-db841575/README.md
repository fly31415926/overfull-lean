# Verified Lean checkpoint recovery archive

This data archive preserves the exact verified local checkpoint `db841575ca2c427e230387c1c95fa74bedb463d6`, with tree `a7e59e8303f670fab6c95348cd100acd1aaa5899` and sole parent `1c9404a454c99fe5c11ba8d774cb9c259f291f20`. The incremental Git bundle requires that baseline commit to be present in the repository used for restoration.

## Verification represented by this checkpoint

The committed `full-01` verifier and preservation check both passed. The archived result contains **14,820 audited declarations**, including **193 new declarations**, **2,840 completed-result mappings**, and **63 public proofs** in the reconstructed continuation. The full run froze **855 inputs** and **24 controls** and retained **26 verifier outputs**. Numbered assertion coverage is **51 of 69**, with exactly assertions **4.16** and **4.17** promoted from the 49-assertion baseline. The recorded main-theorem flag remains **false**.

[manifest.json](manifest.json) binds the exact committed terminal receipt, preservation report, frozen manifests, actual verification counts, bundle identity, and every part. The original successful and failed development evidence is included in the checkpoint's Git objects.

## Bundle identity

- Bundle size: **2,101,917 bytes**.
- Bundle SHA-256: `b28ad8fdf21678b583458683c58d04ce7cb823c9dc08b7932b988f22aa54d57e`.
- Encoding: **63 canonical base64 ASCII parts**, each at most **45,000 characters**.
- The original bundle passed `git bundle verify`. The recorded restoration check reassembled all parts, verified the reconstructed bundle with Git, and compared every byte with the original.

## Restore the exact checkpoint

Keep this directory's `manifest.json`, `restore-bundle.py`, and all `bundle.part-*.b64` files together. Use an existing clone containing the baseline commit, then run from this archive directory:

```sh
python3 restore-bundle.py --output /tmp/overfull-db841575.bundle --verify-repo /path/to/overfull-lean
```

The restorer checks every part's length, SHA-256, and Git blob SHA-1, then the complete decoded bundle length and SHA-256. The optional repository check verifies the prerequisite and exact bundle head. The restore command creates the requested bundle file and leaves repository refs unchanged.

To import the checked bundle deliberately into that clone:

```sh
git -C /path/to/overfull-lean fetch /tmp/overfull-db841575.bundle HEAD
git -C /path/to/overfull-lean show --stat FETCH_HEAD
```

The fetched commit must be `db841575ca2c427e230387c1c95fa74bedb463d6`. Publication of this recovery archive preserves the checkpoint independently of later updates to the requested source branches.

## Preparation evidence

The native bundle creation, verification, head inspection, and restoration receipts are retained in the `native-*` subdirectories. `committed-verification.json` records the immutable Git evidence inspected before bundling. `manifest-before-reassembly.json` is the exact manifest used for the recorded restoration check. The finalized manifest adds that successful check. `prepare-bundle-archive.py` is the exact preparation helper identified by the manifest.
