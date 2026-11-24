# Publication receipt archive

This data-only packet preserves actual publication records for checkpoint `db841575ca2c427e230387c1c95fa74bedb463d6`, including the successful public restoration from recovery commit `c0c7c88e19a634f956027911beb11aa54e3d9674`.

**Cutoff: 2026-11-24T22:42:51.219994+00:00.** All selected paths and bytes were checked stable. Later receipts for uploading this archive are separate to avoid recursive archiving.

The compressed archive contains **498 original regular files** (8,722,633 bytes), plus its complete `inventory.json`. Successful, failed, denied, and unknown outcomes are preserved byte-for-byte. Proposed scripts and workflow text remain inert evidence; nothing archived is executed.

## Restore

Keep `manifest.json`, `restore-receipts.py`, and every `receipts.part-*.b64` file together, then choose a new directory:

```sh
python3 restore-receipts.py --output-dir /tmp/overfull-publication-receipts
```

The helper verifies every part, the full archive, the inner inventory, and every file before writing. It rejects links, unexpected/duplicate members, and unsafe paths, restores non-executable data files, and makes no network, Git, or subprocess calls. The inventory binds each relative path, byte count, SHA-256, and Git blob SHA-1.

## Scope and identity

`source-selection.json` lists the requested source sets and exclusions. The public clone, extracted public archive, restored bundle, and two raw cat-file body streams are excluded; their command/result receipts remain. Actual git ls-tree inventories remain as readback metadata. Readable status files and the inert review-packet upload receipts are included.

- Archive: **1,933,136 bytes**, SHA-256 `12585dba35a82feb94cdea7d37684b8610e6f7c49530835c80b3747c99406dc9`.
- Base64: **58 parts**, each at most **45,000 ASCII characters**.
- A single exact reassembly/member-inventory check passed; see `verification.json`.
- Tar file order, ownership, modes, and timestamps are normalized; gzip has no filename and a zero timestamp. Cutoff metadata is outside the compressed archive, so identical selected paths/bytes produce identical archive bytes.
- `preparation-01-failure.json` honestly records the initial missing-path collection failure and its resolution.

This packet preserves evidence and approval materials. It does not execute the proposed publication action or update either requested source branch.
