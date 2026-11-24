# Independent public proof readback: exact evidence archive

This archive preserves all 41 requested top-level JSON/log files from the completed independent public readback, totaling 2,514,898 original bytes. The regular source records and logs retain their exact bytes. The large integrity snapshot, full path listing, and binary Git-tree output are preserved losslessly as deterministic gzip data split into canonical base64 ASCII parts of at most 45,000 bytes.

`readback-summary.json` is the original completed readback summary. `snapshot-integrity-summary.json` is a clearly labeled generated derivative excluding the 1,810-entry `checks` array for readability. The complete unmodified `snapshot-integrity.json`, including every check, is recoverable from the encoded archive. Its original SHA-256 is `d044ac187c1c630a34c185f36eb86e5b39b89be88c6f8bd10cbebddebeb99baa`.

The native readback starts, terminal records, empty outputs, and actual stderr are all retained. In particular, the expected proof-absence check's exit 128 and diagnostic output are preserved. This package performs no proof rerun and creates no commit, ref, workflow, or remote execution path.

## Restore the exact originals

Keep this directory and its `encoded/` subdirectory together, then run:

```sh
python3 restore-evidence.py --output-dir /tmp/restored-public-proof-readback
```

The restorer checks the fixed manifest SHA-256, every original file's byte count/SHA-256/Git blob SHA-1, each encoded part, the joined base64, and the compressed gzip bytes before writing the exact original filenames. It also verifies canonical base64, the declared deterministic gzip header, and the derived summary's hashes. Existing destination files are refused.

Manifest SHA-256: `444c4cea13e0cf6913e95bfd37bd32c6bd8d837f3b667c53cc457aef65b9f4a0`.

Restorer SHA-256: `b8f841ee9cc9bc42afd19c8739581fa33092e1f7af7dd656bbb50f9264825fa7`.

The archive manifest identifies readable originals versus encoded originals and explicitly records all original, compressed, encoded, and part sizes and digests. No generated summary is presented as raw validator output.
