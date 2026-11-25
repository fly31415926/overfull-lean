# Exact staged-tree publication helper

`prepare-upload.py` reads the local Git index and object database and writes only
beneath this directory. It does not stage files, create commits, update refs, or
contact GitHub. Run
`prepare` only after the intended proof snapshot has been staged. Generated
`upload-data*` directories are ignored so a subsequent broad `git add` cannot
accidentally add duplicate binary payloads to the proof tree.

The default baseline is `ac05c3232425399af6c0f29e1f7d3ddc1037424d`.
The helper computes the exact index tree, inventories only objects absent from
the baseline tree, checks blob hashes, and exports immutable payload copies.
Its Git tree calculation writes no objects into `.git`.

From the repository root:

```sh
PUB=verification/runs/20261125T002000Z/publication
python3 "$PUB/prepare-upload.py" prepare --output "$PUB/upload-data-proof"
python3 "$PUB/prepare-upload.py" list --snapshot "$PUB/upload-data-proof"
python3 "$PUB/prepare-upload.py" read --snapshot "$PUB/upload-data-proof" --sha SHA --encoding base64 --offset 0 --limit 4000
python3 "$PUB/prepare-upload.py" check-index --snapshot "$PUB/upload-data-proof"
```

For each listed blob, concatenate successive `content` chunks, requiring the
reported `offset` to equal the previous `next_offset`, until `done` is true.
Pass the assembled string to the GitHub `create_blob` connector with
`encoding: "base64"`. Require its returned SHA to equal the manifest SHA before
continuing. UTF-8 reads are also available for text files and reject invalid
UTF-8. Chunk offsets count characters of the selected representation.

The `conventional_git_object_base64` representation additionally prefixes the
body with `TYPE SIZE` and a NUL byte before base64 encoding. It is returned in a
field of that exact name. This is useful for independently checking Git object
identity; it is **not** the payload expected by GitHub `create_blob`.

After all new blobs are present, `root-tree-request.json` supplies a single
GitHub `create_tree` request with the original base tree and exact staged path
changes, including deletions. Require the returned tree SHA to equal
`manifest.json`'s `expected_tree`. `tree-requests.json` provides equivalent
child-before-parent requests if explicit individual-tree creation is needed.
Every newly required tree's actual bytes, SHA, byte length, and paths are also
recorded. Unchanged baseline objects are reused.

Before creating a commit or updating either branch, run `check-index` again and
perform the independent source-preservation and verification gates. Use the
current remote branch SHA as the expected ref value; this helper does not infer
or claim remote state. If the index changes, create a new named output directory
and a new snapshot. Existing snapshots are never overwritten.

Publication receipts can be added in a later commit; its preparation should use
the actual preceding published commit as `--baseline`. Do not stage generated
payload directories. The payloads are transport copies of objects already
included in the prepared tree, not additional mathematical sources or logs.

## Larger bounded transport chunks

`read-upload-chunk.py` reads the same immutable snapshots without changing the
original preparation helper. It validates the full payload against its Git
blob SHA-1, SHA-256, and byte length, and emits base64 body chunks of at most
128,000 characters (64,000 by default). Use `--snapshot`, `--sha`, `--offset`,
and `--limit 128000`. For these larger chunks, request
`exec_command` `max_output_tokens: 100000`. Parse each returned JSON object
inside the orchestration call and reject invalid/truncated JSON, a nonzero exit,
a mismatched SHA, an unexpected offset, or an inconsistent total before
concatenating its `content`. Print only small progress metadata. Require the
final `create_blob` response SHA to equal the expected SHA.

The read-only check reassembled an existing 1,907,574-byte frozen archive from
20 such chunks with exact byte equality. A real 128,000-character chunk also
passed the `exec_command`-to-functions JSON transport without truncation; the
receipt is `wide-chunk-readonly-check.json`.
