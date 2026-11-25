# Successful publication of the ordinary-core checkpoint

The authorized proof snapshot is public at commit
`fffee212de70f2a4c7eb988b9453f5d4a90a4445`.
Its complete tree is `fad7fbd161680326be5c4a7834d37cfa89ec096b`, exactly the
tree of the approved local checkpoint
`339c69d356a8bd4c4945afec085af1f794da5c4a`. Its sole parent is the original
public baseline `ac05c3232425399af6c0f29e1f7d3ddc1037424d`.

GitHub created the public commit with its own commit metadata, so the public
commit identifier differs from the original local identifier. The source
bytes and paths are identical. `original-local-commit.txt` retains the exact
original commit object body, whose Git object hash is the approved local ID.

Both requested branches, `main` and
`verified-bipartite-continuation-2026-11-21`, were updated without force using
the expected old head. GitHub ref reads and an independent native Git read
then confirmed both branches at the public proof commit. Those actual update
and readback responses are retained beside this document. This directory is
added separately as publication evidence after the exact proof snapshot.

## Verification remains intact

The full strict build passed 3,901 jobs and the transitive audit checked
14,830 declarations. All 14,820 previous declaration records and 2,840 previous
result mappings remain intact. Four public proofs and six generated proof
declarations were added in two modules. All 861 frozen inputs, 17 controls,
and 27 verifier outputs were checked again after publication and are unchanged.
The stock logical-axiom allowance remains `propext`, `Classical.choice`, and
`Quot.sound`. The frozen numbered inventory is still 51/69, and the main theorem
remains unverified.

`publication-summary.json` records the successful publication and checks.
`independent-check.md` records the independent local integrity review.
The `blob-*.json` receipts cover the ten separately uploaded large/binary or
initial source objects. `inline-blob-manifest.json` inventories the other 106
unique text blobs, supplied as inline content through the Git tree API.
`proof-tree.json` confirms the exact expected tree hash. Together these cover
all 116 new unique blobs and all 131 changed paths in the approved checkpoint.

The earlier approval rejections and blocked-status records are preserved as
historical evidence. The user's direct authorization for this exact checkpoint
and the subsequent successful operations are recorded in this directory.
