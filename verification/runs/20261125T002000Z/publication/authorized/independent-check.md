# Independent publication integrity review

## Result and scope

The independent read-only check passed with no mismatch. This receipt records
the completed inspection of the authorized proof checkpoint. It is a new
publication receipt, outside that checkpoint's frozen proof snapshot, and is
intended for a separate later receipt commit.

No Lean command was rerun, no remote service was contacted, and no repository
file was edited during the inspection. Creating this receipt does not repeat
the checks or assert that remote publication has completed.

## Exact checkpoint identity

| Item | Verified value |
| --- | --- |
| Local HEAD | `339c69d356a8bd4c4945afec085af1f794da5c4a` |
| Committed tree | `fad7fbd161680326be5c4a7834d37cfa89ec096b` |
| Sole parent | `ac05c3232425399af6c0f29e1f7d3ddc1037424d` |
| Upload target repository | `fly31415926/overfull-lean` |

The tracked worktree and staged index were clean at inspection. The HEAD,
tree, and sole-parent identities matched the authorized checkpoint exactly.

## Full-run evidence and frozen bytes

`full-02/terminal.json` records the actual full verifier command as passed
with exit code zero, unchanged inputs and controls, no wrapper errors, and
no missing required outputs. The inspection independently checked:

- All 861 frozen input files against their current bytes and recorded SHA-256
  digests.
- All 17 frozen control files against their current bytes and recorded
  SHA-256 digests.
- All 27 recorded output files against their current bytes and recorded
  SHA-256 digests.
- Each of the three corresponding archive files against its checksum in
  the terminal receipt.
- The exact file inventory and count in each archive, followed by the
  checksum of every archived member against its manifest.
- The outer `full-02/output.log` against its terminal-receipt checksum.

No mismatch was found between current files, frozen manifests, archived
members, or recorded archive and log checksums.

## Declaration and manuscript preservation

The read-only preflight and final preservation functions were evaluated
without invoking Lean. Their result matched the saved preservation receipt.

| Inventory | Verified count |
| --- | ---: |
| Previous declarations retained | 14,820 |
| Added public, private, and generated declarations | 10 |
| Complete declaration inventory | 14,830 |
| Previous completed-result mappings retained | 2,840 |
| Complete result-mapping inventory | 2,844 |
| New mathematical modules | 2 |
| New public theorem proofs | 4 |
| Completed pinned numbered assertions | 51 of 69 |

The check retained the previous declarations' names, module owners, and
axiom lists, the previous result mappings, and the previous declaration-map
bytes. The added declaration map was checked against the verifier's recorded
checksum, audited records, counts, and source identities. The allowed axioms
remain `Classical.choice`, `Quot.sound`, and `propext`. The main theorem remains
unverified, and the 69 pinned assertion records retain their baseline scope.

## Exact upload snapshot

The inspected transport snapshot was
`verification/runs/20261125T002000Z/publication/upload-data-proof`.

| Transport inventory | Verified count |
| --- | ---: |
| Indexed committed paths | 15,123 |
| Changes relative to the baseline tree | 131 |
| New blob payloads | 116 |
| New tree payloads | 23 |

The snapshot's staged-index checksum matched the actual index. Its complete
index inventory, including paths, modes, object types, and object identities,
matched the authorized committed tree exactly. Applying the root-tree
request's 131 changes to the baseline inventory reproduced that same index.
The request's repository and base-tree identities also matched.

For every exported blob and tree, the inspection checked its actual byte
length, SHA-256 digest, conventional Git object SHA-1 including the type and
length header, and exact equality with the corresponding local Git object
body. All 139 exported objects passed.

This establishes local proof-evidence and transport integrity for the named
checkpoint. Remote upload acknowledgements, commit creation, branch updates,
and subsequent remote readback are separate publication evidence.
