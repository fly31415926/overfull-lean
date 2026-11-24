# Independent review of the saved publication snapshot

Reviewer: `/root/verification_infrastructure`.

The read-only checks completed successfully at **2026-11-24 13:01:15.700130
UTC**. They inspected the current source and verification files, the immutable
local proof commit and Git trees, the preserved full-run and preservation
receipts, the prepared upload payloads, and the earlier upload receipts. No
Lean command was rerun. No source, frozen control, index, commit, upload, or
ref was changed. This review file is the sole repository addition made by
the reviewer for this resumption task.

## Immutable proof snapshot

| Item | Independently checked value |
| --- | --- |
| Proof commit | `da6c2be9170823d3f7f04913863910b1661f739a` |
| Exact proof tree | `63b623f73fcb4333d38f46d8e845a2c3f4ff6f23` |
| Proof commit parent | `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` |
| Baseline tree | `9013f6d5c07676ba130d4bb794062d700bab6136` |
| Proof-tree file leaves | 10,490 |
| Observed metadata HEAD | `e2775717c146e0b61a4b6bc6fb083c03e80c9f1e` |

The saved target and baseline inventories match the actual local Git tree
objects. Their tree hashes were also reconstructed from exact leaf paths,
modes and object hashes using Git's raw tree encoding and ordering. Both
reconstructed hashes equal the recorded immutable trees.

The saved proof tree contains all **2,070 required source and verification
evidence paths** from the upload index, with the exact expected bytes. This
inventory includes the 794 frozen inputs in their normal source locations,
the development and setup evidence, and the complete `full-01` archive.
Separately, every one of the **1,304 current nonpublication files in this run**
is present in the proof tree with the same blob hash. This additional check
covers the run report, original preservation result, live verification
controls, independent reviews, research notes, snapshots and retained logs.
No required source or verification evidence was missing from the saved target.

Publication receipts created after the proof tree are preserved separately in
the observed metadata commit. The 33 successful content-upload receipts and
the distinct rejected upload receipt were checked against that commit's exact
blob hashes, as were the saved status, upload index, automatic-review rejection
and post-block integrity records. These later records belong in the final
publication receipt stage; the earlier proof tree is not represented as having
contained receipts that did not yet exist when it was saved.

## Frozen inputs and genuine verification evidence

All **794 current inputs** match `full-01/frozen-inputs.json`, and all **16
current controls** match both `full-01/frozen-controls.json` and the genuine
command receipt. The archived copies were checked against the same hashes.
The current inventory contains no added or missing frozen input or control.

The original full-run receipt still records a passed verifier, child exit 0,
wrapper exit 0, no wrapper errors, no missing principal outputs, and unchanged
inputs and controls. Its command and terminal receipt bytes are identical.
The raw command log retains its recorded SHA-256. All **24 recorded verifier
outputs** still match both their live files and archived copies, including
their recorded sizes and hashes.

The original preservation report retains its exact previously recorded hash
and its successful baseline-anchored result. Its command-receipt hash matches
the preserved full-run receipt. The original verification was not repeated
under the later metadata HEAD or described as having run there.

The current audit and result maps were also checked directly against the
baseline records:

- All **14,055 prior declarations** retain their names, owning modules and
  transitive axiom sets. The current total remains **14,260**, including
  **205 new declarations**.
- Every declaration's axioms are contained in `Classical.choice`, `Quot.sound`
  and `propext`.
- All **2,536 prior completed-result mappings** are retained exactly; the
  current total remains **2,609**.
- Every prior source/declaration map retains its recorded content and file
  hash.
- The new source inventory still identifies **11 modules and 73 public proof
  declarations**. Its source hashes match the current files. The generated
  map contains exactly the **205** audited proofs owned by those modules,
  including private and generated proofs.
- All **69 numbered assertion records and statement identities** remain
  unchanged. The completed count is **49**, and the main theorem remains
  unverified.
- The verifier still contains only the four exact additive registrations,
  and the stock `Audit.lean` is byte-identical to baseline.

The development index also retains all **334 files from 26 attempts**:
10 passed, 13 failed and 3 interrupted. The one recorded development input
change and the three interrupted attempts' unknown child exits/input-change
statuses remain recorded honestly. No interrupted receipt was recategorized
as a successful Lean command.

## Prepared payloads and prior successful uploads

The saved transport metadata matches the separate prepared directory byte
for byte. The manifest hash matches the upload index. All **212 new blob
payloads** were independently checked for byte length, SHA-256, and raw Git
blob SHA-1. Every target-path association points to the matching leaf in the
verified proof tree.

All **162 ordered chunks across five large blobs** were checked for offsets,
lengths, raw-content hashes, JSON-file hashes, UTF-8 round trips, blob identity
and chunk index. Concatenating each ordered sequence produces exactly its
complete raw blob payload. No chunk was omitted or reordered.

All **36 content batches** were checked against their indexed request-file
hashes, lengths and entry counts. Each content entry's UTF-8 bytes produce
the Git blob hash named by its temporary path. The complete temporary tree
hash was reconstructed for every batch and equals its indexed expected tree.
The batches collectively contain exactly the 207 new blobs not assigned to
the large-blob transport.

For the **33 prior successful receipts, `upload-content-0000.json` through
`upload-content-0032.json`**, every recorded request hash and expected tree
hash matches the corresponding upload-index entry. Every stored tool result
has `isError: false`, and its returned tree SHA equals the independently
reconstructed expected tree SHA.

The earlier `upload-content-0033.json` still records an automatic-review
rejection with `isError: true`; it has no successful returned tree hash and
was not counted among the 33 successes. This review does not erase or
reinterpret that historical result.

The **three final-tree batches** were applied in memory to the exact baseline
leaf inventory. Every intermediate reconstructed tree equals the expected
hash in the upload index, and the final inventory and hash equal the saved
proof tree exactly. The plan contains no deletion.

These are checks of preserved local evidence and prepared object payloads.
The reviewer did not contact the remote repository or independently recheck
current remote availability of previously uploaded objects. Publication still
requires its actual resumed upload results, exact final-tree confirmation,
commit receipt and both-branch readbacks.

## Evidence hashes

| File | SHA-256 |
| --- | --- |
| `transport/manifest.json` | `217c6732e9d86c97adc2bda5ca6463a7b4020e2b98f9f0dce0b56306e9260db5` |
| `transport/upload-index.json` | `ab099a6c660867979499d5d7bd29ac45c2ad3ca758d5c896bdc8d4d9def78498` |
| `../REPORT.md` | `863da10a478f866534d4b8333835de52c80204ab31579677ee533e6988fb85a6` |
| `../preservation.json` | `0c48080a95476e87cf439ee2372fe6cc032d81f1e6dcfd3368c92219cb27bfe3` |
| `../full-01/command.json` | `02c16881a3f0b32cc3f80304451e599fbc11c838dfbb6eee73a6aa8e23ce815b` |

The saved snapshot and existing upload receipts are consistent with the
verified source set and complete evidence inventory. The reviewer will make
no further repository writes after this review, leaving final receipt staging
and publication to the root agent.
