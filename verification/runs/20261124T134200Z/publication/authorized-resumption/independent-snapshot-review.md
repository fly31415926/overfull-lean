# Independent review of the approved publication snapshot

**Passed. No blocker found to publishing the exact approved commit and tree.**

| Identity | Verified value |
| --- | --- |
| Approved commit | `2188bd1233aa66e32195e743ac8b32f97a2bbec2` |
| Approved tree | `46dda25b581f227718eb3c32a6ee4e6d88d3116d` |
| Direct parent / verified baseline | `3991bb7eee091a329046073e0366daa84a603e5d` |
| Baseline tree | `6424bf81123aa75b2254aea7eceff6260611f397` |
| Review time | `2026-11-24T14:34:41.282078+00:00` |

This review read actual Git blob objects at the approved commit. It did not
rely on the index or commit-message claims. It performed 122 independent
read-only checks and made no Lean invocation, control-script invocation,
index write, or Git-ref change. Detailed results are in the adjacent
`independent-snapshot-review.json`.

## Committed bytes match the verified snapshot

The review checked **3,000 committed file paths**, represented by 1,077
distinct Git blobs. All match the previously reviewed workspace bytes.
Specifically:

- All **826 frozen inputs** match their recorded hashes in both their
  ordinary project paths and the committed `full-01/input` archive.
- All **17 frozen controls** match the frozen-control manifest, execution
  receipt, ordinary run paths, and committed control archive.
- All **25 outputs** match receipt hashes and byte lengths in both their
  ordinary verification paths and the committed artifact archive.
- All **2,149 nonpublication run files** are present in the commit. Their
  inventory and bytes exactly match the reviewed run evidence; no such
  file is missing or changed.

The command and terminal receipts are byte-identical and record a finished,
successful verifier execution, exit code 0, wrapper exit code 0, unchanged
inputs and controls, and no wrapper errors. Their raw-output hash matches.
The archived build and audit logs also occur in that actual command output.

## Build, audit, and baseline preservation

The committed build log reports successful completion of **3,874 jobs**.
The raw kernel audit contains exactly **14,627 distinct theorem records**
and a matching success marker. These records independently match the
reported declaration owners and axiom sets. Every axiom set is contained
in `{propext, Classical.choice, Quot.sound}`.

Comparison with the baseline Git objects confirms preservation of:

- All **14,260** previous declaration names, owner modules, and axiom sets.
- All **2,609** previous completed-result mappings.
- All **19** previous declaration maps, including their full bytes.
- All previous immutable inputs and the byte-identical stock kernel audit.
- The root file except for the two recorded imports, and the verifier except
  for its four recorded additive registration edits.

The **28 new Lean modules** exactly match the new-source inventory and
source hashes. Their proof map equals the full set of module-owned kernel
theorems and the full difference from the baseline audit: **367 proofs**,
including **168 public proof declarations** and **199 additional kernel
proof declarations**. The map does not filter out generated or private names.

All **1,252 development-evidence files** remain indexed and byte-correct.
The **81 genuine command receipts** preserve their matching output, recorder,
and source snapshots: **40 passed and 41 failed**. No unsuccessful attempt
was replaced by a success claim.

Coverage and manuscript inventory files are byte-identical to the baseline.
The verified count remains **49/69**, and the main theorem remains unverified.

## Receipt identities and publication boundary

The committed command/terminal receipt SHA-256 is
`18f27dde12dd0388d9bdf2af4c34410ed20c625f50fcdc1fec022db543a56a0d`.
The committed preservation report SHA-256 is
`adf1cb8b9acb301f8ddd0f52c1edc44ba3ec8d914e6d59172fb76e24fb554a5f`.
The earlier final independent audit review is committed intact and binds to
these same receipts.

The explicitly approved checkpoint can be published as inspected. This
review and subsequent authorization/publication receipts postdate that
checkpoint and belong in a receipt-only follow-up. No claim about successful
remote publication is made here; independent remote readback remains the
next verification step.
