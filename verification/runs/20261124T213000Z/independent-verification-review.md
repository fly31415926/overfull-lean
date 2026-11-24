# Independent verification infrastructure review

## Verdict and review boundary

**Ready for the frozen full-verification attempt. No unresolved substantive flaw was found in the reviewed final controls.** One provenance race was identified during review and corrected before any full attempt: the runner previously imported the preservation checker before waiting for the build lock, then recorded later live control hashes. The final runner captures runner/checker bytes before waiting, executes the checker from the captured bytes, rejects changed live runner/checker files after acquiring the lock, and requires the frozen copies to equal the captured executing versions.

This is a read-only code and evidence review, followed by writing this report. No additional Lean build, kernel audit, or test suite was run for the review. A successful complete run and the final preservation check remain required; this report does not claim that either has already passed. The reviewer authored the grouping/all-even mathematical support, not these verification controls. File hashes below bind the reviewed versions; this report's own hash is supplied by the subsequent frozen-control inventory.

## Baseline and exact coverage boundary

The independently read baseline `1c9404a454c99fe5c11ba8d774cb9c259f291f20`, tree `087e26b5f004af1f9423a6f2b137d805f5991f1a`, reports **14,627 audited declarations, 2,777 completed-result mappings, and 826 frozen inputs**. The baseline coverage is **49/69**. Direct comparison of the current coverage data found exactly two changed numbered records, **4.16 and 4.17**, and no change to any of the 69 statement identities. The current declared coverage is **51/69**, with `main_theorem_verified` false.

The preservation checker independently enforces those baseline counts, requires every previous frozen input to remain present, and requires unchanged bytes outside a small explicit documentation/root-registration whitelist. All previous nonroot mathematical sources and stock `Audit.lean` remain immutable. Root changes must be exactly the recorded additive import of a mapped new module. The old 67 unpromoted numbered records must remain completely identical, not merely retain their status fields. The number, kind, labels, section, pinned source lines, statement SHA-256 and imported-statement identity remain unchanged for all 69 records.

The only permitted promotions have sole endpoints `Overfull.frequent_pattern_result_one_factorization` for 4.16 and `Overfull.regular_core_one_factorization` for 4.17. The completed set must be exactly the old 49 plus those two. Existing component catalog entries and manuscript completed-result entries are preserved as prefixes; the only appended manuscript completed results are the exact two endpoints. The main theorem remains explicitly unverified.

## Verifier integration and complete kernel evidence

An independent reconstruction of `scripts/verify.py` from the baseline and the recorded edit list matched the live file exactly. There are exactly **seven** edits, each with a unique anchor: the exact 49-to-51 count change, removal of only 4.16 from the intentionally-incomplete guard, and five additive source/map/endpoint registrations. The final verifier is also byte-identical to the genuinely recovered Git blob `4ff0ffb4cdf316c34b747aa69eeed73f59b618ed`, SHA-256 `67ad063ae2f9baecf44944a01abc92344b210568d6fa3e680921e685d3e7f4e2`. Stock `Audit.lean` is byte-identical to baseline.

The inherited verifier deletes any old `results.json` before starting. It checks the pinned Lean and dependency source revisions, unchanged tracked dependency sources, reviewed source hashes and module ownership, and reachability of every mathematical source from the root. It then launches the actual strict `lake build --wfail` and actual `lake env lean Audit.lean`. The stock audit rejects project/external audited axioms and transitively rejects every axiom outside `propext`, `Classical.choice`, and `Quot.sound`; it enumerates kernel theorem declarations by actual module ownership, including private and generated proofs. The reported audited-module set must equal the complete source inventory.

The extension registration requires all mapped public proof names to occur in the actual audit under their expected owners. Complete module maps are generated from actual audited declarations, not only the public-name inventory, and every reviewed module must occur. The post-run preservation checker requires every old declaration to retain its name, module owner and axiom set, every old completed-result mapping to remain unchanged, and all prior source/declaration-map files and recorded hashes to remain identical. The new declaration map must equal the full audited set owned by the new modules. Thus a shortened public-only declaration list cannot satisfy this gate.

The source-manifest generator inventories the exact new Lean files relative to the pinned baseline, records their bytes and public declarations, rejects duplicate public names, and requires both full endpoints. The preflight independently requires that this inventory equal all actual new Lean inputs. At review time it contains 25 modules and 63 public proofs; those counts are inventory facts, not a claimed new kernel declaration total.

## Freeze, command execution, and output preservation

The final runner uses a unique, nonoverwriting attempt directory, serializes with the build lock, and writes an initial running receipt and empty output file before preflight. It freezes complete source/verification inputs and all required controls as both hash inventories and exact byte copies. The captured executing runner/checker identities are checked before and during this freeze. A preflight failure or an unlaunched command cannot acquire a fabricated child exit code.

The actual verifier runs in its own process group with recorded command, working directory and timestamps. Exceptions stop that group, retain wrapper diagnostics, and fail the wrapper. A passed full receipt requires a launched verifier, successful preflight, actual child exit zero, no wrapper errors, unchanged full input inventory, unchanged complete control inventory, and every principal output. Fresh verifier JSON/log outputs are archived and hashed. Both command and terminal receipts are written from the final actual state.

The preservation stage then requires the exact expected command and baseline, child/wrapper zero exits, no wrapper errors, empty missing-output list, passed status, unchanged inputs/controls, identical command and terminal receipts, and the actual raw output hash. It compares every live input and frozen copy, every live control and frozen copy, and every archived output against the recorded hashes and byte lengths. It also requires the verifier's own reported input inventory to equal the wrapper's frozen inventory. A stale successful report, a focused pass, or an earlier unavailable full run cannot substitute for this chain.

## Successful, failed, interrupted, and recovered evidence

`index-development.py` records every actual development file with its length and SHA-256 and summarizes commands without rewriting them. The preservation gate requires the exact file set, bytes, command statuses, source snapshots and output hashes to remain consistent with that frozen index. Focused passes remain focused evidence; the complete kernel run is independently mandatory.

The two interrupted attempts, `four-grouping-even-01` and `twoodd-cuts-01`, retain their original `running` status and null child exit. Separate interruption records identify the observed tool exit 130 and explicitly leave the child exit unknown. They are categorized as interrupted, never as passed. Their original recorder-hash discrepancy is accepted only under the two exact attempt names and pinned old snapshot/live-file hashes, with a clarification bound to the unchanged original receipt. The current recorder captures a single immutable source byte string before waiting, using the same bytes for its saved source and hash. This narrow historical exception does not weaken a successful full-run check.

All 11 recovered Git blobs are checked by recomputing both Git blob SHA-1 and SHA-256, with exact size and file-set checks for the surrounding recovered evidence. The recovery provenance explicitly says the requested original checkpoint and the previous reconstructed raw full-run archive are unavailable, and requires a new full run. It does not synthesize missing historical logs.

Scoped source-evidence checks bind the raw statement blocks to the actual recorded source-read responses and their file/version/line metadata. They allow exactly the recorded notation newline and the single `$1$-factorization` to `one-factorization` spelling normalization in each of 4.16 and 4.17, then require the pinned block hashes for notation, 4.13, 4.16 and 4.17. The records explicitly disclaim recovery or identity of the entire old manuscript. Frozen indexes plus post-run rechecking preserve the nested development, recovery and statement evidence even though their individual files are not each top-level control entries.

## Operational boundary

The full wrapper and preservation checker must run on the pinned baseline HEAD before the proof commit is created. Publication and subsequent public-commit readback are separate operations and are not certified by this review. The control files and this review must remain unchanged throughout and after the frozen full attempt; any necessary change requires a fresh attempt with newly frozen evidence.

Reviewed at UTC: 2026-11-24T21:52:11.248882+00:00

## Reviewed file identities

| File | SHA-256 |
|---|---|
| `verification/runs/20261124T213000Z/record-command.py` | `4cd306acc3af48c380a773914403eca58c53acd93f30731721b7f9bd1c65924d` |
| `verification/runs/20261124T213000Z/run-verifier.py` | `4ad343e1811b2e02dc274d6ed04596d3d625347a7dcad980dd0ad1d96dbd658e` |
| `verification/runs/20261124T213000Z/check-preservation.py` | `632bfbf6afb9b6017ba970831b583f8c94b8266fe282cabaf22209e6dcdfe428` |
| `verification/runs/20261124T213000Z/index-development.py` | `be59bf8ca4b5d795569c3133b60526e88ede9a9e425d946a0712d1e57f9a95ce` |
| `verification/runs/20261124T213000Z/verification-scope.json` | `f581c55acda3fe9ef8aeb665635f28b38bb7829ecd93deb5b65487df05bd4ad6` |
| `verification/runs/20261124T213000Z/verifier-additions.json` | `e7e72528642a6e3598a576f30b097ee8301c4c5777daf093ce1494e341576a28` |
| `verification/runs/20261124T213000Z/root-added-imports.json` | `0bb8e6b7f6bc47aa35de26f96448e3ebb6408aa633d1c1f542f9f3d08907eec8` |
| `verification/runs/20261124T213000Z/recovered-verifier-provenance.json` | `ad6116d5edcc9c9b5f798898bcd7bdd30166640437d809a365daa0ee6dbb448b` |
| `verification/runs/20261124T213000Z/recovery-provenance.json` | `776baaaba0aeae68bbc2a6eb5e016ee4e6b019771e7530304a3c5e53987b92a0` |
| `verification/runs/20261124T213000Z/recovered-evidence-index.json` | `c8fe6dc951e970a3ba87895cd9e9403d50b5a60865525b6ef27ebacdf58e740c` |
| `verification/runs/20261124T213000Z/source-statement-recovery.json` | `d5c520c3a0ff186530831fc33d68ed3a83918016156f9f4121dec7dcf2dcccea` |
| `scripts/verify.py` | `67ad063ae2f9baecf44944a01abc92344b210568d6fa3e680921e685d3e7f4e2` |
| `scripts/update_four_core_continuation_manifest.py` | `f2cd8ee506c1c88dff48585425af94c555e72897ddaf4e55a4cc1c565c00714a` |
| `Audit.lean` | `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603` |
| `docs/coverage.json` | `af106e3ead08548698b4878811497e71ffa4c8ed88e889ed811a260ced7677a3` |
| `docs/manuscript-source.json` | `35384073f99510f8e3a765aa8fe0aec4f9670acdc27d653956f94774ad1553b8` |
| `docs/four-core-continuation-source.json` | `c73da1fb351ed0a8a4fd0033552320be0644ee98bfc36d2f891ffda8df7e4db1` |
