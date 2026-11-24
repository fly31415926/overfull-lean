# Independent semantic and infrastructure review

- Reviewer: continuation subagent `/root/verification_setup`.
- Recorded at UTC: `2026-11-24T03:38:18.409985+00:00`.
- Worktree: `/workspace/scratch/7dae4c9bb5a1/overfull-three-core`.
- Run: `verification/runs/20261124T032118Z`.
- Review mode: **read-only semantic inspection and structural preflight**. This report is not a full Lean build or axiom-audit result and does not assert final candidate verification. The reviewer did not run the full verifier, publish, or commit this candidate.

## Findings and precise mathematical scope

No substantive mathematical transport or quantifier-order gap was found in the reviewed three-core composition. The public theorem pair has original-host hypotheses: even order, simple regular host, no overfull set, three disjoint covering robust core parts, fixed positive common density, nonnegative core error, and `a + 1 ≤ ε n`. The fixed robust range is `ν ≤ τ ≤ min α 1 / 64`. The tolerance and order threshold precede all host data.

The result covers exactly three core parts. It is supporting progress for Proposition 4.16, not the full proposition. All 69 numbered assertion records, their statement identities and hashes, and all 48 completed records must remain identical. Four-core cases and the main theorem remain incomplete.

### Constructed prefix and actual residual

`Palette` selects exactly the requested number of primary pieces, assigns one selected primary to each prefix label, and assigns even surplus pieces without changing required cut parity. The retained pieces are precisely the unselected primary pieces. `PrefixCompletion` invokes the proved adaptive packing rules on actual matching subgraphs; its containment and internal-only addition fields prove exact joining-copy deletion. `Prefix` chooses surviving robustness before every requested residual tolerance and order threshold and then constructs the actual prefix from the original host. Its numeric bounds include floors, grouping capacity, footprints and nontruncated degree subtraction.

`SimpleBridge` represents each simple matching by a finite set of original host edge copies. Completion presence implies disjointness. The exact deleted union yields an explicit equivalence between the simple residual edge type and the subtype of original copies that survive. The map keeps the unordered edge and both endpoints unchanged. `ResidualPools` transports matching, disjointness, support and cut cardinalities, and turns the exact retained-family union into exact residual joining coverage.

`RemainingProfile` uses a true finite bijection between retained pieces and `Fin (h - rounds)`. It neither discards nor duplicates original pieces. Its cardinal and singleton-cut hypotheses are provided by the constructed prefix parity alternatives. The latest normalization of a `DecidableEq` instance changes no mathematical assumption or conclusion. `CoreBridge` preserves actual residual core embedding and robustness; its real-degree lower bound explicitly requires `s ≤ h` when converting natural subtraction.

### Both parity cases and simultaneous contraction

With all three parts even, the residual joining set is empty, so each part is a closed component. `ClosedCores` constructs the local colors through the proved robust-shore factorization and glues them; local colorings are conclusions.

With two odd parts, `Contraction` retains the even part as distinct original vertices, sends the odd parts to separate apices, and retains actual copies with distinct contracted endpoints. Only collapsed internal odd-part copies are removed. Explicit incidence equivalences preserve core degrees and identify each apex degree with its exact original cut size.

`CentralMatchings` proves that each retained original matching remains a matching after both contractions: the singleton bounds on the two odd cuts prevent collisions at either apex. Exact joining coverage supplies every central exterior copy. `CentralCuts` bounds internal edges of any shore meeting the core in at most one vertex by the actual matching cover. The proved robust small-cut classification gives this minority case on one side of a putative violating odd cut. Regularity and even-order complement parity complete the no-overfull argument. The central degree upper bound is derived from the simple core degree and small error.

`CentralFactorization` constructs the central coloring using the already proved bounded-input result. `OddFactorization` constructs both odd-leaf colorings using the proved shore theorem. `OddGluing` relabels each leaf boundary on the same original crossing copies using the same central coloring, so copies joining the two odd parts receive equal labels on both sides. No central no-overfull certificate, local coloring, residual coloring or original-host coloring is assumed by the public theorem.

### Uniformity and restoration

`CompletedFactorization` takes one common residual tolerance and order threshold for both parity cases. `ThreeCore` first fixes the surviving expansion parameter, then the residual tolerance and order threshold, then the original tolerance and threshold, before introducing the host. It eliminates the helper prefix and profile hypotheses using the constructed prefix.

`Reassembly` pulls the actual simple residual coloring back through the exact edge-copy equivalence, reserves the first labels for the completed matchings, and shifts residual labels. Original degree arithmetic identifies the combined palette with `Fin h`. Regularity gives exactly `h` pairwise disjoint perfect matchings covering all original copies. The stronger generic reassembly statements also preserve prefix and residual color classes exactly.

## Observed focused checks

These are actual recorded component checks, not the final full-project audit:

| Attempt | Recorded status | Exit | Inputs recorded as concurrently changed |
| --- | --- | ---: | --- |
| `simple-bridge-001` | failed | 1 | None |
| `simple-bridge-002` | passed | 0 | None |
| `terminal-reassembly-001` | failed | 1 | None |
| `terminal-reassembly-002` | failed | 1 | None |
| `terminal-bridges-003` | failed | 1 | Overfull/Terminal/CoreBridge.lean |
| `terminal-bridges-004` | passed | 0 | Overfull/Terminal/PrefixCompletion.lean |

The successful `simple-bridge-002` command used `lake build --wfail Overfull.Terminal.SimpleBridge` and observed exit zero with no concurrent input change. The successful `terminal-bridges-004` command used `lake build --wfail Overfull.Terminal.Reassembly Overfull.Terminal.ResidualPools` and observed exit zero. It honestly records a concurrent `PrefixCompletion.lean` edit; the three bridge modules were unchanged and do not import that new module. All three current bridge source hashes still equal that successful attempt's frozen snapshots. Every genuine failure remains in its original directory with output and source snapshots.

## Structural infrastructure preflight

The committed baseline was read directly and checked as:

| Pinned item | Observed value |
| --- | --- |
| Published baseline commit | `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640` |
| Exact tree | `5d031253d02d0d0878422f8fbc367f04b812450c` |
| Tracked files | 5,478 |
| Audited declaration records | 13,366 |
| Completed-result mappings | 2,272 |
| Mathematical source hashes | 609 |
| Other verification-input hashes | 107 |
| Complete frozen input inventory | 716 |
| Completed numbered assertions | 48 of 69 |

The baseline frozen manifest from `verification/runs/20261124T021500Z/frozen-candidate-inputs.json` agrees exactly with the baseline result. The new checker confirms exactly four reviewed additive verifier substitutions and preservation of every previous guard. It confirms all 69 numbered assertion records are identical, allows only the recorded supporting component and top-level scope changes, and confirms `docs/manuscript-source.json` remains byte-identical. The root is exactly the complete baseline import prefix plus `import Overfull.Terminal.ThreeCore`, followed by unchanged original documentation. All three new infrastructure scripts pass Python syntax parsing.

The full runner uses the shared build lock, freezes every mathematical source and verification input byte, and separately snapshots nine control files. It runs the real strict verifier and checks input and control hashes after the actual process exits. The attached supervisor retains its runner output, including preflight failures, records 30-second observations, and writes a terminal receipt only from an observed process exit. The supplementary checker requires the actual latest exit zero, unchanged inputs and controls, raw audit/result agreement, all prior declaration names/modules/axiom sets, all old mappings and historical bytes, and the exact new source/declaration map. It does not infer a successful audit from a focused pass or a heartbeat.

The source manifest still needs regeneration after the latest source fixes. At this review, its hash or public-source-line inventory differs for: `Overfull/Terminal/CompletedFactorization.lean`, `Overfull/Terminal/PrefixCompletion.lean`, `Overfull/Terminal/RemainingProfile.lean`, `Overfull/Terminal/ThreeCore.lean`. This is a preflight dependency, not a Lean failure; the full runner will reject a stale manifest.

Before the full run, all focused processes must finish, the final source manifest must be fresh, and `development-archive.json` must enumerate every genuine development file with its SHA-256 and absolute original recorded path. Then run the attached supervisor, await its actual terminal exit, invoke the preservation wrapper with temporary output outside this run, and only then package the checked candidate. Publication remains a separate exact-tree and branch-readback operation.

## Exact reviewed file bytes

The following hashes identify the reviewed bytes. Later source or documentation edits require corresponding re-review or the final preservation checks; this table does not claim a future candidate's verification result.

| Repository-relative file | SHA-256 |
| --- | --- |
| `Overfull.lean` | `1e2dd42bc5be97ea1d8d830654960369841ee9e144856b5814cfe8c902841853` |
| `Audit.lean` | `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603` |
| `Overfull/Terminal/CentralCuts.lean` | `5ca689fd09c4838c8620a950aa38884fc8b39b14a8eab079d82e1e2161527b13` |
| `Overfull/Terminal/CentralFactorization.lean` | `cb29f0cc83e5b69fd3f92d13b02bca75c93a83992f3c422a3f661627548a7823` |
| `Overfull/Terminal/CentralMatchings.lean` | `2d2901129a3bc1d13bd529d6abf1b8c35fe3fd72becad7b54944c9be9c1492c5` |
| `Overfull/Terminal/ClosedCores.lean` | `27a7377ae0469e7048563214f7c3598445e3d95ca964ecc460ce4c81fb0d704e` |
| `Overfull/Terminal/CompletedFactorization.lean` | `f73eb10d44c333f03f6a103eaa621955c50ae6337bb90c49f52bb9f886a24435` |
| `Overfull/Terminal/Contraction.lean` | `405b8e7b3f2d8b1b692632aec60707a355df9d417056707d8ac22a0cd7521fa4` |
| `Overfull/Terminal/CoreBridge.lean` | `a2defcea9dad137a8ad224368b4b4567f623126559387bfbcfc3becd97b0763e` |
| `Overfull/Terminal/OddFactorization.lean` | `e1957ec7fe99d68ac4cc9a728a8a8d02d012eedfa39d8485a19a4c3d54e5bf3d` |
| `Overfull/Terminal/OddGluing.lean` | `1c375e5388a215230424c057928383024fbcf624d54b8a3041fd70ed326ddc93` |
| `Overfull/Terminal/Palette.lean` | `6035ed6e9a0828b5425902dead42f11906c9402a84fad9da8d62881a6816b33d` |
| `Overfull/Terminal/Parameters.lean` | `d57bc73b64e75780308a292f2c18cc534792fd6dbc89e8e1d8381db9dc055040` |
| `Overfull/Terminal/ParityCases.lean` | `d733f577d2b90119df46be37007bdd0e9bee1efa1d002a1fd820e5cc9ecf2c92` |
| `Overfull/Terminal/PartLabels.lean` | `6bbeec4479ea2cdc2244f59ea5ab678ced3629d707447beec3bed7543f8f8c4a` |
| `Overfull/Terminal/Prefix.lean` | `d4ab3bb6eaf6c6540a071c93928fa1e9ea299d8f365da383dd06752edfba4977` |
| `Overfull/Terminal/PrefixCompletion.lean` | `5851a4b1256d92642a65712a485b31ec9966a8128da623a8a37d7860cf770afa` |
| `Overfull/Terminal/PrefixResult.lean` | `8ba5b690dde71440ccff6af41817eed7ca2dd4f0b5a6897ada0915aefd4e1159` |
| `Overfull/Terminal/Reassembly.lean` | `4a038b5861a83b7c374f1af02b7fb5a3a2a45c7b2cd23cc8b638a230b06879df` |
| `Overfull/Terminal/RemainingProfile.lean` | `f59ce3a3da2fcfc33331a32eaa2110e87165c9cfb6f0386e13e9e3bc7ef2bccb` |
| `Overfull/Terminal/ResidualPools.lean` | `518e4aa84b0426c580ef3198199d1fce38fbde156221f9a4b3559ae046260035` |
| `Overfull/Terminal/SimpleBridge.lean` | `2530264ac1564ca80711928af2577ebaae25eec7e6f60ccdace0fb88e9cf5cd9` |
| `Overfull/Terminal/ThreeCore.lean` | `0b3088e0a199d67f58d580a8cce48777cfd81625ee9a3249d05c62fe3aa092b1` |
| `README.md` | `f30d99bb956b70642132f210eeb72b2d6b08472b034be62a31726a346ebf7d50` |
| `docs/coverage.json` | `4f575aad71d600bef12d4ea9af00c19b718f4e5d1add5aa95d10ea6ec5ec0933` |
| `docs/manuscript-source.json` | `78897640fdfefbb0aca21d27de6c3fbcc7fbafae72d0255713ebaf0bbf5e3d3c` |
| `docs/continuation-handoff.md` | `fed7443e975bb6c0f0b0a192c10cbc2982e17b0f8b15c627abfb3305cafffb4c` |
| `docs/three-core-terminal-source.json` | `c407e3179f5323b91fbf01eef294664d2504baa2fdfbd1d7cf9a36ab24c1b62a` |
| `docs/three-core-terminal-semantic-review.md` | `ea6cd1b3bc1cf02576492c40e8efc5910de8650476edcd70ce60f4f411209ad4` |
| `docs/three-core-terminal-verification.md` | `7db2d56312259b01e2556263f97db25c83d75003e1fc4a102b8df884db81facd` |
| `scripts/verify.py` | `cd49340e3db99c70fe4dc32382e27cff5b981a9ca2d4a866c802036bc49a0062` |
| `scripts/update_three_core_terminal_manifest.py` | `75756e5ed42221f3072b7ac78ee76b420c5004bd666083a7832570d3abcefbf9` |
| `verification/runs/20261124T032118Z/record-final.py` | `1d676846501e2b3371cc000a628d9bf3866c597ef8db1133bedd93b19d5ceecf` |
| `verification/runs/20261124T032118Z/run-verifier.py` | `bf15791777c388c4297dbdf7aa22561e2c12c2ff018b9fe6c547005ebb256adf` |
| `verification/runs/20261124T032118Z/supervise-verifier.py` | `edf2ee15eb2e4f5c049b0a43b9e6cec40a93ceaaccb7cf272eedbfe0a8753ac6` |

## Focused-receipt identities

```json
[
  {
    "attempt": "simple-bridge-001",
    "status": "failed",
    "exit_code": 1,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/simple-bridge-001/command.json",
    "command_receipt_sha256": "47f7d3f80a35e80c503fa609f30be378775640acec56a2226ecfa08b5a48b277",
    "output_sha256": "4566d9101ac7067b69465bf706bf4d67762d619fca2a42360dcd879431aefe04",
    "concurrent_changes": []
  },
  {
    "attempt": "simple-bridge-002",
    "status": "passed",
    "exit_code": 0,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/simple-bridge-002/command.json",
    "command_receipt_sha256": "9bfee30841e292026e470810bca079fb3277ec54259549c9c9fb9f64130a55dc",
    "output_sha256": "bdd9585564c2d738b3edebafe2486d16811b6bf6e64ee4f3e718f30b96e0456b",
    "concurrent_changes": []
  },
  {
    "attempt": "terminal-reassembly-001",
    "status": "failed",
    "exit_code": 1,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/terminal-reassembly-001/command.json",
    "command_receipt_sha256": "aca0e6a5239f04a23ed25d4021fb66ea3c03da78ed7bd3b4d1f4ee187406e16c",
    "output_sha256": "e5db2593194205aea1b3fa371edef777285e43609730bb5a68bdc1881646a11c",
    "concurrent_changes": []
  },
  {
    "attempt": "terminal-reassembly-002",
    "status": "failed",
    "exit_code": 1,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/terminal-reassembly-002/command.json",
    "command_receipt_sha256": "4bb03597fe8f22a3c9a1a7dc4c375c6ed07412d717fc23f1f434db732294a970",
    "output_sha256": "e1329446b090af87c8b992ab406dd918f0216aa65d45a3f7ccefbca8e4ca06af",
    "concurrent_changes": []
  },
  {
    "attempt": "terminal-bridges-003",
    "status": "failed",
    "exit_code": 1,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/terminal-bridges-003/command.json",
    "command_receipt_sha256": "50a9e6209070f13af00b3dc7ad20f4760a318db5164127a37bc171afed133e59",
    "output_sha256": "a212d350de2c253627a925629476bb58e58e8895a61818daa2619d804413f001",
    "concurrent_changes": [
      "Overfull/Terminal/CoreBridge.lean"
    ]
  },
  {
    "attempt": "terminal-bridges-004",
    "status": "passed",
    "exit_code": 0,
    "command_receipt_path": "verification/runs/20261124T032118Z/development/terminal-bridges-004/command.json",
    "command_receipt_sha256": "d96d0e9bb662313fb862b8c4faa033fd68f96245266a5f73610bd877459014cc",
    "output_sha256": "441ac34cb3cf5a623ea219f14f43a0b0e39e5d7f8f59dbb98758bde2c890cd10",
    "concurrent_changes": [
      "Overfull/Terminal/PrefixCompletion.lean"
    ]
  }
]
```
