# Independent review of four-label verification controls

## Finding and execution status

I found no concrete blocker in the reviewed registration, source inventory,
full-verifier wrapper, preservation checks, or declared scope. The live
registration was checked after it was applied, rather than only inspecting
the proposed edit script. The independent preservation preflight completed
successfully before the final freeze.

This review establishes that the controls implement the intended checks.
It does **not** assert that the final frozen whole-project build, transitive
axiom audit, post-run preservation gate, or publication readbacks have
already passed. Those outcomes require their genuine execution receipts.
The mathematical review in `independent-mathematical-review.md` separately
records the completed theorem interfaces and focused-build evidence.

## Baseline and immutable content

The baseline is `3991bb7eee091a329046073e0366daa84a603e5d`; direct local Git
inspection confirms tree `6424bf81123aa75b2254aea7eceff6260611f397`.
The baseline results contain 14,260 audited declarations, 2,609
completed-result mappings and 794 combined frozen source/input hashes.
Those values agree with the new preservation control. Remote baseline
readbacks are separate recorded evidence; this control review does not
replace their independent connector/native-Git observations.

The live `Audit.lean`, `docs/coverage.json` and
`docs/manuscript-source.json` were independently byte-compared to the
baseline and are identical. All 69 assertion records and their statement
identities remain unchanged, with 49 completed and the main theorem
unverified. No numbered assertion is promoted by this supporting theorem.

The preservation checker allows changes to five existing input paths:
`Overfull.lean`, `scripts/verify.py`, `README.md`,
`docs/continuation-handoff.md`, and `docs/next-verification-target.md`.
The first two have exact additive-content checks. The three prose files
are the explicitly declared current-status documentation updates. The
next-target document now reports 49/69 and directs work to the remaining
four-core terminal composition; it no longer calls four-label existence
unfinished. Every other old frozen input must preserve its baseline hash.
Existing live generated logs/results are a separate explicit output allowlist.

## Exact additive verifier registration

The live `scripts/verify.py` was reconstructed from the baseline by applying
`verifier-additions.json`. It contains exactly four recorded additive edits:

1. Register `four-label-existence-source.json` in the existing extension-map
   validation loop.
2. Require its support-only kind, zero numbered closures, false main-theorem
   status, and the exact seven principal existence/safe-selection/tight-shore/
   original-host joining endpoints, each present in the public proof inventory.
3. Assign the new generated map the distinct basename
   `four-label-existence`.
4. Include that generated map's evidence in `verification/results.json`.

The original source/hash validation, public-name ownership checks, dependency
pin checks, whole-library reachability test, build, kernel audit, coverage
checks and all previous result registrations remain present. The new guard
adds no exception to the allowed axiom set and skips no old assertion.
Python AST parsing passed for the edited verifier and all six reviewed
control/inventory scripts.

The root file is exactly the old root plus the two recorded import lines
immediately before its first module documentation comment:
`Overfull.CompatibleCircuits.FourJoiningComplete` and
`Overfull.CompatibleCircuits.FourCharacterization`. A read-only reconstruction
of source imports found every one of the 702 project modules reachable.
The full audit independently checks that Lean's actual imported project-module
set equals the source inventory.

## Exact source and declaration inventories

The new manifest generator enumerates every `Overfull/**/*.lean` path not
present in the pinned baseline, rather than using a manually selected subset.
Its live output inventories 28 new modules and 168 distinct public theorem
proofs. Independent parser execution produced the same counts, and every
recorded module SHA-256 matched its current bytes. Required principal names
are present and duplicate public names are rejected.

The generator reuses the unchanged source parser from the prior continuation.
The parser's public-name inventory is bookkeeping, not proof verification.
The unchanged stock kernel audit inspects all theorem declarations owned by
all imported project/Vizing modules, rejects declared axioms, and collects
transitive axioms of public, private and generated proofs. Its only allowed
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The existing extension loop checks every inventoried public proof's actual
kernel owner. It emits every audited theorem from the new modules, including
private/generated declarations, into the new map. The post-run preservation
gate compares that map against the complete audited subset, preventing an
omission of private or generated proofs. The additional exact-characterization
lemmas are fully inventoried even though the seven-item principal-endpoint
list is not a list of every public theorem.

## Full execution recorder and preservation gate

`run-verifier.py` is byte-identical to the previous run's wrapper.
`record-command.py` differs only in its baseline commit. The changes to
`check-preservation.py` are exactly the baseline commit/tree, previous counts,
the allowed next-target documentation path, and four additional required
evidence controls: `environment.json`, `authorization.md`,
`baseline-branch-0.json`, and `baseline-branch-1.json`. The final hardening
change was checked by exact reconstruction from the prior run after the
previously reviewed baseline/count/documentation adjustments; its only
additional edit adds those four required-control names. All four files exist
and are included by the actual control snapshot function. They preserve
recorded environment, existing authorization and baseline readbacks; they
introduce no new mathematical premise or success condition beyond evidence
integrity. The generated integration script and source-inventory generator
were also inspected directly.

The full wrapper creates a unique attempt directory, holds the shared build
lock, records a running receipt before preflight, and snapshots all inputs
and controls before launching the actual `python3 scripts/verify.py`.
Source inputs include every mathematical module, the root and stock audit,
toolchain/manifests, all script files, current documentation inventories and
prose, dependency patch files, notices and licenses. Controls include the
runner, preservation checker, focused recorder, registration data, scope,
development inventory, recorded environment and authorization, both baseline
branch readbacks, this review, other independent reviews and all run Python
scripts. Input and control inventories and bytes are compared again
after the child exits.

The actual verifier runs `lake build --wfail` followed by Lean on unchanged
`Audit.lean`; it does not replay a historical audit. The wrapper preserves
combined genuine stdout/stderr, actual child exit status, wrapper errors,
source/control snapshots and newly written output artifacts. A successful
wrapper receipt requires the child to exit zero, preflight success, unchanged
inputs and controls, no wrapper errors, and every principal output. Exceptions
or interruptions cannot silently become a successful full receipt.

Post-run checks require identical command/terminal receipts, matching raw
output hashes, exact archived/live output bytes, exact frozen/live input and
control hashes, and actual verifier success. They also require every old
proof name, owning module and transitive axiom set, every old completed-result
mapping and every previous complete declaration-map object/hash to remain
unchanged. The new map must equal the audited theorem subset for the new
modules. The completed numbered count remains exactly 49.

## Development evidence

The reviewed development inventory contains 81 genuine focused attempts:
40 passed, 41 failed and zero interrupted, comprising 1,252 recorded files.
The preflight checked the inventory, exact sizes/hashes, recorder snapshots,
source snapshots, genuine command statuses and raw output hashes.

Fourteen attempts record source changes during execution; none have unknown
change status. These were concurrent development checks, and the inventory
retains those limitations. They are not treated as the final frozen result.
All failed attempts and their genuine outputs remain present. The final
complete gate, on unchanged inputs and controls with `--wfail`, is required
regardless of focused success or a package-option build's treatment of warnings.

## Remaining gates

The independent preflight has passed with all 28 modules inventoried and
all baseline immutability/coverage constraints satisfied. The remaining
required execution evidence is the complete frozen verifier receipt,
post-run preservation report, and separate publication tree/branch readbacks.
No changes to the mathematical or control files should occur during the
frozen verifier. A later change requires rechecking the affected review and
running a new uniquely named complete attempt rather than rewriting evidence.

## Reviewed control SHA-256 values

These hashes identify the control bytes inspected before the full run.
The full wrapper separately freezes this review and all other controls.

| Control | SHA-256 |
| --- | --- |
| `verification/runs/20261124T134200Z/check-preservation.py` | `bb3ea9c298118c3d99d3b97961029de733d40455ed5506623506e06d1f3e19e9` |
| `verification/runs/20261124T134200Z/run-verifier.py` | `7748055dd0d430ace3ad7a2febbf5311977469ebbb717fb7babdfec28f5e8dec` |
| `verification/runs/20261124T134200Z/record-command.py` | `2396714741ad0cb2ef669a387e9bfcf8ff835bda50394dc6211cad8b129675cd` |
| `verification/runs/20261124T134200Z/prepare-integration.py` | `35d07430b360b0b8e8509165e390126822ddd12ada44bc34bc5bd6b1d924279b` |
| `verification/runs/20261124T134200Z/index-development.py` | `be59bf8ca4b5d795569c3133b60526e88ede9a9e425d946a0712d1e57f9a95ce` |
| `verification/runs/20261124T134200Z/verification-scope.json` | `7523feca0cc3690a5d0c9c9680056526a555c670ccd41c7f303fa5fa5d913b28` |
| `verification/runs/20261124T134200Z/verifier-additions.json` | `89a865bb583fb9bd3077e26c184585d98cc51d25b31a006440d975f044b08269` |
| `verification/runs/20261124T134200Z/root-added-imports.json` | `0f2c638e13d05b810d8ea39c73416acf7f9aa69381b85908200a8d257f0b6273` |
| `scripts/update_four_label_existence_manifest.py` | `ee4742caa9d73c487eeae9d013eedb38614eb63a9df0ac167df92bfa36f58763` |
| `scripts/verify.py` | `ebecf748ff42da97cbf26b802a0245720805f43dee58412eb2751aa07ab9422d` |
| `Audit.lean` | `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603` |
| `docs/four-label-existence-source.json` | `3f1b6278c682fe9461ef2acbea072e9a5b341da6167adc90bb3d81676341c4f0` |
| `verification/runs/20261124T134200Z/authorization.md` | `2d5319abe9b23f1871c14b8ad7bc199d81c4560d865d35bc68533532ea2644b4` |
| `verification/runs/20261124T134200Z/baseline-branch-0.json` | `ddd81085e8e49484dd60e86ee7325697f9ce3fa2b6a87967815a4f266f7978cc` |
| `verification/runs/20261124T134200Z/baseline-branch-1.json` | `2fd9a1a3565ab439bda418fb48aa1a0a29a4d524fc4329af9b79a5c50dc9b2ba` |
| `verification/runs/20261124T134200Z/environment.json` | `aa9b7d9a10422beed4905af144068c2bf8a015f10261d010c979618c99356b2f` |
