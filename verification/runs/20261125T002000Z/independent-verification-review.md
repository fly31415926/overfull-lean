# Independent review of the verification controls

## Scope and actual inspection

This review examines `check-preservation.py`, `run-verifier.py`,
`verifier-additions.json`, `record-command.py`, the additive changes to
`scripts/verify.py`, the unchanged `Audit.lean`, and the current source and
coverage manifests. It is a control review, not a substitute for execution
of the full Lean build or axiom audit. No full verification attempt had been
run when the initial review was written.

The reference is public commit
`ac05c3232425399af6c0f29e1f7d3ddc1037424d`, tree
`8cfcdcc6cdd08b3209bc21b1823122bb141c330e`. Its checked inventory has 14820
proof declarations and 2840 completed-result mappings.

A read-only execution of the current `preflight(current_inputs())` passed.
It confirmed 727 unchanged previous nonroot mathematical source files,
the unchanged stock audit, the exact additive root import, all 69 identical
numbered assertion records, and the unchanged count of 51 complete
assertions. Independent direct comparisons found no added or removed
top-level keys in either old manuscript metadata document. Both new Lean
module hashes matched the new source manifest.

The initial inspected control hashes were:

| File | SHA-256 |
| --- | --- |
| `check-preservation.py` | `cd0d5980e277abb3e0b239056cd875b02a3eb65ac43f789bc4291cc0c09e2a72` |
| `run-verifier.py` | `02534fbd8b20e4a26c7dca7907b079bb37f8ac0bbf35ce4cf42a9fab0c047484` |
| `record-command.py` | `7a81be5fa4cff8dcd0802d4c25cda3f59d4ed4c2d9c79c2126e076829dc384ce` |
| `verifier-additions.json` | `1d9ead66a86447ee5277ed8637b0e0e6817a57905e740987a1316fcf8d7fbd50` |
| `scripts/verify.py` | `e027555491bbd63ddbe31fe6dd24cb88c145e5d8cbebd4ec441a9775270df84c` |
| `Audit.lean` | `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603` |

These identify the reviewed initial versions; the final frozen-control
manifest identifies the versions actually used by a verification attempt.

## Initial findings, resolved in the final recheck

### Focused-command success must require unchanged source snapshots

The inspected `record-command.py` computes `changed_sources` but sets
`status` to `passed` solely from the child exit code and exits with that
same code. If a source changes while a focused command runs, the receipt
can therefore say `passed` while also listing changed sources. It would
not establish that the saved initial source snapshot passed that command.

The complete verifier wrapper already rejects persistent input changes,
so this issue does not bypass the complete gate. Nevertheless the focused
receipt should set success only when the child exits zero **and** the
source snapshot is unchanged. Its wrapper exit should also be nonzero on
source drift, while preserving the actual child exit code separately.

### Bind the generated new declaration map to its recorded checksum

The inspected `final_checks` compares the set of new declaration names
with the names in the new map, and requires their actual audited module
owners to equal the two expected modules. It does not independently check
the new map's bytes against the checksum written into `results.json`, nor
compare each map record's audit fields with the actual audited record.

The stock verifier generates those records correctly. However a map
overwritten or corrupted after its generation, preserving only its names,
could pass this extra preservation check while disagreeing with the
result's checksum or its source/axiom fields. The final checker should
require the actual map checksum to equal the recorded checksum, reject
duplicate or count-inconsistent map records, and compare each map record's
`name`, `module`, and `axioms` fields with the actual audit inventory.
Its `source_path` and `source_sha256` should match its module's reviewed
source record. These are direct consistency checks, not a second Lean run.

## Safeguards that are already adequate for the planned run

The four registered verifier edits were read in full. They add the two
new modules to the existing source/declaration-map pipeline, require the
specific public endpoint, verify its exact current-source excerpt hash,
and record the new map in the final results. They remove no existing
verification condition. The exact edited verifier is reconstructed from
the immutable baseline and the four registered changes in preflight.

The source manifest identifies four public theorem proofs in two modules.
The existing verifier independently checks the source paths and hashes,
the public-name inventory, and the actual audited module owners. Every
first-party mathematical module must be reachable from the root import,
and Lean's imported module list must agree with the source inventory.

The unchanged audit examines the loaded kernel environment. It rejects
axiom declarations in the audited project modules and checks the transitive
axioms of all theorem declarations, including private and generated proofs.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The full
preservation check also requires every old declaration record, with its
owner and axiom list, to remain exactly present. Old result mappings and
declaration-map files are retained. A missing new public theorem cannot
be hidden by an unchanged old declaration total.

The stock verifier removes any old `results.json` before starting. It
executes `lake build --wfail` and the unchanged audit, checks the pinned
Lean and dependency configuration and actual tracked dependency sources,
and writes success only after the checks finish. The wrapper requires
zero child exit, completed preservation checks, unchanged frozen inputs
and controls, and fresh `results.json`, `build.log`, `axioms.log`, and the
new map. A leftover old success report or a focused endpoint build alone
cannot meet this complete gate.

The wrapper's unique attempt directories use `exist_ok=False`, preventing
an accidental retry from overwriting earlier attempt receipts and archives.
The raw wrapper output, actual exit status, input/control snapshots,
outputs, and archive hashes are retained separately for each attempt.
Normal failing child commands write their actual output before the stock
verifier exits nonzero. Such a failure cannot be recorded as a full pass.

The input and control comparisons are before/after integrity checks. They
detect persistent edits during execution; they are not a filesystem event
monitor capable of detecting an edit that is made and restored mid-run.
Keep source and control editing stopped during a full attempt. No active
concurrent source editing is needed for this run.

## Interrupted-run limitation

The stock verifier's `run` function buffers each child command's output
until that child returns. If the verifier and its child are terminated
mid-build, partial child output may never reach `build.log` or the outer
`output.log`. The wrapper can record the actual verifier termination and
the evidence that survived; it must not synthesize missing output or
claim an unobserved child's final exit status. Similarly, an interrupted
focused recorder may leave a `running` receipt until an actual observation
is recorded. Such a receipt is not a pass.

This is an evidence-scope limitation, not a route to a successful full
gate. A clean completed build and audit can retain their complete logs.
Any interrupted attempt should be described explicitly according to the
output and process status actually observed.

## Mathematical and manuscript scope retained by the gates

The new endpoint is the separately sourced current-manuscript theorem for
one, two, or three ordinary robust cores with arbitrary palette `k`.
The source-facing review establishes the disjoint-partition convention,
uniform parameters, construction of the auxiliary completion, restriction
to the original edges, and the absence of supplied coloring assumptions.

The new verifier check pins the current theorem excerpt to
`43b21f5ea1e98772ee258c145ddb206ca37e72ffa34b7eb13de25739823509b3`.
It explicitly requires zero newly completed assertions in the older
inventory. Preflight requires all 69 old records, including their source
hashes and statuses, to be identical. The full gate preserves the 51
complete assertion list and keeps the main theorem unverified. This
prevents the unresolved older Theorem 1.2 identity from silently passing
as a new numbered completion.

## Final recheck of the corrections

Both concrete findings were corrected and independently reread before any
Lean verification command ran.

The focused recorder now defines success as a zero child exit with no
changed source snapshots. It preserves the actual child exit in
`exit_code`, records a separate `wrapper_exit_code`, and exits nonzero on
source drift. Thus an actual successful child process is not falsely
reported as validating different archived source bytes.

The complete final checker now binds the map path and actual map checksum
to `results.json`. It requires the map length, its reported declaration
count, and the exact set of added audited names to agree. For every map
record it checks `name`, `module`, and `axioms` against the actual audited
record, then checks `source_path` and `source_sha256` against the module's
source manifest. These changes close the identified map-consistency gap.

The corrected versions are:

| File | SHA-256 |
| --- | --- |
| `check-preservation.py` | `c2d683c8578ffd335cd0f90fa37450ea26a906f8f25c9aa46768e082ce91401b` |
| `record-command.py` | `314cab473315211579436cd3e652baf0e7b64522c3817804db974ffdfa1a0524` |

The full wrapper and stock verifier retained their initially reviewed
hashes. Python syntax parsing passed for all three control scripts and
the stock verifier. A second read-only preflight also passed, again
confirming the 727 unchanged previous mathematical sources, all 69
unchanged assertion records, the unchanged stock audit, and exactly four
registered additive verifier edits. This recheck did not execute Lean or
the post-build `final_checks` function.

No further verification machinery or extra mathematical tests are needed
before running the planned strict full build and axiom audit. The run's
actual terminal receipt, frozen manifests, and preservation result must
still establish execution success. The interrupted-output limitation
above remains a limitation on the evidence available after interruption;
it does not permit such an attempt to pass.

## Root import placement correction after full-01

The genuine full-01 attempt failed at the root module because the new import
was appended after the module documentation comment. The proof modules had
compiled. The new import is now inserted immediately after the unique baseline
`import Overfull.FourCoreReduction.Regular` line and before the documentation.
An independent read-only review confirmed that the resulting root file equals
the baseline bytes plus exactly this single import line, with all previous
bytes preserved. The preservation checker now requires this exact insertion
and a unique anchor instead of requiring an invalid end-of-file append.
Its preflight passed: 727 previous nonroot source files unchanged, all 69
numbered assertion records identical, the stock audit unchanged, and exactly
the four registered additive verifier edits. No mathematical proof changed.
The failed full-01 input/control archives and logs remain untouched.
