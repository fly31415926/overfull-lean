# Terminal continuation: verification infrastructure

The exact verified local baseline is `f557ae03355f14a0441b37283f35186a95aca2d7`,
tree `efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d`. It has 4,321 committed files,
13,170 audited declarations, 2,176 completed-result mappings and 696 frozen
inputs. Successful public baseline promotion is independently recorded in
`baseline-publication-success.json`; local proof provenance continues to use
the exact local baseline identity.

## Focused development

Use `record-command.py UNIQUE-ATTEMPT COMMAND ...`. It serializes commands on
this run's `build.lock`, captures genuine complete output, preserves failed
attempts, and snapshots every new `NativeTerminal` source with the complete
original source hash inventory. Prior build artifacts were copied into an
independent worktree build directory. Pinned dependencies are shared through
the package symlink. The setup command and its actual result are recorded in
`cache-setup.json`.

## Prepare the exact candidate

The live manifest generator is `scripts/update_native_terminal_manifest.py`.
Its scope must describe the final established mathematical conclusions and
remaining obligations. Run it only once source scope is stable. Draft proof
maps and an independently recomputed draft manifest can be created with
`prepare-docs.py`; this writes only this run's `docs-draft/` files.

Write the reviewed semantic report, final continuation handoff and README.
Append every new import after the entire original `Overfull.lean` import
prefix. Record the exact added import lines, including newlines, in
`root-added-imports.json`. Apply only the seven exact reviewed verifier substitutions specified in
`verifier-additions.json`: terminal mapping registrations, count 48, and the
precise positive 4.6 guard replacing only its former incomplete status. Every
old `Audit.lean` byte, previous nonroot source, old proof-source manifest and
declaration map, and historical evidence file remain unchanged. All 69 statement
identities and hashes and the 68 other assertion records remain exact. The
coverage JSON changes only as specified in `promotion-plan.json`, appending one
complete component. The only manuscript-source metadata edit is count 47 to 48.

Once all focused commands have terminated and source edits are complete,
run `prepare-docs.py --archive-development` to record every focused diagnostic
file with its exact bytes. Do not discard a failed attempt. The checker will
reject an unresolved active/incomplete diagnostic at the freeze.

## Attached complete verification

Run `python3 -u verification/runs/20261124T021500Z/supervise-verifier.py full-01`.
The attached supervisor emits genuine observations every 30 seconds and waits
for its actual child to terminate. The underlying command is exactly
`python3 scripts/verify.py`, with the unchanged strict build and full axiom audit
gates. Await its actual terminal exit. Never infer completion from log existence
or another tool session's process state.

The runner checks every committed baseline source/input hash, the exact seven
reviewed verifier substitutions, the complete original root prefix and every new
manifest entry before running Lean. It freezes every input byte and source hash.
Fresh logs, results, complete declaration maps and raw audit byte segments are
retained under the immutable attempt directory. Do not change frozen inputs
during the command. A failed complete attempt remains intact; any retry uses
a new name such as `full-02`.

## Preservation, local packaging and publication

After genuine complete verification success, run
`record-preservation.py preservation-check-01`. It invokes the independent
preservation checker and retains its actual command, output and exit status.
The checker compares every old declaration name/owner/axiom set and mapping,
all prior sources and historical evidence, all 69 original statement identities
and hashes, the 68 other exact assertion records, the precise 4.6 promotion, and
the exact new source/audit maps. It verifies that the console equals
the actual stage-log concatenation and that raw audit segments reassemble the
complete audit. It writes success only after all gates pass.

After the supplementary evidence freeze, do not alter checked files. The
`package-verified.py` command rechecks every frozen/evidence byte, observes the
recorded successful full and preservation exits, commits the exact local
candidate and constructs an independently checked Git bundle and ZIP. It makes
no network call. Publication is separately authorized; exact public tree and
branch readback receipts establish the final published state.
