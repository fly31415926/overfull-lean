# Independent review of weighted-continuation verification infrastructure

Reviewed at 2026-11-23T23:14:00.779543+00:00.

## Conclusion

No blocking defect was found in the adapted preservation checker for the current source and evidence layouts. The verifier preserves its preceding gates by exactly four additive substitutions. The full runner executes the actual strict build and unchanged audit, and the supplementary checker requires their complete current outputs, exact frozen inputs, and preservation of the public baseline.

This review did not execute a Lean command, run the full verifier, invoke the checker's report-writing `main`, or alter prior source/evidence files. It exercised read-only checker functions against real focused receipts and actual baseline Git objects. At the final review observation, no `full-*` attempt or `development-archive.json` existed yet; therefore this document does **not** claim a new complete build/audit or a completed preservation run.

## Public baseline and exact preservation

The reviewed baseline is public commit `c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2`, exact tree `6a9e73eee4e944b104ff98630b04655e8bfb959d`. Its preceding verified result contains 558 source inputs, 91 other verification inputs, 12,738 audited declarations, and 1,938 completed-result mappings.

Read-only checks independently confirmed:

- `check_verifier_extension()` accepts exactly four reviewed substitutions against the committed baseline `scripts/verify.py`. They register the new source manifest, require zero newly completed numbered assertions, register the new declaration-map filename, and include the new map in results. No preceding gate or audit invocation is removed or bypassed.
- `Audit.lean` is byte-identical to the public baseline; SHA-256 is `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603`.
- All 2,345 baseline files outside the ten explicitly mutable current paths are presently byte-identical. This includes all prior nonroot sources, source/provenance manifests, declaration maps, and historical verification evidence.
- All 69 numbered assertion records are unchanged, including their statement hashes. Every parsed coverage field except its allowed top-level scope prose remains identical; 47 assertions remain complete and the main theorem remains unverified.
- The root-import checker accepts the full original import prefix plus exactly `Overfull.WeightedPalette.AsymmetricHall` and `Overfull.WeightedPalette.Grouping`, before the unchanged original documentation.
- The current source manifest has five modules and 41 public theorem proofs. Its source hashes and independently recomputed lexical names/line numbers match the actual files. These are source-inventory observations; the actual full audited declaration count must come from the forthcoming audit.

The supplementary checker also enforces the following after the full run: unchanged prior declaration names, audited modules, and axiom sets; exact preservation of all preceding completed-result mappings; byte-identical previous declaration maps and their result metadata; unchanged dependency revisions and external-source provenance; all old source inputs unchanged except the root's reviewed import insertion; only the four permitted edited previous verification inputs and four new weighted input files; exact current source/input inventory; exact new-module difference; and an exact new completed-result mapping generated from the new public names. Permitted axioms remain precisely `propext`, `Classical.choice`, and `Quot.sound`.

## Genuine full verification and frozen evidence

`run-verifier.py` freezes the complete source and verification-input inventory, including the actual `lakefile.toml`, before launching `python3 scripts/verify.py`. It records the real command, working directory, UTC start/end, elapsed time, exit code, and before/after frozen-input equality. Each attempt gets a new directory and retains its output and exact new-source snapshots.

The unchanged core of `scripts/verify.py` invalidates any previous `results.json`, then invokes the source setup, observed Lean version, `lake build --wfail`, and `lake env lean Audit.lean` through real subprocesses. It writes the actual combined command output to the stage logs. The four additive edits introduce no alternative execution, historical-log loading, or synthetic success path.

`full_attempts()` checks each recorded attempt against its own frozen source hashes, chooses the latest actual start time, requires that latest attempt to have exited zero with unchanged inputs, and requires all top-level command/frozen/console aliases to match its actual files. Thus an earlier successful attempt cannot stand in for a later incomplete or failed attempt.

The preservation checker recomputes all current hashes and requires equality with both the frozen candidate and the freshly generated result maps. It independently parses every raw audited declaration and every project/external import marker, checks unique names and exact agreement with results, and requires the single audit-success count. It also requires exactly one strict-build success marker and exact concatenation of the four current stage logs plus the verifier's final summary. `final/` copies must equal their actual origins. Evidence hashes are rechecked before the successful reports are written.

No new full verification result has been manufactured or replayed by the reviewed preparation scripts. Complete verification is still required through the actual runner.

## Focused receipts and nested snapshots

The current recorder stores focused candidate snapshots under `development/<attempt>/source/<repository-relative source path>`. The adapted `command_record()` validates canonical source paths, first reads that nested location, and falls back to the flat attempt-local basename used by full-run snapshots. Every retained source snapshot is checked against the SHA-256 in its original command receipt.

I exercised this reader on all 11 completed focused receipts available at review: ten passed, and the genuine failed `loads-001` attempt remained failed. All recorded source hashes and snapshot locations validated. All 11 receipts report an empty `inputs_changed_during_command` list. No source snapshot was replaced by its later current source.

The retained basename-uniqueness check is stricter than necessary for a fully nested snapshot layout, but it does not reject any current record: all new sources are unique basenames in the one `Overfull/WeightedPalette` directory. If future sources use duplicate basenames in different subdirectories, that guard should apply only to flat fallback snapshots.

## Focused configuration omission and correction

One concrete provenance omission was found in the original focused recorder: it enumerated `lakefile.lean`, which does not exist here, and omitted the actual `lakefile.toml`. Earlier focused receipts therefore do not contain that configuration hash. Their original receipts remain intact; no missing historical field was retroactively invented.

The root corrected the helper for future attempts at `2026-11-23T23:12:51.670188+00:00`, adding `lakefile.toml` and a `recorder_sha256` field. I reviewed the exact two additions and checked their recorded hashes:

| Recorder version | SHA-256 |
|---|---|
| Preserved `record-command-initial.py` | `c52f390873b0a9b5b994eb4cea013f0f3b057e00d245eb8798e9f354468ed21a` |
| Corrected `record-command.py` | `67732030c5ff6f765bafaea13f13213b31b32a7e7de5aaa47263da8fea58fbb9` |

`recorder-correction.json` records the correction and explicitly states that prior receipts were not rewritten. The full runner and final checker already included `lakefile.toml`, so this limited focused-provenance omission does not weaken the required complete frozen-input verification. No redundant focused rerun is needed solely to fill an absent historical metadata field.

The focused command summary retains success/failure as the compiler command's result; unlike the full-run acceptance, it does not currently promote the `inputs_changed_during_command` list into a failure gate. All observed completed focused lists were empty. The full-run before/after freeze remains the authority for the integrated candidate.

## In-place development archive

The archive adaptation is consistent with evidence being recorded directly in the new run. It expects kind `genuine_development_evidence` and `recorded_at_path`, and reports `all_recorded_byte_hashes_match`; it does not falsely label this process as copying from an independent earlier archive.

`check_development_archive()` validates every listed repository-relative path and hash, requires the manifest path set to equal every file actually present under `development/`, and reads every real command receipt exactly once. It retains failed and incomplete records according to their actual metadata instead of reconstructing missing timing or status. When `recorded_at_path` is the same in-place file, the additional original-path check naturally repeats that byte comparison; completeness is provided by the independently enumerated directory and original receipt/snapshot checks.

The archive must be generated after focused commands have finished and include all their source snapshots, logs, and receipts. At review it was not yet generated, and its checker was therefore inspected rather than reported as having passed. The forthcoming full preservation run will require it and will reject missing/unlisted or changed files.

## Reviewed script identities

| Script | SHA-256 at review |
|---|---|
| `prepare-integration.py` | `89c452f89b3e11aa9af14e746c2942b021ea96defc23f773f5582833cd19f959` |
| `record-final.py` | `9b745f3fba5f66f4d280fe552ea641771a88d640ecc7f65eb02f24ded80133ea` |
| `run-verifier.py` | `2209c7231d4304f9423e002def0efd60cea6c5e0e8fca9328351e5f54920adfc` |
| `scripts/verify.py` | `72fb02c3c483766b04264eaf23d88a13981254323f60a1a782ed97279149ae10` |
| `scripts/update_weighted_palette_manifest.py` | `7e223ee0b0d7fd3efe155258748771a17cf01cd931d49c2d32a79ddf519cfa72` |

All six requested Python files were syntax-checked in memory. The source mapper only creates the new source manifest and explicitly states that full verification remains required. No fixed new module or public theorem count is hardcoded into the acceptance checker; the counts are recomputed from the actual manifest, sources, and full audit.
