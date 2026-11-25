# Publication evidence for the protected-trace checkpoint

## Published result

The verified proof is public at [`c685a6ffb08591d048722cf13e4debaff6eb39ea`](https://github.com/fly31415926/overfull-lean/commit/c685a6ffb08591d048722cf13e4debaff6eb39ea), with tree `6d5ccce3895e186caaf0b85018c30cf1ffe5028b`, exactly matching local checkpoint `c59d4d740bd3a66937e71ee6538216444e63383e`. Both requested branches were read back at that proof commit before the receipt-only successor. The full strict build and exhaustive audit passed: 3,930 build jobs and 15,162 proof declarations. Coverage remains 51/69 and the main theorem remains unverified.

`publication-summary.json`, `proof-readback.json`, and `proof-native-readback.json` record the actual publication and readback. The earlier rejection is retained as history; `authorized-publication-authorization.json` records the explicit user approval that resolved it.

This directory records exact-object publication of the supporting
two-pair external-assembly continuation to `fly31415926/overfull-lean`.
The authorized branches are `main` and
`verified-bipartite-continuation-2026-11-21`.

The baseline is commit `f2510d10c114bcf3d0003b5e2e4e35cb0400167d`, tree
`58fe77f4afaba4b0ab6cf77956afb1c23608cd35`. The scope is 16 new mathematical
modules and 75 public theorem proofs. The numbered manuscript inventory
remains 51/69 and the main theorem remains unverified.

## Reading the evidence

1. `../full-01/terminal.json` and `preservation.json` give the actual strict
   build, exhaustive axiom audit and preservation outcome. The frozen
   input/control archives and output archive contain the exact checked bytes.
2. `focused-evidence-index.json` indexes every retained development attempt,
   including failures. It checks each actual log, recorder and saved source
   snapshot against the original receipt; it does not rerun a compiler or
   replace missing evidence with a later successful source.
3. `checkpoint-report.json` rechecks the full-run files against their recorded
   hashes and checks every archived member against the frozen manifests.
4. `local-commit.json` and `original-local-commit.txt` identify the local
   checkpoint and its exact tree. GitHub may supply different author/time
   metadata for the public commit; the full tree and parent must agree.
5. `upload-object-manifest.json`, the transport plan and the individual blob,
   tree and commit receipts record the exact Git objects. Every object SHA
   returned by the connector is compared to the prepared local identity.
6. Branch-update receipts use an expected-head lease without force. The
   subsequent commit/tree and both-branch readbacks establish publication.
   A local commit or successful upload by itself is not sufficient.
7. `publication-summary.json` connects the verified tree, local checkpoint,
   public proof commit, both requested branch readbacks and preservation
   outcome. A receipt-only successor records those publication results
   without changing any verified source, frozen input, control or output.

Files are created as those steps actually occur. Their absence is not a
successful outcome. The concrete status is in the execution and remote
readback receipts rather than inferred from this guide.

## Reproduction helpers

`prepare-upload.py` snapshots the staged Git index and computes its tree and
all changed object identities offline. `plan-upload.py` prepares small UTF-8
blobs inline and identifies larger or binary bodies for individual upload.
`read-payload.py` verifies immutable payload bytes and reads bounded chunks.
Transport snapshots contain redundant copies of already recorded Git objects
and are excluded locally; their complete identity manifest is retained.

`index-focused-evidence.py` checks the saved development receipts and writes
their index once. `verify-frozen-checkpoint.py full-01` is a read-only check of
the actual full-run receipt, current files and archived bytes. Neither helper
substitutes for the full Lean verifier.
