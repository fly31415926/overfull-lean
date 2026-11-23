# Recovery checkpoint: joining proof complete, full verification pending

This is an interim, unverified-source recovery snapshot for run
`20261123T010829Z`. All five new modules pass strict targeted compilation,
and all 75 public theorem names resolve. The whole repository verifier and
stock axiom audit are still required before either verified branch moves.

The actual original-host joining decomposition and precise scope are in
`docs/joining-circuit-verification.md`; the self-contained resume instructions
are in `docs/continuation-handoff.md`. This is not a complete proof of
Corollary 4.6, and the numbered inventory remains 47/69.

The eventual final run report supersedes this snapshot's pending status.
Historical top-level results/axiom/build logs are omitted from this interim
tree so they cannot be mistaken for verification of the new candidate.
The baseline commit preserves them, and the final checkpoint will contain
fresh outputs from `python3 scripts/verify.py` if it succeeds.

All actual targeted failures, command records and source snapshots are
retained. Setup records and final audit evidence may be added after this
recovery snapshot as those operations finish.
