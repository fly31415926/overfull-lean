# Frozen candidate awaiting the full audit

This is a historical status snapshot from run `20261123T042619Z`. Read the
later `verification-command.json`, `run.json` and `REPORT.md` when present
for the final result; this file does not certify a finished full audit.

All three new targeted module checks and the inventory check for 118 public
proof names passed. The complete candidate's strict repository build then
passed all 3,675 jobs. Its genuine output is copied verbatim to
`full-strict-build-before-audit.log`; the complete axiom audit is still pending
at this snapshot. There are 579 frozen inputs: 504 Lean sources and 75 other
verification inputs.

The candidate includes 75 public joining proofs recovered byte-for-byte from
GitHub and 43 recreated/new assigned-part public proofs. The latter construct
the actual matching-based parts, prove exact selected cuts and parity, and
compose with the joining stage in the same host or another host. No additional
numbered manuscript assertion is marked complete; full 4.6 and the main
theorem remain open.

This source checkpoint belongs on `continuation-attempt/20261123T042619Z`.
The two verified branches may advance only after the complete fresh verifier
passes, preservation checks succeed, and the exact publication tree is checked.
The top-level `verification/results.json`, `axioms.log` and `build.log` are
omitted from an interim publication so old or active whole-tree evidence is
not mistaken for a fresh completed audit. All retained current-run logs are
actual outputs, including genuine failed development checks and cache setup.
