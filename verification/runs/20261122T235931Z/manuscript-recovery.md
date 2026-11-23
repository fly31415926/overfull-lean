# Manuscript source identity check and publication restriction

The exact statement identities recorded for assertions 4.4, 4.5 and 4.6
were checked against recovered source text. All three SHA-256 values match
the existing public inventory in `docs/coverage.json`. This is a source
identity check, not an additional Lean proof. The actual check output is
in `source-statement-hash-check.log`, with method and limitations in
`source-statement-hash-check.json`.

## Public-release boundary

Automatic approval review rejected uploading the recovered manuscript
statements and proof excerpts because the source came from a private
workspace and the existing publication authorization did not clearly
cover disclosure of that connector-sourced text. The source text and
source-specific proof passages have therefore been withheld from this
public checkpoint. No verbatim replacement or indirect disclosure is
included here. `publication-restriction.json` records the blocked action.

This public record establishes what identity checks were actually run,
but the withheld statement bytes cannot be reconstructed or independently
rehashed from this record alone. Identity of the entire recovered
manuscript and its proof text is not asserted. The exact statement hashes
already in the public repository remain unchanged.

The new Lean proofs were completed before this source-recovery task.
They do not depend on publishing these recovered excerpts. The complete
strict build, stock axiom audit, declaration maps, source hashes, and
preservation checks are recorded separately. The next proof interfaces
and mathematical obligations established from public repository sources
are described in `next-target-assessment.md`.
