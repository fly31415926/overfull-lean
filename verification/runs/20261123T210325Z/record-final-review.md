# Supplementary preservation checker: pre-execution review

The checker is ready for execution after the latest full verifier has passed
and the actual preceding native-reserve verified commit is available locally.
This note records code review, not a successful preservation run.

Reviewed checker SHA256:
`74e94106c15389c46baae662051a7e2b734c66e3295e4b4c48b87ef0c94a5c0a`.

Python AST parsing and in-memory syntax compilation both completed with
exit code 0. The checker's `main` and preservation helpers were not executed.
At the last observed status, `full-03` remained running, had no exit code,
and had not produced a new `verification/results.json`; the checker must
therefore remain blocked.

An independent read-only review inspected current command metadata, source
snapshots, manifest schemas, actual log format, and verifier output order.
It found no current-schema mismatch in the latest-attempt gate, string or
dictionary source-hash handling, completion timestamps, raw audit parsing,
or exact console reconstruction. It independently confirmed the 12 source
module hashes and 75 explicit public proof entries.

That review identified one missing preservation check: preserving generated
old declaration maps alone does not preserve scope and source-line metadata
in earlier source manifests. The checker now requires every previous
verification input to remain byte-identical except the explicitly updated
README, continuation handoff, and verifier. The verifier is independently
restricted to the exact four recorded additive edits. The four new
residual-palette input paths are also explicit. Earlier source/provenance
manifests and proof-map documents are consequently preserved.

The checker pins the genuine `full-01` and `full-02` failure records, their
frozen inputs and logs, the initial manifest error, setup observation, and
initial integration tool output. It validates every archived development
file against `development-archive.json` and preserves all tracked prior
verification/recovery paths other than the five current live outputs.

After successful execution, the checker copies only actual current evidence
and writes `preservation.json` and `final-report.md`. Their publication status
remains pending. They distinguish the source-only checkpoint from the actual
preceding verified commit and retain the explicit palette hypotheses and
unfinished internal-completion/factorization scope.
