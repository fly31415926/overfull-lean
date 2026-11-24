# Verified outcome of the four-label continuation

The actual `full-01` verifier and its wrapper both exited zero. The run
finished at 2026-11-24T14:20:27Z after 1,077.85 seconds. The strict
`lake build --wfail` completed 3,874 jobs. The unchanged stock kernel audit
reported `OVERFULL_AXIOM_AUDIT_OK 14627`.

The separate preservation gate passed at 2026-11-24T14:20:51Z. It checked
826 unchanged frozen inputs, 17 unchanged frozen controls, and 25 genuine
archived outputs. All 14,260 prior audited declarations retain their names,
owning modules, and transitive axiom sets; all 2,609 previous completed-result
mappings and all previous declaration maps are preserved.

The new source inventory has 28 modules and 168 public theorem proofs.
Its complete kernel declaration map has 367 entries, including private and
generated proofs. The only permitted transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The main new endpoint is unrestricted compatible-circuit existence for any
finite label type of cardinality at most four, from the original half-cut
inequalities and even degrees. Its exact necessary-and-sufficient criterion
and the original-host even-fiber and exactly-two-odd-fiber joining circuit
stages are also complete. No degree or parallel-multiplicity bound is an
assumption of the compatible-circuit theorem.

Numbered manuscript coverage remains 49/69. No assertion identity or completed
record changed. Full Proposition 4.16, Theorem 4.17, and the main theorem
remain incomplete. The next target is four-copy bounded grouping followed by
the remaining four-core terminal factorization cases.

The full evidence is in `../full-01/terminal.json`,
`../full-01/artifacts/verification/results.json`, and `../preservation.json`.
Development evidence retains all 81 attempts: 40 passed, 41 failed, and none
interrupted. This outcome records successful local verification; publication
is established separately by the publication receipts and remote readbacks.
