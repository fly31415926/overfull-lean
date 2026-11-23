# Continuation handoff — concurrent verified native-pattern checkpoint supersedes this attempt

The current authoritative verified remote is **not** this branch. Fresh readback before promotion found both `main` and `verified-bipartite-continuation-2026-11-21` at `98c6b228a997fead863d05041f12799c93fac18b`. Resume from that commit and its `docs/continuation-handoff.md` and `verification/runs/20261123T113235Z/` records.

The verified run at `98c6b228...` reports a complete unchanged verifier pass with 3,683 strict build jobs and 12,055 audited declarations, preserving all 11,927 declarations from its previous verified baseline and adding 128 verified declarations. It has 512 Lean source hashes and 79 verification-input hashes. Coverage remains 47/69; full Corollary 4.6 and the main theorem are still unproved. It implements the native two-core weight/signature/pool/boundary-compression bridge that this stale-base attempt was independently pursuing.

This branch, `continuation-attempt/20261123T055027Z`, began earlier from `ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6`. It contains an **uncompiled, unaudited** `Overfull/MultigraphMatchingProbabilityCapacities.lean` plus exact finite arithmetic evidence. The environment had no Lean/lake or old checkout and direct Git transport failed DNS. No full verifier was run here. Keep this branch only as honest historical attempt evidence; do not merge it over the newer verified native modules.

## Next concrete proof target from the authoritative checkpoint

Implement simultaneous native reserve realization and residual safety described in `verification/runs/20261123T113235Z/next-native-reserve-target.md` at `98c6b228...`:

1. Build the native actual-copy pool catalog for the internal exceptional pool, each exceptional-to-core pool, and the old-core crossing pool; prove pairwise disjointness.
2. Instantiate the graph-independent rounding/selection APIs with native signatures and multiplicities, preserving positive-weight representatives and exact copy-pool capacities.
3. Realize all prescribed rounds simultaneously as pairwise edge-disjoint actual boundary matchings with exact pool accounting and even uncovered core orders.
4. Complete them in the robust cores while preserving prescribed copies.
5. Prove residual regularity **and** no-overfull odd-cut safety from exact cut losses; regularity after perfect-matching deletion alone is insufficient.
6. Apply the already checked assigned-part/joining decomposition, then palette grouping, auxiliary regularization, robust completion and final factorization.

Do not collapse parallel copies or reuse a simple-host endpoint-pair weight bound of one. Preserve the same heavy representative when connecting signature and crossing statistics. Full 4.4/4.5/4.6, remaining 4.16 cases, Section 6, structural inputs and the main theorem remain separate gaps.

No supported operation in this runtime can open a fresh ChatGPT conversation. The public repository handoff is the durable continuation point.
