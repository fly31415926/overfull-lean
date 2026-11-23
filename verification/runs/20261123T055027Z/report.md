# Native multigraph actual-copy capacity continuation — 20261123T055027Z

This attempt began from then-fetched verified head `ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6` (tree `8e59576eb2b94c02b6b1072c4afaf29543540db6`) on `continuation-attempt/20261123T055027Z`.

## Mathematical work

`Overfull/MultigraphMatchingProbabilityCapacities.lean` is an uncompiled source attempt to port finite weighted-capacity arguments to genuine multigraph edge copies. It gives scaled copy marginals, selected-copy pool capacity, aggregate pattern capacity, and the correct parallel-copy multiplicity bound. Parallel copies remain separate elements of `E`; an endpoint-pair pattern with m parallel copies is bounded by m rather than one. No numbered manuscript statement or hypothesis was modified and no axiom/admission was added.

## Genuine checks

The environment lacked `lean`, `lake`, and the previous checkout; direct Git transport failed DNS resolution. Thus targeted Lean compilation, `python3 scripts/verify.py`, strict build and stock audit were **NOT RUN** for this source. The finite exact-rational script passed 510 pool equalities for k=1,...,8; this is not Lean verification.

## Concurrent advance discovered before promotion

Before any protected-branch update, fresh remote reads showed that another verified run had already advanced **both** `main` and `verified-bipartite-continuation-2026-11-21` to `98c6b228a997fead863d05041f12799c93fac18b`. Its run `20261123T113235Z` reports a complete verifier pass: 3,683 strict build jobs, 12,055 audited declarations, 128 new verified declarations, 512 source hashes, and unchanged 47/69 numbered coverage. It already implements native weights, signatures, heavy-pool bounds, exact pool weights, boundary compression, compression cuts and native pattern construction.

Therefore this branch is deliberately retained only as **historical/stale-base attempt evidence**. Its source overlaps work now verified more strongly on `98c6b228...`. The two protected branches were not moved or overwritten by this run.

## Authoritative next target

Resume from `98c6b228...` and its handoff. The next new obligation is simultaneous native reserve realization and residual safety: choose/round native signature multiplicities, realize them by pairwise edge-disjoint actual boundary matchings under copy-pool capacities, complete prescribed boundaries in robust cores, then prove residual regularity and no-overfull odd-cut safety before invoking the checked assigned-part/joining decomposition. Full 4.6 and the main theorem remain open.
