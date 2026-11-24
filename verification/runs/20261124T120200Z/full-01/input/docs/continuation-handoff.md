# Continuation handoff: four-label low-degree and cut reductions

## Current mathematical scope

Coverage remains **49/69**, with 20 incomplete assertions including the main
theorem. This round promotes no numbered assertion. All 69 assertion records
and source-statement identities are unchanged. The previous complete
single-core Lemma 3.1, bounded-input Corollary 4.6, three-core composition,
all-four-odd terminal theorem, and exact four-regular compatible partition
remain available.

The new low-degree endpoint constructs a compatible circuit partition from
original admissibility and even degrees on four labels when some label has
degree at most two. It places no bound on the other degrees and assumes no
partition or safe selector. Its proof restricts an isolated label to three
active labels, or handles two parallel incidences, or suppresses a path with
two distinct neighbors and restores the exact original copies and classes.

The existing exact four-regular theorem then gives maximum degree at most
four and at most eight selected copies. Any possible counterexample to
unrestricted four-label existence has every degree at least four, some degree
at least six, and at least nine copies. Arbitrary finite label types of size
at most four are covered by injective padding.

The exact safe-deletion criterion separates tight-cut and slack-two
obstructions. For circuits of length at most three only the tight-cut
conditions remain. A separate theorem proves that tight local incidence
coarsening preserves all global half-cut inequalities. This last result
applies to arbitrary vertex types and degrees, without evenness.

An elementary finite-bundle selector is also proved: if each of three
nonempty bundles is monochromatic at one endpoint, absence of a compatible
triple forces a common monochromatic class on one entire corner. Its graph
support classification and use in the unrestricted induction remain open.

Original-host matching applications cover all-even fibers with a boundary
of size at most two, all-even fibers with every boundary at most four, and
two odd fibers with a small even boundary. The two-odd theorem allows
arbitrary regular degree: it constructs exactly that many primary pieces
of size at most three, plus surplus pieces of size at most four, with exact
copy cover and the stated odd/even footprints.

These are supporting results. Full Proposition 4.16 and Theorem 4.17 remain
incomplete.

## Baseline and evidence

The authoritative baseline is public commit
`e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8`, tree
`9013f6d5c07676ba130d4bb794062d700bab6136`. Both public branches were
independently read back before this round. It contains 9,163 tracked files,
14,055 audited declarations, 2,536 completed-result mappings and 779 frozen
source/input hashes.

The repository is `/workspace/scratch/77adbfc63087/overfull-lean`, with local
working branch `continuation-20261124-four-circuits`. The run is
`verification/runs/20261124T120200Z/`. Its immutable terminal receipts,
frozen inputs/outputs, preservation report and publication readbacks
determine actual verification and publication status. A handoff or focused
build alone is not a full audit or publication receipt.

Principal source endpoints are in:

- `Overfull/CompatibleCircuits/FourDegreeTwo.lean`
- `Overfull/CompatibleCircuits/FourBounded.lean`
- `Overfull/CompatibleCircuits/FourCutCriterion.lean`
- `Overfull/CompatibleCircuits/FourGlobalCoarsening.lean`
- `Overfull/CompatibleCircuits/FourBoundedJoining.lean`

The complete inventory is `docs/four-label-reduction-source.json`. Its
semantic review and verification map describe all eleven modules, exact
hypotheses, cut identities and original-copy restoration. The generated
declaration map includes private and generated proof names.

Every prior nonroot mathematical source and `Audit.lean` is byte-identical.
The root receives only four imports. The verifier receives precisely four
reviewed additive map registrations, without changing previous guards,
coverage or the transitive axiom policy. The complete frozen gate preserves
every old declaration, owner, axiom set, completed-result mapping, prior
source/declaration map, and all 69 assertion records. Allowed axioms remain
`propext`, `Classical.choice`, and `Quot.sound`.

The run retains actual failed and successful development commands and setup
attempts. Interrupted preliminary tool sessions retain their observed tool
status; an uncaptured Lean-child exit is not invented. Frozen final builds
require unchanged inputs. Publication has separate exact-tree and branch
readbacks for `main` and `verified-bipartite-continuation-2026-11-21`.

## Next mathematical obligations

1. **Unrestricted four-label compatible circuits.** The remaining degree
   range has four positive even degrees, all at least four, with one at least
   six. A reduction must preserve global half-cut constraints and exact copies.
   `analysis/four-label-selector-route.md` in this run develops a possible
   route using nonlocal tight-shore elimination and a compatible pair/triangle
   selector for strict nonlocal cuts. Its finite support classification and
   two-transposition inequalities require Lean formalization before use.
2. **Nonlocal tight-shore elimination.** The research notes
   `analysis/tight-singleton-suppression.md` and
   `analysis/tight-shore-suppression.md` use the three-label theorem on an
   inside graph and an outside graph. Paths, virtual classes, global cuts,
   and exact restoration still require formal construction. These notes
   are not admitted lemmas or verified claims.
3. **Other four-core terminal cases.** General four-even and two-odd joining
   partitions are still needed beyond the explicit boundary cases above.
   The all-four-odd terminal result is already complete and reusable.
4. **Full regular factorization Theorem 4.17.** The three-core subcase with a
   small linear exceptional set is complete; the four-core range needs the
   remaining terminal cases and uniform composition.
5. **Critical, bipartite and global inputs.** Lemma 3.1 does not alone supply
   the critical corollaries, bipartite branch, all padding results or the main
   theorem. The numbered inventory records their unchanged status.

Retain the earlier diagnostic counterexamples: arbitrary splitting may
violate a nonlocal half-cut bound; an admissible suppressed partition may
fail partwise restoration at a high-degree vertex; a spanning four-regular
layer or compatible spanning two-factor need not exist. Slack-two cuts can
obstruct arbitrary four-cycle deletion even without tight nonlocal cuts.

Do not promote a supporting theorem as a complete numbered assertion,
assume a partition the target must construct, or choose uniform constants
after the host. Preserve every actual copy through all reductions.
