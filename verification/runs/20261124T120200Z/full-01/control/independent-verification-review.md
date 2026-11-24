# Independent review of verifier registration and scope

## Reviewed integration

The reviewer inspected the root agent's four additive changes to
`scripts/verify.py`, their exact `verifier-additions.json` anchors, the generated
registration patch, `prepare-integration.py`, the new manifest generator, and
the supporting semantic and verification maps. A direct reconstruction from
baseline `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` confirmed that the live verifier
contains precisely those four additions. `Audit.lean`, `docs/coverage.json`, and
`docs/manuscript-source.json` were independently compared with their baseline
bytes and are unchanged. Python parsing of the relevant code passed.

The registration adds the new source inventory to the existing extension-map
loop, checks its support-only status and nine exact public endpoints, gives
its generated declaration map a distinct basename, and retains that map in
the final report. The existing loop still checks source hashes, unique public
proof names, actual audited ownership, complete private/generated proof
declarations, and the imported-module inventory. Every prior guard, result
registration and axiom restriction is retained. The completed-assertion count
remains 49, and the new guard explicitly rejects a numbered closure or a
main-theorem claim by this continuation.

The final manifest generator enumerates six new `FourDegreeTwo*.lean` files
plus the bounded-degree, cut-criterion, joining, global-coarsening and finite
triangle-selection modules. The resulting inventory contains 11 modules and
73 public proof declarations. It reuses the previous source parser, checks
duplicate names and the nine required endpoints, and records exact file
hashes and public source locations. Its inventory is separate from kernel
verification. The complete audit must still demonstrate that each mapped
name exists in its claimed module and that every new private/generated proof
is included in the emitted declaration map.

An initial root-import format mismatch was reported: the integration script
first proposed prepending module names, while the preservation guard expects
full import lines inserted immediately before the original root's first
module documentation comment. The root agent corrected the script before
applying the imports. The final preflight checks the exact recorded lines and
requires every imported endpoint module to appear in the new source inventory.

## Scope and preservation

The endpoint list is consistent with the documented support-only scope:
four-label degree-at-most-two reduction, bounded-degree and eight-copy
consequences, necessary bounds on a hypothetical unresolved instance, exact
cut deletion criteria, global admissibility after tight local coarsening,
and original-host joining decompositions under explicit
small-boundary hypotheses. The additional finite triangle selector is mapped
with all its public and audited proofs; it does not add a numbered endpoint
or claim safe circuit deletion. No general four-label compatible-circuit theorem,
full terminal proposition, full regular factorization theorem, or main theorem
is registered by this addition. All 69 assertion records must remain identical.

The ninth endpoint was reviewed after its addition. A locally tight class
occupies half of its vertex's incidence set. Applying its original half-cut
bound to the shore with that vertex toggled proves the complementary class's
bound on the original shore. Thus the proposed simultaneous coarsenings really
preserve all cut inequalities, without requiring Eulerianity or four vertices.
Coarse compatibility transfers to original compatibility on the same copies.
This is a valid preprocessing result; it does not construct a circuit partition
for arbitrary four-label input, and the registration makes no such claim.

The preservation gate uses the public baseline's 14,055 audited declarations,
2,536 completed-result mappings and 779 frozen inputs. It requires all old
nonroot mathematical sources, the audit, old maps, statement identities,
declaration owners and transitive axiom sets to remain unchanged. Only exact
recorded additive root imports and verifier registration, plus current README
and handoff prose, are allowed to change among the existing source inputs.
The actual full command is run after freezing inputs and controls; a successful
receipt also requires unchanged bytes during execution and complete output
archives. The permitted axiom set remains `propext`, `Classical.choice`, and
`Quot.sound`.

## Genuine setup and development evidence

Lean 4.24.0 and all pinned dependencies were restored. The initial Mathlib
cache attempt failed because the shallow ProofWidgets checkout lacked its
release tag; fetching the exact pinned tag resolved that error without source
edits. A subsequent broad download hit HTTP 429. The successful required-root
retry used reduced request concurrency and rate, followed by extraction under
the shared build lock. Original failed outputs and all retry receipts remain.

Two premature focused builds were interrupted before the cache recovery
finished. A later baseline warmup was also interrupted at the supervising
parent's request after sufficient old modules had been rebuilt, so focused
proof debugging could proceed. The final frozen gate must still complete the
whole project. These attempts' original in-progress command receipts and raw outputs are
preserved, with separate owning-agent tool receipts showing exit 130. Their
Lean child exits were not observed and are recorded as unknown. They are
indexed as interrupted, never as passed. Later recorder versions retain their
own exact source per attempt and include ordinary Python interrupt cleanup.
Direct tool cancellation can stop the wrapper before that cleanup is observed;
the interrupted baseline attempt therefore also retains an unknown Lean child
exit. No tool exit is silently substituted for a Lean exit.

This review does not claim that the complete Lean build or axiom audit has
already passed. The genuine full-attempt terminal receipt and subsequent
preservation report determine that outcome. Publication likewise requires
its separate exact-tree and both-branch readbacks.
