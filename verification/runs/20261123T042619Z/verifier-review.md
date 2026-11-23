# Independent verifier preflight review

Run: `20261123T042619Z`.
Reviewer: `recreate_cuts_0427`.
Baseline: `5f46a36d87f9ca1cee382f46687d9d155b9b5bc2`, which was also local
`HEAD` during this review.

**Result: no verification-gate regression or numbered-completion change was
found.** This is a read-only source/configuration review, with the present
report as its only written artifact. It does not execute `scripts/verify.py`
and does not claim a complete build or audit passed. The author did not
edit the verifier, manifests, coverage, audit, or project sources in this
review task.

## Exact reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `scripts/verify.py` | `001cd0700f8242fbd025a7233871ad4d037b4c2180f4c1e100257e6b2e28db99` |
| `Audit.lean` | `76886fd9261a3a7b07660f9a434272c0347130a4013cf57da6e1761a34fc6603` |
| `docs/coverage.json` | `488f809627ac4792d486f750b3a58cdfe4d20009ea2c37c963da6192bf0e0c44` |
| `docs/manuscript-source.json` | `875b84338e1fe04d74d4365d23dd9327904dbed6ffe4d01eecc5ff23d88c6969` |
| `docs/joining-circuit-source.json` | `f54ae88562c658c9093b7669dcdb368d3ca5f2dabb1e2c0dce6e3035916b1d69` |
| `docs/assigned-part-source.json` | `aa739836e310643ff1e15ae318f58b2e56fafa3d15a4f1c7b6c92edaf0f6a299` |

The stock audit is byte-for-byte identical to its baseline version. Its
hash also equals `stock_audit_sha256` in the unchanged
`docs/checkpoint-reconstruction-source.json`.

## Existing gates are preserved

The complete verifier diff was inspected. Its only modifications are:

1. Register the joining and assigned source manifests in the existing
   extension-manifest checking loop.
2. Require zero additional completed numbered assertions from each of
   those two manifests.
3. Add their declaration-map output basenames.
4. Include the two declaration-map evidence records in the final results.

A read-only textual projection removed exactly those additions from the
current verifier and compared the resulting text with `git show
5f46a36d87f9ca1cee382f46687d9d155b9b5bc2:scripts/verify.py`. The comparison
was exact. This confirms that the previous gate code was preserved,
including its existing completed-result catalog and failure behavior.
The current Python program also parsed successfully with `ast.parse`;
it was not executed for this review.

In particular, the verifier still invalidates any earlier `results.json`
before work, checks the pinned Lean and mathlib configuration and actual
dependency checkouts, checks historical recovered sources and their
manifests, and rejects missing project imports. It still runs the strict
`lake build --wfail`, then the complete `lake env lean Audit.lean`.
Subprocess failures still abort. The audit marker must equal the full
number of emitted declaration records, and the actually imported project
module set must equal the complete source inventory.

The unchanged stock audit traverses theorem declarations from all imported
`Overfull` and `Vizing` modules, rejects declared axioms in those modules,
and checks each theorem's transitive axiom set. Its only permitted logical
axioms remain `propext`, `Classical.choice`, and `Quot.sound`. Private and
generated theorem declarations are included in that traversal.

## Joining and assigned mappings are enforced by the fresh audit

The existing extension loop now applies to both new groups. Before the
compiler runs, it checks unique module inventories, exact path-to-module
identity, exact source hashes, unique public names, per-module counts,
total counts, and equality with the required-proof name list. After the
fresh complete audit, every listed public name must be present and its
audited module must equal the mapped module. The declaration output then
collects all audited theorems in the listed modules, including private and
generated proofs, and requires every reviewed module to appear.

The current manifest contents were independently inspected without running
their generators:

| Group | Modules | Public proofs | Source hashes current | Public names and source lines match |
| --- | ---: | ---: | --- | --- |
| Joining | 5 | 75 | Yes | Yes |
| Assigned parts | 5 | 43 | Yes | Yes |

The assigned count is `3 + 7 + 23 + 8 + 2`, including both same-host and
separate-host joining wrappers. The joining count is
`17 + 29 + 11 + 3 + 15`. There were no duplicate names or inconsistent
required-proof lists. A namespace-aware public-declaration scan agrees
with every recorded name and source line. An initial basename-only
convenience check produced false positives for qualified declarations
such as `IsMatching.edgeSupport_card`; correcting the reviewer check to
respect namespace-qualified theorem tokens resolved those diagnostics
without changing any project file.

A separate read-only import traversal found **503 first-party modules,
all 503 reachable from `Overfull.lean`**, with no omitted mathematical
module. The full verifier will still check the actual imported module
set independently after compilation.

## Manuscript coverage is preserved

Parsed baseline and current coverage records were compared directly:

- Both inventories contain the same **69 numbered assertions**.
- All **69 original `statement_sha256` values are unchanged**.
- All **69 `full_assertion_verified` flags are unchanged**.
- The **47 previously completed assertion records are exactly equal as
  JSON objects**, including their proof mappings and scope fields.
- The only changed numbered record is incomplete **4.6**. It adds the
  joining/assigned supporting components and explains the remaining
  two-core obligations; its original statement hash and incomplete flag
  remain unchanged.
- Both main-theorem flags are false; the declared completed total is
  still 47. The two new source manifests each declare zero additional
  completed numbered assertions.

The verifier retains its count checks, audited-proof requirements for
completed assertions and catalog components, explicit incomplete-assertion
guards, pinned full 4.2/4.14 mappings, and the main-theorem guard. The
baseline/current comparison of all 69 original statement hashes is this
review's additional direct check; it is not a claim that the verifier
gained a new general baseline-comparison gate.

## Publication boundary

No current whole-repository result is established by this preflight.
Publication as a new verified source checkpoint still requires the
unmodified complete verification flow to finish successfully on the final
candidate. The generated declaration maps, source/input hashes, and final
results must come from that actual run.
