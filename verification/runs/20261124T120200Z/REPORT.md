# Four-label reduction continuation: completed verification

The frozen full verifier and the independent baseline-preservation gate both
passed. This continuation adds 11 mathematical modules containing 73 public
proof declarations and 205 audited declarations in total, including private
and generated proofs. The project now has 14,260 audited declarations and
2,609 completed-result mappings.

The manuscript status remains **49 of 69 numbered assertions fully verified**.
All 69 assertion records and statement identities are unchanged. This run
completes supporting results and does not claim the unrestricted four-label
compatible-circuit theorem, the unrestricted terminal factorization
proposition, or the main Overfull Conjecture theorem.

## Exact baseline and completed commands

| Item | Recorded value |
| --- | --- |
| Baseline commit | `e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8` |
| Baseline tree | `9013f6d5c07676ba130d4bb794062d700bab6136` |
| Lean version | 4.24.0 |
| Full attempt | `full-01` |
| Actual verifier command | `python3 scripts/verify.py` |
| Full strict build | `lake build --wfail Overfull`, successful; 3,846 jobs reported |
| Stock kernel audit | `lake env lean Audit.lean`, successful |
| Verifier child / wrapper exit | 0 / 0 |
| Full run start | 2026-11-24 12:23:17.190555 UTC |
| Full run finish | 2026-11-24 12:43:51.679433 UTC |
| Full run elapsed time | 1,234.488932387 seconds |
| Independent preservation check | Passed at 2026-11-24 12:43:58.020228 UTC |
| Frozen inputs | 794, all unchanged during and after the full run |
| Frozen verification controls | 16, all unchanged |
| Archived verifier outputs | 24, all matching their live output bytes |
| Allowed axioms | `Classical.choice`, `Quot.sound`, `propext` |

The command and terminal receipts are byte-identical. The runner recorded
no wrapper errors, no changed inputs or controls, and no missing principal
outputs. The stock `Audit.lean` remained byte-identical to the baseline. The
full audit completed normally; it was neither interrupted nor replaced with
a shortened checker.

The completed commands, run from the repository root, were:

```text
python3 verification/runs/20261124T120200Z/index-development.py
python3 verification/runs/20261124T120200Z/run-verifier.py full-01
python3 verification/runs/20261124T120200Z/check-preservation.py full-01
```

`full-01` is an immutable attempt directory. A later verification must use a
new attempt name rather than overwrite this receipt or its archived inputs.

## Mathematical results and their limits

The six degree-two modules construct a compatible circuit partition for an
admissible even-degree selected-copy instance on four labels whenever one
label has degree at most two. The other degrees are unrestricted. Degree
zero reduces to the existing complete three-label theorem. Degree two is
handled either by removing and restoring a parallel two-circuit, or by
suppressing a two-edge path, proving every residual class-cut inequality,
solving the resulting three-label instance, and restoring every original
copy. The public theorem assumes no residual partition or lifting certificate.

The bounded-degree module combines this construction with the previous
complete four-regular result. It proves existence when every selected degree
is at most four, and separately when there are at most eight actual selected
copies. The eight-copy conclusion permits unequal degree sequences with some
degrees larger than four. The corresponding necessary conditions for a
hypothetical unresolved four-label instance are minimum degree at least four,
degree at least six somewhere, and at least nine actual copies. These are
necessary conditions, not an assertion that a counterexample exists. The
module also transports the proved existence results to arbitrary finite
vertex types with at most four vertices.

The cut-criterion module gives exact tight-cut and near-tight-cut witnesses
for preserving admissibility after circuit deletion. It identifies the
remaining deletion obligations without assuming that a suitable circuit can
always be selected. The global-coarsening module proves that simultaneous
local coarsenings at tight incidence classes preserve every admissibility
cut inequality. This preprocessing result is generic in the vertex type
and does not require Eulerianity. Compatible circuits for the coarser classes
remain compatible for the original classes on the same copies.

The finite triangle-selection module proves a bundle-selection result under
its explicit endpoint-coordinate and corner-class hypotheses. Its conclusion
selects actual members with the three required class inequalities. Applying
it to a graph still requires the endpoint-bundle identification and the
appropriate critical-cut witnesses. It does not establish safe triangle
deletion or unrestricted four-label existence.

The joining module derives exact original-host matching families in three
stated regimes: at most four even fibers with one boundary of size at most
two; at most four even fibers with all boundaries of size at most four; and
two odd fibers with a small boundary at a distinct even fiber. The regular
host and no-overfull-set hypotheses supply admissibility and parity. In the
two-odd case the virtual multiplicity is unrestricted, and exactly that many
distinct primary pieces are obtained. Primary pieces have at most three
original copies, surplus pieces at most four, and the families are pairwise
disjoint with exact coverage of all joining copies. These are circuit-stage
constructions under explicit boundary hypotheses.

Detailed statement correspondence and proof scope are recorded in the
[semantic review](../../../docs/four-label-reduction-semantic-review.md) and
[verification map](../../../docs/four-label-reduction-verification.md).
Independent reviews of the exact final sources are retained in
[degree-two and bounded joining review](independent-degree-bounded-review.md),
[cut and coarsening review](independent-cut-coarsening-review.md), and
[suppression and triangle review](independent-suppression-triangle-review.md).

## Source inventory and complete declaration map

The [source inventory](../../../docs/four-label-reduction-source.json) identifies
all 11 new modules, their exact SHA-256 hashes, and 73 public proof declarations.
The verifier checks nine named public endpoints as well as the full mapped
inventory. The [generated declaration map](../../four-label-reduction-declarations.json)
contains all 205 audited proof declarations owned by the new modules, including
every private and generated proof. Preservation independently compared this
map with the actual full audit.

| Evidence | SHA-256 |
| --- | --- |
| Source inventory | `864630c0280280c1770b6810fede29a01377e829ace1aa8b74204ea293ec974f` |
| Complete new declaration map | `439221fd2742d52d101f95f009fa085170d7ad66f26ec81eedcecce2cb8624c9` |
| Full project results | `593c1cd44d7000546e14e15be1a4a2e639c597a7b36c51d66c1d0148b1905900` |
| Genuine full command receipt | `02c16881a3f0b32cc3f80304451e599fbc11c838dfbb6eee73a6aa8e23ce815b` |
| Full raw command output | `a0ae96d437ca48999098f4fde42f316df5c21407acc80276eef21b7a04292271` |
| Independent preservation report | `0c48080a95476e87cf439ee2372fe6cc032d81f1e6dcfd3368c92219cb27bfe3` |

## Baseline preservation

The independent gate remained anchored to the original baseline HEAD and
confirmed all of the following:

- All 14,055 prior audited declarations retain their names, owning modules,
  and transitive axiom sets.
- All 2,536 prior completed-result mappings are retained exactly.
- Every previous source/declaration map is unchanged, including its bytes.
- All old nonroot mathematical source files and the stock audit are unchanged.
- All 69 numbered assertion records and statement identities are unchanged.
  The completed count remains 49 and `main_theorem_verified` remains false.
- The verifier differs from baseline only by four exact recorded additive
  registrations. Existing guards, axiom restrictions and coverage checks remain.
- Root imports differ only by the four exact recorded additional import lines.
- Every frozen input, verification control, raw output, archived output,
  and indexed development evidence file matches its recorded hash and size.

The [preservation report](preservation.json) records these checks and the
baseline's 779 frozen inputs. The full current input snapshot contains 794.
The extra 73 public proof mappings raise the completed-result-map total to
2,609 without promoting any numbered manuscript assertion.

## Genuine setup and development evidence

Lean 4.24.0 and all exact pinned dependencies were restored, and the stock
Vizing setup succeeded. The initial Mathlib cache restoration failed because
the shallow ProofWidgets checkout lacked its release tag; the exact pinned
tag was fetched. A later broad cache download received HTTP 429. The required
cache roots were then restored with lower request concurrency and rate, and
extracted while holding the shared build lock. Original failures and successful
retry outputs remain under [setup](setup/); no dependency-source bypass was used.

The [development index](development-index.json) preserves 334 files from
26 attempts: **10 passed, 13 failed, and 3 interrupted**. The interrupted
baseline warmup and two premature focused builds retain their original
in-progress receipts, with separate actual owning-tool exit-130 observations.
Their Lean child exits and input-change status were not observed and remain
unknown. They are not counted as successful builds. One development attempt,
`d2-reassembly-02`, recorded input changes during its command; that fact is
retained. The final full run had no changed inputs or controls.

The exact final degree-two, bounded and joining sources match the successful
focused attempts `d2-final-02`, `four-bounded-02`, and `four-joining-02`.
The corresponding strict builds reported 3,124, 3,131 and 3,174 jobs, all with
exit zero and unchanged inputs. The cut, coarsening, suppression and triangle
reviews likewise identify their genuine successful final-source receipts.
These focused checks supplement the completed full verification.

## Reviewable evidence and publication boundary

The principal evidence is the [full command receipt](full-01/command.json),
[terminal receipt](full-01/terminal.json), [raw output](full-01/output.log),
[frozen input inventory](full-01/frozen-inputs.json),
[frozen control inventory](full-01/frozen-controls.json),
[full project results](../../results.json), and
[independent preservation report](preservation.json). Exact input and control
copies, plus the actual verifier outputs, are archived inside `full-01/`.

HEAD was still the baseline commit when both gates passed. This report was
added afterward without changing a frozen source, document or control file.
Publication uses its separate exact Git-object transport, target-tree checks
and both-branch readbacks under [publication](publication/). This report records
the completed verification checkpoint and does not substitute for those
publication receipts.
