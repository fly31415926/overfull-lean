# First continuation run: complete compatible circuits on at most three vertices

**Verification passed.** The complete original half-cut and even-degree
hypotheses now yield an exact compatible circuit partition on every finite
vertex type of cardinality at most three. All selected pieces retain the
original edge copies. The theorem allows arbitrary class types, parallel
multiplicities, isolated vertices and empty selected copy sets.

Run began at `2026-11-22T23:59:31+00:00`; this verification record was completed at
`2026-11-23T00:26:51.638339+00:00`. The base was `b5afb03a0f0613eedd0cb3310e06706942afe2e7`. An interim recovery
checkpoint, `af6c68a561b0beae97d693b6ee099a230a294988`, preserved the sources
while the full audit was running.

## Genuine checks

| Check | Result |
| --- | --- |
| Complete verifier | Exit 0 |
| Strict repository build | 3,665 jobs passed |
| Unchanged full axiom audit | 11,727 declarations passed |
| Previous audited declarations preserved | 11,514, with unchanged modules and axiom sets |
| New audited declarations | 213 |
| New proof modules | 11 |
| New mapped public theorems | 94 |
| Recorded Lean source hashes | 494 |
| Recorded verification input hashes | 67 |
| Numbered manuscript assertions | 47/69 complete; 22 remain |

The only allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. All 482 pre-existing non-root Lean sources,
including `Audit.lean`, are byte-identical to the base. The root gains one
import and retains every previous line. All 69 original statement hashes,
all 47 completed assertion records, and all five older declaration maps
are preserved. `run.json` records exact evidence hashes.

## New proof and precise scope

The construction proves local tight-class coarsening, unequal-bundle safe
pair selection, equal-bundle safe pair/triangle selection, exact singleton
cut reduction, actual vertex renaming, the unconditional three-label
selector, strong induction with exact disjoint coverage, and injective
padding to arbitrary finite vertex types with at most three vertices.

The final interface is
`Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_three`.
It assumes neither a selector nor a pre-existing compatible partition.
The iff theorem proves necessity and sufficiency under even degrees.
The independent semantic review is in
`docs/three-label-circuit-semantic-review.md`; the complete source and
public declaration inventory is in `docs/three-label-circuit-source.json`.

No numbered assertion is newly declared complete. General four-label
compatible circuits, the remaining original-host joining construction in
the two-core branch of 4.6, terminal 4.16, general Section 6 and the main
theorem remain open. The original reconstructed `cb05ef5` provenance is
preserved and is not confused with this new run.

## Development corrections and continuation

Targeted compiler iterations corrected decidability-instance rewrites,
an implication-notation syntax error, and a specialized parallel-pair
helper that duplicated an existing declaration. The duplicate was removed
and the existing checked theorem reused. No admission, additional axiom,
weakened original hypothesis, or disabled verification gate was retained.
Earlier targeted failures are summarized here; their raw terminal output
was not separately captured in the published log files. The retained
public-name check and full-verifier logs contain their actual command output.

Read `docs/continuation-handoff.md` and `next-target-assessment.md` in this
run directory before continuing. `manuscript-recovery.md` records the
source-identity check result for statements 4.4, 4.5 and 4.6: all three
hashes matched the pinned original inventory. Automatic approval review
blocked public upload of the recovered manuscript excerpts because they
came from a private workspace. The actual hash-check output is retained,
but all recovered statement and proof text is withheld; it cannot be
rehashed from the public record alone. Identity of the entire newer
manuscript or its proof text is not claimed. The extended source
assessment was also withheld after automatic approval review. The public
target file points to the checked Lean interface and existing handoff
for remaining proof obligations. The new Lean proofs
were completed before the separate source-recovery task.

This report records verification, before the remote branch update. The
containing publication commit and final delivery identify the published
state and confirm both requested branches.
