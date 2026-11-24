# Original-host joining decompositions on at most three labels

## Result and original-copy meaning

Let `G : Multigraph V E` be a finite loopless `h`-regular multigraph with
no `h`-overfull vertex set. Let `label : V → I` assign every original
vertex to one of at most three labels. Every joining copy is retained as
an element of the subtype `FourOdd.joiningCopies G label`; parallel
copies are never identified. The results treat two parity cases.

**All fibers even.** The original even-shore cut bounds imply every
endpoint-class half-cut inequality and every quotient degree is even.
The proved small-quotient theorem constructs an exact partition of all
original joining copies into nonempty host matchings of size at most
three. No bound on individual joining degrees is assumed.

**Exactly two odd fibers.** Specify two distinct odd labels `a,b`; all
other fibers are even. Add `h` distinct virtual parallel copies between
those two labels, with one fresh incidence class at both ends. The
original host supplies every augmented half-cut inequality and the
augmentation repairs degree parity. The small-quotient theorem therefore
constructs a genuine compatible circuit partition internally.

Removing virtual copies and projecting through the injective joining-copy
subtype yields the following actual host data:

- Exactly `h` distinct nonempty primary matchings, each with at most two
  original copies.
- A finite family of nonempty surplus matchings, each with at most three
  original copies.
- Disjoint primary and surplus families and pairwise edge-disjoint parts.
- Exact union equal to **all** original joining copies.
- Every primary matching has exactly one crossing copy at each specified
  odd fiber; its fiber-cut count is odd exactly at those two labels.
- Every surplus matching has even fiber-cut count at every label.

These footprint counts are written as original graph quantities
`(G.cutOn M (labelShore label {i})).card`. They are not merely counts in
an unconnected abstract quotient. The original-copy restriction of a
zero-virtual part remains a circuit in the unaugmented joining quotient;
its host projection is a matching. The one-virtual
case records the degree profile and size bound; this development does
not introduce a separate formal connected-path object for that case.

## Main interfaces

All host interfaces below are in the historical namespace
`Overfull.FourOdd`; they do not assume four labels or four odd fibers.

| Declaration | Checked mathematical role |
| --- | --- |
| `joiningQuotient_classCutOn_card` | Exact endpoint-class count as an original cut degree, or zero outside its label fiber. |
| `joiningQuotient_degreeOn_eq_cut` | Selected quotient degree equals the actual host fiber-cut footprint. |
| `joiningQuotient_admissible_of_even_fibers` | Derives all half-cut inequalities from regularity, no overfull set and even fibers. |
| `exists_joining_matching_partition_of_even_fibers` | Constructs the complete all-even joining matching partition. |
| `twoOddJoiningQuotient_admissible` | Derives all augmented original and virtual class-cut inequalities. |
| `twoOddJoiningQuotient_even_degrees` | Derives augmented degree parity from the original fibers. |
| `exists_twoOddJoining_circuitPartition` | Constructs the compatible augmented circuit partition without assuming one. |
| `exists_twoOddJoining_decomposition` | Constructs the complete primary/surplus original-copy matching data. |

`TwoOddJoiningDecomposition` exposes the actual finite families and their
counts, matching properties, disjointness, coverage, and host footprints.
The separate `exists_joining_matching_partition_of_even_degree_bound`
wrapper openly assumes an even regular degree and joining degree at most
`D`, with `2 * D ≤ h`. That extra sufficient condition is not used in the
all-even-fiber or two-odd-fiber results and is not attributed to the full
manuscript assertion.

## Proof chain

| Module | Contribution |
| --- | --- |
| `QuotientCuts` | Actual-copy cut and endpoint-class transport; host cut bounds; all-even and two-odd fiber parity; singleton-fiber obstruction. |
| `PairAugmentation` | One virtual family on arbitrary labels; exact cut/degree formulas; admissibility and parity repair; restriction injectivity, coverage and exactly `h` virtual-containing parts. |
| `JoiningPartitions` | Injective whole-partition lifting and actual all-even/generic sufficient host wrappers. |
| `TwoOddQuotient` | Composes the host cut inequalities, fiber parity, augmentation and completed at-most-three theorem. |
| `TwoOddDecomposition` | Converts the constructed augmented partition to exact primary/surplus original host matchings and footprints. |

For a shore not separating the two odd labels, the union of original
fibers is even, so the checked vertex-toggle argument supplies its
half-cut bounds. A separating shore is odd and has at least `h` original
crossing copies. Each original endpoint class has at most `h` copies,
and the augmentation adds exactly `h` crossing copies. The fresh class
and every original class therefore satisfy the augmented inequality.

Compatibility allows at most one virtual copy in each circuit. A
compatible circuit cannot consist entirely of virtual copies, so every
original restriction is nonempty. The restrictions of distinct circuit
indices are disjoint; nonemptiness then makes restriction injective.
This is the reason the exact primary count survives passage to finite
sets of original matching parts.

## Source relation and remaining obligations

The [authorized source excerpts](../verification/runs/20261122T235931Z/authorized-manuscript-recovery.md)
record the exact hash-matched statements of 4.4, 4.5 and 4.6, and the
relevant assigned-part construction from the inspected later proof.
The complete later manuscript and its proof text were not identified
byte-for-byte with the pinned original manuscript.

For the two-core branch of 4.6, the inspected construction has at most
three assigned quotient parts: two core parts and at most one internal
exceptional pair. The present theorems provide the circuit and matching
stage **after** an actual label assignment with the specified parities
has been constructed. They do not construct that assignment, the
preceding reserve selection, palette grouping, robust completion inputs,
regular auxiliary graphs, or the final original-host one-factorization.

Consequently **47 of 69 numbered assertions remain complete**, and full
4.6, full 4.4/4.5, remaining 4.16, general Section 6 and the main theorem
are still unfinished. No numbered statement or original hypothesis has
been replaced by these supporting interfaces.

## Reproduction and evidence

Use pinned Lean 4.24.0 and the committed dependency manifest, including
mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Run:

```sh
python3 scripts/verify.py
```

This performs the strict build and unchanged complete `Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The [source manifest](joining-circuit-source.json) maps every new public
theorem to its source module; the verifier matches them against the fresh
complete audit. Updating that manifest alone is not proof verification.

Fresh source/input hashes and declaration counts are in
`verification/results.json`; exact mapping is in
`verification/joining-circuit-declarations.json`. Genuine setup failures,
targeted compiler diagnostics, source snapshots, and final run evidence
are retained under `verification/runs/20261123T010829Z/`.

## Later recovery continuation

The final publication following the observed 01:47 UTC audit was interrupted.
The five mapped Lean sources retain their exact bytes from the early
checkpoint. This addendum extends the recovered proof notes to identify
the current recovery/assigned-part continuation, which records
its fresh complete checks under `verification/runs/20261123T042619Z/`.
Read the latest `verification/results.json` only with its exact current hashes;
the earlier run directory retains its actual historical targeted checks.
