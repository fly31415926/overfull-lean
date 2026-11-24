# Weighted palette continuation: proof map and public inventory

This supporting continuation adds **five Lean modules, 41 explicit public
theorem proofs, and four definitions**. The authoritative source inventory
is [weighted-palette-source.json](weighted-palette-source.json), which records
every public name, module, source path, and SHA-256. The complete verifier's
declaration map also includes private and generated support declarations;
the source-level count of 41 is not a global audit total.

**Coverage remains 47/69.** These ingredients complete no additional numbered
assertion. Full Corollary 4.6 and the main theorem remain unproved.

The baseline is public `c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2`, with exact
tree `6a9e73eee4e944b104ff98630b04655e8bfb959d`, reproducing local checkpoint
`89678bc`. Both public verified branches were independently read back at
that baseline. The prior publication blocker is resolved. This document
describes the new local run `20261123T230808Z` and does not assert publication
of the weighted continuation itself.

## Principal contracts

### Dynamic extension with complete resource accounting

`Overfull.NativeReserve.exists_weighted_palette_extension` takes a proper
seed coloring on `P` contained in a finite target `T`. Seed color counts and
resource loads are explicit certificates. New items have resource weight
at most `q`; **total resource weights include every item of `T`, including
seeds**. A total bound `K*(W-q+1)` limits each resource's overloaded colors
to `K`. With `q<=W`, the strict forbidden-color margin and the piece-capacity
bound, the construction extends the seed coloring while preserving
properness, capacity `L`, and whole-color resource load `W`. Only the
surplus `T \ P` must avoid the protected label set `Q`.

### Actual blocked star copies

`Overfull.WeightedPalette.starBlockedCopies` filters original copies from
the exception `z` to its old-core set `U` by whether their **old-core endpoint**
belongs to the piece support. `starWeight` is that set's cardinality.
`starWeight_eq_sum_parallel` identifies it with the sum of actual parallel
multiplicities at occupied core vertices. Bounds on multiplicities and the
support of three-copy pieces give `6*b`; two-copy primary pieces give `4*b`.

`sum_starWeight_le_mul_degree_bound` derives the total `D*h` bound from
actual edge-disjoint pieces, containment in a set of bounded incidence,
and the degree cap at the exception. `starBlockedCopies_biUnion` and
`starWeight_groupedCopies_le` bound blocked copies of the **complete grouped
class**, with all original copy identities retained.

### Weighted grouping into actual matchings

`Overfull.WeightedPalette.exists_star_weighted_matching_grouping` applies
the extension to those actual star weights for at most two resources.
Inputs include actual matching pieces of size at most three, pairwise
edge-disjointness inside a set of maximum degree `D`, parallel multiplicity
at most `b`, exceptional degree at most `h`, explicit seed properness/count/
weight certificates, and

```text
0 < h,  b <= D,  128*D <= h,  2*|Q| <= h,
|I| <= L * (h - |Q| - 32*D).
```

The natural arithmetic derives `6*b<=h/8`, at most `13*D` overloaded labels
per resource, and the positive protected palette gap. The result is an
actual coloring of the indexed pieces with all of the following properties:

- prescribed seed labels are unchanged, and only seeds use protected colors;
- each protected class equals exactly the union of its prescribed seeds;
- endpoint-conflicting pieces receive different colors;
- every grouped class is a matching, and distinct classes are edge-disjoint;
- the union of the grouped classes equals the union of all original pieces;
- actual blocked star copies of each whole class number at most `h/8` for
  each resource;
- every class has at most `3*L` copies and `6*L` support vertices, and every
  vertex belongs to at most `D` color classes.

The explicit seed certificates remain inputs. The conclusion preserves the
union of the supplied pieces; it does not independently identify that union
with all joining copies, establish cut parity, or select native reserve
prescriptions. Those are wrapper obligations.

### Asymmetric finite Hall choice

`Overfull.CircuitPatterns.exists_equiv_of_asymmetric_conflicts` returns an
adjacency-respecting equivalence between balanced finite sides of order `m`
when each row has at most `a` forbidden partners, each column has at most
`b`, and `a+b<=m`. It includes equality and empty sides.

`exists_star_equiv_of_conflict_bounds` specializes the numerical margin to
row bound `D+b`, column bound `h/8+b`, and common order at least `h-s-D`.
The exact actual copy/free-color balance and the actual relation conflict
bounds are still required inputs; their native derivation is not assumed
to have been completed by this abstract Hall result.

## Verification evidence and its limits

All five final modules passed genuine focused `lake build --wfail` target
checks. The retained receipts are `loads-build-001`, `extension-build-001`,
`star-002`, `hall-002`, and `grouping-build-001` under
`verification/runs/20261123T230808Z/development/`. Their target source
snapshots match the manifest, and each records exit zero with no change to
its recorded inputs. The read-only [semantic review](weighted-palette-semantic-review.md)
checks zero/empty cases, seeds in total weights, protected labels,
old-core multiplicities, whole-group bounds, capacity direction, and Hall
boundary cases.

At this documentation freeze, the complete frozen verification is the next
gate. Its actual full-command receipt, frozen hashes, build/audit logs,
`verification/results.json`, complete declaration mappings, and supplementary
preservation report in the current run determine global verification.
No new total audit count or full-run success is asserted here in advance.

The original focused recorder omitted the actual `lakefile.toml` while
looking for `lakefile.lean`. `recorder-correction.json` records the correction:
future focused checks hash `lakefile.toml` and the recorder source. Old
receipts and logs remain unchanged. The complete frozen runner explicitly
covers the actual configuration, toolchain and package manifest. Genuine
failed attempts, including `loads-001`, are retained.

## Remaining construction obligations

The actual unpaired-star step still requires the copy partition and combined
bound `j_z+t<=h-r`, coloring a shared internal exceptional bundle first,
removing prescribed copies and excluding every protected color, and proving
the exact remaining star/free-palette equality. The two actual Hall
relations must then be instantiated sequentially, with the second star
avoiding the first star's occupied old-core endpoints.

Native odd/even weighted wrappers must supply seed certificates, complete
joining coverage, reserve alignment and cut parity. Actual star insertion
must establish matching, exact coverage, prescription preservation and
the final footprint/load/uncovered-core parity bounds. Robust completion,
factorization and reconstruction remain subsequent steps. See the
[continuation handoff](continuation-handoff.md) for the precise order.

## Exact public theorem inventory

The following inventory is copied from `weighted-palette-source.json`.

### Overfull.WeightedPalette.AsymmetricHall

Source: `Overfull/WeightedPalette/AsymmetricHall.lean`; 3 public theorem proofs.

SHA-256: `89f1818188bf9677304fa264dbf4ae0f2e22e8079353bf73630bace9dc3425ea`.

- `Overfull.CircuitPatterns.exists_equiv_of_asymmetric_conflicts`
- `Overfull.CircuitPatterns.star_hall_margin`
- `Overfull.CircuitPatterns.exists_star_equiv_of_conflict_bounds`

### Overfull.WeightedPalette.Extension

Source: `Overfull/WeightedPalette/Extension.lean`; 1 public theorem proofs.

SHA-256: `c01cbd4e88b1800b5d5cc495ba2e7348686972e9e633e7f7330e2d78e39411ac`.

- `Overfull.NativeReserve.exists_weighted_palette_extension`

### Overfull.WeightedPalette.Grouping

Source: `Overfull/WeightedPalette/Grouping.lean`; 2 public theorem proofs.

SHA-256: `3f1d6ff5e30f6f3fd7b20274177b3c9376c0215dacbce3e01e33cc552b187944`.

- `Overfull.WeightedPalette.groupedCopies_eq_seed_on_protected_color`
- `Overfull.WeightedPalette.exists_star_weighted_matching_grouping`

### Overfull.WeightedPalette.Loads

Source: `Overfull/WeightedPalette/Loads.lean`; 18 public theorem proofs.

SHA-256: `9581f824693839be24c8dbc880516d76019238412700253bc3704273fb0fa1b4`.

- `Overfull.NativeReserve.mem_overloadedPalettes`
- `Overfull.NativeReserve.notMem_overloadedPalettes`
- `Overfull.NativeReserve.paletteWeight_empty`
- `Overfull.NativeReserve.paletteWeight_sum`
- `Overfull.NativeReserve.paletteWeight_mono`
- `Overfull.NativeReserve.paletteWeight_congr`
- `Overfull.NativeReserve.paletteWeight_insert`
- `Overfull.NativeReserve.paletteWeight_update_of_notMem`
- `Overfull.NativeReserve.paletteWeight_insert_update`
- `Overfull.NativeReserve.overloadedPalettes_mul_le`
- `Overfull.NativeReserve.overloadedPalettes_card_le`
- `Overfull.NativeReserve.overloadedPalettes_card_le_of_subset`
- `Overfull.NativeReserve.weighted_palette_item_bound`
- `Overfull.NativeReserve.weighted_palette_threshold`
- `Overfull.NativeReserve.overloadedPalettes_card_le_thirteen`
- `Overfull.NativeReserve.weighted_palette_protected_margin`
- `Overfull.NativeReserve.weighted_palette_protected_gap`
- `Overfull.NativeReserve.weighted_palette_hall_bounds`

### Overfull.WeightedPalette.StarWeights

Source: `Overfull/WeightedPalette/StarWeights.lean`; 17 public theorem proofs.

SHA-256: `d0e5473bdba64dc65c08bb83fad14d3f14b5549603f4c4bff31be91d0aa8ae2f`.

- `Overfull.WeightedPalette.mem_starBlockedCopies`
- `Overfull.WeightedPalette.exceptionCorePool_eq_edgesTo`
- `Overfull.WeightedPalette.starBlockedCopies_eq_edgesTo`
- `Overfull.WeightedPalette.starBlockedCopies_subset`
- `Overfull.WeightedPalette.starWeight_eq_sum_parallel`
- `Overfull.WeightedPalette.starWeight_le_inter_support_mul`
- `Overfull.WeightedPalette.starWeight_le_support_mul`
- `Overfull.WeightedPalette.starWeight_le_six_mul`
- `Overfull.WeightedPalette.starWeight_le_four_mul`
- `Overfull.WeightedPalette.sum_starWeight_eq_sum_support_load`
- `Overfull.WeightedPalette.sum_starWeight_le_of_support_load`
- `Overfull.WeightedPalette.sum_starWeight_le_of_degreeOn`
- `Overfull.WeightedPalette.exceptionCorePool_card_le_degree`
- `Overfull.WeightedPalette.sum_starWeight_le_mul_degree_bound`
- `Overfull.WeightedPalette.starBlockedCopies_biUnion`
- `Overfull.WeightedPalette.starWeight_biUnion_le`
- `Overfull.WeightedPalette.starWeight_groupedCopies_le`

## Definitions

The four definitions are `Overfull.NativeReserve.paletteWeight`,
`Overfull.NativeReserve.overloadedPalettes`,
`Overfull.WeightedPalette.starBlockedCopies`, and
`Overfull.WeightedPalette.starWeight`.
