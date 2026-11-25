# Native multi-star extension: read-only next-step review

**Status:** source-based proposal, not a newly proved result. Every extension
below remains unproved. No Lean command was run for this review, no frozen
source/document/control was edited, and no coverage is promoted: 51/69;
main theorem unverified. This supplements the safe-residual pool plan and
continues to assume its eventual safe residual and quantitative budgets.

## Smallest useful new endpoint

First prove a finite-star assembly lemma for distinct unpaired centers
`W`, with `m = |W| <= 5`, and then supply its native inputs. The one-pair
branch needs at most three centers; the zero-pair branch needs at most five.
The base matching family must already contain the joining palette, any
completed two-vertex pair fiber, every selected whole reserve boundary,
and all same-label copies between unpaired centers. The lemma should derive
exact remaining-copy/free-color balance, extend every assigned-core star,
and retain protected classes, exact cuts, saturation and copy coverage.

This is smaller than another foundational Hall theorem. These interfaces
already exist:

| Source / interface | Exact reusable content |
| --- | --- |
| `NativeStar/TwoStars.lean`: `exists_two_star_extension_on_available` | Sequentially compatible extensions for exactly two centers; actual copy/color balance remains an input. |
| Same file: `starExtended_available_support_load_le`, `starExtended_available_starWeight_le` | Each earlier star adds at most its parallel bound to the next available-color load and weight. |
| `WeightedPalette/AsymmetricHall.lean`: `CircuitPatterns.exists_equiv_of_asymmetric_conflicts` | Arbitrary row/column conflict bounds with sum at most the balanced order. |
| `NativeAssembly/TwoPairStar.lean`: `matching_family_remaining_star_balance` | Arbitrary matching family; degree `h` and complete incidence partition derive the exact balance, without assuming `Z` is a singleton. |
| `NativeCore/Coverage.lean`: `external_union_eq_of_saturation` | Exact external coverage follows from disjointness, saturation, joining inclusion and external containment. |

## First obstruction: more than one mutual bundle

`exists_native_same_label_completion` and
`exists_native_separate_stars_extension` explicitly assume
`Z = {z₀,z₁}`. With three or five unpaired centers, the same-label exceptional
pool can contain a triangle or several overlapping bundles. Independently
coloring each parallel bundle does not prevent conflicts at a shared center.
Nor can every bundle color be excluded from every star: a color used on an
edge not incident to a given center remains available there.

**Proposed preparation:** let `B` contain all nonjoining copies between
unpaired centers. Injectively color the whole `B` in colors avoiding the
protected set `Q` and the union of joining-used colors at every center.
`NativeStar.exists_common_bundle_coloring` already accepts an arbitrary
finite copy set: instantiate its two forbidden sets with that union and
`∅`. What remains to prove is its budget and the matching-family adapter.
From the native combined incidence bound
`|J_z| + degree_B(z) <= D`, summing over `W` bounds
`|B| + |union_z J_z|` by `m*D`; this prospective counting argument must be
formalized. The available margin is ample under `128*D <= h` and
`2*|Q| <= h`. Use each center's actual incident bundle colors, or simply
its actual free colors in the resulting base family.

`NativeStar.incidence_partition` and `off_core_degree_add_reserve_le` already
allow arbitrary exceptional sets and labels. Their native adapters still
need an actual assigned-star reserve injection for every unpaired center
from `PartnerBoundaryPacking`; the existing `ReserveInjection.lean` adapter
uses `BoundaryPacking` and the globally unpaired coarse code. The one-pair
branch cannot satisfy that coarse-code premise. Its pair can reuse
`JoiningPalette.exists_pairFiber_completion` and
`PartnerBoundaryPacking.exists_residual_pair_injection`, but needs a
one-pair analogue of whole-boundary union preservation allowing extra stars.

## Proposed finite-star induction

After all exceptional internal copies are colored, incidence partition and
`matching_family_remaining_star_balance` give each star's exact free-color
count. The combined off-core bound gives the lower bound `h-|Q|-D`.
Available colors exclude the protected boundaries, which already saturate
every center. Pair/bundle copies occupy only exceptional vertices, so they
add no old-core weight.

After `j` stars, iterate the existing accounting lemmas to obtain row bound
`D+j*b` and column bound `h/8+j*b`, with `j <= 4` and `b <= D`.
The generic asymmetric Hall theorem can then replace the two-star numerical
wrapper. The proposed inequality
`(D+j*b)+(h/8+j*b) <= h-|Q|-D`
follows numerically from the same `128*D <= h`, `2*|Q| <= h` regime, but its
Lean specialization and finite induction are not yet proved. Distinct
centers outside both old cores ensure earlier stars do not occupy later
centers; existing `star_pools_disjoint` and
`coloredStarCopies_avoids_other_center` supply the pairwise facts.

## Weighted palette adapter still required

`NativeReserve.exists_weighted_palette_extension` already permits arbitrary
finite resource type `κ`; the restriction `card κ <= 2` occurs in
`exists_star_weighted_matching_grouping` and the native wrappers. For at
most three labels, its current proof uses endpoint cost `6*D` and overload
cost `13*D` per resource. A prospective `m`-resource wrapper therefore
needs explicit margin `|Q|+(6+13*m)*D < h` and corresponding piece capacity
`pieces <= L*(h-|Q|-(6+13*m)*D)`, plus actual seed-weight certificates.
For five resources, `128*D <= h` and half-palette protection alone do not
imply this margin. Recompute the budget; do not reuse `32*D` or `40*D`.

`NativeWeighted.two_core_exception_parallel_bound` already supplies `b=D`
for arbitrary `Z` from retained-core degrees. Full-partner protected traces,
assigned fibers and weighted palette adapters for zero/one pairs still
must be constructed without supplying their conclusions as assumptions.
