# Next native construction: two exceptional pair parts

This is a read-only proof plan prepared while the current ordinary-core theorem
was undergoing its full audit. The proposed declarations below are not Lean
proofs and are not counted as verified assertions. No mathematical source was
changed to prepare this plan.

## First independent target

Prove a simultaneous two-fiber version of
`JoiningPalette.exists_pairFiber_completion`, tentatively named
`JoiningPalette.exists_two_pairFiber_completion`.

Start with one original `JoiningPalette G label h D L p`, two distinct assigned
fibers of size two, zero cut parity on both, and degree `h` on their vertices.
Each pair bundle has its own injective seed prescription into colors free at
its endpoints. The resulting family should cover exactly the original joining
copies together with all internal copies of each pair, saturate both pairs in
every color, preserve every assigned-fiber cut and every seed color, and retain
bounds of `3L+2` copies and `6L+4` support vertices per class. Outside the two
pair fibers, load should remain at most `D`.

Invoke the existing single-pair completion twice relative to the same original
palette, then combine the insertions using disjoint supports. The first
completed family is not itself a `JoiningPalette`, so iterating the theorem
directly on that output is not justified. Seed injectivity is separate for each
pair: the two reserved pair copies belonging to one actual boundary must share
that boundary's protected color.

## Native inputs and integration

1. Construct four assigned parts from two actual exceptional matching edges.
   With `Z.card <= 5` and exactly two internal exceptional matching copies,
   split `pairPart G M Z` into two disjoint two-vertex endpoint pairs, together
   with the two old core parts. Give these parts distinct `Fin 4` labels and
   prove the original core-part parities equal. Existing ingredients include
   `pairPart_card`, `coreParts_disjoint`, `corePart_pairPart_disjoint`, and
   `coreParts_cover` in `AssignedParts/Basic.lean`. The present `Fin 3` endpoint
   collapses the two pairs into one four-vertex fiber. Order the new parts by
   endpoint pairs using a fixed order of `Z`, so parallel-copy choices cannot
   change their identities.

2. Retain both pair identities in the native reserve. The existing
   `AssignmentSignature Z := Option (Z -> Fin 2)` does not encode the partner
   information needed when an exceptional pair coexists with another pair or
   an unpaired exception. A finite code `Z -> (Fin 2 + Z)` can record either an
   assigned core or an exceptional partner, with the immediate upper bound
   `(2+|Z|)^|Z| <= 7^5`. Equal codes must determine both core parts and both
   endpoint-pair parts. Reuse the disjoint selected-family argument for
   `compressedBoundary`, of size at most `Z.card+1 <= 6`, to choose one actual
   surviving copy for each pair from each reserved boundary. Injectivity holds
   within each pair family, and the two families are disjoint. This extends
   `exists_native_reserved_pair_injection` in `NativeAssembly/Paired.lean`.
   The heavy-code argument must consider all possible codes; it cannot assume
   its chosen code has two pairs.

3. Combine the simultaneous pair-completion lemma with `ReserveExtension`.
   In a protected color, both inserted prescribed copies already belong to
   that exact original boundary, so its complete copy set is unchanged. In
   other colors, the base is the original joining class. In the two-pair branch
   at most one exceptional vertex remains unpaired; its internal assigned-core
   star can use `NativeStar.exists_star_extension_on_available`. The pair
   insertions have disjoint support from that center and its old core. The
   bookkeeping in `exists_native_single_star_extension` still needs extension
   because its current premise makes all of `Z` a singleton. Generalize the
   assigned-core parity transfer from the present three fibers to the four
   actual fibers.

The existing four-label circuit decomposition and four-piece grouping can
supply the joining-palette stage; they do not provide these native inputs.
The terminal coloring also needs the small extension of
`retained_pair_colorable` to the union of two separately closed pair components.

## Remaining branches

Completing the preceding chain addresses the two-pair branch. It should not be
reported as a complete proof of the five-exception corollary on that basis
alone. Zero exceptional matching pairs can leave five unpaired exceptional
vertices, and one pair can leave three. These cases need their own native star
assembly and bookkeeping unless a general applicable endpoint is established.
The heavy-signature selection must support all three possibilities. The
frozen semantic review identifies the two-pair construction as a next
obstruction; this later plan makes the additional branch obligations explicit.

An independent read-only check confirmed the limits in the current sources:
`NativeAssembly.exists_native_unpaired_completion` in
`NativeAssembly/Unpaired.lean` assumes `Z.card <= 2` and enumerates only the
empty, singleton, and pair cases. `NativeCore.exists_native_external_completion`
retains that bound. `NativeStar.exists_two_star_extension_on_available` constructs
exactly two stars; `WeightedPalette.exists_star_weighted_matching_grouping` and
`NativeWeighted.exists_native_weighted_reserved_palette` cap their resource
count at two. No general native assembly covering the three- or five-star
branches was found.

There are reusable general interfaces: the reserve theorem
`NativeReserve.exists_weighted_palette_extension` permits an arbitrary finite
resource type with its cardinality in the budget, and the terminal theorem
`NativeTerminal.exists_uniform_shore_coloring_of_star_incidence` permits an
arbitrary fixed star count after the required geometry and cuts are available.
Neither interface constructs the missing native palette and assembly. The
zero-pair and one-pair branches therefore still require multi-star and
same-label-bundle assembly, in addition to the two-pair branch described above.
