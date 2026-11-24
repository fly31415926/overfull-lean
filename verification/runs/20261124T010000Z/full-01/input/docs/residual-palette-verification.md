# Native residual joining palettes: scope and proof map

This continuation develops the actual residual produced by the native
reserve completion. Its source manifest records exact module hashes and
every public theorem. Compilation and the complete unchanged axiom audit
determine verification status; this proof map is a scope description.

## Parameters and actual joining degrees

`exists_uniform_native_reserve_completion_parameters` chooses the surviving
robustness parameter `θ>0`, with `θ≤σ`, before any requested surplus error
`δ>0`. It then chooses the original error tolerance and order threshold
before the host. This exposes the order needed to choose later packing
errors as functions of `θ`. The prior completion theorem remains unchanged.

For the original representative's assignment in the actual `h`-regular
residual, `native_residual_joining_degree_bounds` proves joining degree at
most `a` at each old-core vertex and at most `h-r` at every exception. The
second inequality injects the `r` surviving internal reserved incidences
into the nonjoining residual copies. Parallel copies are counted separately.
The representative itself need not survive as a perfect residual matching.

`exists_uniform_native_reserve_completion_with_small_joining` constructs
the original reserve and residual, retains their regularity, no-overfull
condition and robust cores, and derives the joining bounds. With
`B=max(a,h-r)` and natural `D=⌊B⌋₊`, every joining degree is at most `D`,
`B≤δn`, and `6D<h`. The floor introduces no additive rounding error because
the degrees are natural numbers.

## Whole matching classes

The generic finite greedy theorem extends a prescribed proper coloring
while bounding each class by `L` pieces. Its sufficient conditions are a
conflict bound `B<h` and at most `L(h-B)` pieces in total. At each insertion
the already colored set has strictly smaller size, so equality in the
initial total-size condition is allowed.

For actual edge-disjoint matching pieces of at most three copies, the
endpoint-conflict degree is at most `6D`. This follows from the at most six
support vertices per piece and injection of distinct incident pieces into
the actual incident copies. `exists_bounded_matching_grouping` constructs
classes that are actual matchings, disjoint, and cover every original
joining copy exactly once. Each whole class has at most `3L` copies and
`6L` support vertices. At most `D` classes meet any fixed vertex.

The two-odd case has exactly `h` primary pieces. They receive distinct
prescribed palette labels, so every class contains exactly one primary.
All other pieces in it are surplus pieces. The all-even case has no
prescribed primary pieces.

## Parity retained through grouping

`EvenJoiningDecomposition` retains the even cut certificate of every lifted
compatible circuit. The previous all-even wrapper, which forgot these
individual certificates, is preserved and is not used to infer them.
Cut cardinalities add across disjoint copy sets. Thus a union of even
pieces has even cut parity, while one primary plus even surplus pieces
has the primary's parity.

`AssignedParts.exists_assigned_joiningPalette_in_host` applies both cases
to the actual representative assignment in another host on the same
vertices. The resulting `JoiningPalette` includes matching, disjointness,
exact coverage, cut parity, whole-class size and vertex-load certificates.
`assigned_joiningPalette_uncovered_even` proves even uncovered order in
every actual assigned fiber for every palette class.

The uncovered-order assertion concerns assigned fibers. Covering their
exceptional vertices internally is still necessary before using it as an
even uncovered-order assertion on the old core vertex sets.

## Prescribed reserve crossings and protected colors

In the odd assigned-part case, each compressed reserve boundary contains
exactly one old-core crossing. `exists_half_residual_crossing_reserve`
selects `s=⌊r/2⌋` distinct surviving crossing copies in the residual
joining-copy subtype. It retains their membership in the original reserve
and their two quotient endpoints. These copies may share vertices.

`exists_twoOddJoining_decomposition_with_reserved_primary` constructs a
complete circuit decomposition in which each prescribed crossing is its
own singleton primary piece, under the explicit margin `D≤h-s`. It pairs
each selected actual copy with a different virtual copy, proves safe
deletion of these specified pairs, decomposes the remainder, and restores
the pairs. No safe-selector or preconstructed partition is assumed.

`TwoOddJoiningDecomposition.exists_protected_palette` ensures that the
protected primary pieces remain entire palette classes. Its greedy relation
adds a conflict between each surplus piece and every protected primary.
Its conditions are `6D+s<h` and `nD≤2L(h-6D-s)`. The final native wrapper
composes selection, forced primaries, and protected grouping with the
actual original reserve and actual residual copy type.

## Quantitative footprint budgets

For unprotected grouping, choose
`L=(nD/2)/(h-6D)+1`, using natural division. From `h≥αn/30`, `D≤δn`, and
`δ≤α/360`, the available palette margin is at least `αn/60`. The proof
derives `6L≤(180δ/α)n+6`. Thus `δ≤εα/360` and `n≥12/ε` imply `6L≤εn`.

For `s≤h/2` protected colors, choose
`L=(nD/2)/(h-6D-s)+1`. The stronger choice `δ≤α/720` gives a positive
margin at least `αn/120`, and `6L≤(360δ/α)n+6`. With `δ≤εα/720` and
`n≥12/ε`, every whole class again has at most `εn` support vertices.
These formulas also prove the common incidence-capacity input used by the
actual joining-palette wrappers. A bound relative to a core of order at
least `cn` follows by applying the formulas with error `c ε_core`.

## Source modules

| Module | Mathematical contribution |
| --- | --- |
| `UniformCompletion` | Retained robustness chosen before the requested surplus error. |
| `JoiningBounds` | Actual old-core and exceptional joining-degree bounds, with the natural-floor bridge. |
| `UniformJoining` | Uniform original-host construction with the strict joining palette margin. |
| `PaletteGrouping` | Finite bounded grouping, actual matching unions, exact coverage and whole-class bounds. |
| `PaletteParity` | Per-piece even certificates and parity of disjoint grouped cuts. |
| `JoiningGrouping` | Actual assigned-fiber joining palettes and even uncovered assigned fibers. |
| `PaletteBudget` | Explicit unprotected whole-class footprint and capacity bounds. |
| `ReservedPrimary` | Prescribed original/virtual pairs and singleton primary crossings. |
| `ProtectedGrouping` | Surplus avoidance of protected colors, with full palette certificates. |
| `NativeReservedCrossings` | Half-reserve selection and survival in the actual residual joining-copy type. |
| `ProtectedBudget` | Quantitative margin and footprint bounds with protected colors. |
| `NativeProtectedPalette` | Composition with the original reserve and actual residual. |

## Scope still open

These results do not supply the internal assigned-exception coloring,
the equal-free-palette construction for an exceptional pair with arbitrary
parallel copies, the subsequent robust perfect-matching completions, or the
final residual factorization and reconstruction. Protected joining singleton
classes are not yet complete reserved boundary color classes. Other
manuscript obligations, including the full five-exception statement, remain
separate. All 69 original assertion records are retained: **47 complete,
22 incomplete; the main theorem is unproved.**
