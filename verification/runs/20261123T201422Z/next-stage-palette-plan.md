# Next stage: whole-piece palettes and reserved boundaries

**Status: planning only. Every new construction and proposed theorem below is
UNPROVED in this repository.** This note records a read-only inspection and
mathematical proof proposals during the final audit of the native reserve
continuation. No Lean process was run for this note, and no proof source or
frozen verification input was changed. The references to existing declarations
identify available interfaces; they do not certify the proposed compositions.

There is **no increase in manuscript coverage**: 47 of 69 numbered assertions
remain complete. This note proves neither the full two-core Corollary 4.6 nor
the main theorem, and supplies no residual factorization.

**In particular, the proposed `6*d<h` argument is not a construction of
palettes compatible with the whole reserved boundaries.** It only controls
joining-piece conflicts. Compatibility with the reserved internal incidences
at exceptional vertices is a separate unresolved requirement.

## 1. Existing interfaces and their exact limits

Work in the actual residual host `H` returned by
`Overfull.NativeReserve.exists_native_reserve_completion_parameters`.
Its label map must remain the original representative's
`AssignedParts.assignedLabel G M U₀ U₁ Z`; the representative `M` need not
survive in `H`.

| Existing declaration or data | Available content |
| --- | --- |
| `AssignedParts.assignedLabel_joining_decomposition_in_host` in `Overfull/AssignedParts/JoiningConstruction.lean` | Uses that original assignment in a different regular, non-overfull host. Returns the all-even or two-odd alternative. |
| `FourOdd.TwoOddJoiningDecomposition` in `Overfull/CompatibleCircuits/TwoOddDecomposition.lean` | Exact original-copy partition; `h` primary pieces, each of size at most two; surplus pieces of size at most three; every piece is a matching. |
| Its fields `primary_cut_eq_one`, `primary_odd_cut_iff`, `surplus_even_cut` | Primary pieces have odd fiber cuts precisely at labels 0 and 1; surplus pieces have even cuts at every fiber. These individual parity certificates survive in the structure. |
| `FourOdd.exists_joining_matching_partition_of_even_fibers` | Returns actual-copy matchings, size bounds, disjointness and coverage, but forgets individual fiber-cut parity. Its present conclusion alone is insufficient for parity-preserving grouping. |
| `Multigraph.CompatibleCircuitPartition`, `Multigraph.IsCircuit.even_degreeOn`, `FourOdd.joiningQuotient_degreeOn_eq_cut` | The underlying all-even circuit partition retains the information needed for a strengthened parity-preserving lift. |
| `Multigraph.family_support_load_le_degreeOn` and `Multigraph.edgeSupport_card_le_six` in `Overfull/CircuitPatterns/IncidenceLoad.lean` | Bound the number of edge-disjoint pieces meeting a vertex by the degree of their containing edge set; bound one three-copy piece's support by six vertices. |
| `CircuitPatterns.support_conflicts_card_le` and `CircuitPatterns.isMatching_union_of_disjoint_support` in `Overfull/CircuitPatterns/Pairing.lean` | Existing support-conflict counting and matching-union tools. |
| `NativeReserve.coreFootprint_load_le_error` | Its load conclusion does not require the individual boundaries to have at most three edges. The separate convenience theorem `coreFootprint_admissible` does require that size bound. |
| `Multigraph.PaletteColoring.ofMatchingClasses` in `Overfull/BoundaryExtension/Palette.lean` | Assembles a coloring from already constructed covering matching classes. It does not construct the grouping or its parity. |

Ordinary edge-coloring interfaces, including
`Multigraph.PartialEdgeColoring.exists_edgeColoring_extending` and the
balanced-coloring results in `Overfull/ColoringExtension/Uniform.lean`, do
not by themselves keep an entire compatible-circuit piece monochromatic.
The `6*q<k` theorem in `Overfull/SparseColoring.lean` concerns sparse vertex
deletion and is not the whole-piece grouping theorem proposed here.

## 2. UNPROVED: a whole-piece greedy extension with class-size control

The first useful new abstraction is a finite family `P : T → Finset E`
of pairwise edge-disjoint matchings, each of size at most three, whose
union is exactly the joining-copy set `J` of `H`. Use an **integer** degree
bound `d : ℕ` satisfying

```text
∀ v, H.degreeOn J v ≤ d,     6*d < h.
```

Supply a selected subfamily of pieces, each of size at most two, with an
injective prescribed map into `Fin h`. In the two-odd case this is the
entire primary family and has cardinality `h`; in the all-even case it can
be empty. The proposed output is a map `color : T → Fin h` extending that
prescription and the actual-copy classes

```text
C i = ⋃ { P t : color t = i }.
```

**UNPROVED proposed conclusions:** every `C i` is a matching, the classes
are pairwise edge-disjoint and cover exactly `J`, every piece remains
whole, and

```text
(C i).card ≤ J.card / (h - 6*d) + 3.
```

Here `/` is natural-number division and `h-6*d` is positive. This bound is
a proposed theorem, not a currently verified result.

The proposed proof proceeds by finite induction over the uncolored pieces.
A new piece has at most six endpoints. At each endpoint, at most `d`
members of the entire piece family are incident, by
`family_support_load_le_degreeOn`. Hence at most `6*d` colors conflict with
previously colored pieces. Choose a color with the smallest current
**edge-copy class size** among the available colors. There are at least
`h-6*d` available colors and at most `J.card` already assigned copies in
total. The chosen class therefore has size at most
`J.card / (h-6*d)` before adding the new piece, and the addition has at most
three copies. Initially each prescribed class has at most two copies.

**UNPROVED derived footprint specification:** each resulting class has
support size at most twice this bound, while the number of classes meeting
any vertex is at most `d`. With `12*d≤h`, `n=|V|`, and `h≥β*n>0`, handshake
counting `2*J.card≤n*d` would yield the real-valued support bound

```text
|support(C i)| ≤ 6 + 2*d/β.
```

For the current residual, `β=α/30` is available from its degree lower
bound. Choosing the error parameters sufficiently small and the order
threshold sufficiently large would still need to be formalized before
using this estimate in robust completion. Grouping only `J` does not
account for any additional internal reserved copies later added to a
class.

If the joining-degree estimate is initially real-valued,
`D=max(a,(h:ℝ)-r)`, a separate conversion to an integer bound is needed;
`d=⌊D⌋₊` is a candidate when `D≥0`. The real inequality `6*D<h` suffices
for `6*d<h`, but its uniform derivation from the chosen parameters is a
new obligation.

## 3. UNPROVED: retain and combine the individual parity certificates

For the all-even case, strengthen the existing lift to retain

```text
∀ piece ∈ parts, ∀ i, Even ((H.cutOn piece (labelShore label {i})).card).
```

The direct route is to retain the constructed
`CompatibleCircuitPartition`, apply `IsCircuit.even_degreeOn` to each
quotient part, and transport that equality using
`joiningQuotient_degreeOn_eq_cut`. The existing `liftJoiningParts_*`
lemmas already handle exact copy coverage, disjointness and matching.

For the two-odd case, precoloring all `h` primary pieces injectively into
`Fin h` puts exactly one primary piece in every class. Every added surplus
piece has even cut at every fiber. Additivity of cut cardinalities for
edge-disjoint pieces would therefore give each class the fiber parities
required by the assigned-part orders. Both the strengthened all-even
wrapper and the grouped-parity theorem remain **UNPROVED**.

These are assigned-fiber parity statements. Covering exceptional vertices
by compatible internal copies and transferring to the old-core completion
inputs remain additional steps.

## 4. UNPROVED speculative route: prescribe reserved crossing pieces

`NativeReserve.BoundaryPacking.crossing_card`, together with the assigned
fiber parity identities in `Overfull/AssignedParts/MatchedCuts.lean`, is
the existing starting point: in the two-odd case each reserved boundary
has one actual old-core crossing copy; in the all-even case it has none.
An arbitrary circuit decomposition is not guaranteed to put a reserved
crossing copy in a primary piece.

The following is a **new, unproved construction proposal**, not an
application already implemented in Lean.

Let `D=max(a,(h:ℝ)-r)` be a proved real joining-degree bound. Set
`s=⌈D⌉₊` and `r'=h-s`. Before using this choice one must prove:

- `D≥0`, `s≤h`, and the exact natural-number identity `h-r'=s`;
- `r'≤r`, using `D≥h-r` and the existing `r≤h`;
- existence of an actual indexed subreserve of size `r'`, with its copy
  disjointness, signature, exceptional incidences and survival retained;
- a sufficiently strong positive linear lower bound for `r'` and a small
  remaining margin `h-r'=s`. The loss from `r` must be recorded, including
  ceiling error. From the proposed choice one expects `s≤D+1`, but this
  and all required uniform estimates must be proved. The original reserve
  theorem's quantitative conclusion cannot silently be reused with `r'`.

For example, `6*D<h` gives a route to `s≤h`; a linear lower bound for `r'`
also requires the appropriate order/degree threshold. No such subreserve
replacement is certified by this note.

For each retained reserved old-core crossing copy, prescribe a quotient
two-circuit consisting of that actual `0–1` copy and a distinct virtual
`0–1` copy. Original endpoint classes and the virtual class are distinct,
so these pairs are candidates for compatible circuits. Remove all `r'`
prescribed actual/virtual pairs from the full augmented quotient.

The intended remainder proof fits the existing general theorem
`Multigraph.pairAugmentation_admissibleOn`:

- A label shore separating 0 and 1 originally has at least `h` actual
  crossing copies, by `FourOdd.regular_odd_cut_lower` and the two-odd
  fiber parity identity. Removing the `r'` prescribed crossing copies
  leaves at least `h-r'=s` actual copies. Every remaining endpoint class
  has at most `D≤s` copies, and exactly `s` virtual copies remain.
- A label shore not separating 0 and 1 loses no prescribed crossing
  copy. Its existing even-shore half-cut inequalities therefore remain
  applicable; there are no virtual copies crossing that shore.
- Deleting the prescribed two-circuits preserves even selected degrees.
  Existing `Multigraph.even_degreeOn_sdiff` and circuit parity provide
  the intended tools.

After these **new hypotheses and identities are actually proved**,
`exists_compatibleCircuitPartition_of_card_le_three` could partition the
remainder. `Multigraph.isCircuit_parallel_pair` and
`CompatibleCircuitPartition.insertCircuit` are existing tools for
inserting the prescribed circuits. This would force the retained
reserved crossing copies into distinct singleton primary pieces.

### Outstanding full-boundary compatibility

Even a successful prescribed-crossing construction would not prove that
each grouped class can contain its associated **whole** reserve boundary.
The greedy `6*d<h` count above includes conflicts among joining pieces
only. Precoloring internal reserved incidences can forbid `r'` colors at
an exceptional vertex, potentially nearly the whole palette. The small
joining degree there does not make that additional forbidden-color set
small. A coupled assignment or Hall argument, or a separately justified
change in how the reserve is used, is still required. This obstruction
must not be omitted from a formal interface.

## 5. UNPROVED: equal free palettes on a two-vertex pair fiber

The existing `AssignedParts.pairPart_card_eq_zero_or_two` identifies the
optional pair fiber. Suppose it is exactly `{z,z'}` and the proposed
grouping has been proved, including matching and even fiber-cut parity
for every class.

**UNPROVED proposed lemma:** a joining matching with even cut into this
two-vertex fiber touches both vertices or neither. Its incidence at each
vertex is at most one; joining copies have no edge internal to the fiber.
The equality in `Multigraph.degreeOn_sum_on`, or the matching incidence
identity `IsMatching.degreeOn_sum_eq_covered`, reduces the assertion to
parity of two indicators.

It follows, as another **UNPROVED** palette lemma, that the used color
sets at `z` and `z'` are equal, hence the free color sets are exactly equal.
Regularity of the actual residual host would identify their common free
palette size with the number of actual internal `z–z'` copies. A finite
bijection between those copies and the free colors would then color all
parallel copies without discarding their identities.

If selected reserved pair copies must receive already prescribed colors,
one must additionally prove that those prescribed colors lie in the
common free palette and are distinct. Palette equality and cardinality
alone do not prove that extension property. This is part of the
full-boundary compatibility issue above.

## Next implementation boundary

The proposed first implementation is a whole-piece grouping interface
with an explicit initial prescription and a separately proved class-size
bound, plus the strengthened all-even parity wrapper. Prescribed reserve
alignment, compatibility with exceptional internal copies, robust
completion, an actual coloring of the entire residual, and reconstruction
of the original host remain separate **UNPROVED** obligations.
