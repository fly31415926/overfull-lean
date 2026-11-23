# Unproved continuation plan: joining-degree bounds in the actual residual

**Status: this is an unproved continuation plan, not a new Lean result, a
completed verification gate, or an increase in manuscript coverage.**
The proposed lemmas and proof routes below have not been entered into Lean
or compiled. Existing declaration names were checked by reading the current
repository sources. Coverage remains **47 of 69 numbered assertions**;
the full two-core Corollary 4.6 and main theorem remain incomplete.

This note records a next step after
`Overfull.NativeReserve.exists_native_reserve_completion_parameters`.
The actual run records, not this note, determine the verification status
of the current proof sources. No existing proof or frozen verification
input was changed to prepare this plan.

## 1. Proposed next interface

Retain the assignment from the original host and representative:

```lean
let L := AssignedParts.assignedLabel G M U₀ U₁ Z
let R := NativeReserve.residualGraph G N Finset.univ
let J := FourOdd.joiningCopies R L
```

Here `G`, `M`, `Q`, `N`, `r`, `h`, and the retained cores `C₀'`, `C₁'`
are the objects supplied by the completion theorem. The representative
`M` is a perfect matching of the original graph `G`; it is not assumed
to survive as a perfect matching of `R`.

The proposed next conclusion is:

```lean
(∀ v ∈ U₀ ∪ U₁, (R.degreeOn J v : ℝ) ≤ a) ∧
(∀ z ∈ Z, R.degreeOn J z + r ≤ h)
```

This is a schematic target, not compiled Lean code. The exceptional
conclusion deliberately uses addition before deriving the equivalent
upper bound `R.degreeOn J z ≤ h - r`; this avoids introducing truncated
subtraction into the initial counting argument.

The needed inputs are original perfectness of `M`, the pairwise disjoint
cover `U₀,U₁,Z`, `Z.card ≤ 2`, the generic boundary packing `Q`, avoidance
of its reserved copies by `N`, regularity of the actual residual, and the
minimum-degree bounds on its two returned embedded cores. The local
degree argument does not need to construct another fractional matching
distribution or repeat the robust-expansion proof.

## 2. Old-core vertices: use the returned retained cores

First prove a generic lemma for a host `H`, a core
`C : SmallCuts.Core H U`, and a label function constant on `U`:

```lean
Disjoint (FourOdd.joiningCopies H label) (OneCore.coreEdges C)
```

Every endpoint of a core copy belongs to `U`, by the existing
`OneCore.coreEdges_endpoint`. Its two labels are therefore equal, so
`FourOdd.mem_joiningCopies` rules out membership in the joining set.
This gives containment of the joining copies in the complement of the
actual embedded core copies.

The degree comparison can then use these existing declarations:

- `FourOdd.restrictEdges_degree_eq_degreeOn` in
  `Overfull/FourOdd/Pools.lean`;
- `Multigraph.restrictEdges_degree_mono` in
  `Overfull/CriticalMultigraph.lean`;
- `OneCore.complement_degree_le_error` in
  `Overfull/OneCore/Complement.lean`.

The last theorem already provides exactly the required error estimate:
if `H` is `h`-regular and every vertex of `C` has core degree at least
`h-a`, the degree in the complement of `C` at a core vertex is at most
`a`. Apply it to the returned residual cores `C₀'` and `C₁'`, not to the
old embedded cores in `G`.

For constancy of the original assignment on each old core, use
`AssignedParts.assignedLabel_fibers` and
`AssignedParts.core_subset_corePart` from
`Overfull/AssignedParts/Basic.lean`. They give `L v = 0` on `U₀` and
`L v = 1` on `U₁`. The graph used to define `L` can remain `G` while the
graph whose joining copies are counted is `R`.

## 3. A generic reserve-degree identity is needed

Set

```lean
let A := NativeReserve.removedCopies Q.boundary Finset.univ
let D := NativeReserve.removedCopies N Finset.univ
```

Prove the generic identity

```lean
∀ z ∈ Z, G.degreeOn A z = r
```

directly from the existing
`NativeReserve.removed_degreeOn`, `Q.pairwise_disjoint`, and
`Q.exceptional_degree`. The sum consists of exactly `r` terms, each one.

There is already a declaration named
`NativeReserve.BoundaryPacking.reserved_degree` in
`Overfull/NativeReserve/ProtectedPacking.lean`, but its section
specializes the packing to a probability distribution and a representative
of the form `D.matching s`. The final completion theorem exposes only a
generic `M` and `Q : BoundaryPacking G U₀ U₁ Z M r`. Its public interface
does not expose the distribution used internally during construction.

Therefore either add the generic version of this short counting lemma,
or prove the identity locally from the three declarations above. Do not
introduce an assumption that a hidden distribution can be recovered.

The supplied avoidance property `∀ j, Disjoint (N j) A` gives
`Disjoint D A`, using `NativeReserve.mem_removedCopies`. Hence every
reserved original copy survives in the actual residual.

## 4. Nonjoining is a local condition at an exception

The required statement is:

```lean
∀ z ∈ Z, ∀ e ∈ A, z ∈ G.edge e →
  L (G.firstEnd e) = L (G.secondEnd e)
```

Do not replace this with a global disjointness assertion between all of
`A` and `FourOdd.joiningCopies G L`. A compressed boundary may contain
an old-core crossing copy, whose labels are `0` and `1`; that copy is
joining. Only the reserved incidences at the exceptions are automatically
internal to their assigned parts.

A useful intermediate lemma to prove is: for any matching `F`, a selected
copy touching `Z` has equal endpoint labels under
`AssignedParts.assignedLabel G F U₀ U₁ Z`. It uses the original partition's
disjointness and cover. Existing declarations supporting this argument are:

- `AssignedParts.firstEnd_mem_corePart_iff`;
- `AssignedParts.secondEnd_mem_corePart_iff`;
- `AssignedParts.corePart_cutOn_eq_core_crossings`;
- `AssignedParts.pairPart_cutOn_eq_empty`;
- `AssignedParts.labelOfThreeParts_eq_zero_iff`;
- `AssignedParts.labelOfThreeParts_eq_one_iff`;
- `AssignedParts.labelOfThreeParts_eq_two_iff`.

These are in `Overfull/AssignedParts/MatchedCuts.lean` and
`Overfull/AssignedParts/ThreePartLabels.lean`. One proof route compares
the endpoints' membership in both assigned core parts. Another splits
the other endpoint among `U₀`, `U₁`, and `Z`, using `mem_corePart`,
`mem_internalOn_of_incident_otherEnd`, and the part-disjointness lemmas
from `Overfull/AssignedParts/Basic.lean`.

Apply the intermediate lemma to `Q.boundary i`, which is a matching by
`Q.isMatching`. Transport its label map to the original representative
using the existing theorem in
`Overfull/NativeReserve/PackingConstruction.lean`:

```lean
Q.assignedLabel hM h01 h0Z h1Z hcover hZ i
```

This identifies the boundary's assignment with `L` without asserting that
its parent matching survives in `R`.

The separate existing `Q.crossing_card` theorem records each compressed
boundary's old-core crossing count as the original representative's
crossing parity. Together with the existing assignment parity formulas,
it indicates that the two-odd case has one joining old-core crossing
copy in each reserve boundary. Aligning those copies with primary palette
pieces remains a later proof obligation.

## 5. Count actual residual copies through the subtype projection

The residual edge type is exactly

```lean
{e : E // e ∉ D}
```

and retains the original endpoints. A useful generic identity to prove is:

```lean
R.degreeOn (FourOdd.joiningCopies R L) v =
  (((FourOdd.joiningCopies G L) \ D) ∩ G.incidenceEdges v).card
```

The existing `NativeReserve.residual_cutIncidence` in
`Overfull/NativeReserve/CutSafety.lean` supplies the proof pattern:
project the residual incidence set with `Subtype.val`, establish the
exact finite-set identity, and use
`Finset.card_image_of_injective` with `Subtype.val_injective`.
`MultigraphMatchingProbability.remaining_degree` in
`Overfull/MultigraphMatchingProbability.lean` gives the corresponding
degree count for all surviving incidences. Equivalently, one can first
prove the exact image identity for `R.incidenceEdges v` and then compare
cardinalities in the original edge-copy type.

At `z ∈ Z`, compare these two original-copy sets:

```lean
((FourOdd.joiningCopies G L) \ D) ∩ G.incidenceEdges z
A.filter (fun e => z ∈ G.edge e)
```

They are disjoint by the local nonjoining statement. Both lie among the
surviving incidences at `z`, because the first excludes `D` explicitly
and the second is contained in the surviving reserve. Their cardinalities
are respectively the residual joining degree and `r`. The containing
incidence set has cardinality `R.degree z = h`. This gives
`R.degreeOn J z + r ≤ h`.

All counting must stay on actual original copies. If an exceptional pair
has many parallel copies, those copies remain distinct elements of `E`;
`Q.pairwise_disjoint` guarantees the required distinctness across reserve
boundaries even when their unordered endpoint pairs coincide. No reduction
to one representative edge per pair is justified here.

## 6. Uniform integer budget and explicit threshold shrinking

After the two local estimates, a useful integer budget is

```lean
D₀ := max ⌊a⌋₊ (h - r)
```

`Nat.le_floor` turns the old-core real bound into a natural-number bound.
The exceptional estimate gives the other term, and the partition cover
then yields `∀ v, R.degreeOn J v ≤ D₀`.

The candidate numerical condition `6 * D₀ < h` can be derived in a
wrapper around the existing uniform theorem:

1. Invoke that theorem with `δ := α / 360`.
2. If it returns an admissible `ξ`, use `min ξ (α / 300)` as the wrapper's
   error threshold. This explicitly preserves applicability of the
   original theorem and gives the additional upper bound needed below.
3. The resulting inputs and outputs give
   `a ≤ α*n/300`, `h-r ≤ α*n/360`, and `h ≥ r ≥ α*n/30`.
4. Since `α*n > 0`, one obtains
   `6 * (D₀ : ℝ) ≤ α*n/50 < α*n/30 ≤ h`, hence the desired natural-number
   inequality. The casts and the equality between the cast of `h-r`
   and the real difference use the supplied `r ≤ h`.

These inequalities remain a proposed formalization. The existing theorem's
proof constructs its own witness with a minimum involving `α/300`, but
the theorem's stated existential conclusion does not expose an upper bound
on `ξ`. The wrapper must perform its own explicit shrinking; it must not
infer an unstated property from an opaque proof's internal witness.

## 7. Existing joining-decomposition entry point

The relevant existing theorem is
`AssignedParts.assignedLabel_joining_decomposition_in_host` in
`Overfull/AssignedParts/JoiningConstruction.lean`. It is designed for the
original representative's assignment on a different host with the same
vertices. Schematically:

```lean
AssignedParts.assignedLabel_joining_decomposition_in_host
  G R hM U₀ U₁ Z h01 h0Z h1Z hcover hRregular hRno
```

Its inputs include original perfectness of `M`, residual regularity, and
absence of overfull sets in `R`. It does not require `M` to survive in
`R`. It gives the all-even or two-odd joining-decomposition alternatives.

The proposed degree estimates above supply a subsequent quantitative
budget. They do not construct palette grouping, prove parity for every
grouped class, bound grouped footprints or loads, align reserved old-core
crossing copies with primary pieces, assign the exceptional parallel
pair copies to equal free palettes, or produce a residual factorization.
Those obligations remain open. In the all-even case, the existing wrapper
also forgets the individual piece parity certificates needed for grouping;
the later proof must retain the underlying compatible-circuit data.

## Scope of this note

This note preserves a concrete proof route and interface cautions from a
read-only source inspection. It creates no new theorem, makes no new Lean
verification claim, and changes no numbered assertion record. Any future
implementation requires fresh Lean compilation, the full project audit,
source/declaration mapping, and the established preservation checks.
