# Protected native traces and complete two-pair external assembly

## Result and scope

This continuation proves **75 public theorems in 16 new modules**. Its final
endpoint is
`Overfull.NativeCore.exists_native_two_pair_external_palette`.
For a native partner representative with exactly two exceptional matching
pairs and at most five exceptional vertices, it constructs the complete
external matching family in a supplied safe residual. It derives the joining
palette, its exact protected traces, the zero-or-one-star case split, and the
remaining star extension. None of those objects or certificates is supplied
as an input to the final theorem.

The endpoint retains the original residual edge copies and selected reserve
indices. Its conclusion includes exact external coverage, saturation of all
exceptions in every color, even uncovered sets in both original cores, and
the genuine core-deficit load bound. It is an external-assembly theorem:
construction of the safe residual, completion inside the robust cores, and
factorization of the terminal remainder remain separate obligations.

**The numbered inventory remains 51/69.** No numbered assertion is promoted.
In particular Lemma 4.4, Corollary 4.5, and the main theorem remain unverified.
All previous mathematical source files and the current-source ordinary-core
coloring theorem are preserved.

The source baseline is public commit
`f2510d10c114bcf3d0003b5e2e4e35cb0400167d`, tree
`58fe77f4afaba4b0ab6cf77956afb1c23608cd35`.
The [source manifest](protected-trace-source.json) lists every new public
theorem and source hash. The full kernel audit separately records private
and generated proofs in the complete declaration map.

## Exact final interface

Write `H` for the residual multigraph, `h` for its regular degree, `r` for
the number of disjoint partner-preserving reserved boundaries, `D` for the
core-deficit budget, `t` for the number of selected reserved boundaries, and
`n` for the vertex count. The theorem assumes:

- An original perfect matching, pairwise disjoint old cores `U₀`, `U₁` and
  exceptional set `Z` covering the vertices, and `|Z| ≤ 5`.
- Distinct actual copies `e₀`, `e₁` with
  `G.internalOn M Z = {e₀,e₁}`. The existing partner reserve is tied to
  this representative; a heavy code is not assumed to have two pairs in
  the general native problem.
- Deletions avoiding the entire reserve, an `h`-regular residual, and no
  `h`-overfull vertex set in that residual.
- Actual retained simple cores embedded in `H`, each with minimum degree
  at least `h-D`, and `h ≤ r+D`.
- An injective selection `q : Fin t → Fin r`, together with
  `h>0`, `128D ≤ h`, `2t ≤ h`, `L>0`, and
  `nD ≤ 2L(h-t-40D)`.

The subtractions in the last inequality are natural-number subtractions as
written in Lean; the proof derives all positivity and conflict margins it
uses. No asymptotic choice of these parameters from the original manuscript
hypotheses is claimed here.

The conclusion provides an injective color assignment `f : Fin t → Fin h`
and `h` pairwise edge-disjoint matching classes `F j` of actual residual
copies, with all of the following properties:

| Property | Exact guarantee |
| --- | --- |
| Protected classes | `F (f i)` equals the entire surviving boundary with original reserve index `q i`. |
| Exceptional saturation | Every `F j` covers every vertex of `Z`. |
| External coverage | The union of the classes is exactly `joiningCopies H label ∪ exceptionalCopies H univ Z`. |
| Assigned-fiber parity | Each class has the required cut parity on each of the four actual assigned fibers. |
| Old-core parity | Both `U₀ \ support(F j)` and `U₁ \ support(F j)` have even cardinality. |
| Class size | Every class contains at most `6L+3` copies and has support size at most `12L+6`. |
| Retained-core separation | Every class is edge-disjoint from each embedded old core. |
| Whole-family load | Each vertex in either old core belongs to the support of at most `D` classes. |

The exact external union is not identified with the entire complement of
the embedded core graphs: unused same-fiber internal copies may remain.
The load conclusion follows from the actual host/core degree deficit, not
from a count of colors available to a star.

## Construction and dependency map

| New module | Public proofs | Role |
| --- | ---: | --- |
| `ResidualPalette/FourReservedPrimary` | 2 | Force chosen actual crossings to singleton primary pieces in the four-label circuit decomposition. |
| `ResidualPalette/FourProtectedPalette` | 3 | Construct injectively indexed empty colors and exact protected singleton palettes. |
| `NativeReserve/PartnerTraces` | 12 | Prove actual empty/singleton joining traces and their surviving-copy images when the two pairs exhaust `Z`. |
| `NativeReserve/PartnerGeneralTraces` | 7 | Extend the trace construction to further exceptions assigned to old cores. |
| `NativeAssembly/TwoPairProtected` | 2 | Construct the protected palette and pair-only completion from native reserve traces. |
| `NativeAssembly/TwoPairBounds` | 6 | Derive the joining-degree bound from surviving reserve incidence and retained core degrees. |
| `NativeAssembly/TwoPairGeneralProtected` | 4 | Remove the no-unpaired restriction from the native degree and protected-palette interfaces. |
| `WeightedPalette/FourGrouping` | 5 | Group four-copy pieces with protected seeds and actual star-weight bounds. |
| `NativeWeighted/FourJoining` | 3 | Construct weighted even and two-odd four-label palettes. |
| `NativeWeighted/TwoPairNative` | 2 | Derive the parallel-copy bounds and native weighted palette from the residual and retained cores. |
| `NativeAssembly/TwoPairStarBase` | 13 | Combine both pair completions with whole prescribed boundaries, retaining extra internal star copies. |
| `NativeAssembly/TwoPairStar` | 7 | Derive remaining-star balance and complete the fifth-vertex star in unused colors. |
| `NativeAssembly/TwoPairStarReserve` | 2 | Supply actual native pair injections and prove exact joining/exceptional coverage. |
| `AssignedParts/TwoPairOneStar` | 4 | Derive the actual two-pair versus two-pair-plus-one-star geometry. |
| `NativeCore/TwoPairParity` | 2 | Transfer assigned-fiber cut parity to the uncovered original cores. |
| `NativeCore/TwoPairExternal` | 1 | Compose the complete conditional external family with parity, size and load conclusions. |

### Actual protected traces

For each reserved boundary, every selected matching edge incident with an
exception is internal to its actual assigned fiber. This follows from
matching uniqueness and the full partner code. A fifth exception is assigned
to one old core, so its reserved edge is internal to that assigned part.
Consequently the joining trace consists only of the possible old-core
crossing. The trace is empty in the even case and is one actual crossing
copy in the odd case. Survival, injectivity and the original reserve index
are all proved on residual-copy subtypes.

In the odd case, the reserved-primary induction removes a selected original
crossing together with a distinct virtual crossing as a compatible
two-circuit. Closed-cut bounds remain unchanged; separating cut bounds and
the virtual budget decrease together. The induction invokes the already
proved unrestricted four-label compatible-circuit theorem at its base.
The host theorem derives its cut inequalities from regularity, absence of
overfull sets, and the stated degree/selected-copy budgets. It supplies a
primary singleton for each selected actual crossing. Protected grouping
then retains those singleton classes exactly.

In the unweighted even construction, the proof reserves the required number
of empty colors and injectively embeds the remaining palette. It proves that
the protected classes are empty rather than assuming that an arbitrary
palette has enough empty colors. The weighted even construction instead
reserves empty colors inside the full `h`-color grouping, so its weight
threshold is measured against that full palette throughout.

### Weighted grouping and the fifth vertex

The fifth-star construction needs a bound on actual copies blocked by a
joining class. A class-cardinality bound alone does not give the desired
linear-error estimate. The new weighted grouping uses pieces of at most
four copies and at most eight support vertices. It proves that at most
`16D` colors are overloaded for each star resource; with at most two
resources and the joining-conflict budget, `40D` is a sufficient total
margin. The hypotheses `128D ≤ h` and `2t ≤ h` provide the threshold slack.
The resulting whole-class star weight is at most `h/8`.

The native weighted theorem derives the parallel bound from the actual
retained simple cores and their degree deficits. It also derives the joining
degree bound using the `r` surviving reserve incidences at every exception.
Thus the final external theorem does not assume these estimates separately.

Two distinct matching pairs use four distinct exceptional vertices. The
five-exception bound therefore leaves either no further exception or one
vertex assigned to an old core. The geometry theorem constructs the exact
fiber `insert z U`, so every copy incident with that vertex is either a
joining copy or an internal assigned-core star copy. The assembler retains
all already prescribed boundary copies and derives the equality between
remaining star copies and free colors from regularity and saturation.
It completes the star without changing the joining cuts.

### Coverage, parity and loads

With no fifth vertex, the pair completion saturates all exceptions in all
`h` colors. Since the classes are disjoint and each exception has degree
`h`, all actual exceptional copies must occur. This gives exact external
coverage even when other exceptional copies are parallel.

With a fifth vertex, the native star assembler proves the same exact union
directly. In both branches, complete exceptional saturation transfers the
actual assigned-fiber cut parities to even uncovered sets in `U₀` and `U₁`.
The classes lie outside the embedded simple cores. Counting disjoint actual
incidences then bounds the total load at an old-core vertex by
`degree_H(v)-degree_core(v) ≤ D`.

## Verification evidence and preservation

The run is
[`verification/runs/20261125T121903Z`](../verification/runs/20261125T121903Z/).
Every focused compiler attempt, including failures, retains the actual
command, exit status, output, source snapshot, timestamps and hashes. A
successful strict receipt exists for the final bytes of every new module.
Independent review covers each module at those same bytes and never uses
the primary author as its sole independent reviewer.

The full gate executes the real `python3 scripts/verify.py` on frozen inputs.
Its `full-*/terminal.json`, `preflight.json`, `preservation.json` and archived
outputs establish the actual full-run status. A focused pass or source
inventory does not substitute for that gate. The stock `Audit.lean` is
unchanged, and the only permitted axioms are `Classical.choice`, `Quot.sound`
and `propext`. No `sorry`, custom axiom or `native_decide` is introduced.

The preservation gate retains all **742 previous nonroot mathematical
modules**, all **14,994 previous audited declarations** with their original
module and axiom lists, all **2,926 previous completed-result mappings**, all
**23 previous declaration maps**, all 69 pinned numbered records, and the
exact current-source manuscript excerpt. Only registered additive imports
and additive verifier registrations are permitted. Source and control hashes
are checked again after the full verifier finishes.

Public delivery requires separate remote commit/tree verification and
readback of both authorized branches. Those receipts belong in the run's
`publication/` directory and must not be inferred from local commit success.

## Remaining construction

The next step is a native reserve-avoiding deletion/rounding construction
that produces the safe residual and the quantitative retained-core budgets.
The previous single exceptional-pair pool is not cut-uniform for a larger
exceptional set; pools must distinguish unordered exceptional endpoint pairs.
See [the concrete residual plan](partner-safe-residual-next-step.md).

The zero-pair and one-pair representatives can leave five and three unpaired
exceptions. They still need native multi-star and same-label-bundle assembly.
A heavy partner code cannot be assumed to choose the two-pair branch.
Robust-core completion and terminal factorization must also be connected to
the newly constructed external family with their original hypotheses.
These obligations are why this checkpoint records supporting progress and
does not close Lemma 4.4 or Corollary 4.5.
