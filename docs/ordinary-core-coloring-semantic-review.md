# Semantic review: nonregular coloring with at most three ordinary cores

## Scope and evidence

This independent review concerns the new source files
`Overfull/AuxiliarySimple/OrdinaryThree.lean` and
`Overfull/OrdinaryCoreColoring.lean`. Its complete source-facing endpoint is
`Overfull.ordinary_cores_coloring`; the three-core maximum-degree wrapper is
an additional specialization. This review examines mathematical scope and
construction. Successful compilation, the transitive axiom inventory, and
publication must be established by the actual run receipts separately.

The inspected manuscript is the current
`Four_Robust_Component_Cases_2026-11-21.tex`, Library version 25, with
285846 bytes and full SHA-256
`ac5911d111a80a8a0230f093a3631e367fcf73b190cdc7a34d122df7eefdf6b7`.
Its statement labelled `three:thm:main` is at source lines 474–487. The exact
begin/end-theorem block, without a terminal line feed, has SHA-256
`43b21f5ea1e98772ee258c145ddb206ca37e72ffa34b7eb13de25739823509b3`.
The raw scoped read, statement bytes, and comparison are recorded in the
current run's source evidence.

This is not the pinned November 20 Theorem 1.2 statement hash
`9b5f67b17f74bda5e830dba24fcf319fb825981566e6282ece5ff73302ae07ac`.
The current statement includes one, two, and three ordinary cores. An older
review describes the one-core case separately under Lemma 3.1, but that
review does not recover the old theorem's exact statement. Removing only
`1,` from the current displayed core-count set does not recover the pinned
hash either. No whole-manuscript or old statement identity is inferred.

The exact current source was retrieved independently of its search snippet.
A read requesting the previously recorded version 19 returned the current
file identifier, current size, and current text while echoing that requested
version; it was not treated as historical source recovery. The original
November 20 Lean archive contains only the pinned statement hashes, not the
missing manuscript blocks. The pinned Corollary 3.2 labels are absent from
the inspected current manuscript. These observations do not justify changing
either pinned assertion's identity or verified status.

## The theorem being reviewed

Fix an arbitrary positive density `α` and parameters
`0 < ν ≤ τ ≤ min α 1 / 2048000`. One positive error tolerance and one positive
order threshold are chosen before the finite host, finite core index type,
palette `k`, or error `a`. The same constants handle any number of cores
between one and three.

The host is a finite simple graph of maximum degree at most `k`, with
`k ≥ α*n` and no `k`-overfull vertex set. Its disjoint core sets each have
at least `α*n` vertices and carry an actual embedded spanning simple robust
`(ν,τ)`-expander of minimum degree at least `k-a`. The cores and a set `Z`
cover the host, and the literal source budget is
`a + |Z| + 1 ≤ ε*n`. The conclusion is a proper coloring of every original
edge with palette `Fin k`.

The manuscript's notation explicitly makes unions describing partitions
disjoint. The public theorem retains disjointness among the core sets and
allows `Z` to overlap them, then removes that overlap. This covers the source
partition convention. The conclusion does not assume that the original
host is regular, has even order, or has a pre-existing coloring.

## Actual three-core completion

`Overfull.three_core_nonregular_factorization` treats `k<n` and uses the
previously proved auxiliary completion. The total original deficiency is
derived from the actual core degrees and exceptional cover:
`sum_v (k-d_G(v)) ≤ n*(a+|Z|)`. Its real-valued bound supplies the completion
lemma's deficiency hypothesis; no completion is supplied as input.

In this palette range the auxiliary order is exactly `n`. The resulting
simple graph has order `2n`, is `k`-regular, retains the actual original
edge copies, and has no `k`-overfull set. The three original cores are mapped
by the left summand embedding. The whole auxiliary graph is the fourth
core, on the right summand. The mapped cores have identical adjacency,
degrees, and robust-expansion parameters under the proved equivalences.

The shared robust parameter is the smaller of the original parameter and
the parameter constructed by the auxiliary completion. Its positivity is
proved. Both the regular density and each core-order lower bound become
`(α/2)*(2n)`. The auxiliary minimum degree is at least
`k-ceil(s/n)`, and the existing deficiency bound gives the common error
`a'=a+|Z|+1`.

The regular theorem's entire error budget is checked, not just its core
degree bound. With `Z'` the mapped original exceptional set,
`a'+|Z'|+1 = a+2|Z|+2 ≤ 2*(a+|Z|+1)`, because `a≥0`.
Thus the selected original error tolerance supplies the required budget
on `2n` vertices. The complete four-core regular theorem constructs the
coloring of this actual completion. `restrictCompletionColoring` restricts
that coloring to the original copies and proves properness there.

The tolerance is the minimum of the completion and regular tolerances.
The order threshold is the maximum of their thresholds and one. These
choices occur before every original graph and its data. No residual
factorization, central coloring, or terminal cut certificate is assumed.

## Uniform assembly and endpoint conditions

`ordinary_cores_normalized_factorization` obtains the existing one-core and
two-core constructions and the new three-core construction for the same
fixed input parameters. It takes the minimum of the three positive error
tolerances and the maximum of their order thresholds before inspecting
the actual core count. It therefore supplies uniform constants for all
three counts, rather than constants chosen after the graph's decomposition.

The final endpoint normalizes an arbitrary positive density with
`β=min α (1/2)`. The displayed sufficient range implies
`τ≤β/1024000`, which meets the most restrictive one-core construction.
The density and core-order hypotheses transfer by `β≤α`.

When `k<n`, the proof selects an actual vertex of a nonempty core. Its core
degree is at most its host degree and hence at most `k`; comparison with
`k-a` derives `a≥0`. This is not an extra public premise. Replacing `Z`
by `Z` minus the union of all cores produces the required disjoint cover
without increasing its cardinality or the budget. Reindexing the arbitrary
finite core type by `Fin (card I)` retains each actual set and graph.

When `k≥n`, the proved finite Vizing theorem gives at most `Δ+1≤n≤k`
colors, which are embedded into the required palette. The public statement
therefore has no artificial upper bound on `k`. The graph order is positive
by its chosen threshold, so the strict simple-graph degree bound used here
is valid.

The final properness proof acts on the original simple graph's unordered
edges. The multigraph intermediate has an injective edge representation,
and the existing restriction theorem accounts for the actual copies.
No quotient coloring is confused with the required original coloring.

## Review conclusion and counting boundary

The construction has the mathematical scope of the inspected current
`three:thm:main` statement, with an explicit sufficient robust range and
uniform constants. The extra maximum-degree wrapper is a specialization;
it alone would not cover the source's arbitrary palette `k`.

No new premise assumes the requested coloring or any unconstructed stage
needed to obtain it. No mathematical defect was found in this semantic
comparison. The actual strict build and axiom audit remain the authority
for kernel verification. The current-source result should be identified
separately from the pinned 69-assertion inventory unless the old statement
identity is independently established. This review does not promote the
pinned Theorem 1.2 or Corollary 3.2 and does not verify the main theorem.

### Pre-freeze review of the final palette injection

The final `OrdinaryCoreColoring.lean` has SHA-256
`3709dd860ef82615e6263bb647b135d60f65d8d8d9c61aeb521de0722206cb52`.
Comparison with the saved first focused-build source confirms that only
the final `k≥n` palette-enlargement proof changed. The restricted helper
call was replaced by the direct map `Fin.castLE hcolors`, where
`hcolors : G.maxDegree + 1 ≤ k` follows from the same simple-graph degree
bound. Equality of enlarged colors gives equality of their natural-number
values; `Fin.ext` recovers equality of the original colors, contradicting
the properness of the Vizing coloring. This is precisely an injective
palette enlargement on the original graph.

All theorem hypotheses, quantifiers, constants, and conclusions are
unchanged. The correction introduces no source-fidelity change or new
mathematical assumption. This final semantic recheck does not establish
or claim completion of the full build and axiom audit.

## Why the five-exception corollary is still a separate obligation

The exact pinned Corollary 4.5, recovered in
`verification/runs/20261122T235931Z/authorized-manuscript-recovery.md`,
allows two robust cores and at most five other vertices in an arbitrary
even-order regular loopless multigraph with no overfull set.
`Overfull.bounded_input_factorization` proves the two-core alternative only
with at most two exceptional vertices. Increasing that cardinality bound
is not a consequence of its statement.

The current native construction uses the two-vertex bound to permit at
most one internal exceptional matching edge. In particular,
`AssignedParts.exists_two_core_assigned_labels` returns three labels and
proves that its pair fiber has size zero or two. The signatures, pool
selection, protected reserves, and native terminal reassembly retain that
single-pair structure.

With five exceptional vertices, a boundary matching may have two internal
exceptional pairs. The pinned fixed-pattern Lemma 4.4 allows those two
pairs when there are two cores. They must be represented by two distinct
pair parts, giving four assigned parts altogether. The now-proved
four-label circuit decomposition and four-piece grouping supply useful
downstream ingredients, but do not construct these assigned pair parts,
their simultaneous native reserves, or their compatible terminal
reassembly. The regular four-core theorem also cannot be substituted:
the pair parts have two vertices, not the required linear order, and the
host here may contain parallel edges.

Consequently no `FewExceptions/Full.lean` wrapper was added and no claim
of complete Corollary 4.5 was made. Its precise missing step is extension
of the native fixed-pattern construction from one exceptional pair part
to two such parts, while preserving actual parallel-copy palettes and the
same original-host quantifier order.
