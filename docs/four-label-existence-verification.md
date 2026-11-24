# Unrestricted four-label compatible-circuit verification

## Exact theorem

Let `G` be a loopless multigraph whose edge type distinguishes all parallel
copies, let `C` be a finite set of selected copies, and let `classOf v e`
assign an arbitrary incidence class. There is no finiteness requirement on
the ambient edge type or the incidence-class type. If the vertex type has
at most four elements, all selected degrees are even, and
`2 * (G.classCutOn classOf C v k X).card ≤ (G.cutOn C X).card`
for every vertex, class and shore, then `C` has an exact compatible-circuit
partition. Every part is nonempty, connected and 2-regular, and no two
distinct copies at a vertex have the same incidence class.

Principal endpoints:

- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label`
- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_four`

The hypotheses do not include bounded degrees, bounded multiplicities,
connected support, a pre-existing partition, a safe selector, a regular host,
or strictness of any cut. The selected-copy restriction is constructed and
lifted back through the injective subtype map.

## Proof dependencies

| Step | New source modules | Verified content |
| --- | --- | --- |
| Strict cut coarsening | `FourStrictCoarsening` | A tight local class and its complement preserve all weak and strict nonlocal cut bounds. Every coarse-compatible circuit meets every original tight local class it visits. |
| Strict support analysis | `FourStrictSupport`, `FourStrictTriangles`, `FourStrictComplete`, `FourStrictDiamond` | No compatible parallel pair forces endpoint-monochromatic bundles. Two-neighbor structure is exact. Triangle blockers satisfy local and nonlocal inequalities that exclude the diamond and complete support when no short compatible circuit exists. |
| Finite classification and transfer | `FourSupportClassification`, `FourSupportReduction`, `FourStrictCycle`, `FourStrictSelection` | Kernel-checked finite support classification, vertex relabeling, and the square contradiction give a genuine compatible pair or triangle for every nonempty strict input. |
| Safe removal | `FourStrictSafeSelection` | The selected pair or triangle is compatible in the original classes, preserves original admissibility and even degrees, and strictly decreases the number of copies. Residual strictness is not assumed. |
| Tight-cut normalization | `FourNonlocalReduction` | Any failure of strictness yields a tight nonlocal shore of size one or two avoiding the class vertex. Zero cuts are included. |
| Inside construction | `FourTightShoreContraction`, `FourTightShoreInside`, `FourTightShorePieces`, `FourTightShorePairing` | Contract the exterior to an apex, retain every touching copy, tag original endpoints/classes, coarsen the designated tight apex class, and apply the proved three-label theorem. Original pieces are compatible, internally even, and have zero boundary or exactly one A-copy and one B-copy. |
| Outside construction | `FourTightShoreOutside`, `FourTightShoreOutsideGeometry` | Contract the shore into its designated class vertex. The redirected class bound follows from the original tight cut and disjoint-shore cut identity. The outside graph is admissible, even, and supported on at most three labels. |
| Exact restoration | `FourTightShoreExpansion`, `FourTightShoreBlocks`, `FourTightShorePieceGeometry`, `FourTightShoreAssembly`, `FourTightShoreClosed`, `FourTightShoreCompletion` | Each surviving copy indexes its original block. A common anchor class permits at most one shore block in each compatible outside part. Expanded parts and saved pieces are compatible and even, so ordinary decomposition gives genuine circuits. Their original-copy unions are disjoint and cover every copy. |
| General existence | `FourTightShoreRestriction`, `FourExistence` | Restrict arbitrary selected copies, induct on their cardinality in the strict branch, apply the direct whole-partition construction in the tight branch, and pad arbitrary vertex types of size at most four injectively. |
| Exact criterion | `FourCharacterization` | Compatible partitions imply even degrees as well as all half-cut bounds; the converse is the new existence theorem. |
| Additional explicit family | `FourUniformCycle` | Arbitrarily repeated simple circuit templates, including equal-size square bundles, have exact-copy compatible partitions under the stated corner-class separation. |

## Original-host applications

`FourJoiningComplete` removes the boundary-size restrictions from the
earlier circuit-stage applications. The original regular host and absence
of overfull sets provide the cut inequalities; the new theorem constructs
the quotient partitions.

- `exists_fourJoining_decomposition_of_even_fibers` covers at most four
  even fibers. It returns disjoint nonempty original matchings of at most
  four copies, covering every joining copy and meeting each fiber in zero
  or two boundary copies.
- `exists_fourJoining_decomposition_of_even_degree_bound` permits arbitrary
  fiber parity when the regular degree is even and each original vertex
  has joining degree at most half the regular degree.
- `exists_fourTwoOddJoining_decomposition` covers exactly two odd fibers.
  It constructs exactly `h` primary matching pieces, each of at most three
  copies and with boundary one at each odd fiber, plus surplus pieces of
  at most four copies with even footprints everywhere. The two families
  are disjoint and together cover every original joining copy.

No small even-fiber cut, bounded virtual multiplicity or supplied compatible
partition is an assumption of these endpoints.

## Verification and preserved scope

The exact source inventory is `four-label-existence-source.json`. The full
verifier regenerates `verification/four-label-existence-declarations.json`,
including public, private and generated audited proof declarations.

The run is `verification/runs/20261124T134200Z/`. Focused attempts retain
their actual commands, source snapshots, raw combined output and exit codes.
The final `full-01/terminal.json` and `preservation.json` establish whether
the complete frozen build and transitive axiom audit passed. A focused
build or this prose document alone is not evidence of the full gate.

The baseline is `3991bb7eee091a329046073e0366daa84a603e5d`, tree
`6424bf81123aa75b2254aea7eceff6260611f397`. The gate preserves all 14,260
baseline audited declarations with their owners and axiom sets, 2,609
completed-result mappings, all earlier source/declaration maps, all 69
numbered assertion records, and all immutable source/input hashes. The
unchanged `Audit.lean` allows only `propext`, `Classical.choice` and
`Quot.sound`.

Coverage remains **49/69**. This completes an important supporting theorem,
not a further numbered manuscript assertion. Full Proposition 4.16,
Theorem 4.17 and the main theorem remain incomplete. Publication is proved
separately by exact-tree and both-branch readbacks.
