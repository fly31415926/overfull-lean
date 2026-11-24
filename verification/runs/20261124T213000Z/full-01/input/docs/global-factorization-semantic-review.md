# Semantic review: full single-core coloring and supporting continuations

## Numbered scope and exact source

This continuation completes **Lemma 3.1**, `single:lem:coloring`, by
`Overfull.single_core_coloring`, raising numbered coverage from 48/69 to
49/69. No other numbered assertion is promoted. The three-core regular,
all-four-odd terminal, and four-regular compatible-circuit theorems are
supporting results with the scopes below. The main theorem, full Proposition
4.16, and full Theorem 4.17 remain unproved.

The authoritative public baseline is
`14978e4dec2bce94f63953df7b1bdd54f61c3e6c`, tree
`c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767`. Both public branches were read back
at that commit. Its nonroot mathematical sources, `Audit.lean`, source maps,
and historical evidence remain unchanged.

The pinned Lemma 3.1 statement has SHA-256
`e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe`.
Its exact bytes were independently recovered from a later local manuscript
and match the pinned statement identity. This does not identify the complete
manuscripts. The excerpt and extraction provenance are retained in
`verification/runs/20261124T042718Z/source-statement-3.1.tex` and
`source-statement-3.1.json`.

## Literal Lemma 3.1 hypotheses

The endpoint fixes `0 < ν ≤ τ ≤ 1/4096000`, then chooses positive `ε` and
`n₀` before the original graph, sets, embedded core and error parameter.

| Source condition | Formal endpoint |
| --- | --- |
| Simple graph, order at least `n₀` | Arbitrary finite vertex type and `SimpleGraph V` |
| Maximum degree `Δ ≥ n/4` | Actual `G.maxDegree`, without a supplied regular degree |
| No `Δ`-overfull set | Every `Finset V` tested by `IsOverfull G G.maxDegree` |
| `V(G) = U ∪ Z` | Pointwise cover; overlap is permitted |
| `|U| ≥ n/4` | Exact finite cardinality lower bound |
| Spanning robust core inside `G[U]` | `H : SimpleGraph U`, `H ≤ G.induce U`, robust expansion |
| Core degree at least `Δ-a` | Pointwise degree bound in `H` |
| `a+|Z|+1 ≤ εn` | The same combined error budget |
| Original graph is `Δ`-edge-colorable | `Nonempty (Overfull.EdgeColoring G G.maxDegree)` |

The explicit range is a sufficient choice of the source's sufficiently small
range. No parity or regularity hypothesis is added. The core is nonempty, and
its degree is at most the ambient maximum degree; its stated lower bound
therefore implies `a ≥ 0`. Replacing `Z` by `Z \ U` preserves the cover and
decreases the budget. Neither nonnegativity nor disjointness is an extra public
premise. Simplicity supplies `G.maxDegree < n` for auxiliary completion.

## Constructed chain and uniform parameters

The proof composes the existing three-core terminal theorem with actual
frequent-pattern reduction and exact prefix restoration. Robust range
reduction yields a bounded-exception theorem. Foreign-edge reduction and
bounded exceptional absorption then give three-core regular factorization
with a small linear exceptional set. One auxiliary completion reduces two
ordinary cores to three regular cores; a second reduces one ordinary core to
two. The source wrapper specializes density to `1/4` and uses actual maximum
degree and the normalized cover.

The absorption tolerance is an entire positive function of the eventual
exceptional cardinality. The proof fixes surviving foreign robustness, then
absorption robustness, and obtains `εB(t), nB(t)` for every natural `t`.
It chooses `f(t) = min (1/4) (εB(t)/2)` before absorption returns its bound
`T`. A finite supremum of `nB(t)` for `t ≤ T` enters the original threshold.
No uniform parameter depends on the eventual host or exceptional set.

Each ordinary wrapper fixes auxiliary robustness before the succeeding error
tolerance. It uses `a' = a+|Z|+1`. The completion has order exactly `2n`, since
the original degree bound is below `n`. Total and ceiling-average deficiency
bounds follow from the original embedded core degrees. The later budget
uses `a'+|Z|+1 ≤ 2(a+|Z|+1)` with an explicit use of `a ≥ 0`.

## Actual original edges and auxiliary simple hosts

The completion has an injective unordered edge map. `AuxiliarySimple.Graph`
realizes its range as a simple graph and constructs an explicit edge
equivalence. Degrees, internal-edge counts, cuts and overfullness are
transported exactly. Core vertex equivalences carry embedding, degree and
robustness certificates. Coloring restriction follows the same original-copy
injection. The final wrapper proves properness directly for the original
simple coloring type.

`robust_instance_transfer` reconciles proof-irrelevant decidability instances.
It changes no graph, parameter or expansion claim and introduces no axiom.

## All-four-odd terminal result

`Overfull.four_odd_terminal_one_factorization` proves the all-four-odd terminal
subcase from the original simple regular host, four odd disjoint covering
robust cores, no overfull set, small core-degree error and actual forest-pair
supplies. Its sufficient range is `τ ≤ min α 1 / 64`. Positive error and
order thresholds precede the host. The conclusion partitions the original
edge copies into exactly `h` disjoint perfect matchings.

The proof constructs the decomposition, selected palette, completed prefix,
residual geometry, local colorings and reassembly. Selection removes `r`
primary classes when `4r ≤ h`, leaving either one common center or at least
`r` singleton classes at every part. The prefix uses `r = h/100+1`, and
density gives singleton reserve `γ = min α 1 / 100`.

In the singleton-rich case, all shores use boundary labels from the same
global primary indices; full boundary extension and copywise gluing color
the residual. In the common-center case, the other three odd shores become
independent apices. Central factorization, singleton alignment at each leaf
and exact gluing reconstruct the residual. The completed prefix is restored.

Forest-pair supply remains an explicit original hypothesis. Four even parts
and exactly two odd parts are not covered. Full Proposition 4.16 is not promoted.

## Four-regular compatible circuits

`Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_regular`
constructs a compatible circuit partition on actual copies of a loopless
multigraph on `Fin 4`, assuming degree exactly four at each label and original
admissibility. Its stronger local form assumes each incidence class has at
most two copies; singleton-cut admissibility supplies that bound.

The proof constructs balanced local pair coarsenings, classifies opposite
bundle counts as `(a,b,c,c,b,a)` with `a+b+c=4`, proves all four template
profiles including the disconnected case, constructs the actual-copy
equivalence and transports the partition back. Equal original classes imply
equal artificial pair classes, so compatibility for the latter implies
compatibility for the original classes. No template or partition is assumed.

The result is limited to degree four at all labels. General admissible
Eulerian four-label existence, with larger or unequal even degrees, remains
open and is still needed for the other terminal cases.

## Verification authority

Focused strict builds establish local elaboration. Final acceptance requires
the complete verifier on unchanged frozen inputs, its genuine terminal
receipt, unchanged transitive axiom audit and preservation report.
`Audit.lean` permits only `propext`, `Classical.choice` and `Quot.sound`;
project axioms and `sorryAx` are rejected.

`docs/global-factorization-source.json` records exact source paths and hashes.
`verification/global-factorization-declarations.json` maps every audited proof
in these modules, including private and generated names, source owners and
axiom sets. Source-hash-linked independent reviews and genuine failed attempts
are retained in the current run.
