# Continuation handoff: current-source ordinary-core coloring

## Authoritative starting state

Both requested branches, `main` and
`verified-bipartite-continuation-2026-11-21`, were independently read at
`ac05c3232425399af6c0f29e1f7d3ddc1037424d`, tree
`8cfcdcc6cdd08b3209bc21b1823122bb141c330e`. The remote source was cloned
successfully and used directly. The previous published full verification
records 51 of 69 numbered assertions, including Proposition 4.16 and
Theorem 4.17, and 14,820 audited declarations. No lost checkpoint is
reconstructed in this continuation.

## New mathematical result

The new endpoint is `Overfull.ordinary_cores_coloring` in
`Overfull/OrdinaryCoreColoring.lean`. It handles one, two, or three ordinary
robust cores with a common positive tolerance and order threshold, arbitrary
finite core labels, arbitrary positive density, and any palette `k` at least
the maximum degree. Its sufficient range is
`0<ν≤τ≤min(α,1)/2048000`. The original linear error/exceptional budget is
`a+|Z|+1≤ε*n`.

`Overfull/AuxiliarySimple/OrdinaryThree.lean` constructs the actual auxiliary
completion for three cores and `k<n`. Its order is exactly twice the original
order. Its fourth core is the actual auxiliary graph, and it has no overfull
set. The proved regular four-core endpoint constructs a coloring of this
completion. Restriction retains the original edge copies and properness.

The uniform endpoint combines the one-, two-, and three-core constructions
before it receives the graph. It derives error nonnegativity from the actual
embedded degrees, removes overlap in the exceptional set, and transfers the
actual finite labels. The `k≥n` case uses proved Vizing and palette enlargement.
No original parity, regularity, supplied completion or supplied coloring is
assumed.

## Source identity and inventory

The exact recovered current statement `three:thm:main`, lines 474–487 of
`Four_Robust_Component_Cases_2026-11-21.tex`, has statement SHA-256
`43b21f5ea1e98772ee258c145ddb206ca37e72ffa34b7eb13de25739823509b3`.
The complete retrieved source has SHA-256
`ac5911d111a80a8a0230f093a3631e367fcf73b190cdc7a34d122df7eefdf6b7`.
Its earlier notation explicitly makes partition unions disjoint.

Pinned Theorem 1.2 instead has hash
`9b5f67b17f74bda5e830dba24fcf319fb825981566e6282ece5ff73302ae07ac`.
Its exact original statement was not recovered; the exact pinned Corollary 3.2
was not recovered either. The current-source theorem is recorded separately.
All 69 old numbered records, identities, and statuses remain identical,
including 51 complete and 18 incomplete records. Do not report a new 52/69
count or imply the new theorem was merely another audit rerun. It is a new
mathematical theorem with a separately identified source.

## Verification and preservation

The actual run is `verification/runs/20261125T002000Z`. The source mapping,
proof notes, and independent review are:

- `docs/ordinary-core-coloring-source.json`
- `docs/ordinary-core-coloring.md`
- `docs/ordinary-core-coloring-semantic-review.md`

Read the run's actual `full-*/terminal.json` and preservation receipt to
establish a successful full build. The full gate executes the stock verifier
with additive registration only, freezes all source inputs and controls,
compares them after execution, and preserves full actual output. The allowed
axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

The preservation check requires every previous nonroot mathematical source,
the stock `Audit.lean`, every previous declaration with its module and axiom
set, every prior completed-result mapping, every old declaration map, and all
69 numbered records to remain unchanged. All new public, private, and
generated proof declarations must belong to the two new modules and appear
in the new declaration map. Publication is established only by the actual
remote object and both-branch readbacks under `publication/`.

## Next mathematical work

The remaining native fixed-pattern construction for Lemma 4.4 and Corollary
4.5 must allow two separate exceptional matching pairs. The current two-core
native construction uses at most two exceptional vertices and hence at most
one such pair. The five-exception source statement can have two pairs.
Two robust core parts plus two pair parts need four distinct assigned labels,
then simultaneous native reserves and original-copy terminal reassembly.

The proved four-label circuit theorem and four-piece grouping can be used
after that setup is constructed. The large regular four-core theorem does not
replace it: exceptional pair parts have order two and the source host may be
a multigraph. Do not close the five-exception statement by silently changing
its exceptional bound to two.

The critical average-degree input, critical-case compositions, mixed and
bipartite constructions, dense integral packing and absorption, padding,
and main theorem retain their recorded unfinished status. Exact recovery of
the older Theorem 1.2 and Corollary 3.2 statement identities remains a separate
source task. Do not repeat the newly completed nonregular composition unless
an actual failed verification gate identifies a defect.
