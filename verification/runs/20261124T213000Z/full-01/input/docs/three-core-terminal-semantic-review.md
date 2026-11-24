# Semantic review: three-core terminal factorization

## Exact scope and source identity

The public declarations `Overfull.three_core_terminal_factorization` and
`Overfull.three_core_terminal_one_factorization` address the **three-core
subcase** of Proposition 4.16, `three:prop:terminal`. The complete proposition
also includes four-core cases, which these declarations do not prove. Its
pinned statement SHA-256 is
`1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c`.
All 69 numbered assertion records remain unchanged. Coverage remains **48/69**;
21 assertions, including the main theorem, remain incomplete.

The exact baseline is published commit
`0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`, tree
`5d031253d02d0d0878422f8fbc367f04b812450c`. Its complete Corollary 4.6
is used as an already proved input to the central contraction theorem.
The initial source assessment and baseline publication readbacks are retained
in `verification/runs/20261124T032118Z/`.

## Public mathematical hypotheses

Fix positive real numbers `α` and `ν`, and a real `τ` with
`ν ≤ τ ≤ min α 1 / 64`. The conclusion chooses one positive error tolerance
`ε` and one positive natural order threshold `n₀`. Only after these constants
are fixed does it quantify over the finite vertex type, the simple graph, the
three core parts and their simple core graphs, the natural degree `h`, and the
real core error `a`.

For the resulting graph of order `n`, the hypotheses are:

- `n ≥ n₀`, and `n` is even.
- The host is `h`-regular and `α n ≤ h`.
- No vertex set is `h`-overfull in the original host.
- Three pairwise disjoint finite parts cover all vertices, and each has
  at least `α n` vertices.
- Each actual simple core embeds in the host induced by its part, is a
  robust `(ν, τ)` expander, and has degree at least `h - a` at every vertex.
- `0 ≤ a` and `a + 1 ≤ ε n`.

Evenness is a condition on the **order**, not on the degree. The public
conclusion is an `h`-edge-coloring of the original edge-copy multigraph, or
equivalently exactly `h` pairwise disjoint perfect matchings whose union is
every original simple-graph edge copy.

The public theorem assumes no joining decomposition, palette, completed
matching family, residual factorization, central coloring, leaf coloring,
or no-overfull certificate for a contracted graph. These objects are
constructed within its proof.

## Uniform parameter order

The proof first normalizes the density to `β = min α 1`. The packing theorem
chooses a positive surviving expansion parameter `θ ≤ τ/2`. This happens
before choosing the residual error tolerance. The even and two-odd residual
factorization theorems then choose a common positive tolerance `η` and a
common minimum part order. Finally the prefix theorem chooses the original
`ε` and `n₀` to meet those requests, before seeing the host.

The residual degree is at least `(β/2)` times each part order. Its core
expansion parameters are `(θ, τ/2)`. The inequality
`τ/2 ≤ (β/2)/64` is inherited from the public range bound. The prefix scalar
proof includes the floor and natural-subtraction bounds; it does not replace
them by an asymptotic assertion. In particular, the actual prefix length is
`h/100 + 1`, it does not exceed `h`, and the surviving core error is at most
`η` times each actual part order.

## Original joining decomposition and completed prefix

The disjoint covering parts define an actual label on every vertex.
Even total order leaves precisely two cases: all three part orders are even,
or exactly two are odd. With three labels, the union of the cuts of any two
distinct parts is exactly the original joining-copy set.

In the even case, the proved at-most-three-label decomposition yields even
joining pieces. They are grouped into small matching classes and all joining
copies are selected for completion. In the two-odd case, the original-host
decomposition supplies exactly `h` primary pieces and even surplus pieces.
The prefix selects the required number of primary pieces and groups the
surplus into their classes. Every other primary piece survives intact.

The adaptive robust-core packing rules complete each selected boundary class
to an actual perfect matching. Every added edge is internal to a core.
Consequently a completed matching deletes exactly its prescribed joining
copies. This proves the exact identity between the original joining pool
minus all deleted original copies and the retained primary pieces.

The core and residual bridges preserve original endpoints and edge identities.
They construct an explicit equivalence between the actual simple residual
edge type and the subtype of original copies not deleted by the prefix.
The retained primary family therefore preserves matching, disjointness,
coverage, support and cut cardinalities in the residual.

## All-even residual

The residual joining set is empty, so each part is an actual closed component.
The uniform independent-exterior shore theorem with zero exterior vertices
constructs a coloring of every component from its robust residual core.
The generic retained-copy gluer constructs the whole residual coloring.
No local coloring is an input to this case.

## Two-odd residual

The surviving family has exactly the residual degree number of matching
classes. Each class crosses the cut of each odd part exactly once, and their
union is exactly the union of those two cuts.

The simultaneous central contraction retains the even part as actual
vertices, replaces the two odd parts by distinct apices, and retains the
original copies whose contracted endpoints differ. It discards only copies
internal to a contracted odd part. Separate proofs establish looplessness,
the exact incidence equivalences, regularity, and the embedded robust core.

Each surviving joining matching remains a matching after contraction: the
singleton cut bounds prevent collisions at either apex. These matchings cover
all central copies outside the internal edges of the even core. Therefore
any shore containing at most one core vertex has at most `k floor(|X|/2)`
internal edges. The proved small-cut classification shows that a putative
violating odd cut has this property on one side. Regularity and even total
order transfer the cut argument to the complement when needed. This proves
the central no-overfull condition from the original matching data.

The completed bounded-input Corollary 4.6 now constructs a central coloring
with one robust core and two exterior vertices. Each odd leaf receives a
coloring from the one-apex shore theorem. Singleton boundary extension
relabels each leaf on the exact original crossing copies according to the
central coloring. This also agrees on copies between the two odd parts.
The generic covering-shore gluer applies without assuming that the even
part was closed.

## Restoration and proof accounting

The residual coloring is transported to the surviving-original-copy subtype.
The completed perfect matchings receive separate prefix labels; the residual
colors receive disjoint later labels. Actual degree arithmetic identifies
the resulting palette with `Fin h`. Regularity makes every final color class
a perfect matching, and all classes partition the original copies.

Focused development checks are evidence for their recorded source snapshots.
The immutable full verifier run and unchanged `Audit.lean` determine the
complete project result. The declaration map must contain every audited
declaration in every new module, including private and generated proofs.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

The preservation checker separately requires all 13,366 previous audited
names, owning modules and axiom sets, all 2,272 prior result mappings, all
previous mathematical sources other than the additive root imports, and all
69 numbered assertion records to remain unchanged. The four verifier edits
only register the new source and declaration map and enforce its zero
numbered-assertion promotion. All previous verifier guards remain in place.
