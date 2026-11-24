# Independent mathematical review: deletion criteria and global coarsening

The reviewer inspected the two complete source files and their successful
focused receipts. The current bytes match the successful snapshots:

| Module | SHA-256 | Focused command |
| --- | --- | --- |
| `Overfull.CompatibleCircuits.FourCutCriterion` | `4764c2c6956b9261a53fc22c8b6db6e315e3baf9e0be786dfb1287208de7de05` | `four-cut-02`, exit 0 |
| `Overfull.CompatibleCircuits.FourGlobalCoarsening` | `d6afd67ac679674e01817d1ca5ad585993fedca366b6c0262c06fa0f1d3b229d` | `global-coarsening-01`, exit 0 |

Both actual receipts record unchanged inputs. This source review and these
focused passes are separate from the required complete frozen project audit.

## Exact deletion criterion

Fix a tested shore and incidence class. Write `c,a` for its original cut and
class-cut sizes, and `q,r` for their sizes in the deleted circuit. The existing
exact deletion identity says that residual admissibility is equivalent to
`2a+q <= c+2r`. Original admissibility gives `2a <= c`; the original cut and the
circuit cut are even. A circuit of at most four copies has `q` equal to zero,
two or four. Compatibility gives `r <= 1`.

When the original inequality is tight, the exact condition is `q <= 2r`.
Consequently the candidate may cross at most twice, and any crossing requires
a selected copy from the tight class. Conversely, these two requirements imply
`q <= 2r`. When the slack is two, the only nonautomatic case is `q=4`, which
requires a copy from that class. All greater nonnegative even slack is at least
four and therefore automatically absorbs `q`. Empty original cuts are included
in the tight case and cause no exception.

These arguments prove both directions of the stated equivalence. They do not
assume the existence of a candidate satisfying it. The four-label specialization
uses the already proved bound that a genuine circuit on four labels has at most
four actual copies. The pair/triangle specialization needs no compatibility
hypothesis: its even cut size is at most two, and meeting tight classes alone
is the exact residual criterion. All counts refer to selected original copies,
including parallel copies.

## Global admissibility of tight local coarsening

At a vertex, let a tight local class have size `m`, so the total selected degree
is `2m`. On a shore let `a` be the crossing count in this class, `b` the crossing
count in its complement, and `c` the whole cut size. Toggling the vertex changes
the whole cut to `c+2m-2(a+b)` and the tight class count to `m-a`. Applying the
original half-cut inequality on that toggled shore yields `2b <= c`. The Lean
proof uses addition identities, avoiding any unjustified subtraction in the
natural numbers.

Thus both classes of the two-class coarsening obey every cut bound. Vertices
whose local coarsening is the identity retain their original bounds. Since a
class-cut inequality refers only to the classes at its specified vertex, these
coarsenings can be chosen independently at all vertices and remain globally
admissible. No Eulerian, cardinality or regularity assumption is needed. The
finite selected set makes every count well defined even with an infinite ambient
vertex type.

The local coarsening's refinement property states that distinct coarse classes
have distinct original classes. Its contrapositive transfers a compatible
coarse edge set to an originally compatible set. The partition transfer keeps
the same parts, circuits, disjointness and exact cover. The final existential
theorem constructs the required coarsenings from the original admissibility
bounds and classical choice; it does not take global coarsenings as an added
hypothesis or claim an unrestricted compatible circuit partition.

## Assessment

No semantic gap or hidden strengthening was found in these two modules. Their
stated scopes match the proofs and supporting documentation. They complete no
additional numbered manuscript assertion. Full Proposition 4.16, the arbitrary
four-label partition theorem and the main theorem remain outside their scope.
