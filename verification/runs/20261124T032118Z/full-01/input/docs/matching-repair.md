# Reserve repair

`Overfull.MatchingRepair.reserve_repair` proves Lemma 4.1 of the recorded
manuscript. It constructs the entire repaired family and proves the two
degree bounds for actual edge unions.

## Statement and quantifiers

Fix positive `b`, `ζ`, and `ν`. The explicit sufficient robust-parameter
conditions are

```text
ν ≤ 4τ,       τ ≤ 1/16,       16τ ≤ ζ/3.
```

The theorem chooses `μ₀ > 0`. For every `0 < μ ≤ μ₀`, it then chooses
`δ > 0` and an order threshold. These constants precede the finite vertex
type, the graphs, and the matching family.

The formal statement uses a host graph `G` and a reserve `R ≤ G` on `m`
vertices. The reserve is a robust `(ν,τ)`-expander of minimum degree at
least `ζm`. The original matchings are subgraphs of `G`, are pairwise
edge-disjoint, and avoid every reserve edge. Taking the host to be the
complete graph gives the manuscript's unrestricted original matchings.

There are at most `bm` original matchings. Each avoids its even forbidden
set `Xᵢ`, of size at most `δm`. The formal set `uncoveredOutside G Mᵢ Xᵢ`
consists precisely of the vertices outside `Xᵢ` not covered by `Mᵢ`.
Its size is at most `δm`, and each vertex belongs to at most `δm` of these
original uncovered sets. The vertex set has even order.

The output is an actual family `Nᵢ` satisfying all of the following:

- Each `Nᵢ` is a matching with vertex set exactly the complement of `Xᵢ`.
- Every edge of `Nᵢ` belongs to `Mᵢ` or to the reserve.
- The output matchings are pairwise edge-disjoint.
- The union of `Nᵢ ∩ R` has degree at most `μm` at every vertex.
- The union of `Mᵢ ∖ Nᵢ` has degree at most `μm` at every vertex.

The last two statements are bounds on actual graph degrees. No completion,
cut, path, or repaired-family existence statement is a hypothesis of the
public theorem.

## Construction

The proof proceeds by induction over finite sets of indices. At every
stage it records actual completed matchings and the union of their reserve
edges. An incidence is internal when its vertex was not in the current
matching's original uncovered set. The internal capacity is
`floor((μ/2)m)`.

For a new index, let `P` be the reserve with all edges used by earlier
repairs removed. The protected set consists of vertices covered by the
current original matching whose internal incidence has reached the
capacity. The one-matching theorem constructs a robust cut in `P` after
deleting the current forbidden set and completes the matching while using
no reserve edge at a protected vertex.

Vertices in the original uncovered set may still be endpoints after their
internal capacity has been reached. Their contributions are accounted for
by the separate prescribed incidence bound. Thus actual used-reserve
degree is at most internal incidence plus endpoint incidence throughout
the construction.

Each new repair uses only its own original edges and currently unused
reserve edges. Original disjointness and reserve avoidance therefore give
disjointness from every earlier repair. The exact union-degree update
proves the total-use bound needed to control the number of protected
vertices. The degree of the released original edges is bounded by the
degree of the reserve edges used in the completed family.

## Numerical choices

The proof takes `μ₀ = min(ν,ζ)/4`. After obtaining the uniform cut
parameter `ξ > 0`, it fixes `ℓ = ceil(2/ξ)+2`. It chooses `δ > 0` so that

```text
δ ≤ ν/2,  δ ≤ ζ/4,  δ ≤ μ/3,  δ ≤ 1/2,
(8bℓ/μ + ℓ)δ ≤ min(ξ,ζ/3)/16.
```

The order threshold guarantees `μm ≥ 4`,
`min(ξ,ζ/3)m ≥ 16`, and the order condition of the actual cut construction.
The internal capacity and total-use bound then give at most
`4bℓδm/μ` protected vertices. This is precisely the budget used by the
one-matching completion theorem. Every parameter is fixed before the
graph and matching family.

## Proof map

| Module | Content |
| --- | --- |
| `Overfull/MatchingRepairStep.lean` | Actual robust cut and protected completion of one matching |
| `Overfull/MatchingRepairParameters.lean` | Positive error and uniform order threshold |
| `Overfull/MatchingRepairLoad.lean` | Internal and endpoint incidence, exact updates, capacity, and saturation bounds |
| `Overfull/MatchingRepairFamily.lean` | Disjointness of the new repair and updated family |
| `Overfull/MatchingRepairAccounting.lean` | Released-edge degree bounded by used-reserve degree |
| `Overfull/MatchingRepair.lean` | Finite-family construction and full Lemma 4.1 |

The strict Lean build and axiom audit permit only `propext`,
`Classical.choice`, and `Quot.sound`. The main theorem and the later
ordinary-core coloring argument remain unproved in this development.
