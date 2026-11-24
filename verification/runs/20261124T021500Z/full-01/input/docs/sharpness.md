# The sharpness formalization

### The actual graph

[`Overfull/Sharpness/Family.lean`](../Overfull/Sharpness/Family.lean) defines the graph on

```text
(Fin 4 × Fin Δ) ⊕ Fin 5.
```

It contains four cliques, the three edges joining consecutive cliques, the specified spoke edges, and the step-two cycle on the five additional vertices. For every natural number `Δ ≥ 3`, Lean proves that adjacency is symmetric and irreflexive, the order is `4Δ + 5`, and the graph is connected. The two distinguished endpoint vertices have degree `Δ - 1`, the additional vertex `w₀` has degree `2`, and every other vertex has degree `Δ`. The maximum degree is therefore `Δ`. Summing the actual degrees gives the actual edge count `2Δ(Δ + 1)`.

These statements hold for every `Δ ≥ 3`. The coloring obstruction and no-overfull proofs also require `Δ` to be odd.

### The coloring obstruction

[`Overfull/Sharpness/WeightedPetersen.lean`](../Overfull/Sharpness/WeightedPetersen.lean) defines the ten Petersen vertices and separate copies of every edge. It proves that the multigraph with `Δ - 2` copies of each spoke has no proper `Δ`-edge-coloring. The incident-edge lists are proved to be injective and exhaustive, and matching patterns are derived from a proposed proper coloring.

[`Petersen.lean`](../Overfull/Sharpness/Petersen.lean) and [`Encoding.lean`](../Overfull/Sharpness/Encoding.lean) provide the finite matching classification, the zero-or-four nonspoke count, and the obstruction to covering all ten nonspoke edges exactly once. They also provide the odd-cut certificates used below. Finite certificates use ordinary `decide`, whose proof term is checked by Lean's kernel; they do not use `native_decide`.

[`DeletedPetersen.lean`](../Overfull/Sharpness/DeletedPetersen.lean) proves that deleting the distinguished outer vertex preserves the coloring obstruction. A hypothetical coloring of the deleted graph would extend to a proper coloring of the original weighted graph. The proof establishes the actual degrees, remaining edge count, unique missing vertices, and properness of the restored coloring.

[`Overfull/CliqueColors.lean`](../Overfull/CliqueColors.lean) proves that distinct edges crossing a saturated odd set have distinct colors. [`ColoringObstruction.lean`](../Overfull/Sharpness/ColoringObstruction.lean) applies this fact to the actual four cliques. It proves the edge correspondence and the properness of the coloring obtained after contraction. Its conclusion is `Overfull.Sharpness.Family.not_edge_colorable`: the constructed simple graph has no proper `Δ`-edge-coloring.

[`UpperColoring.lean`](../Overfull/Sharpness/UpperColoring.lean) supplies the other direction of the exact chromatic-index assertion. It defines a proper coloring of the whole graph with `Δ + 1` colors and proves `Overfull.Sharpness.Family.has_upper_coloring`.

### Every vertex set satisfies the edge bound

[`Overfull/CutCounting.lean`](../Overfull/CutCounting.lean) proves the incidence identities for actual edges of finite simple graphs. For a vertex set `X`, twice the number of internal edges plus the number of crossing edges equals the degree sum over `X`. The file also proves the deficiency identity, its relation to odd-set overfullness, and the lower bound contributed by a partially intersected clique.

[`WholeCliques.lean`](../Overfull/Sharpness/WholeCliques.lean) handles sets containing each clique either wholly or not at all. It proves the actual internal-edge count, encodes every such set by a ten-bit Petersen mask, and checks the membership and parity correspondence. The resulting graph identity equates its deficiency with the weighted Petersen cut expression. The finite odd-cut certificate then supplies the required lower bound.

[`OddSets.lean`](../Overfull/Sharpness/OddSets.lean) combines this argument with the partial-clique bound and the even-set degree bound. The final theorem is

```lean
Overfull.Sharpness.Family.no_overfull
    {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (X : Finset (Overfull.Sharpness.Family.Vertex Δ)) :
    ¬ Overfull.IsOverfull (Overfull.Sharpness.Family.graph Δ) Δ X
```

The quantifier ranges over every actual vertex subset of the graph. No graph cut or induced-edge formula is assumed in this conclusion.

### Relabeling and the density conclusion

[`Overfull/Relabeling.lean`](../Overfull/Relabeling.lean) proves that graph isomorphisms preserve proper edge-colorability, degrees, maximum degree, internal-edge counts, and the absence of overfull sets. These results transport the construction to `Fin (4 * Δ + 5)` in the final specification.

[`SharpnessArithmetic.lean`](../Overfull/SharpnessArithmetic.lean) proves that, for every real `c < 1/4`, arbitrarily large odd parameters satisfy `c ≤ Δ/(4Δ + 5)`. The final theorem combines those parameters with the verified graph construction to prove Corollary 7.2.

