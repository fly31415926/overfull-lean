# Simultaneous palettes and blocks from actual graph bounds

This continuation starts at published commit
`9684dadac3621e889c5df49aa25e0b16efb51625`. It proves the finite simultaneous
selection stage of the palette and block argument in Section 6. The palette
and block existence theorems derive their probability estimates from the
actual graph. Their collective assumptions are explicit numerical budgets
below one, together with the displayed graph and integer-size conditions.
There are **75 new public theorem proofs in ten modules**.

These are supporting results for Proposition 6.2. The completed numbered
inventory remains **44 of 69**. Proposition 6.2 asserts a factorization of
the whole graph; selecting suitable palettes and blocks completes only part
of its proof. The regularity construction, special path systems, robust
absorber, and final factorization remain unformalized. The main theorem
remains unverified.

The definitive strict build, transitive axiom audit, complete declaration
list, and exact input hashes are recorded in
[`verification/results.json`](../verification/results.json).

## Principal interfaces

| Component | Source | Principal declarations |
| --- | --- | --- |
| Allowed-population comparison and actual pool tails | [PaletteBudgets.lean](../Overfull/BipartiteFactorization/PaletteBudgets.lean) | `allowed_fraction_le`, `mean_poolDemand_le_scaled`, `variance_poolDemand_le_scaled`, `poolDemand_upper_tail_all` |
| Actual active-row concentration | [PaletteRowTails.lean](../Overfull/BipartiteFactorization/PaletteRowTails.lean) | `row_poolDemand_eq_count`, `palette_row_tail`, `palette_row_tail_of_exclusions` |
| Simultaneous disjoint palettes | [SimultaneousPalettes.lean](../Overfull/BipartiteFactorization/SimultaneousPalettes.lean) | `exists_simultaneous_palettes`, `exists_simultaneous_palettes_of_uniform_budget`, `exists_simultaneous_palettes_of_exclusions` |
| Exact finite product pushforward | [ProductMap.lean](../Overfull/Probability/ProductMap.lean) | `probability_pi_map_eq`, `mean_pi_map`, `probability_pi_map` |
| Shared permutations for fine and coarse labels | [PartitionPermutation.lean](../Overfull/Probability/PartitionPermutation.lean) | `probability_sample`, `exists_good_images`, `sample_biUnion` |
| Concentration across independently sampled parts | [PartitionConcentration.lean](../Overfull/Probability/PartitionConcentration.lean) | `exponential_moment_le`, `chernoff_lower`, `half_mean_lower_tail` |
| Actual ordinary and special preferred copies | [PreferredSampling.lean](../Overfull/BipartiteFactorization/PreferredSampling.lean) | `representative_edges_lower_tail`, `special_preferred_lower_tail` |
| Combined graph-specific block budget | [BlockSelectionBudget.lean](../Overfull/BipartiteFactorization/BlockSelectionBudget.lean) | `probability_bad_le`, `exists_good_block` |
| Simultaneous actual blocks with all position relations | [SimultaneousBlocks.lean](../Overfull/BipartiteFactorization/SimultaneousBlocks.lean) | `exists_good_permutations`, `exists_good_blocks`, `RealizesPositions` |
| Uniform scalar error tolerance and order threshold | [UniformFailureBudget.lean](../Overfull/Probability/UniformFailureBudget.lean) | `exists_uniform_failure_budget` |

## Palette rows and correction pools

Let the exterior multigraph have a proper coloring with labels in
`Fin k`, with `k > 0`. Let `C` be the actual allowed set of labels and
suppose

$$
|C|\ge\frac{32}{33}k.
$$

A uniform palette of size `s` is sampled from `C`. Its true sampling
fraction is `s/|C|`. With $\lambda=s/k$, the proved comparisons are

$$
\lambda\le\frac{s}{|C|}\le\frac{33}{32}\lambda.
$$

For an exceptional vertex $x$, put $c_x=|E_G(x,U)|$. Properness of the
coloring identifies these original incident copies with distinct labels.
The row theorem assumes at least $31c_x/32$ of the labels remain in `C`.
The exclusion wrapper derives this from the stronger retained fraction
$511/512$ in the manuscript's actual excluded-color construction.

The selected row count $r_x$ therefore has its actual mean between
$31\lambda c_x/32$ and $33\lambda c_x/32$. Applying the already proved
hypergeometric concentration theorem with relative error $1/32$ gives

$$
\Pr\left(r_x<\frac{15}{16}\lambda c_x
          \ \text{or}\ r_x>2\lambda c_x\right)
\le 2\exp\left(-\frac{\lambda c_x}{4096}\right).
$$

For a pool `P` of original edge copies, assume each allowed color occurs
at most $b$ times in that pool. With $M=|P|$, the actual demand $e_I$
satisfies

$$
\mathbb E e_I\le\frac{33}{32}\lambda M,
\qquad
\operatorname{Var}(e_I)\le\frac{33}{32}\lambda bM.
$$

For $s>0$ and $M>0$, Chebyshev yields

$$
\Pr\left(e_I>\frac54\lambda M\right)
\le\frac{32b}{\lambda M}.
$$

The public `poolDemand_upper_tail_all` also covers empty pools: their
demand is exactly zero and the bad event is empty. It does not cancel
their cardinality or assume that an empty pool is positive.

For a finite collection of pools $P_j$ and active vertices $Z$, define

$$
\varepsilon(s)=
\sum_{x\in Z}2\exp\left(-\frac{(s/k)c_x}{4096}\right)
+\sum_j\frac{32b}{(s/k)|P_j|}.
$$

If the prescribed positive palette sizes $n_i$ sum to at most $|C|$ and
$\sum_i\varepsilon(n_i)<1$, `exists_simultaneous_palettes` constructs
actual pairwise disjoint subsets $I_i\subseteq C$, each of size $n_i$,
with every row and pool inequality. The proof uses uniform permutation
marginals and a union bound. It assumes no independence between palettes,
rows, or pools. A separate corollary bounds the budget by one scalar using
common lower bounds for palette fractions, row sizes, and nonempty pools.

## Preferred copies and the block failure budget

Let pairwise disjoint finite parts $D_i$ partition a side $B$. A block
samples exactly $s_i=p|D_i|$ vertices in every part, with $0<p\le1$.
Every nonempty part must select at least two vertices; empty parts are
allowed. The exterior graph has degree at most $a\ge0$ at vertices of
$B$.

Ordinary preferred rows use actual representative copies $F_x$ into $B$,
with distinct other endpoints and $|F_x|\ge\beta c_x/4$. The new
product-concentration theorem gives

$$
\Pr\left(|F_x\cap E_G(x,T)|<\frac{\beta p c_x}{8}\right)
\le\exp\left(-\frac{\beta p c_x}{48}\right).
$$

Special preferred rows use all original copies to their preferred side.
For $c_x>0$ and $|E_G(x,B)|\ge c_x/2$, the actual mean and
coefficient-one variance imply

$$
\Pr\left(|E_G(x,T)|<\frac{p c_x}{3}\right)
\le\frac{18a}{p c_x}.
$$

The ordinary preferred set $W_o$, special preferred set $W_s$, and
correction set $Z_{\mathrm{corr}}$ are separate inputs. Only the last
must be disjoint from $B$. For correction rows the graph hypotheses are
$c_x>0$, $|E_G(x,B)|\le c_x/2$, and $a\le pc_x/4096$. The real caps
must satisfy

$$
\frac{59}{64}\lambda c_x\le\ell_x
\le\frac{15}{16}\lambda c_x,
\qquad \lambda>0.
$$

Let $M>0$ be the number of copies in the actual correction pool. The
previously proved score tail combines with the two preferred-row tails
to give the explicit budget

$$
\eta(p)=
\sum_{x\in W_o}\exp\left(-\frac{\beta p c_x}{48}\right)
+\sum_{x\in W_s}\frac{18a}{p c_x}
+\frac{2^{21}a}{p^3M}.
$$

`BlockSelectionBudget.probability_bad_le` derives this bound from the
graph hypotheses. No moment or probability conclusion is supplied as an
assumption. `GoodBlock` asserts the two actual preferred-copy lower
bounds and score at least $13\lambda M/8$.

## Fine blocks and their exact coarse unions

For each label $j$, supply position subsets $S_{j,i}\subseteq D_i$.
One uniformly random permutation of each $D_i$ is shared across every
label. For each fixed label, the sampled coordinates have exactly the
independent fixed-size product law. `FiniteProbability.probability_pi_map` and
`PartitionPermutation.probability_sample` prove this equality for every
joint event on the coordinates, including the nonlinear correction score.

The position sets for different labels may overlap. If label $j$ is
defined as the union of certain fine position sets, its actual vertex
block is exactly the corresponding union of actual fine blocks.
Coordinate inclusions, coordinate disjointness, prescribed component
cardinalities, and coverage of the entire side are all retained.

If $\sum_j\eta(p_j)<1$, `SimultaneousBlocks.exists_good_blocks`
constructs actual vertex sets satisfying every `GoodBlock` conclusion
and all these position relations. Fractions $p_j$, palette fractions
$\lambda_j$, and caps $\ell_{j,x}$ may vary with the label. The proof
uses a union bound on shared permutations, so no independence between
fine and coarse blocks is required.

This theorem assumes the position sets, their exact common fractions,
the two-selected-vertices condition, a positive correction pool, the
cap interval, and the displayed graph bounds. It does not yet construct
the manuscript's integer partitions from arbitrary robust-core input.

## A uniform scalar threshold

For fixed $u,v,w\ge0$ and $r>0$, `exists_uniform_failure_budget`
chooses $\varepsilon>0$ and a natural threshold $m_0$ before the order
$m$ and error $a$. Every $m\ge m_0$ and $0\le a\le\varepsilon m$
then satisfy

$$
um e^{-rm}+\frac{va}{m}+\frac{w}{m}<1.
$$

The proof uses the explicit choices

$$
\varepsilon=\frac{1}{4(v+1)},
\qquad
m_0>4\left(\frac{2u}{r^2}+w\right)+1,
$$

and the elementary estimate $e^{rm}\ge (rm)^2/2$. This proves a
uniform numerical mechanism for making such failure budgets small.
It does not yet identify all graph-specific coefficients or prove that
the manuscript's complete collection of estimates is bounded by this
expression. Those comparisons must be composed with the integer and
boundary conditions in the next stage.

## What remains before a numbered result can be completed

| Stage | Status |
| --- | --- |
| Actual allowed-palette row and pool estimates | Proved, including the population-denominator comparison |
| Actual ordinary/special preferred-row and capped-score estimates | Proved from graph data |
| Simultaneous disjoint palettes under the explicit total budget | Proved |
| Simultaneous fine/coarse blocks preserving supplied position relations | Proved under the explicit total budget |
| Uniform realization from the original robust-core hypotheses | Still needs the graph-specific choices of fractions, integer partitions, positive even palette sizes, floor caps, boundary exclusions, and residual reserves |
| Spanning regularity setup and special path systems | Unformalized |
| Theorem 6.3, the robust absorber | Unformalized |
| Proposition 6.2 and Theorem 6.1, full factorization | Incomplete |

The eventual route to the boundary result remains: complete the Section 6
factorization, compose the proved ordinary-core reduction to close
Lemma 4.2, and apply its two-exceptional-vertex specialization to close
Lemma 4.14. A proof of a supporting existence theorem does not increment
the count of complete numbered manuscript statements.

## Manuscript provenance

The palette and block portions were checked against
`Four_Robust_Component_Cases_2026-11-21.tex`, SHA256
`ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`,
particularly `old:palettes`, `old:fac:row-sampling`,
`old:fac:pool-demand`, `old:fac:score`, and `old:fac:swap-variance`.
The numbered assertion inventory remains pinned to the November 20
source recorded in `manuscript-source.json`; this continuation does not
rebase that inventory or count a weaker conditional result as a complete
manuscript assertion.
