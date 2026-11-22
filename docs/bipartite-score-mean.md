# Expected correction scores for actual partition samples

This continuation starts from sampling checkpoint
`5a5550119108fb11371fca0de0b50b7a74af0269`. It completes the actual
partition-sample score mean, combines it with the already proved product
variance, and constructs a block with the prescribed part sizes when the
explicit failure bound is below one.

There are **31 new public theorem proofs in five modules**. They are
supporting results for Section 6. The completed numbered inventory remains
**44 of 69**; Theorem 6.1, Proposition 6.2, the absorber theorem, and the main
theorem remain unverified. The definitive strict build, transitive axiom
audit, and exact source hashes are recorded in `verification/results.json`.

## Sources and principal interfaces

| Component | Source | Principal declarations |
| --- | --- | --- |
| Product expectations and coordinate independence | [ProductMoments.lean](../Overfull/Probability/ProductMoments.lean) | `mean_pi_product`, `mean_pi_coordinate`, `mean_pi_sum`, `mean_pi_mul_coordinates` |
| Constant shifts and additive product variance | [VarianceShift.lean](../Overfull/Probability/VarianceShift.lean) | `variance_add_const`, `variance_const_add`, `variance_pi_sum_le` |
| Actual vertex-pair laws and internal edge-copy expectation | [BlockMembership.lean](../Overfull/BipartiteFactorization/BlockMembership.lean) | `mean_pair_indicator_eq`, `mean_pair_ge_half`, `mean_internalEdges_ge` |
| Actual exceptional-row moments and capped means | [BlockRowMoments.lean](../Overfull/BipartiteFactorization/BlockRowMoments.lean) | `mean_edgesTo`, `variance_edgesTo_le_of_degree`, `capped_row_mean` |
| Full score mean, lower tail, and supported good block | [BlockScoreMean.lean](../Overfull/BipartiteFactorization/BlockScoreMean.lean) | `cappedScore_product_mean`, `cappedScore_product_lower_tail`, `exists_block_large_score` |

## The actual sampling experiment

Pairwise disjoint finite vertex sets $D_i$ partition a finite set $B$.
Each part has a prescribed integer sample size $s_i\le |D_i|$. The outcomes
are tuples $\tau=(\tau_i)_i$, with $\tau_i\subseteq D_i$, and their
weights are the product of the actual uniform fixed-size subset weights.
The resulting block is $T(\tau)=\bigcup_i\tau_i$.

The mean statements use exact equal fractions $s_i=p_0|D_i|$, and every
nonempty part selects at least two vertices. Empty parts are permitted and
force only $s_i=0$; their cardinalities are never cancelled. Exact integer
sizes and ratios are explicit hypotheses, to be supplied by the later
uniform parameter construction.

For the capped-row and full score theorems, $p_0>0$ and $\lambda>0$.
The lower-tail application additionally assumes $p_0\le1$.

In the intended application, the multigraph $G$ below is the **exterior
multigraph**, with its original edge copies. Thus $d_G(v)\le a$ is a bound
in that exterior graph, not a bound on the degree in the dense ambient
host. Parallel copies are retained, and loops are excluded by the model.
The whole vertex type need not be finite; the edge-copy type, partition
index type, and displayed vertex sets are finite.

## Exact pair laws and internal edge copies

Every vertex of $B$ is selected with probability $p_0$. Distinct vertices
in different parts have joint inclusion probability $p_0^2$. If they lie
in a common part of order $n$ with sample size $s$, the exact probability is

$$
\frac{s(s-1)}{n(n-1)}.
$$

Under $s\ge2$ and $s=p_0n$, this is at least $p_0^2/2$. The proof counts
uniform fixed-size samples containing the prescribed pair. The sample-size
condition is essential: a one-vertex sample cannot retain an internal edge
of its part.

Summing the inclusion indicators over the original edge-copy type gives

$$
\mathbb E\,|E_G(T)|\ge\frac{p_0^2}{2}|E_G(B)|.
$$

Every parallel copy is a separate summand. Independence between different
edge-inclusion events is unnecessary. The exact product-moment identities
prove independence only where it is used, for distinct vertex parts.

## Exceptional-row moments with coefficient one

Fix $x$, put $d_x=|E_G(x,B)|$, and set
$X_x(\tau)=|E_G(x,T(\tau))|$. Each part contributes the sum of the
parallel-copy weights at the selected vertices. The actual moments are

$$
\mathbb E X_x=p_0d_x,
\qquad \operatorname{Var}(X_x)\le a p_0d_x.
$$

The variance conclusion holds when every parallel-copy weight to a vertex
of $B$ is at most $a$. The exterior degree bound $d_G(v)\le a$ on $B$
implies this condition. No degree bound at $x$ itself is needed.

The proof retains coefficient one by applying the weighted
without-replacement variance estimate in each part. A coordinate section
of $X_x$ differs from its local weighted sum by a constant. Translation
invariance and finite-product variance tensorization then sum the local
bounds. The factor-four general swap estimate is unnecessary for this
additive statistic.

## Capped row means

Let $c_x=|E_G(x,U)|>0$ and suppose $d_x\le c_x/2$. The real cap
$\ell_x$ satisfies

$$
\frac{59}{64}\lambda c_x\le\ell_x\le\frac{15}{16}\lambda c_x,
\qquad a\le\frac{p_0c_x}{4096}.
$$

The lower cap bound proves positivity. With $\omega_1=64\lambda/p_0$,
the proved capped-mean inequality applied to the actual row moments gives

$$
\mathbb E\min\{\omega_1X_x,\ell_x\}\ge\frac74\lambda d_x.
$$

`capped_row_mean` derives both moments from the graph sample. It does not
assume either moment conclusion. The cap interval and original graph
inequalities remain explicit hypotheses. Natural-number caps are included
by coercion once their floor estimates have been established.

## The full score mean

Let $Z$ be disjoint from $B$. The actual correction pool $P$ contains the
internal copies in $B$ and the copies between $Z$ and $B$. Exact counting
gives $|P|=|E_G(B)|+\sum_{x\in Z}d_x$.

With $\omega_2=64\lambda/p_0^2$, the actual score is

$$
S(T)=\omega_2|E_G(T)|+
\sum_{x\in Z}\min\{\omega_1|E_G(x,T)|,\ell_x\}.
$$

Linearity, the internal-copy expectation, and the capped-row bounds yield

$$
\mathbb E S(T)\ge32\lambda|E_G(B)|+
\frac74\lambda\sum_{x\in Z}d_x
\ge\frac74\lambda|P|.
$$

`cappedScore_product_mean` proves this directly from the finite partition,
actual sample sizes, exterior degrees, row sizes, and cap bounds. Its
intermediate accounting theorem `cappedScore_mean_of_counts` exposes the
two contributions; the product-sampling theorem discharges those moment
premises. An empty correction pool is permitted in the mean theorem.

## Lower tail and an actual good block

For $0<p_0\le1$, one has $0\le\omega_1\le\omega_2$. The previously
proved product score variance therefore gives

$$
\operatorname{Var}S(T)\le8p_0\omega_2^2a|P|.
$$

When $|P|>0$, the gap from the mean lower bound to the target
$13\lambda|P|/8$ is $\lambda|P|/8$. Finite Chebyshev yields

$$
\Pr\!\left(S(T)<\frac{13}{8}\lambda|P|\right)
\le\frac{2^{21}a}{p_0^3|P|}.
$$

Both moments are derived inside `cappedScore_product_lower_tail`. If
$2^{21}a<p_0^3|P|$, `exists_block_large_score` produces an actual tuple
with $|\tau_i|=s_i$ for every part and $S(T)\ge13\lambda|P|/8$.

The existence proof selects an outcome of positive weight. The ambient
finite outcome type also contains tuples with the wrong component sizes,
but those tuples have weight zero. `sample_card_of_weight_ne_zero` proves
that every selected component has its prescribed size.

## Remaining work

The standalone score-mean calculation and its graph-specific lower tail
are complete. The next finite task is to establish palette-row,
correction-pool, preferred-edge, and score conditions simultaneously and
to make their combined failure budget less than one. The allowed-color
fraction must retain its actual denominator before comparison with
$\lambda=s/k$.

Fine parts, coarse unions, integer sizes, cap floor bounds, boundary
exclusions, and residual reserves still require uniform choices from the
original robust-core assumptions. The regularity setup, special path
systems, robust absorber, and final factorization remain further tasks.
A successful audit of these finite results does not close those dependencies.
