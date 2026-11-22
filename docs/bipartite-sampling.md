> **Historical continuation notes.** Coverage and status statements below describe the earlier checkpoint documented here. The current inventory is **47 of 69**, including complete Lemmas **4.2**, **4.14**, and **4.15**. The one-core branch of 4.6 is complete; its two-core branch and the main theorem remain incomplete. See [the current scope](next-verification-target.md) and [reconstruction record](checkpoint-reconstruction.md).

# Finite sampling for bipartite palettes and correction scores

This continuation starts from verified checkpoint
`9e07dbec01094434779b0d91b8779cf069089bea`. It proves finite probability
ingredients for the palettes and block capacities in Section 6 of
`Four_Robust_Component_Cases_2026-11-21.tex`, especially
`old:palettes`, `old:fac:score`, and `old:fac:swap-variance`.

The distributions are defined on actual finite subsets, permutations,
and tuples of subsets. The palette application counts copies of the
original multigraph with their original color labels. The weighted
swap bound is proved from pointwise changes under exchanges; a
concentration or variance bound is not an assumption of that theorem.

These results supply probability tools and graph adapters for the
previous [two-family constructor](bipartite-two-families.md). The full
simultaneous quantitative input to that constructor remains to be
assembled. The current completed numbered inventory is **45 of 69**, with
24 remaining, after the [complete proof of Lemma 4.15](four-odd-decomposition.md).
Theorem 6.1, Proposition 6.2, Theorem 6.3, and their dependent
factorization assertions remain incomplete.

## Sources and principal interfaces

| Component | Source and principal declarations |
| --- | --- |
| Disjoint samples from one permutation, with exact individual laws | [PermutationSampling.lean](../Overfull/Probability/PermutationSampling.lean): `probability_sample_eq`, `expectation_sample`, `exists_disjoint_samples` |
| Weighted sample moments and nonlinear product variance | [WeightedSampling.lean](../Overfull/Probability/WeightedSampling.lean): `mean_weightedSum`, `variance_weightedSum_le`, `variance_weightedSum_le_max_mul_mean`, `variance_pi_le` |
| Capped means and numerical lower-tail estimates | [CappedMean.lean](../Overfull/Probability/CappedMean.lean): `capped_mean_lower_of_variance`, `correction_capped_mean_lower`, `correction_score_lower_tail` |
| Weighted variance from actual exchanges | [SwapVariance.lean](../Overfull/Probability/SwapVariance.lean): `weighted_slice_variance`, `variance_of_swap`, `variance_product_of_swap`, `variance_product_of_swap_bounded` |
| Sampling actual allowed colors and counting original copies | [PaletteSampling.lean](../Overfull/BipartiteFactorization/PaletteSampling.lean): `mean_poolDemand`, `variance_poolDemand_le`, `exists_disjoint_allowed_palettes` |
| Actual graph-score exchanges and single-block variance | [BlockSampling.lean](../Overfull/BipartiteFactorization/BlockSampling.lean): `cappedScore_swap_le`, `vertexWeight_le`, `sum_vertexWeight_le`, `variance_cappedScore_le` |
| Actual graph-score variance for independent sampled parts | [BlockProductSampling.lean](../Overfull/BipartiteFactorization/BlockProductSampling.lean): `sampledBlock_update_swap`, `cappedScore_coordinate_swap`, `cappedScore_product_variance` |

Probability definitions and the earlier membership and containment
bounds are in
[Hypergeometric.lean](../Overfull/Probability/Hypergeometric.lean).
The graph-specific block adapters retain the original vertex and
edge-copy identities throughout.

## 1. Actual uniform laws, including empty and full samples

For a finite population `E` of cardinality `n`,
`Hypergeometric.weight s T` assigns weight

\[
\frac{1}{\binom ns}
\]

to each actual subset `T` of size `s`, and zero to all other subsets.
The condition `s≤n` proves that these nonnegative weights sum to one.
The weighted moment and swap theorems all retain this condition.

The sample of size zero is the deterministic empty set; the sample of
size `n` is the deterministic whole population. Both variances are
proved to be zero for every statistic. An empty population forces
`s=0` and is covered by the same statements. Fractions such as `s/n`
use Lean's real division, so the empty case has value zero; the proof
does not cancel a zero population size.

`FiniteProbability.mean p f` and `variance p f` are the finite sums

\[
\mathbb E_p f=\sum_\omega p(\omega)f(\omega),\qquad
\operatorname{Var}_p f
=\sum_\omega p(\omega)\bigl(f(\omega)-\mathbb E_p f\bigr)^2.
\]

Normalization is an explicit hypothesis where it is needed. For
example, the second-moment identity uses `∑ω p ω=1`, and variance
nonnegativity uses nonnegative weights. The finite Chebyshev estimate
is also proved directly: for `t>0`,

\[
\Pr_p\{|f-\mathbb E_p f|\ge t\}
\le\frac{\operatorname{Var}_p f}{t^2}.
\]

That finite weighted inequality itself needs nonnegative weights but
does not need normalization; its probability applications use the
normalized laws above.

## 2. Disjoint samples with exact uniform marginals

`PermutationSampling.sample S σ` is the image of an actual position
set `S⊆E` under a permutation `σ` of `E`. Every permutation preserves
its size, and the images of disjoint position sets remain disjoint.
The permutation law assigns weight `1/|Perm(E)|` to every permutation.
It is normalized even when `E` is empty, because the identity
permutation always exists.

For every target subset `T` with `|T|=|S|`, the proof first constructs
a permutation sending `S` to `T`. Translation by that permutation
gives a bijection between the corresponding fibers. Partitioning all
permutations by their image of `S` gives

\[
|\operatorname{Perm}(E)|
=\binom n{|S|}\,|\{\sigma:\sigma(S)=S\}|.
\]

Consequently the image of `S` has exactly the uniform `|S|`-subset
law. `expectation_sample` transfers every real-valued statistic, and
`probability_sample` transfers every event, to that law.

For arbitrary prescribed sample sizes `n_i` with `∑i n_i≤n`,
`exists_positions` embeds the disjoint union of `Fin (n_i)` into `E`
and obtains actual disjoint position sets. Suppose the marginal
failure bounds satisfy

\[
\Pr\{\operatorname{bad}_i(T_i)\}\le\varepsilon_i,
\qquad \sum_i\varepsilon_i<1.
\]

The union bound on the single permutation experiment then constructs
pairwise disjoint samples of the requested sizes for which all the
events are good. The samples need not be independent. The numerical
marginal estimates and their total budget remain explicit inputs to
`exists_disjoint_samples`; the result does not presume that those
estimates have already been established for every manuscript event.

## 3. Weighted sample expectation and variance

For weights `w:E→ℝ`, define the actual sampled sum

\[
X(T)=\sum_{e\in T}w(e),\qquad p=\frac{s}{n}.
\]

`mean_weightedSum` proves, for arbitrary real weights,

\[
\mathbb E X=p\sum_e w(e).
\]

For nonnegative weights, `variance_weightedSum_le` proves

\[
\operatorname{Var}X\le p\sum_e w(e)^2.
\]

If also `w(e)≤M` for every member of the population, then
`variance_weightedSum_le_max_mul_mean` gives

\[
\operatorname{Var}X\le M\mathbb E X.
\]

The proof expands `X` into actual membership indicators and `X²`
into pairs of indicators. Each member has inclusion probability `p`.
Distinct members have simultaneous inclusion probability at most
`p²`, from the proved fixed-size containment law. Nonnegative weights
allow these pair inequalities to be summed. Subtracting the square
of the mean leaves the stated variance bound. The final inequality
uses `w(e)²≤M w(e)`. Signed weights are allowed for the expectation
identity, but the displayed variance bound requires nonnegative
weights.

## 4. The full weighted swap-variance proof

Let `S` be a finite ground set of size `n`, let `0≤s≤n`, and let
`ω(x)≥0` on `S`. Suppose a statistic `f` satisfies

\[
\left|f\bigl((T\setminus\{x\})\cup\{y\}\bigr)-f(T)\right|
\le\omega(x)+\omega(y)
\]

whenever `T⊆S`, `|T|=s`, `x∈T`, and `y∈S\T`.
`SwapVariance.weighted_slice_variance` proves

\[
\operatorname{Var}f(T)\le4\frac{s}{n}\sum_{x\in S}\omega(x)^2.
\]

The proof is finite induction on the ground set. It supplies an
alternative to the continuous-priority argument in the manuscript.
There is no supplied Efron–Stein inequality or supplied concentration
estimate for the statistic.

The endpoint cases `s=0,n` are deterministic. In the remaining cases,
choose a member `x` of maximum weight and write `R=S\{x}`. A uniform
`s`-subset contains `x` with probability `p=s/n`. Conditional on that
event, the other members form a uniform `(s−1)`-subset of `R`;
conditional on its complement, the sample is a uniform `s`-subset
of `R`. Exact finite double counting proves these conditional means
and the identity

\[
\operatorname{Var}f
=pV_1+(1-p)V_0+p(1-p)(\mu_1-\mu_0)^2.
\]

The two conditional statistics inherit the same exchange bounds on
`R`. To compare their means, sample a uniform `(s−1)`-subset `T⊆R`
and then a uniform member `y∈R\T`. The larger set `T∪{y}` is uniform
on the `s`-subsets of `R`: each larger subset has exactly `s`
preimages under this construction. The exchange hypothesis and the
choice of `x` give

\[
|f(T\cup\{x\})-f(T\cup\{y\})|
\le\omega(x)+\omega(y)\le2\omega(x),
\]

so `|μ₁−μ₀|≤2ω(x)`. The induction coefficients for the remaining
weights combine exactly as

\[
p\frac{s-1}{n-1}+(1-p)\frac{s}{n-1}=\frac{s}{n}.
\]

The last variance term is at most `4pω(x)²`. These two bounds complete
the induction. `hypergeometric_variance_eq` identifies this finite
slice variance with the same actual uniform-subset law used by the
other sampling results; `Hypergeometric.variance_of_swap` is the
public population-type version.

### Independent parts and nonlinear statistics

`FiniteProbability.variance_prod` proves the exact law of total
variance for two independent finite coordinates. Finite Jensen gives
the bound on the variance of a conditional mean. Iterating these
results proves `variance_pi_le` for arbitrary finite dependent
products of normalized nonnegative coordinate laws.

Its input is a bound `b_i` on the variance of every section obtained
by varying coordinate `i` and fixing all other coordinates. Its
conclusion is `Var f≤∑i b_i`. The statistic may depend on all parts
nonlinearly; additivity across parts is not required.

Applying the single-slice swap theorem to these sections gives

\[
\operatorname{Var}f\le
\sum_i4\frac{s_i}{n_i}\sum_{x\in E_i}\omega_i(x)^2
\]

for independent uniform samples in the finite parts `E_i`. The API
requires the pointwise exchange bound for every fixed configuration
of the other parts and every valid sample in the varying part.
Empty parts force their sample size to zero, and an empty index set
has a single empty configuration; both are covered.

If every fraction `s_i/n_i≤p`, all weights are at most `W`, and their
total is at most `M`, then `variance_product_of_swap_bounded` gives

\[
\operatorname{Var}f\le4pWM.
\]

Here `p,W≥0`; the proof sums the pointwise inequality
`ω_i(x)²≤Wω_i(x)` and uses the actual product law.

## 5. Capped means and the manuscript constants

Let `X≥0`, `μ=E X`, and suppose `Var X≤aμ`, where `a≥0`. For
`ω>0` and `ℓ>0`, `capped_mean_lower_of_variance` proves

\[
\mathbb E\min\{\omega X,\ell\}
\ge\frac{\ell\mu}{\ell/\omega+\mu+a}.
\]

The pointwise lower bound is
`ℓX/(ℓ/ω+X)≤min(ωX,ℓ)`. Finite Cauchy–Schwarz gives

\[
\mu^2\le
\mathbb E\frac{X}{q+X}\;\mathbb E\bigl[X(q+X)\bigr],
\qquad q=\ell/\omega.
\]

The variance bound controls the second factor by `μ(q+μ+a)`.
When `μ>0` cancellation gives the claimed result; when `μ=0`,
nonnegativity proves it directly. A separate theorem accepts the
second-moment bound itself and does not require normalization.

`correction_capped_mean_lower` proves the specific bound

\[
\mathbb E\min\{\omega X,\ell\}\ge\frac74\lambda d
\]

under the explicit premises

\[
\begin{gathered}
\mu=p_0d,\quad \operatorname{Var}X\le a\mu,\quad
0\le d\le c/2,\quad p_0,c,\omega,\ell>0,\quad \lambda,a\ge0,\\
\ell\ge\frac{59}{64}\lambda c,\qquad
\frac\ell\omega\le\frac{15}{1024}p_0c,\qquad
a\le\frac{p_0c}{4096}.
\end{gathered}
\]

These imply `ℓ/ω+p₀d+a≤(2109/4096)p₀c`, which supplies the numerical
margin. The theorem does not assume that natural-number floors already
satisfy the cap premises; those arithmetic conditions still need to
be derived in the manuscript instantiation.

`correction_score_lower_tail` proves the numerical Chebyshev step.
For `p₀,λ,M>0`, if

\[
\mathbb E X\ge\frac74\lambda M,
\qquad
\operatorname{Var}X
\le8p_0\left(\frac{64\lambda}{p_0^2}\right)^2aM,
\]

then

\[
\Pr\left\{X<\frac{13}{8}\lambda M\right\}
\le\frac{2^{21}a}{p_0^3M}.
\]

The gap between the mean lower bound and the threshold is `λM/8`.
Squaring that gap and dividing the supplied variance budget gives
the constant `2²¹` exactly. The statistic need not be nonnegative in
this lower-tail lemma. Its mean and variance premises are explicit;
the theorem records their numerical consequence and does not
construct the graph-specific score mean.

## 6. Actual allowed palettes and original pool copies

Fix an original proper `Fin k` edge coloring `c`, an actual allowed
set `C⊆Fin k`, and a pool `P` of original edge copies. The random
population in `PaletteSampling` is the subtype of labels in `C`.
Sampling `s` of those labels and applying `liftPalette` produces an
actual palette of the original labels, contained in `C` and of the
same size. Lifting preserves disjointness.

For an allowed label `i`, define

\[
w_i=|\{e\in P:c(e)=i\}|.
\]

`poolDemand_eq_weightedSum` proves that the weighted sample sum is
exactly the actual intersection count

\[
e_{I,P}=|\{e:c(e)\in I\}\cap P|.
\]

In particular,

\[
\mathbb E e_{I,P}
=\frac{s}{|C|}|\{e:c(e)\in C\}\cap P|
\le\frac{s}{|C|}|P|.
\]

If every allowed color has pool weight at most `M`, its variance is
at most `M E e_{I,P}`; for `M≥0` it is therefore at most
`M(s/|C|)|P|`. The denominator is the number of allowed colors.
Obtaining the manuscript's bound in terms of `λ=s/k`, such as the
factor `33/32`, requires the previously proved lower bound on `|C|`
and the appropriate numerical comparison. The palette adapter does
not replace `|C|` by `k` silently.

`probability_permuted_poolDemand` transfers every event of this actual
copy count to a uniform permutation of the allowed population.
`exists_disjoint_allowed_palettes` then constructs simultaneously
good, pairwise disjoint palettes of original labels whenever their
total size fits in `C` and the explicit marginal failure bounds sum
to less than one.

The pool `P` is arbitrary, so this identity applies to a correction
pool or to an exceptional-to-core row. All counts retain distinct
parallel copies. The necessary bounds on a color's pool weight,
active row sizes, and the final collection of failure probabilities
are additional data to derive from the preceding graph preparation.

## 7. The actual graph score and its variance

Let `G` be the actual exterior multigraph, let `B` be a core side,
and let `Z` be the exceptional class whose correction copies enter
`B`. Define

\[
\begin{aligned}
S(T)&=\omega_2|E(G[T])|
 +\sum_{x\in Z}\min\{\omega_1|E_G(x,T)|,\ell_x\},\\
w(v)&=\omega_2d_{G[B]}(v)+\omega_1|E_G(v,Z)|.
\end{aligned}
\]

These are `BlockSampling.cappedScore` and `vertexWeight`. Every
incidence is a count of actual original copies, including parallel
copies. The bound on `d_G(v)` below is a bound in this exterior
multigraph, after removing the embedded dense core.

Adding a vertex `v` to `T⊆B` introduces only internal copies incident
with `v` and copies from `v` to `Z`. Capping a row cannot increase its
insertion cost. Summing the row changes over their actual other
endpoints proves

\[
0\le S(T\cup\{v\})-S(T)\le w(v).
\]

Applying this twice around `T\setminus\{u\}` proves

\[
|S((T\setminus\{u\})\cup\{v\})-S(T)|\le w(u)+w(v).
\]

This exchange bound needs only nonnegative `ω₁,ω₂`; the real caps
`ℓ_x` may be arbitrary. It does not require disjointness of `B,Z`.

For the quantitative weight budget, assume `B∩Z=∅`,
`0≤ω₁≤ω₂`, `a≥0`, and `d_G(v)≤a` for every `v∈B`.
The incidence sets into `B` and into `Z` are disjoint, so

\[
w(v)\le\omega_2a.
\]

Counting internal copies twice and crossing copies once gives

\[
\sum_{v\in B}w(v)
=2\omega_2|E(G[B])|+\omega_1|E_G(Z,B)|
\le2\omega_2|P|,
\quad
P=E(G[B])\cup E_G(Z,B).
\]

`P` is precisely `correctionPool G B Z`. Thus, for a uniform
`s`-subset `T⊆B` with `s≤|B|`, `variance_cappedScore_le` proves

\[
\operatorname{Var}S(T)
\le8\frac{s}{|B|}\omega_2^2a|P|.
\]

The theorem constructs the required pointwise exchange estimate from
the graph. It assumes neither that estimate nor a variance bound as
an external input. It requires no simplicity, positive side order,
or upper bound `ω₂≤1`; the latter belongs to the later capacity
application. The zero and full sample sizes are included.

### Unions of actual samples from disjoint parts

`BlockProductSampling.sampledBlock D τ` is the actual union of the
sampled original vertices from a finite family of parts `D_i⊆B`.
Each coordinate `τ_i` is a finite subset of the subtype belonging to
`D_i`. Assume the parts are pairwise disjoint, their sample sizes
satisfy `s_i≤|D_i|`, and

\[
\frac{s_i}{|D_i|}\le p_0\quad\text{for every }i,\qquad p_0\ge0.
\]

The distribution is the actual product of the normalized uniform
`s_i`-subset laws. `sampledBlock_update_swap` proves that exchanging
two members in one coordinate is exactly the corresponding exchange
of original vertices in the union. Thus the graph-score exchange
bound applies to every coordinate section, even when the fixed
configuration is outside the supported sample sizes.

Disjointness also proves that each original vertex weight is counted
at most once across the parts. The already proved graph maximum and
total weight bounds then supply every hypothesis of the nonlinear
product variance theorem. `cappedScore_product_variance` concludes

\[
\operatorname{Var}\,S\!\left(\bigcup_i\tau_i\right)
\le8p_0\omega_2^2a|P|.
\]

Its remaining graph hypotheses are exactly those for the quantitative
single-block bound: `B∩Z=∅`, `0≤ω₁≤ω₂`, `a≥0`, and original degrees
at most `a` on `B`. The caps may again be arbitrary real numbers.
The parts need only be contained in `B`; covering all of `B` is
unnecessary for this upper variance bound. Equal sampling fractions,
positive part orders, and `ω₂≤1` are also unnecessary.

This proves the variance budget for the actual graph score under
independent sampling in disjoint parts. The subsequent
[score-mean continuation](bipartite-score-mean.md) proves the actual mean,
graph-specific lower tail, and supported good-block existence. The
complete simultaneous numerical sampling conditions remain open.

## 8. Remaining simultaneous composition

The deterministic selection and coloring results already construct
both localized exterior families and the coloring of their exact
remaining graph once the finite supplies hold. The next composition
must derive those supplies simultaneously from the actual robust-core
input. In particular it must:

- Realize the required fine labels and coarse unions inside the
  prescribed partition, with their integer sizes and sampling ratios.
- Derive all active palette-row bounds, correction-pool demand
  bounds, preferred-edge supplies, and score lower tails, and prove
  that the combined failure budget is strictly below one.
- Choose the uniform parameter hierarchy and large-order thresholds
  so that floor errors, palette sizes, positive caps, fine-to-coarse
  reserves, and the residual coloring inequalities all hold.
- Construct the boundary exclusions with the local deletion budgets
  used by the capacity and two-family interfaces.

The subsequent regularity setup, special path systems, robust
absorber, final factorization, and reconstruction remain further
obligations. The finite probability and graph-counting lemmas in this
continuation do not change the completed numbered assertion count.

The source and numbered-statement provenance remain as described in
[bipartite-prerequisites.md](bipartite-prerequisites.md) and
`manuscript-source.json`. Final verification results and source hashes
belong to the checkpoint's verification record.
