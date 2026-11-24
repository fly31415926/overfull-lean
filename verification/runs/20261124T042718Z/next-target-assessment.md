# Next proof targets after the single-core closure

This is an exploratory mathematical and source-dependency assessment made
while the complete audit of the frozen candidate was running. It contains
**no new Lean theorem and no additional numbered closure**. The verified
candidate's mathematical sources and verification controls were not changed.
The finite diagnostics under `analysis/` are separate from the Lean audit.

## Remaining ordinary and bipartite routes

The locally inspected later manuscript reproduces the pinned individual
statements in Section 3. This comparison concerns those statement blocks,
not identity of the two whole manuscripts.

| Target | What the present continuation supplies | Remaining source-route dependency |
| --- | --- | --- |
| Corollary 3.2: exclude ordinary outcomes `(1,0)`, `(2,0)`, `(3,0)` | Coloring endpoints for one and two ordinary cores | Actual partition/core extraction and uniform assembly; the three-core case additionally needs nonregular three-core coloring |
| Theorem 1.2: two or three ordinary cores | The full nonregular two-core wrapper | The nonregular three-core branch, obtained in the source by adding a fourth auxiliary core |
| Full Theorem 4.17 | Three-core regular factorization with a small linear exceptional set | The other four-core terminal parity cases and their uniform composition |
| Corollary 3.4: mixed outcome `(1,1)` | One-/two-core auxiliary transport machinery | The source route needs nonregular three-core coloring and dense bipartite extension |
| Theorem 3.5: almost spanning bipartite core | Two-core comparison coloring after the empty-ordinary-core construction | Full dense bipartite extension, Theorem 5.1 |
| Corollaries 3.6 and 3.7 | Existing balanced-core and parameter infrastructure | Their preceding critical exclusions, with a common parameter choice |

The pinned Corollary 3.2 hash is
`64b4da9bb77675dc01c8895e7b9fed92dd289050eae127f581b2aa1be8d1c747`.
It excludes all three ordinary outcomes together. The current regular
three-core theorem cannot be applied to an arbitrary nonregular three-core
host. The source adds one auxiliary core: two original cores become three
regular cores, while three original cores become four. The latter regular
branch is not yet available.

The source extraction for an ordinary part obtains a core of order at least
`Δ-3ρn+1 ≥ n/4`, degree at least `Δ-3ρn`, and total exceptional set of size
at most `4ρn`. With `a=3ρn`, the combined budget is at most `8ρn` for large
enough order. Surviving robust parameters are `(ν/2,2τ₀)`. The fixed range
`τ₀ ≤ 1/8192000` suffices for both currently available coloring endpoints.
The actual induced-graph transports and uniform dyadic parameter assembly
still need proofs. The source chooses tolerances at every dyadic scale before
the partition returns its lower bound, then takes a finite maximum of the
needed order thresholds.

The critical average-degree input is a **separate absent formal dependency**.
The source explicitly invokes Cao--Chen Theorem 3 in Proposition 2.24 to obtain
the needed small deficiency for sufficiently large critical graphs. The
current `Overfull.RobustPartition.exists_uniform_partition_of_average_degree`
retains the actual average-degree estimate as a hypothesis. This assessment
does not identify a mathematical gap in that citation, and does not claim
to have formalized the cited theorem.

Excluding outcomes from an already supplied actual small-deficiency partition
is a conditional target and can be pursued without constructing that partition
for every critical graph. A complete statement constructing the critical
partition needs the missing formal average-degree input.

Theorem 3.5 is a distinct route: its source supplies an almost spanning dense
balanced bipartite core, so constructing a critical robust partition is not
required there. The empty-ordinary-core comparison uses only two ordinary
cores after completion and replacement. The new two-core theorem supplies its
comparison coloring, but it does not color the original bipartite core;
Theorem 5.1 still supplies that extension. Its pinned statement hash is
`59ed7a06b9e3942cf1229f57310dab66368e2883b757f816982ca46988a5cb3b`.

## A sound next reduction for four-label compatible circuits

The exact-degree-four theorem is complete. A useful next formalization is
degree-two suppression, giving an arbitrary admissible even four-label graph
with **some label of degree zero or two**, without bounding the other degrees.

For degree two with distinct neighbours, replace the actual path `a-v-b` by
one virtual copy `ab`, inheriting the old endpoint classes. To prove a tested
class-cut inequality in the reduced graph, place `v` on the side that makes
its corresponding original class-cut contribution identical. If `a,b` are
on the same side, use that side. If they are on opposite sides, place `v`
opposite the endpoint whose class is being tested. For another tested vertex,
either side works. Both cut counts then agree exactly.

The remaining graph has three labels and can use the existing complete
three-label theorem. The virtual-edge circuit lifts by restoring the two
original copies. The removed label cannot already occur in that circuit,
and its two classes differ by singleton-cut admissibility.

If the two neighbours coincide, the two copies form a compatible parallel
pair at both endpoints. Remove the pair and the degree-two label; place that
label with its neighbour in each cut comparison. Again use the three-label
theorem and restore the original pair.

Once formalized, this reduction and the current four-regular theorem would
cover every admissible even four-label graph of maximum degree at most four.
**This suppression theorem is a proposed next result, not part of the current
verified declaration inventory.**

## Exact obstruction to greedy deletion

For an original class-cut of size `a`, total cut size `δ`, and a removed
subgraph with corresponding sizes `b,d`, the existing exact deletion criterion
in `CompatibleCircuits/Deletion.lean` is

`2a + d ≤ δ + 2b`.

Writing the original slack as `s=δ-2a`, the residual slack is `s-d+2b`.
For a compatible circuit on four labels, `b≤1`, and `d` is zero, two or four.

| Original slack | Required condition for safe removal |
| --- | --- |
| Zero | The circuit misses the cut, or crosses twice and meets the tight class |
| Two | If the circuit crosses four times, it must meet the class |
| At least four | Automatic |

A parallel pair or triangle needs the tight-cut conditions. A Hamiltonian
four-cycle also has one alternating two-versus-two cut crossed four times.
That cut must have no tight class, and the cycle must meet every relevant
slack-two class there. Positive tight constraints number at most four per cut;
relevant slack-two constraints number at most eight. Only three pair cuts can
be alternating cuts.

A concrete counterexample uses bundle counts
`01=02=03=2`, `12=13=23=1`, giving degrees `(6,4,4,4)`. At label zero,
put one `01` and one `03` copy in class `A`; all other classes are singletons.
The original graph is admissible and has no positive tight class-cut
constraint. The cycle `0-1-2-3-0` using the other `01` and `03` copies is
compatible, but crosses `{0,2}` four times and misses `A`. Original slack
is two; the residual cut has size two and still contains both `A` copies.

## A bounded-layer target, and what cannot be assumed

A sufficient unproved extraction target for the remaining high-degree case
is an actual nonempty `D⊆C` such that every degree in `D` is in `{0,2,4}`,
both `D` and `C\D` are admissible, and `C` is admissible and even with all
degrees at least four and at least one degree at least six. The bounded layer
has at most eight copies; the original graph has at least nine. The proposed
small-degree theorem partitions `D`, and induction partitions its complement.

This is a substantive selection problem. Merely stating the extraction lemma,
or assuming a compatible partition as an input, does not advance the proof.
The finite diagnostics rule out several stronger shortcuts:

- A compatible split can preserve every local half-degree bound while
  destroying a tight two-versus-two cut inequality.
- Even an admissibility-preserving split can yield a compatible reduced
  circuit that cannot be lifted part by part: it can already visit the split
  label. Degree-two suppression avoids this problem by removing that label.
- A spanning four-regular layer need not exist. Degrees `(6,4,4,4)` would
  leave impossible residual degrees `(2,0,0,0)` after such a layer.
- Even an admissible four-regular graph need not have a compatible spanning
  two-factor. A concrete `(2,1,1)` opposite-bundle template has ten spanning
  two-factors and no compatible one, but has a compatible partition into two
  triangles and a parallel pair.
- Admissibility of a chosen layer alone does not imply admissibility of its
  complement. The exact residual inequalities must be proved.

The next implementation order is therefore degree-zero/two reduction, the
maximum-degree-four consequence, and then a genuine bounded-layer extraction
or safe-circuit selection proof. The unrestricted four-label theorem remains
open until that last construction is proved.
