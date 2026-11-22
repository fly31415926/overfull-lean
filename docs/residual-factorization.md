# Coupled absorber parameters and the exact oriented remainder

**The completed numbered-assertion inventory remains 45 of 69.** This
continuation completes the numerical parameter construction and the final
packing-to-remainder stage of Section 6. Theorem 6.1, Proposition 6.2,
the robust absorber of Theorem 6.3, and the dependent Lemmas 4.2 and 4.14
are still incomplete. The main theorem remains unverified.

The new public theorem is
`Overfull.BipartiteFactorization.exists_uniform_reserved_remainder` in
[ReservedRemainder.lean](../Overfull/BipartiteFactorization/ReservedRemainder.lean).
It starts with the original regular host and an explicit set of reserved
original copies, derives the entire prepared graph, completes every color
of its remaining exterior, and constructs an actual regular oriented
remainder. It does not assume the internal matching family or the existence
of that remainder.

The construction has eight proof modules. Their exact source hashes and
public proof mappings appear in [residual-factorization-source.json](residual-factorization-source.json).
The complete audited declaration mapping, including private and generated
proofs, is [residual-factorization-declarations.json](../verification/residual-factorization-declarations.json).
The [semantic review](residual-factorization-semantic-review.md) checks the
statement correspondence and limits of the construction.

## 1. The public graph theorem

Fix

\[
0<\alpha\le1,\qquad 0<\gamma<1,\qquad
0<\nu\le\tau<\alpha/32.
\]

The theorem chooses positive \(\varepsilon,\theta,\sigma\), with
\(\sigma\le\tau\), and an order threshold before the graph and every
subsequent choice of reserved copies and colors.

Let \(R\) be a finite loopless \(k\)-regular multigraph. Its embedded
simple core \(H\) is bipartite with equal sides of order \(m\), robust
\((\nu,\tau)\), and has minimum degree at least \(k-a\), where
\(0\le a\le\varepsilon m\) and \(k\ge\alpha m\).

Let \(T\) be an explicit set of original edge copies, and let \(r,s\)
be nonnegative integers satisfying

\[
r\le s,\qquad 4s\le k,\qquad \gamma m\le2r,
\qquad 2(s-r)\le\nu m/2.
\]

The actual degrees in the reserved graph are required to be \(2(s-r)\)
at every core vertex and \(2s\) at every exterior vertex. Write
\(q=k-2s\). The theorem constructs the surviving embedded core \(H_0\)
inside \(R-T\). Its complement is the actual remaining exterior.
The coloring input is a proper \(q\)-coloring of that complement, with
equal core footprints on both sides and with each whole core footprint
of size at most \(2ma/q+4\).

From these inputs the theorem constructs:

- Exactly \(q\) pairwise edge-disjoint perfect matchings of \(R-T\).
- Exact retention of the supplied remaining-exterior labels in those
  completed classes.
- The actual residual graph after deleting their original edge copies.
- An embedded simple bipartite core containing every surviving copy;
  each exterior vertex is isolated in this residual.
- Degree exactly \(2r\) at every residual core vertex, with robust
  parameters \((\theta,\sigma)\).
- An actual orientation of every residual core edge, exactly once,
  with indegree and outdegree \(r\) at every core vertex.

The supplied reserved set and compressed exterior coloring are the stage
inputs that the special-factor and absorber construction must eventually
produce. Their existence from the original hypotheses of Theorem 6.1 is
not asserted by this interface.

## 2. Why the residual degree is exact

[ReservedCore.lean](../Overfull/BipartiteFactorization/ReservedCore.lean)
retains an embedded core edge precisely when its specified original copy
lies outside \(T\). It identifies the new exterior with the surviving
old exterior copies, preserving parallel-copy identity and both endpoints.
Reservation cannot increase its degree at a core vertex.

For each core vertex \(v\), the actual degree identity is

\[
d_{H_0}(v)+d_{\mathrm{ext},0}(v)
=k-2(s-r)=q+2r.
\]

The exterior vertices have degree exactly \(q\) in \(R-T\). The retained
core has minimum degree at least \(q+2r-a\), and its robust parameter
is at least \(\nu/2\). Both properties follow from the actual copy
deletion and its degree budget.

For each exterior color, its internal completion avoids precisely the
core vertices already covered by that color. Therefore the \(q\) completed
classes remove exactly \(q\) incidences at every ambient vertex. At a core
vertex the internally used degree is exactly
\(q-d_{\mathrm{ext},0}(v)\), leaving \(2r\) core incidences. At an exterior
vertex all \(q\) incidences are used.

[ComplementCompletion.lean](../Overfull/BipartiteFactorization/ComplementCompletion.lean)
proves these facts on actual original copies. Its
`remainingCore_exhausts` theorem proves that the embedded residual core
contains every surviving ambient edge copy. Thus degree accounting does
not conceal a parallel edge or an exceptional incidence.

## 3. Uniform packing with a small positive reserve

[ResidualPacking.lean](../Overfull/BipartiteFactorization/ResidualPacking.lean)
proves `pack_fixed_bipartite_forbidden_sets`. For any fixed positive
reserve fraction \(\gamma\), it derives the smaller robust range needed
by the already proved adaptive packing theorem. It accepts any packing
length at most \(\lfloor d-\gamma m\rfloor\), with balanced forbidden
footprints of small size and total incidence load.

The proof pads the finite input family by empty sets, proves that this
preserves its total incidence count, and then restricts the actual
adaptive packing to the requested number of rounds. The unused graph
remains robust after every subfamily, including each prefix.

[CompletionTransport.lean](../Overfull/BipartiteFactorization/CompletionTransport.lean)
transports the side-indexed matchings to the original embedded core.
It identifies the footprint load with the actual complementary degree,
and identifies the complete unused graphs in both indexings.

[UniformRemainder.lean](../Overfull/BipartiteFactorization/UniformRemainder.lean)
chooses an input tolerance at most \(\varepsilon_{\rm pack}\alpha/8\)
and an order threshold with \(\varepsilon_{\rm pack}m\ge8\). The density
bound supplies \(q>0\). It then derives every degree, footprint, load,
and horizon inequality needed for packing. In particular,
\(\gamma m\le2r\) gives
\(q\le\lfloor q+2r-\gamma m\rfloor\).

## 4. An explicit balanced orientation

[ResidualOrientation.lean](../Overfull/BipartiteFactorization/ResidualOrientation.lean)
proves `exists_regular_bipartite_orientation` for every actual simple
bipartite \(2r\)-regular graph, including \(r=0\).

The checked König theorem gives a \(2r\)-coloring. A chosen palette of
exactly \(r\) colors and its complement define two disjoint spanning
\(r\)-regular subgraphs. Direct the first from the left side to the right
and the second in the opposite direction. The explicit arc relation has
one direction of every original edge, no pair of opposite arcs, and exact
incoming and outgoing neighbor counts \(r\). This supplies the source's
balanced orientation by a different proved construction.

## 5. Coupled integer parameters

[AbsorberParameters.lean](../Overfull/BipartiteFactorization/AbsorberParameters.lean)
constructs the numerical parameters together. In this paragraph \(Q\)
denotes the manuscript's number of fine palettes, to distinguish it from
the remaining-color count above. The construction proves the exact
identities

\[
\begin{aligned}
r_2&=96\ell' g^2tr, & Qr_3&=rft,\\
r_\diamond+(Q-1)r_3&=r_1+r_2+r,
&s&=Qr_3+7r_\diamond,\\
k_1&=2r_3, & k_2&=2r_\diamond.
\end{aligned}
\]

It proves that the natural subtraction defining \(r_\diamond\) is
nontruncated, that both palettes are positive and even, and that

\[
Qk_1+7k_2=2s,\qquad
r_1+r_2+r_3+6r_\diamond=s-r.
\]

It also constructs the uniform positive palette fractions, verifies the
source palette inequalities with their constants, proves the required
integer divisibilities and cluster-order arithmetic, and proves
\(rt^2\le m_{\rm cl}\) and
\(100(r_2+r+Qr_3)\le r_1\).

The main ratio is fixed before the reduced cluster count. The smaller
ratio and thresholds are then chosen before the actual cluster order and
ambient degree. A finite-family result gives a common positive palette
lower bound and order threshold across the bounded possible cluster counts.
The full geometric regularity hierarchy and an actual bi-setup are separate
obligations.

## Remaining full-assertion obligation

Theorem 6.1 still requires an actual spanning bi-setup, its compatible
special path systems and factors, and a proved robust absorber or a
sufficient replacement. These must construct the reserved set and the
compressed balanced exterior coloring used above, then turn the final
Hamilton decompositions into perfect matchings of the whole original host.

König factorization of the remaining core would leave its exterior vertices
uncovered. It does not finish that final reconstruction. The new supporting
theorems therefore leave the completed inventory at **45/69**, with **24**
numbered assertions still incomplete.
