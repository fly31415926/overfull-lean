# Next target: the two-core branch of Corollary 4.6

Run: `20261122T235931Z`. This is a read-only source/API assessment, followed
by this run-result artifact. It adds no Lean theorem and changes no audited
source, documentation map, or verifier input. The mathematical arguments
and proposed proof steps below are distinguished from existing Lean results.

## Outcome

The compatible-circuit selector and exact partition theorem on at most
three vertices are now available. Applying them to the two-core branch of
Corollary 4.6 still requires an actual host-to-quotient construction,
verification of its half-cut and parity hypotheses, and reconstruction of
the desired factorization. There is a concrete obstruction to a naive
application: an exceptional vertex made into a singleton quotient label
cannot have positive joining degree in an admissible endpoint-class
quotient. Section 5 gives the mathematical argument; it was not newly
formalized in Lean during this assessment.

Source identity has since been checked privately against the recorded
statement hashes. Manuscript-derived statement and proof text is withheld
from this public run artifact because automatic approval review rejected
that disclosure. This assessment uses repository facts and mathematical
arguments developed independently from its public Lean interfaces.
The recorded inventory remains **47 of 69** complete numbered assertions;
this assessment completes none.

## 1. Public source records and the publication boundary

[manuscript-source.json](../../../docs/manuscript-source.json) identifies
the pinned manuscript as:

- `Four_Robust_Component_Cases_2026-11-20.tex`;
- SHA-256 `4605bdf3ee5b241a7b52dd59d08537fa0a439335cd6f119394cddd4609efffc1`;
- `manuscript_included: false`;
- source identification: “No manuscript text is reproduced in this repository.”

No tracked `.tex` or `.pdf` was found. The recovered-original-files archive
at `recovery/cb05ef5/recovered-original-files.tar.gz` contains 26 members and
no `.tex` or `.pdf` member. The repository's source hashes and mappings
identify statements without reproducing their text.

A subsequent private source check means that source availability is no
longer the general blocker. Publication of manuscript-derived passages
was rejected by automatic approval review. This public assessment
therefore retains the existing repository metadata and public proof
interfaces, without those passages, paraphrases, or a link to the
withheld material. Statement-hash agreement does not establish identity
of entire manuscript files or their complete proof text.

[coverage.json](../../../docs/coverage.json) records:

| Assertion | Source label | Pinned statement lines | Current scope |
| --- | --- | --- | --- |
| Lemma 4.4 | `two:short:fixed-pattern` | 2386–2398 | Supporting fixed-pattern and terminal components; full construction incomplete. |
| Corollary 4.5 | `two:thm:two-four-exceptions` | 2587–2591 | Full assertion incomplete. |
| Corollary 4.6 | `three:lem:bounded-input` | 2600–2608 | Complete one-core branch and supporting at-most-three-vertex circuit theorem; two-core construction/reassembly incomplete. |

For 4.6 the statement SHA-256 is
`86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26`.
[few-exception-source.json](../../../docs/few-exception-source.json) maps
that same statement hash to inspected manuscript lines 2748–2756 and
explicitly records `full_assertion_verified: false`.

The exact original two-core hypotheses are not restated in this public
artifact. A source-level composition must be reviewed against the exact
authorized source, preserving its assumptions and quantifiers. The
labels and the checked one-core specialization alone do not determine
the distinct two-core statement.

## 2. The exact available host formulation

[FewExceptions/Factorization.lean](../../../Overfull/FewExceptions/Factorization.lean)
provides `Overfull.one_core_three_exception_factorization` and
`Overfull.one_core_three_exception_one_factorization`. Their available
host-normalized interface is:

1. Fix real parameters `α, ν, τ` with `0 < α`, `0 < ν`, `ν ≤ τ`, and
   `τ ≤ min α 1 / 16`.
2. Choose `ε > 0` and `n₀` before all graph data.
3. Take finite vertex and actual-copy types `V, E`, a loopless multigraph
   `G`, `U : Finset V`, an embedded `SmallCuts.Core G U`, degree `k`, and
   real deficit `a`.
4. Require host order at least `n₀` and even; `Uᶜ.card ≤ 3`; every host
   degree equal to `k`; `α * |V| ≤ k`; `α * |V| ≤ |U|`; no `k`-overfull
   vertex set; robust expansion of the embedded core with parameters
   `ν, τ`; `a + 1 ≤ ε * |V|`; and every core degree at least `k - a`.
5. Obtain an actual `G.EdgeColoring k`, or exactly `k` pairwise disjoint
   perfect matchings of original copies whose union is every copy.

No complement coloring or parity of `U` is supplied to these wrappers.
They construct the former and normalize the latter internally.

The underlying [SmallCuts.Core](../../../Overfull/SmallCuts.lean) contains
a simple graph on the actual subtype `U`, an injection from its edges
into `E`, and an endpoint-preservation proof. It is not an identification
of all internal parallel copies with a simple edge. This distinction must
survive any two-core construction.

These are checked available one-core hypotheses, not a complete formal
statement or proof of the distinct two-core branch. In particular, the
bounded exterior of a single core does not include a second large core
automatically.

## 3. Exact new circuit entry point

[CompatibleCircuits/AtMostThree.lean](../../../Overfull/CompatibleCircuits/AtMostThree.lean)
provides, in namespace `Overfull.Multigraph`:

```lean
G.exists_compatibleCircuitPartition_of_card_le_three
  (hV : Fintype.card V ≤ 3)
  (classOf : V → E → K)
  (C : Finset E)
  (hadmissible : G.AdmissibleOn classOf C)
  (heven : ∀ v, Even (G.degreeOn C v)) :
  Nonempty (G.CompatibleCircuitPartition classOf C)
```

The module also gives `exists_safe_circuit_of_card_le_three` and
`compatibleCircuitPartition_iff_admissible_of_card_le_three`. It permits
arbitrary actual-copy and incidence-class types, including empty types
when appropriate. It does not require a preselected safe circuit.

[Basic.lean](../../../Overfull/CompatibleCircuits/Basic.lean) defines the
essential input by the full family of inequalities

\[
2\,|\operatorname{classCut}(i,x,A)|\le |\delta_C(A)|
\qquad\text{for every label }i,\text{ class }x,\text{ and label shore }A.
\]

The output is a finite family of genuine connected 2-regular circuits,
with compatible incidence classes, pairwise disjoint actual-copy sets,
and union exactly `C`. It is not a factorization of the original host.

The application requires a proof that the **actual chosen label type**
has cardinality at most three. “Two cores” does not establish this if
exceptional vertices receive extra labels. Aggregating or absorbing
labels also requires proofs that the required incidences and inequalities
survive.

## 4. Existing quotient and lifting APIs

The following definitions in
[FourOdd/OriginalGraph.lean](../../../Overfull/FourOdd/OriginalGraph.lean)
are generic in the label type `I`, despite the module namespace:

```lean
J := Overfull.FourOdd.joiningGraph G label
Q := Overfull.FourOdd.joiningQuotient G label
classOf := J.endpointClass label
```

Here `label : V → I`. The actual edge-copy type of `J` and `Q` is the
subtype `joiningCopies G label`, whose members have endpoints with
different labels. Parallel host copies remain distinct. The final
application would take all these copies, `C = Finset.univ`, unless the
source construction first selects a justified residual or augments it.

| Required connection | Existing API and exact role |
| --- | --- |
| Loopless quotient | `joiningGraph_join` supplies the distinct-label condition for `Multigraph.labelQuotient`. Internal copies must be excluded before contraction. |
| Endpoint classes | `Multigraph.endpointClass` records the actual host endpoint at an incident label. `endpointClass_eq_of_incident` identifies it with that endpoint. |
| Host cut versus quotient cut | `joiningCut_image` identifies the image under `Subtype.val` with the original cut of `labelShore label A`; `joiningCut_card` preserves its cardinality. |
| Actual endpoint incidence in a cut | `joiningGraph_degreeOn_image` and `joiningCut_degreeOn` transport actual incident-copy counts to the host. |
| Quotient degree | `joiningQuotient_incidence_image` and `joiningQuotient_degree_eq_cut` identify it with the cut of a label fiber. |
| Host parity and cut bounds | `FourOdd.regular_cut_parity`, `regular_odd_cut_lower`, and `regular_even_cut_twice_degree_le` derive exact parity, odd-shore lower bounds, and even-shore half-cut bounds from the regular host and no-overfullness where needed. |
| Compatible parts are matchings | `Multigraph.compatible_endpointClass_iff` and `CompatibleCircuitPartition.isMatching` turn quotient compatibility into the matching property in `J`. |
| Size | `CompatibleCircuitPartition.card_le` bounds each part by `Fintype.card I`, hence by three in the new application. |
| Virtual-copy lifting | `isMatching_of_compatible_embedding` permits an injected original-copy type in a larger quotient, given incidence and endpoint-class witnesses. |

The endpoint-class and lifting results are in
[CompatibleCircuits/Lifting.lean](../../../Overfull/CompatibleCircuits/Lifting.lean);
the cut bounds are in
[FourOdd/CutBounds.lean](../../../Overfull/FourOdd/CutBounds.lean).

Individual matching lifting is already proved. A convenient final wrapper
still needs to transport the whole partition through `Subtype.val`,
retaining disjointness and the exact union of original joining copies.
More substantially, the reviewed APIs do not yet assemble the required
`Q.AdmissibleOn classOf univ` from a general two-core host construction.

## 5. Exceptional singleton labels obstruct direct admissibility

**Mathematical argument from the existing definitions; not a newly
checked Lean theorem in this run.** Suppose the fiber of a quotient
label `i` is exactly `{z}`, and the quotient uses all actual joining
copies with endpoint classes. Every copy incident with `i` then has
class `z`. Its singleton cut is therefore entirely one class:

\[
\operatorname{classCut}(i,z,\{i\})=\delta_Q(\{i\}).
\]

Admissibility at that class and cut requires

\[
2\deg_Q(i)\le\deg_Q(i),
\]

so `deg_Q(i) = 0`. If the original host is `k`-regular, all copies at
`z` leave its singleton fiber because the host is loopless. Thus
`deg_Q(i) = k`, contradicting the condition whenever `k > 0`.

The same obstruction has a direct matching interpretation: a circuit
meeting `i` uses two copies there, while a host matching can use only one
copy at `z`.

Consequently a quotient consisting of two core labels and one individual
exceptional vertex is not automatically an instance of the new theorem,
even though its label count is three and even if its degree parity is
correct. A valid construction must address exceptional endpoints through
justified assignment, absorption, selected boundary edges, or an
appropriate augmentation. Grouping several exceptions into one label
removes the singleton-fiber argument, but still does not prove the
half-cut inequalities or endpoint-load bounds.

## 6. A concrete generic bridge that can be proved next

The following is a **proposed supporting theorem**, not an existing
declaration or a substitute for full 4.6. It is derived from the public
Lean APIs and was assessed independently before the private source check.

Take a finite `k`-regular host with no `k`-overfull set, a label map into
at most three labels, and its actual joining quotient. Suppose every
host vertex has joining degree at most `D`, with `2 * D ≤ k`, and every
quotient degree is even. Then prove endpoint-class admissibility,
apply the new partition theorem, and lift the result to an exact
partition of the host's joining copies into matchings of size at most
three.

The first useful lemma is an exact class-cut transport identity. For
label `i`, original endpoint `v`, and label shore `A`, the class-cut
cardinality should equal

\[
\begin{cases}
\deg_{\delta_G(\operatorname{labelShore}(A))}(v),
   &\operatorname{label}(v)=i,\\
0, &\operatorname{label}(v)\ne i.
\end{cases}
\]

Prove this with `endpointClass_eq_of_incident`, quotient incidence, and
the injective copy map. Then split according to the parity of the
original label shore:

- For an even shore, `regular_even_cut_twice_degree_le` gives the exact
  half-cut inequality directly.
- For an odd shore, `regular_odd_cut_lower` gives cut size at least `k`,
  while the class size is at most `D`, so `2 * classSize ≤ 2 * D ≤ k`.

For parity, `joiningQuotient_degree_eq_cut` together with
`regular_cut_parity` gives degree parity equal to
`k * |label fiber|` modulo two. Thus even `k`, or even size of every
fiber, supplies even quotient degrees. If `k` and some fiber are odd,
parity repair is necessary. When every fiber is even, every union of
fibers is even, so the odd-shore bound and the additional `D` hypothesis
can be omitted entirely in that special case.

The common bound `2 * D ≤ k` is a sufficient condition for this proposed
generic bridge. This assessment does **not** establish it from the
original two-core hypotheses. In particular it cannot hold for an
unabsorbed positive-degree exceptional singleton, whose joining degree
is `k`.

## 7. What remains after a circuit partition

**Parity and virtual copies.** A quotient circuit uses degree zero or
two at each core label. Its matching footprint therefore preserves the
parity of the uncovered core order. An odd core generally needs an odd
boundary footprint before an internal perfect matching can finish it.
This is a construction obligation, not a consequence of compatibility.

[Virtual.lean](../../../Overfull/CompatibleCircuits/Virtual.lean) and
[VirtualPartition.lean](../../../Overfull/CompatibleCircuits/VirtualPartition.lean)
already provide actual-copy augmentation and counting patterns, but their
augmentation is specifically on `Fin 4`, adding virtual families on
`01` and `23`. They classify a supplied compatible partition; they do
not establish its existence or augmented admissibility. The new
at-most-three-vertex theorem cannot directly be applied to that four-label
interface. Any additional augmentation would need its own incidence,
half-cut, parity, and deletion-count proofs. The public four-label
patterns can guide such proofs without assuming the unfinished
four-label theorem.

**Palette and coverage.** Small lifted matchings do not automatically
give exactly `k` color classes, cover every exceptional vertex in each
round, or complete to pairwise edge-disjoint perfect matchings. The
construction must establish the round count/grouping, exceptional
coverage, even uncovered core orders, small footprints, and sufficient
edge and robustness reserves.

**Available completion interfaces.**
[CircuitPatterns/Completion.lean](../../../Overfull/CircuitPatterns/Completion.lean)
provides `exists_core_boundary_completion` and
`exists_boundary_completion` for actual fixed boundary matching
families with certified packing rules and limits, disjointness, parity,
core-degree and footprint bounds. The latter also requires coverage of
the exceptional set in each round. Its host is a `SimpleGraph`; using it
for an actual-copy multigraph requires appropriate injective edge
transport or an extension of that interface, not identification of
parallel copies.

[OrdinaryFactorization/Full.lean](../../../Overfull/OrdinaryFactorization/Full.lean)
provides full `ordinary_core_factorization` and
`ordinary_core_one_factorization`, but requires a bounded exterior and an
actual `k`-coloring of the core complement. The parity variant in
[OrdinaryFactorization/Parity.lean](../../../Overfull/OrdinaryFactorization/Parity.lean)
still requires that complement coloring.

[TerminalComplement/Factorization.lean](../../../Overfull/TerminalComplement/Factorization.lean)
provides `exists_uniform_terminal_factorization` and its exact
one-factorization version. It constructs the complement coloring for a
bounded exterior with a possible unrestricted apex, assuming that every
other exterior vertex has at most `b` copies to the exterior, the core
deficit is at most `a`, and `a + b` is sufficiently small. It still
requires an even, regular auxiliary host and a large robust core.
Contracting a second core to an apex does not by itself prove the apex
has degree `k` or that the auxiliary graph meets these conditions.

The final assembly must preserve original-copy identities, prove every
required residual degree and robust-expansion bound, and put all uniform
constants before the host. Those obligations must be discharged from
the recovered original hypotheses rather than added to a purported
full-source theorem.

## 8. Recommended next-run order

1. Review the exact original two-core statement and proof in an authorized
   context. Match the required host/core types, exceptional cases, error
   normalization, and quantifiers. Respect the current restriction on
   publicly disclosing private manuscript material.
2. Prove the endpoint-class cut transport identity and the singleton-label
   obstruction as small reusable Lean lemmas. These settle the precise
   admissibility interface and prevent an invalid naive quotient.
3. Prove the generic host-to-quotient admissibility and partition bridge
   in Section 6, including actual-copy partition lifting. State its extra
   sufficient conditions openly; do not label it complete 4.6.
4. Establish a source-correct host construction and all its quotient
   hypotheses. If an essential fourth label remains, address the actual
   four-label theorem rather than applying a three-label result to it.
5. Supply the boundary family, completion inputs, terminal auxiliary
   graphs, and exact original-copy factorization. Only then reassess the
   numbered assertion's status against the original statement.

No build was started for this assessment. It is a restart aid and a
mathematical/API review, not a replacement for the run's independent
compiler and audit results.
