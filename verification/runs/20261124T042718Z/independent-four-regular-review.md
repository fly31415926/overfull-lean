# Independent review: degree-four compatible circuits on four labels

Reviewed by the `four_odd` agent on 2026-11-24. The five mathematical source files were read only; this review is the sole file written for this task. The `four_label` author confirmed the sources were frozen after the successful strict build identified below.

## Conclusion and exact scope

**Endorsement: no mathematical or scope concern found for degree exactly four at every one of the four labels.** The public result constructs a compatible circuit partition of the selected actual edge copies from `Q.AdmissibleOn classOf C` and `∀ v : Fin 4, Q.degreeOn C v = 4`. Its stronger local version assumes that each incidence class has at most two selected copies at each label. Neither theorem requires a template, a copy bijection, class pairings, connectivity, or a circuit partition as an input.

This review does **not** extend the result to arbitrary even degrees, mixed degrees, or the unrestricted four-label compatible-circuit theorem. In particular, the result is not by itself the missing high-degree reduction needed for the general four-label theorem.

## Findings

### 1. Classification covers every degree-four input, including disconnected graphs

`degree_bundle_sum` counts the six distinct unordered nonloop endpoint pairs using actual-copy cardinalities. The four degree equations yield the opposite-pair vector

```text
(a, b, c, c, b, a), with a + b + c = 4.
```

`regular_bundle_counts` derives these equalities from the public regularity premise. It does not assume an ordering, connectivity, or an isomorphism type. Each of `a`, `b`, and `c` therefore belongs to `Fin 5`.

`finite_template_counts` covers all such triples with a kernel-checked finite proof. Up to the recorded vertex permutations, the four profiles are `(4,0,0)`, `(3,1,0)`, `(2,2,0)`, and `(2,1,1)`. The first template has four parallel copies between labels 0 and 1 and four parallel copies between labels 2 and 3. Thus the disconnected possibility is present explicitly, rather than excluded by an unstated connectedness requirement. The remaining three templates reuse the checked connected small-kernel certificates.

The six permutations fixing label 0 suffice because the finite theorem explicitly verifies every ordered triple satisfying the sum condition; this is not inferred from an informal symmetry assertion.

### 2. Actual-copy transport preserves parallel multiplicities and exact cover

`exists_template_copy_equiv` proves equality of fiber cardinalities for every element of `Sym2 (Fin 4)`. It handles diagonal pairs separately using looplessness, and every non-diagonal pair belongs to the enumerated six-pair list. `Equiv.ofFiberEquiv` then constructs an endpoint-preserving equivalence `Fin 8 ≃ C`.

The public proof composes that equivalence with the subtype embedding to obtain an injection `ψ : Fin 8 ↪ E`. Distinct parallel copies remain distinct. The map is onto precisely `C`, as proved by `univ.map ψ = C`; it is not merely a map onto the set of endpoint pairs.

`FourAdmissibleTransfer.lean` transports support, degree, cuts, circuits, compatibility, disjointness, and the exact union through a copy embedding. The cut argument explicitly permits the two orientations of an unordered edge. Circuit connectivity is retained via nonempty proper cuts of the unchanged vertex support. The final partition therefore consists of genuine circuits of `Q` on its original copies and covers exactly `C`.

Vertex relabeling is also applied in the correct direction. The local original classes are pulled back along the vertex permutation and copy embedding, then transported forward after the template partition has been constructed.

### 3. Local-class coarsening has the required direction

`four_incidence_pair_coarsening` proves

```text
equal original classes ⇒ equal balanced-pair classes.
```

The original classes refine one of the three partitions of four incidences into two pairs. The balanced-pair classes may introduce additional forbidden pairs. Consequently, compatibility for those larger forbidden classes implies compatibility for the original classes. The public proof uses exactly this implication in `hcomp`; it does not reverse the refinement relation.

The coarsening argument first rules out three distinct incidences with one original class using the cardinality bound. It then exhausts the possible equalities among four ports. It imposes no finiteness or cardinality assumption on the class type `K`.

The port maps are checked to be injective, incident, and surjective at every template vertex, with `rank_port` identifying their ranks. Thus the four incidences to which coarsening is applied are the actual four incidences at that vertex. Their class counts are bounded by an injective map into the corresponding original incidence-class filter.

### 4. Disconnected templates receive genuine compatible circuit partitions

For each four-copy parallel component, `different` chooses one of the three pairings distinct from the forbidden balanced pairing at both endpoints. Each selected pair contains two distinct parallel copies, so `isCircuit_parallel_pair` proves it is a circuit. The finite `pairClass_ne` check proves compatibility at both endpoints.

The two pair circuits from each component yield four circuits in total. `disconnected_disjoint` and `disconnected_cover` verify their pairwise disjointness and exact cover of all eight copies. No argument requires paths between the two components.

### 5. The public admissibility hypothesis is sufficient

`AdmissibleOn` is the existing half-cut condition on actual selected copies. Its existing `local_class_bound` theorem specializes the condition to the singleton shore `{v}`. Under degree four, this gives twice each local incidence-class size at most four, hence local class size at most two.

The final public corollary uses only this valid consequence before invoking the stronger local theorem. There is no assumed admissibility for the artificial coarsened classes and no hidden safe-deletion or residual admissibility premise. The finite template construction already supplies compatible partitions for every balanced local pairing assignment.

### 6. Proof and verification boundaries

The new finite classification, incidence facts, and disconnected-case checks use Lean proof terms through `decide` or `decide +kernel`. The connected certificates in `SmallKernelData.lean` are also kernel-checked and are converted by `SmallKernel.lean` to the same `CompatibleCircuitPartition` structure used by the public theorem. The reviewed five-file source scan found no `sorry`, `admit`, new `axiom`, or `native_decide`.

This is an independent source review, not a substitute for the repository-wide axiom audit. The strict focused build below was run by the author through the shared recorder; the reviewer read its output and metadata and independently recomputed the five source hashes. Every hash matched the build record, which reports no changed inputs.

## Exact reviewed source hashes

Paths are relative to the repository root. SHA-256 hashes bind this review to the source bytes that were read and to the successful recorded build.

| Source | SHA-256 |
| --- | --- |
| `Overfull/CompatibleCircuits/FourAdmissibleClassification.lean` | `2a5da1bb730e67328f164374e97be95c3a466abcee8b2517f5f15766a31df56a` |
| `Overfull/CompatibleCircuits/FourAdmissibleCoarsening.lean` | `bdc35142440d2819535ef573463ec002f66794ab224fdf559a7c3c6a7692ce4e` |
| `Overfull/CompatibleCircuits/FourAdmissibleRegular.lean` | `fca5cdafa376204eaed32c875e791d165ade8d7f9f97866ff55c0c7807e4c68e` |
| `Overfull/CompatibleCircuits/FourAdmissibleTemplates.lean` | `cfbf52982ddafa04e488babab92daa4c10a344668a271f1c8d77ef1d5cd59894` |
| `Overfull/CompatibleCircuits/FourAdmissibleTransfer.lean` | `1225ffbada7dff5880dfec7a40ebe74575db12043fe84ae20778a6bb81f98231` |

Supporting definitions and existing proofs inspected:

| Source | SHA-256 |
| --- | --- |
| `Overfull/CompatibleCircuits/Basic.lean` | `8db58454fa3550ace9e31936f2e46e5362b0566dd83c630f69dbab8618749247` |
| `Overfull/CompatibleCircuits/SmallKernel.lean` | `5d6519273a62adcd6e29a528b3ea97f35a95ef81bc7680c46f655eed5fde381c` |
| `Overfull/CompatibleCircuits/SmallKernelData.lean` | `31d16fa0fba3fe6fc2b40bac1933f7cdf84f5a22c2c32c234347dbec1b5fd28b` |
| `Overfull/CompatibleCircuits/ThreeLabelBundles.lean` | `43031263d6910df71a867f1e42caacf07456a782ddfba1ea2d2e4801e85b7a97` |
| `Overfull/CompatibleCircuits/VertexRelabeling.lean` | `dbc640993ca2987c90eb79457a6712433553d76d7e9ea0365f26b4268cdabee9` |

## Recorded strict build

- Command: `lake build --wfail Overfull.CompatibleCircuits.FourAdmissibleRegular`.
- Evidence directory: `verification/runs/20261124T042718Z/development/four-label-regular-11/`.
- Started: `2026-11-24T04:43:41.838382+00:00`.
- Finished: `2026-11-24T04:43:46.035063+00:00`.
- Result: passed, actual exit code 0, 3,124 jobs, no warnings, no changed inputs.
- `command.json` SHA-256: `327755d7b105e4ea1326382316d8642cf180c3a1f5cd0600aa0fa71f05b74c25`.
- `output.log` SHA-256: `013579b3397ddf2ee84cc58bb0766f35a07bd1ba13b43103c34c38aa64d83212`.

No source change is requested by this review. The remaining limitation is the explicit mathematical scope: degree four at all four labels.
