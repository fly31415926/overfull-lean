# Remaining verification targets after the three-label circuit proof

The current complete numbered inventory is **47 of 69**, with **22**
remaining, including the main theorem. Full ordinary-core Lemma 4.2 joins
the previously completed Lemmas 4.14 and 4.15. The recovered continuation
completes the one-core branch of Corollary 4.6 but not its two-core branch.
The latest continuation also proves the full compatible-circuit selector
and exact partition on every finite vertex type of cardinality at most three.

The preceding checkpoint recreated eleven unavailable supporting modules and
preserved nine recovered original source modules. The
[reconstruction record](checkpoint-reconstruction.md) distinguishes this
new proof-checking run from the original unavailable `cb05ef5` tree.

## Next substantive obligations

| Target | Available checked inputs | Remaining proof work |
| --- | --- | --- |
| Full Corollary 4.6 | Complete one-core branch with at most three exceptional vertices; full ordinary-core factorization; complete compatible-circuit decomposition on at most three vertices | Prove the distinct two-core branch and the joining construction required by the original statement, including actual quotient hypotheses and reconstruction. |
| Full Lemma 4.4 and Corollary 4.5 | Actual fixed-pattern components and terminal one-core factorization under its incidence hypotheses | Construct the requisite compatible joining edges and incidence conditions and complete all branches. |
| Four-label compatible-circuit decomposition | Complete safe selector and exact partition on at most three vertices, plus exact four-label critical-cut correction and checked small kernels | Prove a four-label selector handling both tight and slack-two constraints, or prove the needed joining construction using the completed three-label theorem. Do not apply the three-label tight-only criterion to four labels. |
| Proposition 4.16 | Frequent-pattern reduction, full boundary extension 4.14, full four-odd decomposition 4.15, and complete one-core bounded input | Complete every remaining parity branch and reassemble the full original host factorization. |
| General Theorem 6.1 and Proposition 6.2 | Uniform localization, coupled parameters, actual reserved-remainder packing and exact balanced orientation | Construct the compatible spanning setup, special path systems, robust absorber and required stage inputs, then prove complete reconstruction. |
| Main theorem and structural cases | Robust partition, many safe matching and absorption components, and the completed special factorizations | Supply the remaining structural exclusions, critical average-degree input, and source-level compositions. |

The numbered inventory stays pinned to
`Four_Robust_Component_Cases_2026-11-20.tex`. Later manuscript inspections
and supporting branches do not silently replace that inventory or count
as complete numbered assertions.

The next run should first inspect the original two-core branch of 4.6
and its quotient/lifting interfaces, seeking an exact application of the
completed at-most-three-vertex theorem. If an essential fourth label remains,
record that obstruction and address the genuine four-label selector.
The [restart handoff](continuation-handoff.md) lists the checked entry points.
