# Continuation handoff: unrestricted four-label compatible circuits

## Completed mathematical scope

The unrestricted compatible-circuit existence theorem on at most four labels
is now proved in Lean. The source endpoints are:

- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label`
- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_four`
- `Overfull.Multigraph.compatibleCircuitPartition_iff_admissible_and_even_of_card_le_four`

The input is any loopless multigraph, any finite selected set of actual copies,
and arbitrary incidence classes. The only mathematical conditions are even
selected degrees and every original half-cut class inequality. There is no
bound on degrees, parallel multiplicities, or selected-copy count. Neither a
selector nor a partition is assumed. Connectedness and finite ambient edge
type are not required. The exact necessary-and-sufficient criterion is proved.

The strict branch constructs a safely removable compatible pair or triangle.
The residual retains original admissibility and even degrees; residual
strictness is not assumed. The tight branch normalizes a nonempty shore of
size at most two avoiding the class vertex, constructs inside and outside
three-label partitions, restores exact original blocks and saved closed
pieces, and covers every original copy. Tight zero cuts are included.

The new original-host applications are:

- `Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers`
- `Overfull.FourOdd.exists_fourJoining_decomposition_of_even_degree_bound`
- `Overfull.FourOdd.exists_fourTwoOddJoining_decomposition`

They remove the small-boundary restrictions of the previous continuation.
Even fibers give disjoint matching pieces of size at most four with zero/two
footprints. Exactly two odd fibers give exactly the regular degree many primary
matching pieces of size at most three, plus surplus pieces of size at most
four with even footprints, covering every actual joining copy. The even-degree
variant retains its explicit half-joining-degree bound.

**Coverage remains 49/69.** This completes a central supporting theorem, not
a further numbered manuscript assertion. All 69 numbered records and statement
identities remain unchanged. Full Proposition 4.16, Theorem 4.17 and the main
theorem remain incomplete. Previous single-core, bounded-input, three-core and
all-four-odd terminal results remain available.

## Baseline and evidence

Both public branches were fetched and independently read at
`3991bb7eee091a329046073e0366daa84a603e5d`, tree
`6424bf81123aa75b2254aea7eceff6260611f397`, before source edits. That baseline
contains 10,595 tracked files, 14,260 audited declarations, 2,609 completed-result
mappings and 794 frozen source/input hashes.

The repository is `/workspace/scratch/77adbfc63087/overfull-lean`. The working
branch for this round is `continuation-20261124-strict-four`. The run is
`verification/runs/20261124T134200Z/`. Its genuine terminal receipts, frozen
inputs/outputs, preservation report and publication readbacks determine actual
verification and publication status. A focused build or this handoff alone
is not a full-project audit or a publication receipt.

The exact new inventory is `docs/four-label-existence-source.json`, with the
semantic review and proof map in the corresponding Markdown documents. The
full verifier generates `verification/four-label-existence-declarations.json`,
including private and generated proof declarations.

Every previous nonroot mathematical source and `Audit.lean` is byte-identical.
The root receives only recorded imports. Four precisely recorded additive map
registrations leave all previous verifier guards and the transitive axiom policy
intact. All old declarations, module owners, axiom sets, completed-result maps,
source/declaration maps and numbered assertions are checked for preservation.
Allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

All genuine failed and successful development commands are retained. Focused
commands may record unrelated source changes during parallel work; the final
full gate requires all sources and controls to be unchanged. Exact-tree and
both-branch readbacks establish publication separately.

## Next proof obligations

1. **Group pieces of size at most four.** Extend the existing bounded grouping
   API to the complete even/two-odd four-label families. Keep actual matching
   parts, original seeds, conflict bounds and exact cover. A natural target is
   the conflict bound `8D` and per-group support bound `8L`.
2. **All-even four-core terminal branch.** Use those grouped original pieces to
   construct the completed prefix; the remaining closed robust cores can use
   the existing generic closed-core factorization.
3. **Exactly two odd four-core branch.** The old three-core residual theorem
   cannot simply be relabeled. A primary path between the odd cores may contain
   a copy joining the two even cores. Thus the equality saying every joining
   copy lies in an odd-core cut is unavailable. Retain those even-even copies
   and both even robust cores in the central contraction. Prove its no-overfull
   condition, invoke the existing two-core/two-exception factorization, then
   align and restore the odd-leaf boundary colors.
4. **Full Proposition 4.16 and Theorem 4.17.** Combine all parity branches with
   uniform original-host constants, prefix construction and exact reassembly.
   Promote a numbered assertion only after its entire original statement is
   proved from its pinned hypotheses.
5. **Other global branches.** The critical average-degree input, outstanding
   critical corollaries, bipartite spanning/absorber construction, padding and
   global main-theorem compositions retain their recorded unfinished status.

The old diagnostic examples remain valid warnings about incorrect reductions:
arbitrary splitting or four-cycle deletion can violate nonlocal bounds, and
arbitrary suppressed partitions need not restore partwise. The completed proof
avoids those moves through the explicit strict/tight split and exact block
restoration. Do not reintroduce a supplied-selector assumption into applications.
