# Continuation handoff: full single-core coloring

## Current mathematical scope

`Overfull.single_core_coloring` completes pinned **Lemma 3.1**,
`single:lem:coloring`. Coverage is **49/69**; 20 assertions remain incomplete,
including the main theorem. Only Lemma 3.1 is promoted. All other 68 assertion
records and all 69 source-statement identities are unchanged.

The theorem chooses positive `ε` and `n₀` after fixed
`0<ν≤τ≤1/4096000` and before the finite original simple graph. It uses actual
maximum degree, the source's spanning robust core and covering sets, no
overfull set, density and combined error budget. It derives nonnegative error,
removes overlap in the exceptional cover, and adds no regularity or parity
hypothesis. Its conclusion is a coloring of the original simple graph.

The supporting chain now contains frequent-pattern and bounded-exception
three-core composition, full three-core regular composition, simple auxiliary
realization with exact original-copy transport, and uniform nonregular
two-core and one-core factorization. The whole absorption tolerance function
is fixed before the eventual exceptional bound.

The all-four-odd terminal one-factorization is also proved from original-host
hypotheses and actual forest-pair supplies. The proof constructs the selected
prefix and both residual alternatives: singleton-rich boundary extension or
three independent apices around a common center, followed by exact reassembly.

The new compatible-circuit theorem constructs actual-copy partitions under
original admissibility for four-label multigraphs of degree exactly four at
each label, including disconnected inputs. It is a degree-four special case.
Neither supporting result completes full Proposition 4.16.

## Baseline and evidence

The authoritative baseline is public commit
`14978e4dec2bce94f63953df7b1bdd54f61c3e6c`, tree
`c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767`. Both public branches were fetched
and independently read back at that commit. It contains 6,916 tracked files,
13,675 audited declarations, 2,396 completed-result mappings and 741 frozen
source/input hashes.

The repository is `/workspace/scratch/5793769ed3f4/overfull-lean`, initially
on `continuation-20261124`. The run is
`verification/runs/20261124T042718Z/`. Its actual terminal receipts, frozen
snapshots, final preservation and execution reports, and publication receipts
determine verification and publication status. A handoff or focused build
alone is not a complete audit or publication receipt.

Principal source endpoints:

- `Overfull/AuxiliarySimple/SingleCore.lean`
- `Overfull/ThreeCoreReduction/Regular.lean`
- `Overfull/TerminalFourOdd/Theorem.lean`
- `Overfull/CompatibleCircuits/FourAdmissibleRegular.lean`

The exact inventory is `docs/global-factorization-source.json`. Its accompanying
semantic review and verification map describe source agreement, quantifier
order, original-copy transport, proof responsibilities and scope. The complete
generated declaration map includes private and generated names.

All prior nonroot mathematical sources and `Audit.lean` are unchanged. The
root has only three added imports. The verifier has precisely the reviewed
48-to-49 count update and four additive registrations; old guards and the
transitive axiom policy remain intact. The complete gate must pass on unchanged
frozen inputs, preserve every old declaration/owner/axiom set, all previous
result mappings and source/declaration maps, and use only `propext`,
`Classical.choice` and `Quot.sound`.

Every genuine failed and successful development command is archived with
source snapshots and real output/exit. Publication requires the complete
artifacts and separate exact-tree and both-branch readbacks for `main` and
`verified-bipartite-continuation-2026-11-21`.

## Next mathematical obligations

1. **General four-label compatible circuits.** Arbitrary admissible Eulerian
   quotients can have larger and unequal even degrees. The degree-four theorem
   does not cover them. A reduction must preserve all half-cut constraints and
   actual copies; ordinary Eulerian circuits are insufficient.
2. **Other four-core terminal cases.** Four even parts and exactly two odd
   parts still need the general compatible partition. The all-four-odd case
   with actual forest-pair supplies is now complete and reusable.
3. **Full regular factorization Theorem 4.17.** The three-core subcase with a
   small linear exceptional set is complete. The full four-core range still
   requires the remaining terminal cases and uniform composition.
4. **Global and bipartite inputs.** Lemma 3.1 alone does not prove the critical
   corollaries, bipartite factorization branch, all padding results or the main
   theorem. The numbered inventory gives their exact unchanged status.

Do not promote a support theorem as a complete numbered assertion, assume a
coloring or partition that the target must construct, or choose uniform
constants after the host. Preserve every actual edge through contraction,
auxiliary completion, residual construction and prefix restoration.
