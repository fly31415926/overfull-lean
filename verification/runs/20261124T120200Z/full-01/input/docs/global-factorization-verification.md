# Verification map: single-core closure and supporting continuations

## Public conclusions

| Result | Declaration | Scope |
| --- | --- | --- |
| Complete Lemma 3.1 | `Overfull.single_core_coloring` | Actual maximum degree, one robust core, literal source cover and error budget, arbitrary original parity |
| Two ordinary cores | `Overfull.two_core_nonregular_factorization` | Nonregular host, degree bound `k<n`, two robust cores and small linear exceptional set |
| One ordinary core | `Overfull.one_core_nonregular_factorization` | One-core wrapper through a second auxiliary completion |
| Three-core regular factorization | `Overfull.three_core_regular_factorization` | Even-order simple regular host with three robust cores and small linear exceptional set |
| Exact three-core factorization | `Overfull.three_core_regular_one_factorization` | The degree number of perfect matchings partitioning every original copy |
| Four odd terminal parts | `Overfull.four_odd_terminal_one_factorization` | All-four-odd subcase with original forest-pair supplies |
| Four-regular compatible circuits | `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_regular` | Four labels, degree four at each label, original admissibility |
| Local-class strengthening | `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_regular_local` | Degree four and local incidence classes of size at most two |

Only the first row completes a numbered assertion. Coverage is 49/69; the main
theorem is unproved. All 69 statement identities and the other 68 assertion
records remain unchanged.

## Module responsibilities

| Source family | Responsibility |
| --- | --- |
| `ThreeCoreReduction/Frequent.lean` | Frequent-pattern reduction, terminal factorization and prefix restoration |
| `ThreeCoreReduction/Bounded.lean` | Robust range reduction for a fixed exceptional bound |
| `ThreeCoreReduction/Regular.lean` | Foreign reduction, absorption tolerance function, finite threshold maximum and exact reassembly |
| `AuxiliarySimple/Deficiency.lean` | Total and ceiling-average deficiency bounds |
| `AuxiliarySimple/Graph.lean` | Actual simple realization, edge equivalence, degree and cut identities |
| `AuxiliarySimple/Coloring.lean` | Exact coloring transport and restriction |
| `AuxiliarySimple/CoreTransport.lean` | Core equivalences, embedding and robustness transport |
| `AuxiliarySimple/Completion.lean` | Simple completion with original and auxiliary core certificates |
| `AuxiliarySimple/OrdinaryTwo.lean` | Uniform nonregular two-core factorization |
| `AuxiliarySimple/OrdinaryOne.lean` | Uniform nonregular one-core factorization |
| `AuxiliarySimple/SingleCore.lean` | Exact Lemma 3.1 wrapper and actual maximum-degree coloring |
| `TerminalFourOdd/` | Decomposition, selection, completion, residual geometry, both residual alternatives and reassembly |
| `CompatibleCircuits/FourAdmissible*.lean` | Copy transport, local coarsening, template proofs, complete four-regular classification and admissibility endpoint |

Every path in this table is under `Overfull/`. The three added root imports
are `Overfull.AuxiliarySimple.SingleCore`,
`Overfull.TerminalFourOdd.Theorem`, and
`Overfull.CompatibleCircuits.FourAdmissibleRegular`. Their dependency closure
contains every new mathematical source; the full verifier checks that closure.

## Inventories and unchanged audit

`scripts/update_global_factorization_manifest.py` records final modules,
repository paths, SHA-256 hashes and public proof lines. It creates an
inventory, not proof evidence. The unchanged Lean audit enumerates actual
proof declarations after the complete build. The verifier matches source
proofs to that environment and writes the complete new declaration map,
including private and generated names. Its digest is in
`verification/results.json` alongside all earlier maps.

The supplementary preservation check compares every baseline declaration
name, owner and axiom set (13,675 declarations), all 2,396 prior completed-result
mappings, and every earlier declaration-map byte. All previous nonroot
mathematical sources and `Audit.lean` are byte-identical.

## Complete gate and frozen evidence

The project pins Lean 4.24.0 and Mathlib revision
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Its normal gate is:

```sh
python3 scripts/verify.py
```

This executes the complete `--wfail` Lean build, actual transitive axiom audit,
source/statement/coverage checks and complete declaration mapping. Only
`propext`, `Classical.choice` and `Quot.sound` are accepted. No project axiom
or admitted proof is permitted.

The current run wraps that exact command as follows:

```sh
python verification/runs/20261124T042718Z/run-verifier.py full-01
python verification/runs/20261124T042718Z/check-preservation.py full-01
```

Attempt names are immutable. Failed attempts remain, and retries use a new
name. The final preservation and execution reports identify the successful
attempt. The wrapper snapshots all source and verifier inputs and controls,
records actual command output and exit, verifies unchanged bytes, and retains
the generated artifacts. The preservation checker binds the live results,
raw build/audit logs and declaration map to that exact recorded execution.

Every focused command is retained under the current run's `development/`
directory with source snapshots, input hashes, timestamps, raw output and
actual exit. Failed and discarded intermediate attempts are preserved.
Early commands using `-KwarningAsError=true` did not make Lake reject warnings;
their original logs remain. Subsequent strict focused commands and the final
complete gate use `--wfail`. The latter is the acceptance criterion.

Parallel development sometimes changed unrelated inputs during a focused
build; the recorder lists those paths. The final complete run requires all
candidate inputs to remain unchanged across all proof families.

The verifier receives exactly the 48-to-49 count update and four additive
source-family registrations/guards, recorded in `verifier-additions.json` and
`verifier-changes.patch`. All prior guards and the axiom audit are preserved.

## Publication and outstanding mathematics

Publication requires separate exact-tree and both-branch readbacks in
`fly31415926/overfull-lean`, for `main` and
`verified-bipartite-continuation-2026-11-21`. Neither a focused pass nor a local
complete pass is a publication receipt.

The general admissible Eulerian four-label compatible partition, the other
four-core terminal parity cases, full Theorem 4.17, remaining global and
bipartite inputs, and the main theorem are separate outstanding obligations.
The degree-four special case and all-four-odd case do not close those assertions.
