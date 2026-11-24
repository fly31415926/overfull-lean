# Completed verification: full single-core Lemma 3.1

The genuine complete verifier and supplementary preservation check passed.
**Numbered coverage is 49/69. The main theorem is unproved.** Only pinned
Lemma 3.1, `single:lem:coloring`, is promoted in this continuation.

## Observed execution

| Check | Actual result |
| --- | --- |
| Full command | `python3 scripts/verify.py` |
| Immutable attempt | `full-01` |
| Exit code | `0` |
| Strict complete Lean build | 3,835 jobs, `--wfail`, passed |
| Transitive axiom audit | 14,055 proof declarations |
| New audited declarations | 380 |
| New public proof declarations | 140 in 34 new modules |
| Complete result mappings | 2,536 |
| Frozen inputs | 779: 664 source files and 115 other inputs |
| Inputs and verification controls | Unchanged throughout execution and preservation check |
| Allowed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Actual elapsed time | 1075.560 seconds |

These values come from the actual command receipt, raw build/audit output,
complete verifier result, and the preservation report. They are not inferred
from focused builds. The receipt, raw output, full frozen input/control bytes,
and every generated output are retained under `full-01/`.

## Mathematical result and scope

`Overfull.single_core_coloring` proves the literal source lemma with a
sufficient fixed range `0 < ν ≤ τ ≤ 1/4096000`. It chooses positive error
and order thresholds before the original simple graph, uses actual maximum
degree, and concludes an original simple-graph maximum-degree coloring.
It derives nonnegative error and removes overlap from the exceptional cover.
No original regularity, even order or disjoint cover is imposed.

The proof constructs three-core regular factorization by composing the
foreign-edge, absorption, frequent-pattern and terminal reductions, then uses
exact simple auxiliary completions for two and one ordinary cores. All
prefixes and restricted colorings retain the original edge copies. The full
absorption tolerance function is chosen before its eventual exceptional bound.

The continuation also proves original-host all-four-odd terminal
one-factorization with the source forest-pair supplies, and compatible circuit
partitions for admissible four-label multigraphs of degree four at every label,
including disconnected inputs. These are supporting subcases. The general
four-label compatible partition, the other four-core terminal parity cases,
full Proposition 4.16, full Theorem 4.17 and the main theorem remain open here.

The exact source statement hash for Lemma 3.1 remains
`e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe`.
Independent source-hash-linked reviews cover the literal lemma and the
four-regular construction. The source manifest and semantic review are in
`docs/global-factorization-source.json` and its accompanying Markdown files.

## Preservation

The baseline is public commit `14978e4dec2bce94f63953df7b1bdd54f61c3e6c`,
with tree `c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767`. Every prior nonroot mathematical source
and `Audit.lean` is byte-identical. All 13,675 previous declaration names,
module owners and axiom sets, all 2,396 previous result mappings, and every
previous source/declaration map survive unchanged. All other 68 assertion
records and all 69 source-statement identities are identical.

The complete declaration map includes private and generated names, original
source paths and hashes, owning modules and actual transitive axiom sets.
The verifier received only the reviewed count update and additive registrations;
its prior guards and unchanged axiom audit remained active.

The development archive retains 55 genuine
focused attempts (16 exited zero,
39 failed) across
1,258 evidence files. Original commands,
failed source snapshots, warnings and concurrent input-change records are
preserved. Early uses of `-KwarningAsError=true` were not a strict warning gate;
the final complete gate uses `--wfail`. Only this final frozen execution is
release acceptance evidence.

## Exact evidence links

- [Actual command and terminal receipt](full-01/command.json)
- [Raw complete command output](full-01/output.log)
- [Strict build log](full-01/artifacts/verification/build.log)
- [Raw transitive axiom audit](full-01/artifacts/verification/axioms.log)
- [Complete verifier results](full-01/artifacts/verification/results.json)
- [Complete new declaration map](full-01/artifacts/verification/global-factorization-declarations.json)
- [Frozen source/input inventory](full-01/frozen-inputs.json)
- [Frozen controls](full-01/frozen-controls.json)
- [Preservation report](preservation.json)
- [Development inventory](development-index.json)
- [Independent single-core review](independent-single-core-review.md)
- [Independent four-regular review](independent-four-regular-review.md)
- [Independent verification-integrity review](independent-verification-review.md)

Publication is a separate step. Its exact Git tree and both branch heads must
be read back; this verification report alone does not assert publication.
