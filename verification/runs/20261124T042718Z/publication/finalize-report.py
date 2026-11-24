#!/usr/bin/env python3
"""Write a human-readable report only from a genuine successful frozen run."""
from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT=Path('/workspace/scratch/5793769ed3f4/overfull-lean')
RUN=ROOT/'verification/runs/20261124T042718Z'
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    preservation=read(RUN/'preservation.json')
    assert preservation['status']=='passed'
    attempt=preservation['full_verifier_attempt']
    folder=RUN/attempt
    receipt=read(folder/'command.json')
    assert receipt['status']=='passed' and receipt['exit_code']==0
    assert receipt['inputs_unchanged'] and receipt['controls_unchanged']
    assert preservation['genuine_command_receipt_sha256']==sha(folder/'command.json')
    result=read(ROOT/'verification/results.json')
    manifest=read(ROOT/'docs/global-factorization-source.json')
    development=read(RUN/'development-index.json')
    assert result['lean_build_passed'] and result['axiom_audit_passed']
    assert result['fully_verified_numbered_assertion_count']==49
    assert result['main_theorem_verified'] is False
    frozen=read(folder/'frozen-inputs.json')
    assert {**result['source_sha256'],**result['verification_input_sha256']}==frozen
    assert all(sha(ROOT/path)==digest for path,digest in frozen.items())
    jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(ROOT/'verification/build.log').read_text())
    assert jobs
    axioms=sorted({a for d in result['verified_declarations'] for a in d['axioms']})
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    summary={
      'schema_version':1,'status':'complete_verification_and_preservation_passed',
      'attempt':attempt,'actual_command':receipt['command'],'actual_exit_code':receipt['exit_code'],
      'finished_at_utc':receipt['finished_at_utc'],'elapsed_seconds':receipt['elapsed_seconds'],
      'strict_build_jobs':int(jobs.group(1)),
      'numbered_assertions_complete':49,'numbered_assertions_total':69,
      'only_promoted_assertion':'3.1','main_theorem_verified':False,
      'new_source_modules':manifest['module_count'],'new_public_proofs':manifest['public_theorem_count'],
      'audited_declarations':result['verified_declaration_count'],
      'new_audited_declarations':result['verified_declaration_count']-13675,
      'completed_result_mappings':len(result['completed_results']),
      'frozen_input_count':len(frozen),'source_count':len(result['source_sha256']),
      'other_input_count':len(result['verification_input_sha256']),
      'observed_transitive_axioms':axioms,
      'development_attempt_count':development['attempt_count'],
      'development_status_counts':development['status_counts'],
      'development_evidence_files':development['file_count'],
      'inputs_unchanged':True,'controls_unchanged':True,
      'all_previous_declarations_owners_axiom_sets_preserved':True,
      'all_previous_completed_result_mappings_preserved':True,
      'all_previous_source_declaration_maps_preserved':True,
      'all_other_68_numbered_records_identical':True,
      'all_69_statement_identities_identical':True,
      'baseline_commit':preservation['baseline_commit'],'baseline_tree':preservation['baseline_tree'],
      'receipt_sha256':sha(folder/'command.json'),'preservation_sha256':sha(RUN/'preservation.json'),
      'results_sha256':sha(ROOT/'verification/results.json'),
      'publication_status':'Recorded separately by exact-tree and both-branch readbacks.'
    }
    (RUN/'completion-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    report=f'''# Completed verification: full single-core Lemma 3.1

The genuine complete verifier and supplementary preservation check passed.
**Numbered coverage is 49/69. The main theorem is unproved.** Only pinned
Lemma 3.1, `single:lem:coloring`, is promoted in this continuation.

## Observed execution

| Check | Actual result |
| --- | --- |
| Full command | `python3 scripts/verify.py` |
| Immutable attempt | `{attempt}` |
| Exit code | `0` |
| Strict complete Lean build | {summary['strict_build_jobs']:,} jobs, `--wfail`, passed |
| Transitive axiom audit | {summary['audited_declarations']:,} proof declarations |
| New audited declarations | {summary['new_audited_declarations']:,} |
| New public proof declarations | {summary['new_public_proofs']:,} in {summary['new_source_modules']} new modules |
| Complete result mappings | {summary['completed_result_mappings']:,} |
| Frozen inputs | {summary['frozen_input_count']:,}: {summary['source_count']} source files and {summary['other_input_count']} other inputs |
| Inputs and verification controls | Unchanged throughout execution and preservation check |
| Allowed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Actual elapsed time | {summary['elapsed_seconds']:.3f} seconds |

These values come from the actual command receipt, raw build/audit output,
complete verifier result, and the preservation report. They are not inferred
from focused builds. The receipt, raw output, full frozen input/control bytes,
and every generated output are retained under `{attempt}/`.

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

The baseline is public commit `{summary['baseline_commit']}`,
with tree `{summary['baseline_tree']}`. Every prior nonroot mathematical source
and `Audit.lean` is byte-identical. All 13,675 previous declaration names,
module owners and axiom sets, all 2,396 previous result mappings, and every
previous source/declaration map survive unchanged. All other 68 assertion
records and all 69 source-statement identities are identical.

The complete declaration map includes private and generated names, original
source paths and hashes, owning modules and actual transitive axiom sets.
The verifier received only the reviewed count update and additive registrations;
its prior guards and unchanged axiom audit remained active.

The development archive retains {summary['development_attempt_count']} genuine
focused attempts ({summary['development_status_counts']['passed']} exited zero,
{summary['development_status_counts']['failed']} failed) across
{summary['development_evidence_files']:,} evidence files. Original commands,
failed source snapshots, warnings and concurrent input-change records are
preserved. Early uses of `-KwarningAsError=true` were not a strict warning gate;
the final complete gate uses `--wfail`. Only this final frozen execution is
release acceptance evidence.

## Exact evidence links

- [Actual command and terminal receipt]({attempt}/command.json)
- [Raw complete command output]({attempt}/output.log)
- [Strict build log]({attempt}/artifacts/verification/build.log)
- [Raw transitive axiom audit]({attempt}/artifacts/verification/axioms.log)
- [Complete verifier results]({attempt}/artifacts/verification/results.json)
- [Complete new declaration map]({attempt}/artifacts/verification/global-factorization-declarations.json)
- [Frozen source/input inventory]({attempt}/frozen-inputs.json)
- [Frozen controls]({attempt}/frozen-controls.json)
- [Preservation report](preservation.json)
- [Development inventory](development-index.json)
- [Independent single-core review](independent-single-core-review.md)
- [Independent four-regular review](independent-four-regular-review.md)
- [Independent verification-integrity review](independent-verification-review.md)

Publication is a separate step. Its exact Git tree and both branch heads must
be read back; this verification report alone does not assert publication.
'''
    (RUN/'execution-report.md').write_text(report)
    publication=RUN/'publication';publication.mkdir(exist_ok=True)
    for name in ['prepare.py','selftest-result.json','finalize-report.py']:
        source=Path('/workspace/scratch/5793769ed3f4/publication-work')/name
        shutil.copy2(source,publication/name)
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
