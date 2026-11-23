#!/usr/bin/env python3
"""Record this run's genuine verification and preservation evidence.

Run only after scripts/verify.py and its command recorder finish successfully.
This does not replace or modify the stock Lean axiom audit.
"""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[3]
RUN = Path(__file__).resolve().parent
BASE = "b5afb03a0f0613eedd0cb3310e06706942afe2e7"
START = "2026-11-22T23:59:31+00:00"


def old_bytes(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    command = json.loads((RUN / "verification-command.json").read_text())
    assert command["exit_code"] == 0, "Complete verifier did not pass"
    current = json.loads((ROOT / "verification/results.json").read_text())
    previous = json.loads(old_bytes("verification/results.json"))
    assert current["lean_build_passed"] and current["axiom_audit_passed"]
    before = {d["name"]: (d["module"], frozenset(d["axioms"]))
              for d in previous["verified_declarations"]}
    after = {d["name"]: (d["module"], frozenset(d["axioms"]))
             for d in current["verified_declarations"]}
    missing = sorted(set(before) - set(after))
    changed = sorted(n for n in before.keys() & after.keys() if before[n] != after[n])
    assert not missing and not changed, (missing, changed)
    unchanged_sources = []
    for path, digest in previous["source_sha256"].items():
        if path == "Overfull.lean":
            continue
        assert sha(ROOT / path) == digest, path
        unchanged_sources.append(path)
    new_root = (ROOT / "Overfull.lean").read_text().splitlines()
    new_root.remove("import Overfull.CompatibleCircuits.AtMostThree")
    assert new_root == old_bytes("Overfull.lean").decode().splitlines()
    for mapping in ("source_sha256", "verification_input_sha256"):
        for path, digest in current[mapping].items():
            assert sha(ROOT / path) == digest, (mapping, path)
    expected_sources = {"Overfull.lean", "Audit.lean"} | {
        p.relative_to(ROOT).as_posix() for p in (ROOT / "Overfull").rglob("*.lean")
    }
    assert set(current["source_sha256"]) == expected_sources
    expected_inputs = {
        p.relative_to(ROOT).as_posix() for p in [
            ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
            ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
            *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
            *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
            ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
            ROOT / "LICENSE_BMATCHING.txt",
        ]
    }
    assert set(current["verification_input_sha256"]) == expected_inputs
    old_coverage = json.loads(old_bytes("docs/coverage.json"))
    coverage = json.loads((ROOT / "docs/coverage.json").read_text())
    statements = lambda c: [(a["number"], a["statement_sha256"])
                            for a in c["numbered_assertions"]]
    complete = lambda c: [a for a in c["numbered_assertions"] if a["full_assertion_verified"]]
    assert statements(old_coverage) == statements(coverage)
    assert complete(old_coverage) == complete(coverage)
    assert len(complete(coverage)) == 47 and not coverage["main_theorem_verified"]
    old_maps = ["four-odd-declarations.json", "residual-factorization-declarations.json",
                "boundary-extension-full-declarations.json",
                "ordinary-factorization-full-declarations.json", "few-exception-declarations.json"]
    for name in old_maps:
        assert (ROOT / "verification" / name).read_bytes() == old_bytes("verification/" + name)
    source = json.loads((ROOT / "docs/three-label-circuit-source.json").read_text())
    evidence = json.loads((ROOT / "verification/three-label-circuit-declarations.json").read_text())
    assert set(source["required_proof_declarations"]) <= set(after)
    audited_log = (ROOT / "verification/axioms.log").read_text()
    assert f"OVERFULL_AXIOM_AUDIT_OK {len(after)}" in audited_log
    jobs = int(re.search(r"Build completed successfully \((\d+) jobs\)",
                         (ROOT / "verification/build.log").read_text()).group(1))
    finished = datetime.now(timezone.utc)
    evidence_paths = [
        "verification/results.json", "verification/build.log", "verification/axioms.log",
        "verification/three-label-circuit-declarations.json",
        "docs/three-label-circuit-source.json", "docs/continuation-handoff.md",
        *(p.relative_to(ROOT).as_posix() for p in [
            RUN / "public-name-check.lean", RUN / "public-name-check.log",
            RUN / "verification-command.json", RUN / "verification-console.log",
            RUN / "build-passed-checkpoint.json", RUN / "record_run.py",
        ]),
    ]
    assessment = RUN / "next-target-assessment.md"
    if assessment.exists():
        evidence_paths.append(assessment.relative_to(ROOT).as_posix())
    recovered_statements = {}
    recovery = RUN / "manuscript-recovery.md"
    if recovery.exists():
        expected_statements = {a["number"]: a["statement_sha256"]
                               for a in coverage["numbered_assertions"]}
        identity = json.loads((RUN / "source-statement-hash-check.json").read_text())
        assert not identity["source_text_published"]
        assert len(identity["checks"]) == 3
        assert {c["number"] for c in identity["checks"]} == {"4.4", "4.5", "4.6"}
        for check in identity["checks"]:
            number, digest = check["number"], check["statement_sha256"]
            assert check["matches_pinned_inventory"] and digest == expected_statements[number]
            recovered_statements[number] = digest
        evidence_paths.append(recovery.relative_to(ROOT).as_posix())
        evidence_paths.extend((RUN / name).relative_to(ROOT).as_posix() for name in [
            "source-statement-hash-check.json", "source-statement-hash-check.log",
            "publication-restriction.json",
        ])
    record = {
        "schema_version": 1,
        "status": "verification_passed",
        "run_id": RUN.name,
        "run_started_at_utc": START,
        "recorded_at_utc": finished.isoformat(),
        "elapsed_seconds_to_record": round((finished - datetime.fromisoformat(START)).total_seconds(), 3),
        "baseline_commit": BASE,
        "interim_recovery_commit": "af6c68a561b0beae97d693b6ee099a230a294988",
        "verification_command": command,
        "strict_build_jobs": jobs,
        "verified_declaration_count": len(after),
        "previous_verified_declarations_preserved": len(before),
        "new_verified_declaration_count": len(set(after) - set(before)),
        "all_prior_declaration_names_modules_and_axiom_sets_preserved": True,
        "all_previous_nonroot_lean_sources_byte_identical": True,
        "byte_identical_previous_nonroot_lean_source_count": len(unchanged_sources),
        "root_change": "One new import; every previous line preserved.",
        "stock_audit_byte_identical": True,
        "source_hash_count": len(current["source_sha256"]),
        "verification_input_hash_count": len(current["verification_input_sha256"]),
        "imported_project_module_count": len(current["imported_project_modules"]),
        "all_recorded_hashes_match_current_files": True,
        "all_current_source_and_verification_input_paths_recorded": True,
        "all_69_original_statement_hashes_preserved": True,
        "all_47_previous_completed_assertion_records_preserved": True,
        "recovered_original_statement_hashes": recovered_statements,
        "recovered_manuscript_text_published": False,
        "recovered_manuscript_text_release": "Withheld after automatic approval review; explicit approval required for public source excerpts.",
        "extended_next_target_assessment_published": False,
        "fully_verified_numbered_assertion_count": 47,
        "remaining_numbered_assertion_count": 22,
        "main_theorem_verified": False,
        "new_module_count": source["module_count"],
        "new_public_theorem_count": source["public_theorem_count"],
        "new_module_audited_declaration_count": evidence["verified_declaration_count"],
        "previous_declaration_maps_preserved": old_maps,
        "allowed_logical_axioms": current["allowed_logical_axioms"],
        "evidence_sha256": {path: sha(ROOT / path) for path in evidence_paths},
        "publication": {
            "repository": "fly31415926/overfull-lean",
            "target_branches": ["main", "verified-bipartite-continuation-2026-11-21"],
            "note": "Verification record generated before branch updates. The containing publication commit identifies this tree; the delivery report verifies both remote branch heads.",
        },
        "scope": source["scope"],
    }
    (RUN / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    report = f"""# First continuation run: complete compatible circuits on at most three vertices

**Verification passed.** The complete original half-cut and even-degree
hypotheses now yield an exact compatible circuit partition on every finite
vertex type of cardinality at most three. All selected pieces retain the
original edge copies. The theorem allows arbitrary class types, parallel
multiplicities, isolated vertices and empty selected copy sets.

Run began at `{START}`; this verification record was completed at
`{finished.isoformat()}`. The base was `{BASE}`. An interim recovery
checkpoint, `af6c68a561b0beae97d693b6ee099a230a294988`, preserved the sources
while the full audit was running.

## Genuine checks

| Check | Result |
| --- | --- |
| Complete verifier | Exit 0 |
| Strict repository build | {jobs:,} jobs passed |
| Unchanged full axiom audit | {len(after):,} declarations passed |
| Previous audited declarations preserved | {len(before):,}, with unchanged modules and axiom sets |
| New audited declarations | {len(set(after) - set(before)):,} |
| New proof modules | {source['module_count']} |
| New mapped public theorems | {source['public_theorem_count']} |
| Recorded Lean source hashes | {len(current['source_sha256'])} |
| Recorded verification input hashes | {len(current['verification_input_sha256'])} |
| Numbered manuscript assertions | 47/69 complete; 22 remain |

The only allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. All {len(unchanged_sources)} pre-existing non-root Lean sources,
including `Audit.lean`, are byte-identical to the base. The root gains one
import and retains every previous line. All 69 original statement hashes,
all 47 completed assertion records, and all five older declaration maps
are preserved. `run.json` records exact evidence hashes.

## New proof and precise scope

The construction proves local tight-class coarsening, unequal-bundle safe
pair selection, equal-bundle safe pair/triangle selection, exact singleton
cut reduction, actual vertex renaming, the unconditional three-label
selector, strong induction with exact disjoint coverage, and injective
padding to arbitrary finite vertex types with at most three vertices.

The final interface is
`Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_three`.
It assumes neither a selector nor a pre-existing compatible partition.
The iff theorem proves necessity and sufficiency under even degrees.
The independent semantic review is in
`docs/three-label-circuit-semantic-review.md`; the complete source and
public declaration inventory is in `docs/three-label-circuit-source.json`.

No numbered assertion is newly declared complete. General four-label
compatible circuits, the remaining original-host joining construction in
the two-core branch of 4.6, terminal 4.16, general Section 6 and the main
theorem remain open. The original reconstructed `cb05ef5` provenance is
preserved and is not confused with this new run.

## Development corrections and continuation

Targeted compiler iterations corrected decidability-instance rewrites,
an implication-notation syntax error, and a specialized parallel-pair
helper that duplicated an existing declaration. The duplicate was removed
and the existing checked theorem reused. No admission, additional axiom,
weakened original hypothesis, or disabled verification gate was retained.
Earlier targeted failures are summarized here; their raw terminal output
was not separately captured in the published log files. The retained
public-name check and full-verifier logs contain their actual command output.

Read `docs/continuation-handoff.md` and `next-target-assessment.md` in this
run directory before continuing. `manuscript-recovery.md` records the
source-identity check result for statements 4.4, 4.5 and 4.6: all three
hashes matched the pinned original inventory. Automatic approval review
blocked public upload of the recovered manuscript excerpts because they
came from a private workspace. The actual hash-check output is retained,
but all recovered statement and proof text is withheld; it cannot be
rehashed from the public record alone. Identity of the entire newer
manuscript or its proof text is not claimed. The extended source
assessment was also withheld after automatic approval review. The public
target file points to the checked Lean interface and existing handoff
for remaining proof obligations. The new Lean proofs
were completed before the separate source-recovery task.

This report records verification, before the remote branch update. The
containing publication commit and final delivery identify the published
state and confirm both requested branches.
"""
    (RUN / "report.md").write_text(report)
    print(json.dumps({key: record[key] for key in [
        "status", "verified_declaration_count", "new_verified_declaration_count",
        "previous_verified_declarations_preserved", "source_hash_count",
        "verification_input_hash_count", "new_module_count", "new_public_theorem_count",
    ]}))


if __name__ == "__main__":
    main()
