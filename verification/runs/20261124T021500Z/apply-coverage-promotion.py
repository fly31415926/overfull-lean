#!/usr/bin/env python3
"""Install the reviewed Corollary 4.6 candidate after its strict target pass.

This is candidate bookkeeping, not a claim that the complete frozen verifier
or the unchanged full axiom audit has run. Every allowed edit is recorded.
"""
from datetime import datetime, timezone
import copy
import hashlib
import json
from pathlib import Path
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "f557ae03355f14a0441b37283f35186a95aca2d7"
STATEMENT = "86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26"
PUBLIC = ["Overfull.bounded_input_factorization", "Overfull.bounded_input_one_factorization"]
SCOPE = (
    "Complete Corollary 4.6 for even regular multigraphs with no overfull set and either "
    "one robust core with at most three exceptional vertices or two robust cores with at "
    "most two exceptional vertices. Fixed positive degree and core-order densities and "
    "robust parameters precede one common positive core-error tolerance and order threshold. "
    "The conclusion constructs a coloring and an exact partition of all original edge copies "
    "into k perfect matchings. No representative matching, reserve, complementary coloring or "
    "residual factorization is assumed. Full fixed-pattern Lemma 4.4, five-exception "
    "Corollary 4.5, terminal Proposition 4.16 and the main theorem remain unproved."
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def old(path):
    return subprocess.check_output(["git", "show", BASELINE + ":" + path], cwd=ROOT)


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def main():
    receipt_path = RUN / "development/bounded-input-001/command.json"
    receipt = json.loads(receipt_path.read_text())
    require(receipt["command"] == ["lake", "build", "--wfail", "Overfull.NativeTerminal.BoundedInput"]
            and receipt["status"] == "passed" and receipt["exit_code"] == 0
            and receipt["inputs_changed_during_command"] == [],
            "The actual strict BoundedInput target has not passed with stable inputs")
    review_path = RUN / "independent-review/bounded-input-source-review.json"
    review = json.loads(review_path.read_text())
    require(review["statement_sha256"] == STATEMENT
            and review["exact_statement_sha256_independently_recomputed"] is True,
            "The source statement semantic review is unavailable")
    for path, expected in review["sources_reviewed_sha256"].items():
        require(sha((ROOT / path).read_bytes()) == expected, "A reviewed source changed: " + path)
    require(not (RUN / "promotion-applied.json").exists(), "The promotion is already recorded")
    before_bytes = {p: (ROOT / p).read_bytes() for p in [
        "docs/coverage.json", "docs/manuscript-source.json", "scripts/verify.py",
        "scripts/update_native_terminal_manifest.py"]}
    for path in ["docs/coverage.json", "docs/manuscript-source.json", "scripts/verify.py"]:
        require(before_bytes[path] == old(path), "Unexpected pre-promotion edit: " + path)

    coverage = json.loads(before_bytes["docs/coverage.json"])
    assertion = next(x for x in coverage["numbered_assertions"] if x["number"] == "4.6")
    assertion_before = copy.deepcopy(assertion)
    component = {
        "id": "bounded_input_full", "kind": "graph_theoretic_result",
        "description": SCOPE,
        "lean_declarations": [*PUBLIC,
            "Overfull.one_core_three_exception_factorization",
            "Overfull.one_core_three_exception_one_factorization",
            "Overfull.two_core_two_exception_factorization",
            "Overfull.two_core_two_exception_one_factorization"],
        "scope_limit": "Complete Corollary 4.6 under both source alternatives; the main theorem and the separate stronger five-exception and general terminal assertions remain unproved.",
        "manuscript_locations": ["three:lem:bounded-input"]}
    require(not assertion["full_assertion_verified"] and assertion["statement_sha256"] == STATEMENT,
            "The original assertion identity or status differs")
    require(all(x["id"] != component["id"] for x in coverage["checked_component_catalog"]),
            "The complete bounded-input component already exists")
    assertion.update({"full_assertion_verified": True, "status": "fully_verified",
                      "lean_theorems": PUBLIC, "formalization_scope": SCOPE})
    assertion["checked_components"].append(component["id"])
    coverage["checked_component_catalog"].append(component)
    coverage["fully_verified_numbered_assertion_count"] = 48
    coverage["scope"] = SCOPE + " The current candidate has 48 of 69 complete numbered assertions; the full frozen verifier and axiom audit establish its verification status."
    write_json(ROOT / "docs/coverage.json", coverage)

    manuscript = json.loads(before_bytes["docs/manuscript-source.json"])
    require(manuscript["fully_verified_numbered_assertions"] == 47, "Unexpected manuscript count")
    manuscript["fully_verified_numbered_assertions"] = 48
    write_json(ROOT / "docs/manuscript-source.json", manuscript)

    generator = before_bytes["scripts/update_native_terminal_manifest.py"].decode()
    generator = generator.replace("'schema_version': 1, 'kind': 'supporting_continuation',",
                                  "'schema_version': 1, 'kind': 'complete_assertion_source_mapping',")
    generator = generator.replace("        'numbered_assertions_completed': 0, 'main_theorem_verified': False,",
                                  "        'numbered_assertions_completed': 1, 'main_theorem_verified': False,\n"
                                  "        'manuscript_number': '4.6',\n"
                                  "        'manuscript_label': 'three:lem:bounded-input',\n"
                                  "        'statement_sha256': '" + STATEMENT + "',\n"
                                  "        'public_theorems': " + repr(PUBLIC) + ",")
    lines = generator.splitlines(keepends=True)
    require(sum(line.startswith("        'scope': ") for line in lines) == 1,
            "Ambiguous source-generator scope field")
    generator = "".join("        'scope': " + repr(SCOPE) + ",\n"
                        if line.startswith("        'scope': ") else line for line in lines)
    (ROOT / "scripts/update_native_terminal_manifest.py").write_text(generator)

    edits = json.loads((RUN / "verifier-additions.json").read_text())
    edits[1]["new"] = (
        '    terminal_source, terminal_modules, terminal_public_modules = extension_maps["native_terminal"]\n'
        '    if (terminal_source["kind"] != "complete_assertion_source_mapping"\n'
        '            or terminal_source["manuscript_number"] != "4.6"\n'
        '            or terminal_source["manuscript_label"] != "three:lem:bounded-input"\n'
        '            or terminal_source["statement_sha256"] != "' + STATEMENT + '"\n'
        '            or terminal_source["numbered_assertions_completed"] != 1\n'
        '            or terminal_source["public_theorems"] != [\n'
        '                "Overfull.bounded_input_factorization", "Overfull.bounded_input_one_factorization"]\n'
        '            or not set(terminal_source["public_theorems"]) <= set(terminal_public_modules)):\n'
        '        raise SystemExit("The terminal closure does not identify the exact complete Corollary 4.6.")\n\n'
        '    # Every first-party mathematical file must be included in the library build.\n')
    edits += [
        {"old": "COMPLETED_NUMBERED_ASSERTION_COUNT = 47\n",
         "new": "COMPLETED_NUMBERED_ASSERTION_COUNT = 48\n"},
        {"old": '    for number in ("2.24", "4.4", "4.5", "4.6", "4.16", "6.1", "6.2", "6.3"):\n',
         "new": '    for number in ("2.24", "4.4", "4.5", "4.16", "6.1", "6.2", "6.3"):\n'},
        {"old": '    ordinary_assertion = next(a for a in coverage["numbered_assertions"] if a["number"] == "4.2")\n',
         "new":
            '    bounded_assertion = next(a for a in coverage["numbered_assertions"] if a["number"] == "4.6")\n'
            '    bounded_source_assertion = next(a for a in few_source["source_assertions"] if a["number"] == "4.6")\n'
            '    if (not bounded_assertion["full_assertion_verified"]\n'
            '            or bounded_assertion["status"] != "fully_verified"\n'
            '            or bounded_assertion.get("lean_theorems") != terminal_source["public_theorems"]\n'
            '            or not set(bounded_assertion["lean_theorems"]) <= audited_names\n'
            '            or bounded_assertion["statement_sha256"] != terminal_source["statement_sha256"]\n'
            '            or bounded_assertion["statement_sha256"] != bounded_source_assertion["statement_sha256"]):\n'
            '        raise SystemExit("Full bounded-input factorization is not mapped to the exact complete Corollary 4.6.")\n'
            '    ordinary_assertion = next(a for a in coverage["numbered_assertions"] if a["number"] == "4.2")\n'}]
    verifier = before_bytes["scripts/verify.py"].decode()
    for edit in edits:
        require(verifier.count(edit["old"]) == 1, "An exact reviewed verifier edit is ambiguous")
        verifier = verifier.replace(edit["old"], edit["new"], 1)
    compile(verifier, "scripts/verify.py", "exec")
    compile(generator, "scripts/update_native_terminal_manifest.py", "exec")
    (ROOT / "scripts/verify.py").write_text(verifier)
    write_json(RUN / "verifier-additions.json", edits)

    plan = json.loads((RUN / "promotion-plan.json").read_text())
    plan.update({"status": "applied_to_candidate_pending_complete_verification",
                 "assertion_before": assertion_before, "assertion_after": assertion,
                 "new_component": component,
                 "coverage_permitted_top_level_fields": ["scope", "fully_verified_numbered_assertion_count",
                                                         "numbered_assertions", "checked_component_catalog"],
                 "assertion_4_6_permitted_changed_fields": ["full_assertion_verified", "status", "formalization_scope",
                                                          "lean_theorems", "checked_components"],
                 "existing_checked_component_catalog_entries_exact": True,
                 "new_component_count": 1,
                 "exact_verifier_edit_count": len(edits)})
    write_json(RUN / "promotion-plan.json", plan)
    changed = {path: {"before_sha256": sha(data), "after_sha256": sha((ROOT / path).read_bytes())}
               for path, data in before_bytes.items()}
    write_json(RUN / "promotion-applied.json", {
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "kind": "reviewed_candidate_promotion_after_actual_strict_target_success",
        "baseline": BASELINE, "assertion": "4.6", "statement_sha256": STATEMENT,
        "strict_target_receipt": receipt_path.relative_to(ROOT).as_posix(),
        "strict_target_receipt_sha256": sha(receipt_path.read_bytes()),
        "semantic_review_path": review_path.relative_to(ROOT).as_posix(),
        "semantic_review_sha256": sha(review_path.read_bytes()),
        "changed_files": changed, "exact_verifier_edit_count": len(edits),
        "complete_frozen_verifier_and_full_audit_run_by_this_script": False})
    print("Applied only reviewed complete-4.6 candidate bookkeeping: 48/69, exact seven verifier substitutions.")
    print("Strict target success and semantic source review are recorded; full frozen verification remains required.")


if __name__ == "__main__":
    main()
