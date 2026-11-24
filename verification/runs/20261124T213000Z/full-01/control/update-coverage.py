#!/usr/bin/env python3
"""Register exactly the two reviewed complete endpoints; full verification is separate."""
import json
from pathlib import Path
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "1c9404a454c99fe5c11ba8d774cb9c259f291f20"
SPECS = [
    {
        "number": "4.16", "label": "three:prop:terminal",
        "hash": "1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c",
        "name": "Overfull.frequent_pattern_result_one_factorization",
        "file": "Overfull/TerminalFour/Result.lean",
        "component": "frequent_pattern_terminal_full",
        "scope": (
            "Complete Proposition 4.16 for the actual CircuitPatterns.FrequentPatternResult, "
            "on an arbitrary finite core index type of cardinality three or four. Uniform "
            "tolerances and the order threshold precede the host and result. The proof "
            "uses the result's actual stored pattern, forest and pair supplies, exhausts "
            "all parity cases, and constructs a one-factorization on the original copies. "
            "The positive regular no-overfull assumptions imply the ambient even order."
        ),
    },
    {
        "number": "4.17", "label": "three:thm:regular-four",
        "hash": "b271893680e87b1c06c35172a138050dbf84009964eb618dce53c53ba595e322",
        "name": "Overfull.regular_core_one_factorization",
        "file": "Overfull/FourCoreReduction/Regular.lean",
        "component": "regular_three_four_core_full",
        "scope": (
            "Complete Theorem 4.17 for the original even-order finite simple regular "
            "host with no overfull set, three or four disjoint robust cores, and the "
            "exceptional set. The original linear budget a + |Z| + 1 <= epsilon*n is "
            "retained. An arbitrary positive density is normalized internally, the "
            "core error's nonnegativity is derived, and all tolerances precede the host. "
            "The whole tolerance function is chosen before bounded absorption fixes "
            "its exceptional bound. All prefixes are restored on original edge copies."
        ),
    },
]


def previous(name):
    return json.loads(subprocess.check_output(["git", "show", f"{BASELINE}:{name}"], cwd=ROOT))


def main():
    coverage = previous("docs/coverage.json")
    source = previous("docs/manuscript-source.json")
    for spec in SPECS:
        assertion = next(a for a in coverage["numbered_assertions"] if a["number"] == spec["number"])
        assert assertion["statement_sha256"] == spec["hash"]
        assert assertion["labels"] == [spec["label"]]
        assert assertion["full_assertion_verified"] is False
        assertion.update({
            "full_assertion_verified": True,
            "status": "fully_verified",
            "checked_components": [spec["component"]],
            "formalization_scope": spec["scope"],
            "lean_theorems": [spec["name"]],
        })
        coverage["checked_component_catalog"].append({
            "id": spec["component"], "kind": "graph_theoretic_result",
            "description": spec["scope"], "lean_declarations": [spec["name"]],
            "scope_limit": "Exact pinned numbered assertion; the main theorem remains unverified.",
            "manuscript_locations": [spec["label"]],
        })
        source["additional_complete_results"].append({
            "lean_name": spec["name"], "file": spec["file"],
            "manuscript_label": spec["label"], "manuscript_number": spec["number"],
            "statement_sha256": spec["hash"], "proved": True,
            "scope": spec["scope"],
            "source_manifest": "four-core-continuation-source.json",
            "semantic_review": "four-core-continuation-semantic-review.md",
        })
    coverage["fully_verified_numbered_assertion_count"] = 51
    coverage["scope"] = (
        "The current four-core continuation completes the exact pinned Proposition 4.16 "
        "and Theorem 4.17, bringing complete numbered coverage to 51 of 69 after a "
        "successful genuine full verification and preservation check. The main theorem "
        "remains unverified. All other 67 numbered records and all 69 statement identities "
        "are preserved. Historical scope descriptions in unchanged earlier records "
        "describe their corresponding checkpoints. " + " ".join(s["scope"] for s in SPECS)
    )
    source["fully_verified_numbered_assertions"] = 51
    for name, value in [("docs/coverage.json", coverage), ("docs/manuscript-source.json", source)]:
        (ROOT / name).write_text(json.dumps(value, indent=2) + "\n")
    print("Registered only 4.16 and 4.17; all statement identities are unchanged. Full verification is required.")


if __name__ == "__main__":
    main()
