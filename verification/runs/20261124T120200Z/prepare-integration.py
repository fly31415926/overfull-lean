#!/usr/bin/env python3
"""Register only the new source/declaration map; retain every existing verifier guard."""
import json
from pathlib import Path
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8"

old = subprocess.check_output(
    ["git", "show", f"{BASELINE}:scripts/verify.py"], cwd=ROOT, text=True)
edits = []


def add(anchor, replacement):
    global old
    if old.count(anchor) != 1 or anchor not in replacement:
        raise ValueError("Ambiguous or nonadditive verifier registration")
    edits.append({"old": anchor, "new": replacement})
    old = old.replace(anchor, replacement, 1)


anchor = '                          ("three_core_terminal", "three-core-terminal-source.json"),\n'
add(anchor, anchor + '                          ("four_label_reduction", "four-label-reduction-source.json"),\n')

anchor = '    # Every first-party mathematical file must be included in the library build.\n'
guard = '''    four_label_source, _, four_label_public = extension_maps["four_label_reduction"]
    if (four_label_source["kind"] != "supporting_continuation"
            or four_label_source["numbered_assertions_completed"] != 0
            or four_label_source["main_theorem_verified"] is not False
            or four_label_source["public_theorems"] != [
                "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_small_degree",
                "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_degree_le_four",
                "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_card_le_eight",
                "Overfull.Multigraph.fourLabel_counterexample_degree_and_size",
                "Overfull.Multigraph.fourLabel_admissibleOn_sdiff_iff_cut_witnesses",
                "Overfull.Multigraph.exists_globally_admissible_localCoarsening",
                "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_small_cut",
                "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_bounded_cuts",
                "Overfull.FourOdd.exists_fourTwoOddJoining_decomposition_of_small_even_cut"]
            or not set(four_label_source["public_theorems"]) <= set(four_label_public)):
        raise SystemExit("The four-label reduction completes no additional numbered assertion.")

'''
add(anchor, guard + anchor)

anchor = '                    "three_core_terminal": "three-core-terminal",\n'
add(anchor, anchor + '                    "four_label_reduction": "four-label-reduction",\n')

anchor = '        "global_factorization_declaration_map": extension_evidence["global_factorization"],\n'
add(anchor, anchor + '        "four_label_reduction_declaration_map": extension_evidence["four_label_reduction"],\n')

(ROOT / "scripts/verify.py").write_text(old)
(RUN / "verifier-additions.json").write_text(json.dumps(edits, indent=2) + "\n")
diff = subprocess.check_output(["git", "diff", "--", "scripts/verify.py"], cwd=ROOT)
(RUN / "verifier-registration.patch").write_bytes(diff)
print(f"Registered {len(edits)} exact additive verifier changes.")

if "--root-imports" in sys.argv:
    imports = ["import Overfull.CompatibleCircuits.FourCutCriterion\n",
               "import Overfull.CompatibleCircuits.FourGlobalCoarsening\n",
               "import Overfull.CompatibleCircuits.FourTriangleSelection\n",
               "import Overfull.CompatibleCircuits.FourBoundedJoining\n"]
    root_before = subprocess.check_output(
        ["git", "show", f"{BASELINE}:Overfull.lean"], cwd=ROOT, text=True)
    split = root_before.index("\n/-!")
    root_after = root_before[:split] + "".join(imports) + root_before[split:]
    (ROOT / "Overfull.lean").write_text(root_after)
    (RUN / "root-added-imports.json").write_text(json.dumps(imports, indent=2) + "\n")
    print(f"Added {len(imports)} root imports at the end of the unchanged baseline import list.")
