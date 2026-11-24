#!/usr/bin/env python3
"""Register one new map through exact additive changes to the existing verifier."""
import json
from pathlib import Path
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "3991bb7eee091a329046073e0366daa84a603e5d"
old = subprocess.check_output(["git", "show", f"{BASELINE}:scripts/verify.py"], cwd=ROOT, text=True)
edits = []


def add(anchor, replacement):
    global old
    if old.count(anchor) != 1 or anchor not in replacement:
        raise ValueError("Ambiguous or nonadditive verifier registration")
    edits.append({"old": anchor, "new": replacement})
    old = old.replace(anchor, replacement, 1)


anchor = '                          ("four_label_reduction", "four-label-reduction-source.json"),\n'
add(anchor, anchor + '                          ("four_label_existence", "four-label-existence-source.json"),\n')
anchor = '    # Every first-party mathematical file must be included in the library build.\n'
guard = '''    four_existence_source, _, four_existence_public = extension_maps["four_label_existence"]
    if (four_existence_source["kind"] != "supporting_continuation"
            or four_existence_source["numbered_assertions_completed"] != 0
            or four_existence_source["main_theorem_verified"] is not False
            or four_existence_source["public_theorems"] != [
                "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label",
                "Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_four",
                "Overfull.Multigraph.exists_safe_short_circuit_of_four_strictNonlocal",
                "Overfull.FourOdd.exists_compatibleCircuitPartition_of_tight_shore",
                "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers",
                "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_degree_bound",
                "Overfull.FourOdd.exists_fourTwoOddJoining_decomposition"]
            or not set(four_existence_source["public_theorems"]) <= set(four_existence_public)):
        raise SystemExit("Four-label existence closes no additional numbered manuscript assertion.")

'''
add(anchor, guard + anchor)
anchor = '                    "four_label_reduction": "four-label-reduction",\n'
add(anchor, anchor + '                    "four_label_existence": "four-label-existence",\n')
anchor = '        "four_label_reduction_declaration_map": extension_evidence["four_label_reduction"],\n'
add(anchor, anchor + '        "four_label_existence_declaration_map": extension_evidence["four_label_existence"],\n')
(ROOT / "scripts/verify.py").write_text(old)
(RUN / "verifier-additions.json").write_text(json.dumps(edits, indent=2) + "\n")
(RUN / "verifier-registration.patch").write_bytes(subprocess.check_output(
    ["git", "diff", "--", "scripts/verify.py"], cwd=ROOT))
print(f"Registered {len(edits)} exact additive verifier changes.")

if "--root-imports" in sys.argv:
    imports = ["import Overfull.CompatibleCircuits.FourJoiningComplete\n",
               "import Overfull.CompatibleCircuits.FourCharacterization\n"]
    before = subprocess.check_output(["git", "show", f"{BASELINE}:Overfull.lean"], cwd=ROOT, text=True)
    split = before.index("\n/-!")
    (ROOT / "Overfull.lean").write_text(before[:split] + "".join(imports) + before[split:])
    (RUN / "root-added-imports.json").write_text(json.dumps(imports, indent=2) + "\n")
    print(f"Added {len(imports)} root imports after the unchanged existing imports.")
