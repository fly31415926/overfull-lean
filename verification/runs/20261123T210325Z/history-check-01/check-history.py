#!/usr/bin/env python3
"""Run only read-only historical/import-order helpers, never the final checker."""
from pathlib import Path
import json
import runpy
import subprocess
import sys


RUN = Path(__file__).resolve().parent.parent
ROOT = RUN.parents[2]
if len(sys.argv) != 2:
    raise SystemExit("Usage: check-history.py ACTUAL_NATIVE_VERIFIED_SHA")
parent = sys.argv[1]
namespace = runpy.run_path(str(RUN / "record-final.py"), run_name="read_only_history_diagnostic")
previous = json.loads(subprocess.check_output(
    ["git", "show", f"{parent}:verification/results.json"], cwd=ROOT))
latest = json.loads((RUN / "full-04/command.json").read_text(encoding="utf-8"))
if latest["attempt"] != "full-04":
    raise SystemExit("The diagnostic must inspect the actual full-04 attempt metadata")
before = {item["name"]: (item["module"], frozenset(item["axioms"]))
          for item in previous["verified_declarations"]}
history, preservation_records = namespace["check_prior_preservation_failure"](parent, previous, latest)
correction, probe_records = namespace["check_import_order_correction"](parent, before, latest, history)
print(json.dumps({
    "status": "read_only_historical_and_import_order_helpers_passed",
    "scope": "Historical full-03 evidence, failed preservation check, root correction and targeted probe only.",
    "final_checker_main_executed": False,
    "current_full_verifier_executed": False,
    "current_full_verifier_attempt_observed": latest["attempt"],
    "current_full_verifier_status_observed": latest["status"],
    "current_full_verifier_pass_claimed": False,
    "parent_verified_commit": parent,
    "historical_full_03": history,
    "import_order_correction": correction,
    "supplementary_preservation_command_count": len(preservation_records),
    "targeted_probe_command_count": len(probe_records),
}, indent=2))
