#!/usr/bin/env python3
"""Read-only final preflight; this is not a full verifier pass."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("preservation", RUN / "check-preservation.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
result = checks.preflight()
result["kind"] = "final_preflight_only"
result["current_input_count"] = len(checks.current_inputs())
result["current_control_count"] = len(checks.current_controls())
print(json.dumps(result, indent=2))
