"""Recheck the already authorized Corollary 4.6 statement identity."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[4]
source = root / "verification/runs/20261122T235931Z/authorized-manuscript-recovery.md"
text = source.read_text()
match = re.search(r"## Exact statement 4\.6\n.*?```tex\n(.*?)\n```", text, re.S)
if match is None:
    raise SystemExit("Exact authorized Corollary 4.6 block not found")
statement = match.group(1).encode()
coverage = json.loads((root / "docs/coverage.json").read_text())
entry = next(item for item in coverage["numbered_assertions"] if item["number"] == "4.6")
digest = hashlib.sha256(statement).hexdigest()
result = {
    "assertion": "4.6",
    "source_path": str(source),
    "source_report_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "statement_bytes": len(statement),
    "statement_sha256": digest,
    "expected_statement_sha256": entry["statement_sha256"],
    "matches_pinned_statement": digest == entry["statement_sha256"],
    "scope": "Statement identity only; this is not a Lean compiler or semantic proof check.",
}
print(json.dumps(result, indent=2))
if not result["matches_pinned_statement"]:
    raise SystemExit(1)
