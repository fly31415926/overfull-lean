#!/usr/bin/env python3
"""Map reviewed assigned-part sources; this does not verify proofs.

Run scripts/verify.py after refreshing this mapping. The verifier checks all
listed public theorem names and modules against its complete fresh audit.
"""

import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "PairFiberParity", "ThreePartLabels", "Basic",
    "MatchedCuts", "JoiningConstruction",
)


def main() -> None:
    modules = []
    for name in MODULES:
        path = ROOT / "Overfull" / "AssignedParts" / (name + ".lean")
        if not path.is_file():
            raise SystemExit(f"Missing reviewed source: {path}")
        namespaces = []
        declarations = []
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            if match := re.match(r"^namespace\s+(\S+)\s*$", line):
                namespaces.append(match[1])
            elif re.match(r"^end\s+\S+\s*$", line):
                if namespaces:
                    namespaces.pop()
            elif match := re.match(r"^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+(\S+)", line):
                declarations.append({
                    "name": ".".join([*namespaces, match[1]]),
                    "source_line": line_number,
                })
        modules.append({
            "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
            "path": path.relative_to(ROOT).as_posix(),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_theorem_count": len(declarations),
            "public_proof_declarations": declarations,
        })
    names = sorted(d["name"] for m in modules for d in m["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate mapped public theorem")
    source = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": "5f46a36d87f9ca1cee382f46687d9d155b9b5bc2",
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "scope": "Constructs actual assigned parts and Fin3 labels from a supplied perfect matching and a disjoint partition into two cores and exceptions. At most two exceptions give one optional pair fiber of size zero or two. Preserves the representative and actual copies, proves exact selected matching cuts and crossing-count parity, and derives both fiber parity alternatives. Composes with joining decomposition in the original host or a separate regular non-overfull host on the same vertices. It does not select a heavy boundary pattern, construct reserves, prove residual safety, align palettes, complete perfect matchings, or prove full Corollary 4.6.",
        "review": "docs/assigned-part-semantic-review.md",
        "proof_map": "docs/assigned-part-verification.md",
        "authorized_manuscript_excerpts": "verification/runs/20261122T235931Z/authorized-manuscript-recovery.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/assigned-part-source.json").write_text(json.dumps(source, indent=2) + "\n")
    print(f"Mapped {len(modules)} modules and {len(names)} public theorems; full proof verification remains required.")


if __name__ == "__main__":
    main()
