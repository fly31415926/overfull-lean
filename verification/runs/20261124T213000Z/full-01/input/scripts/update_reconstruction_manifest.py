#!/usr/bin/env python3
"""Refresh reconstructed source mappings; this does not verify any proof.

The original-source hashes are fixed recovery evidence and are never refreshed.
Run scripts/verify.py after reviewing any regenerated mapping.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    provenance_path = ROOT / "docs/checkpoint-reconstruction-source.json"
    provenance = json.loads(provenance_path.read_text())
    recovered = {item["path"]: item["sha256"]
                 for item in provenance["recovered_original_sources"]}
    for path, digest in recovered.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Recovered original bytes changed: {path}")
    paths = sorted([
        *[p.relative_to(ROOT).as_posix() for p in (ROOT / "Overfull/BoundedExterior").glob("*.lean")],
        "Overfull/PairedCut/BalancedFootprints.lean",
        "Overfull/OrdinaryFactorization/BoundedCutReserve.lean",
        "Overfull/OrdinaryFactorization/FirstHalfBounded.lean",
        "Overfull/OrdinaryFactorization/ReductionBounded.lean",
        "Overfull/OrdinaryFactorization/Full.lean",
    ])
    modules = []
    for relative in paths:
        path = ROOT / relative
        namespace = []
        declarations = []
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if match := re.match(r"^namespace\s+(\S+)\s*$", line):
                namespace.append(match[1])
            elif re.match(r"^end\s+\S+\s*$", line):
                if namespace:
                    namespace.pop()
            elif match := re.match(r"^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+(\S+)", line):
                declarations.append({"name": ".".join([*namespace, match[1]]),
                                     "source_line": number})
        modules.append({
            "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
            "path": relative,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "provenance": "recovered_original_bytes" if relative in recovered else "recreated",
            "public_theorem_count": len(declarations),
            "public_proof_declarations": declarations,
        })
    source_path = ROOT / "docs/ordinary-factorization-full-source.json"
    source = json.loads(source_path.read_text())
    source.update({
        "module_count": len(modules),
        "modules": modules,
        "public_theorem_count": sum(item["public_theorem_count"] for item in modules),
        "required_proof_declarations": sorted(entry["name"] for item in modules
                                               for entry in item["public_proof_declarations"]),
    })
    source_path.write_text(json.dumps(source, indent=2) + "\n")
    provenance["recreated_sources"] = [
        {key: item[key] for key in ("module", "path", "sha256")}
        for item in modules if item["provenance"] == "recreated"
    ]
    provenance_path.write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Mapped {len(modules)} ordinary-closure modules and "
          f"{source['public_theorem_count']} public proofs. Verification is a separate step.")


if __name__ == "__main__":
    main()
