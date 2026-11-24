#!/usr/bin/env python3
"""Record reviewed three-label source identities; this does not check proofs.

Run scripts/verify.py after reviewing this inventory. That verifier requires
each mapped public theorem in the fresh kernel axiom audit, in its exact module.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "LocalCoarsening", "ThreeLabelBundles", "EqualBundleSelection",
    "EqualBundleSafety", "EqualBundlePair", "UnequalBundleSelection",
    "VertexRelabeling", "SafeSelectionInduction", "ThreeLabel",
    "VertexEmbedding", "AtMostThree",
)


def main() -> None:
    modules = []
    for name in MODULES:
        path = ROOT / "Overfull" / "CompatibleCircuits" / f"{name}.lean"
        if not path.is_file():
            raise SystemExit(f"Missing reviewed module: {path.relative_to(ROOT)}")
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
    names = sorted(entry["name"] for module in modules
                   for entry in module["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate public theorem name in reviewed source inventory.")
    source = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": "b5afb03a0f0613eedd0cb3310e06706942afe2e7",
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "scope": "Compatible circuit selection and exact partition for finite loopless multigraphs on at most three vertices, under the original half-cut inequalities and even degrees. Actual edge-copy identities and arbitrary incidence-class types are preserved. This does not prove the four-label case, full Corollary 4.6, terminal Proposition 4.16, or the main theorem.",
        "review": "docs/three-label-circuit-semantic-review.md",
        "proof_map": "docs/three-label-circuit-verification.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    output = ROOT / "docs/three-label-circuit-source.json"
    output.write_text(json.dumps(source, indent=2) + "\n")
    print(f"Mapped {len(modules)} modules and {len(names)} public theorems; "
          "fresh proof verification remains a separate step.")


if __name__ == "__main__":
    main()
