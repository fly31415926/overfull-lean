#!/usr/bin/env python3
"""Map reviewed joining-decomposition sources; this does not verify proofs.

Run scripts/verify.py after refreshing this mapping. The verifier checks all
listed public theorem names and modules against its complete fresh audit.
"""

import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "QuotientCuts", "PairAugmentation", "JoiningPartitions",
    "TwoOddQuotient", "TwoOddDecomposition",
)


def main() -> None:
    modules = []
    for name in MODULES:
        path = ROOT / "Overfull" / "CompatibleCircuits" / (name + ".lean")
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
        "scope": "Exact original-host joining decompositions for regular loopless multigraphs with no overfull set and at most three labels. Even fibers yield a partition into original matchings of size at most three. Exactly two odd fibers yield one constructed virtual family, derived augmented admissibility and parity, exactly h nonempty primary original matchings of size at most two, and surplus original matchings of size at most three, with exact disjoint coverage and actual host fiber-cut footprints. The assigned label map and its fiber parities are inputs. This does not construct manuscript reserves, assigned parts, palettes, perfect-matching completions, or full Corollary 4.6.",
        "review": "docs/joining-circuit-semantic-review.md",
        "proof_map": "docs/joining-circuit-verification.md",
        "authorized_manuscript_excerpts": "verification/runs/20261122T235931Z/authorized-manuscript-recovery.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/joining-circuit-source.json").write_text(json.dumps(source, indent=2) + "\n")
    print(f"Mapped {len(modules)} modules and {len(names)} public theorems; full proof verification remains required.")


if __name__ == "__main__":
    main()
