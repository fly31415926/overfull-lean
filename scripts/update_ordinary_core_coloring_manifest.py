#!/usr/bin/env python3
"""Map this current-source theorem without rebasing the older numbered inventory."""
import hashlib
import json
from pathlib import Path
from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / "verification/runs/20261125T002000Z"


def main():
    modules = []
    for relative in ["Overfull/AuxiliarySimple/OrdinaryThree.lean", "Overfull/OrdinaryCoreColoring.lean"]:
        path = ROOT / relative
        proofs = source_proofs(path)
        modules.append({"module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
                        "path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "public_theorem_count": len(proofs), "public_proof_declarations": proofs})
    names = sorted(p["name"] for m in modules for p in m["public_proof_declarations"])
    if len(names) != len(set(names)) or "Overfull.ordinary_cores_coloring" not in names:
        raise ValueError("Missing endpoint or duplicate public declaration")
    comparison = json.loads((RUN / "ordinary-theorem-comparison.json").read_text())
    excerpt = RUN / "current-ordinary-theorem.tex"
    digest = hashlib.sha256(excerpt.read_bytes()).hexdigest()
    if digest != comparison["current_statement_sha256"] or comparison["matches_pinned_statement"]:
        raise ValueError("The current theorem's independent source comparison changed")
    source = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": "ac05c3232425399af6c0f29e1f7d3ddc1037424d",
        "baseline_tree": "8cfcdcc6cdd08b3209bc21b1823122bb141c330e",
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "public_theorems": ["Overfull.ordinary_cores_coloring"],
        "current_manuscript_statement": {
            "filename": "Four_Robust_Component_Cases_2026-11-21.tex",
            "whole_source_sha256": comparison["whole_source_sha256"],
            "manuscript_label": "three:thm:main",
            "statement_source_lines": comparison["source_lines"],
            "statement_sha256": digest,
            "excerpt_path": excerpt.relative_to(ROOT).as_posix(),
            "pinned_statement_sha256": comparison["pinned_statement_sha256"],
            "matches_pinned_statement": False,
            "normalization": comparison["normalization"],
            "pinned_numbered_inventory_rebased": False,
        },
        "scope": (
            "Construct actual original-host nonregular three-core coloring by adding a fourth robust core, "
            "factoring the actual regular completion, and restricting the coloring. Combine this with the "
            "existing one- and two-core constructions with one positive tolerance and order threshold. "
            "The public current-source endpoint allows one to three cores with arbitrary finite labels, "
            "arbitrary positive density, and every palette k at least the actual maximum degree. "
            "The literal budget a+|Z|+1 is retained. Nonnegative error is derived internally, exceptional "
            "overlap is removed internally, and larger palettes use proved Vizing. No original regularity, "
            "parity, supplied auxiliary graph or supplied coloring is assumed. The current source identity "
            "is recorded separately; all 69 older numbered records and their 51 complete statuses remain unchanged."
        ),
        "review": "docs/ordinary-core-coloring-semantic-review.md",
        "proof_map": "docs/ordinary-core-coloring.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/ordinary-core-coloring-source.json").write_text(json.dumps(source, indent=2) + "\n")
    print(f"Mapped {len(modules)} modules and {len(names)} public proofs; no numbered-inventory promotion.")


if __name__ == "__main__":
    main()
