#!/usr/bin/env python3
"""Inventory exact continuation sources; the complete verifier certifies them."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "14978e4dec2bce94f63953df7b1bdd54f61c3e6c"


def source_proofs(path):
    namespaces, scopes, proofs = [], [], []
    for line_number, line in enumerate(erase_comments(path.read_text()).splitlines(), 1):
        if match := re.match(r"^namespace\s+(\S+)\s*$", line):
            namespaces.append(match[1])
            scopes.append(("namespace", match[1]))
        elif match := re.match(r"^section(?:\s+(\S+))?\s*$", line):
            scopes.append(("section", match[1]))
        elif match := re.match(r"^end(?:\s+(\S+))?\s*$", line):
            if not scopes or scopes[-1][1] != match[1]:
                raise ValueError(f"Unmatched source scope: {path}:{line_number}")
            kind, _ = scopes.pop()
            if kind == "namespace":
                namespaces.pop()
        elif match := re.match(r"^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+([^\s(:{]+)", line):
            proofs.append({"name": ".".join([*namespaces, match[1]]), "source_line": line_number})
    if namespaces or scopes:
        raise ValueError(f"Unclosed source scope: {path}")
    return proofs


def main():
    paths = sorted([
        *(p for folder in ("ThreeCoreReduction", "AuxiliarySimple", "TerminalFourOdd")
          for p in (ROOT / "Overfull" / folder).glob("*.lean")),
        *(ROOT / "Overfull/CompatibleCircuits").glob("FourAdmissible*.lean"),
    ])
    modules = []
    for path in paths:
        proofs = source_proofs(path)
        modules.append({
            "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
            "path": path.relative_to(ROOT).as_posix(),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_theorem_count": len(proofs),
            "public_proof_declarations": proofs,
        })
    names = sorted(p["name"] for module in modules for p in module["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise ValueError("Duplicate public declaration in the continuation manifest")
    public = ["Overfull.single_core_coloring", "Overfull.two_core_nonregular_factorization",
              "Overfull.three_core_regular_factorization", "Overfull.three_core_regular_one_factorization"]
    if not set(public) <= set(names):
        raise ValueError("A claimed public theorem is absent from the current source")
    record = {
        "schema_version": 1,
        "kind": "numbered_assertion_closure_with_supporting_continuations",
        "baseline_commit": BASELINE,
        "baseline_tree": "c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767",
        "baseline_publication_status": "published_exact_tree_and_both_refs_verified",
        "numbered_assertions_completed": 1,
        "main_theorem_verified": False,
        "manuscript_number": "3.1",
        "manuscript_label": "single:lem:coloring",
        "statement_sha256": "e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe",
        "public_theorems": public,
        "scope": "Complete single-core coloring Lemma 3.1, via original-host three-core regular factorization, two-core auxiliary completion, and a second auxiliary completion for one core. All tolerances and order thresholds precede the host. Original edge copies, arbitrary original parity, actual maximum degree, and the literal covering-set hypotheses are preserved. Supporting four-odd terminal and degree-four four-label circuit results have the exact scope of their individual declarations. The full four-core terminal proposition and main theorem remain unproved.",
        "review": "docs/global-factorization-semantic-review.md",
        "proof_map": "docs/global-factorization-verification.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/global-factorization-source.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Mapped {len(modules)} sources and {len(names)} public proofs. Complete verification is required.")


if __name__ == "__main__":
    main()
