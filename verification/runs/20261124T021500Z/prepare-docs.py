#!/usr/bin/env python3
"""Prepare exact source-map drafts and optionally archive genuine development.

This changes only this run's draft/evidence files. It does not edit live sources,
root imports, documentation, manifests, or verifier gates, and does not run Lean.
The draft semantic review is deliberately left to the mathematical reviewer.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "f557ae03355f14a0441b37283f35186a95aca2d7"
TREE = "efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n")


def source_manifest() -> dict:
    spec = importlib.util.spec_from_file_location("terminal_preservation_checker", RUN / "record-final.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    modules = []
    for path in sorted((ROOT / "Overfull/NativeTerminal").glob("*.lean")):
        declarations = checker.source_public_proofs(path)
        modules.append({"module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
                        "path": path.relative_to(ROOT).as_posix(), "sha256": digest(path.read_bytes()),
                        "public_theorem_count": len(declarations), "public_proof_declarations": declarations})
    names = sorted(d["name"] for module in modules for d in module["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate public theorem in the actual new sources")
    updater = ast.parse((ROOT / "scripts/update_native_terminal_manifest.py").read_text())
    scopes = [ast.literal_eval(value) for node in ast.walk(updater) if isinstance(node, ast.Dict)
              for key, value in zip(node.keys, node.values)
              if isinstance(key, ast.Constant) and key.value == "scope"]
    if len(scopes) != 1 or not isinstance(scopes[0], str):
        raise SystemExit("Manifest updater does not have one exact literal scope")
    return {"schema_version": 1, "kind": "complete_assertion_source_mapping", "baseline_commit": BASELINE,
            "baseline_tree": TREE,
            "baseline_publication_status": "verified_local_predecessor_publication_separately_recorded",
            "numbered_assertions_completed": 1, "main_theorem_verified": False, "scope": scopes[0],
            "manuscript_number": "4.6", "manuscript_label": "three:lem:bounded-input",
            "statement_sha256": "86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26",
            "public_theorems": ["Overfull.bounded_input_factorization", "Overfull.bounded_input_one_factorization"],
            "review": "docs/native-terminal-semantic-review.md",
            "proof_map": "docs/native-terminal-verification.md",
            "module_count": len(modules), "public_theorem_count": len(names), "modules": modules,
            "required_proof_declarations": names}


def archive_development() -> dict:
    with (RUN / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        files = [{"path": p.relative_to(ROOT).as_posix(), "recorded_at_path": str(p),
                  "sha256": digest(p.read_bytes()), "bytes": p.stat().st_size}
                 for p in sorted((RUN / "development").rglob("*")) if p.is_file()]
        record = {"kind": "genuine_development_evidence",
                  "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
                  "file_count": len(files), "files": files}
        write_json(RUN / "development-archive.json", record)
        return record


def prepare() -> dict:
    manifest = source_manifest()
    draft = RUN / "docs-draft"
    draft.mkdir(exist_ok=True)
    write_json(draft / "native-terminal-source.json", manifest)
    imports = ["import " + item["module"] + "\n" for item in manifest["modules"]]
    write_json(draft / "candidate-root-added-imports.json", imports)
    rows = "\n".join(f"| `{item['module']}` | {item['public_theorem_count']} |"
                     for item in manifest["modules"])
    inventory = "\n\n".join(
        f"### `{item['module']}`\n\nSource: `{item['path']}`. SHA-256: `{item['sha256']}`.\n\n" +
        "\n".join(f"- `{proof['name']}` (source line {proof['source_line']})."
                  for proof in item["public_proof_declarations"])
        for item in manifest["modules"])
    verification = f"""# Native terminal construction: exact proof map and verification scope

This complete Corollary 4.6 continuation adds {manifest['module_count']} source modules and
{manifest['public_theorem_count']} explicitly named public theorem/lemma proofs.
The exact manifest is `docs/native-terminal-source.json`. Its source hashes,
names and lines describe the candidate source; they do not certify a full run.

The unchanged full `Audit.lean` enumerates every proof declaration actually
imported, including private and generated support proofs. Its successful run
produces `verification/native-terminal-declarations.json`, which ties every
audited new declaration to the exact source path and hash. The current run's
genuine command receipt, full raw logs and `preservation.json` establish the full
verification and preservation state. No audited declaration count is inferred
from this lexical source map or from a focused compiler pass.

## Exact baseline and mathematical scope

The local verified baseline is `{BASELINE}`, exact tree `{TREE}`: 4,321 committed
files, 13,170 audited declarations, 2,176 completed-result mappings and 696 frozen
source/input hashes. Every prior nonroot mathematical source, declaration
name/owner/axiom set and old declaration map are preserved. All 69 original
statement identities and hashes and all 68 other assertion records are exact.
The only promoted assertion is 4.6; one complete-result component is appended.
Root imports are appended after the full original prefix. The verifier permits
exactly seven reviewed substitutions, including a positive 4.6 identity/audit
gate and the completed count 48. All other guards and the full audit are unchanged.
The successful predecessor publication has separate exact tree and branch
readback receipts under this run.

{manifest['scope']}

**The candidate completes Corollary 4.6, with coverage 48/69. The main theorem
and 20 other numbered assertions remain incomplete.** The semantic review records
the precise conclusions and hypotheses rather than inferring mathematical scope
from a passing compiler command.

## Source modules

| Module | Mapped public theorem proofs |
| --- | ---: |
{rows}

## Complete explicit public proof inventory

{inventory}

## Required complete verification

The full command is `python3 scripts/verify.py`, running strict
`lake build --wfail` and the unchanged complete `lake env lean Audit.lean`
under Lean 4.24.0 and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted logical axioms.

Every genuine focused attempt retains its command, actual exit, source hashes,
available input snapshots and complete log. Each complete attempt is immutable,
with all frozen input bytes, fresh output copies and exact raw audit segments.
The attached supervisor observes its real child process through terminal exit.
The separate preservation checker rechecks all old evidence, sources, mappings,
assertion records and new source-to-declaration maps before emitting success.
"""
    (draft / "native-terminal-verification.md").write_text(verification)
    generated = {p.name: digest(p.read_bytes()) for p in sorted(draft.iterdir()) if p.is_file()}
    record = {"prepared_at_utc": datetime.now(timezone.utc).isoformat(),
              "kind": "reviewable_drafts_not_live_inputs_or_verification", "live_inputs_modified": False,
              "module_count": manifest["module_count"], "public_theorem_count": manifest["public_theorem_count"],
              "source_sha256": {item["path"]: item["sha256"] for item in manifest["modules"]},
              "draft_sha256": generated}
    write_json(RUN / "docs-draft-manifest.json", record)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-development", action="store_true")
    parser.add_argument("--archive-only", action="store_true")
    args = parser.parse_args()
    if args.archive_only:
        archive = archive_development()
        print("Archived genuine development files:", archive["file_count"])
        return
    record = prepare()
    if args.archive_development:
        record["development_file_count"] = archive_development()["file_count"]
    print(json.dumps({key: record[key] for key in ["kind", "live_inputs_modified", "module_count",
                                                 "public_theorem_count"]}, indent=2))
    if args.archive_development:
        print("Archived genuine development files:", record["development_file_count"])


if __name__ == "__main__":
    main()
