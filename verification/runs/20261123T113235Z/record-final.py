#!/usr/bin/env python3
"""Check preservation and copy genuine evidence after the full frozen audit.

This is an additional consistency checker, not a replacement for scripts/verify.py
or the stock Audit.lean. Run it directly only after the complete verifier passes.
If capturing its stdout, use a path outside this run directory until it exits.
"""
from __future__ import annotations

from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASE = "ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6"
BASE_DECLARATION_COUNT = 11927
ADDED_IMPORTS = [b"import Overfull.AssignedParts.NativePatternConstruction\n"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
OUTPUT_NAMES = {"preservation.json", "final-report.md", "record-final-output.log"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


@lru_cache(maxsize=None)
def old_bytes(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)


def declaration_index(items: list[dict], label: str) -> dict:
    result = {item["name"]: (item["module"], frozenset(item["axioms"])) for item in items}
    require(len(result) == len(items), f"Duplicate declaration name in {label}")
    return result


def current_paths() -> tuple[set[str], set[str]]:
    sources = {"Overfull.lean", "Audit.lean"} | {
        rel(path) for path in (ROOT / "Overfull").rglob("*.lean")
    }
    inputs = {rel(path) for path in [
        ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
        ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
        *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
        *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
        ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
        ROOT / "LICENSE_BMATCHING.txt",
    ]}
    return sources, inputs


def check_verifier_extension() -> list[dict]:
    """Reconstruct the current verifier with precisely four reviewed changes."""
    changes = [
        (
            '                          ("assigned", "assigned-part-source.json")):\n',
            '                          ("assigned", "assigned-part-source.json"),\n'
            '                          ("native_pattern", "native-pattern-source.json")):\n',
        ),
        (
            '    # Every first-party mathematical file must be included in the library build.\n',
            '    if extension_maps["native_pattern"][0]["numbered_assertions_completed"] != 0:\n'
            '        raise SystemExit("The native-pattern continuation completes no numbered manuscript assertion.")\n\n'
            '    # Every first-party mathematical file must be included in the library build.\n',
        ),
        (
            '                    "assigned": "assigned-part"}[key]\n',
            '                    "assigned": "assigned-part", "native_pattern": "native-pattern"}[key]\n',
        ),
        (
            '        "assigned_part_declaration_map": extension_evidence["assigned"],\n',
            '        "assigned_part_declaration_map": extension_evidence["assigned"],\n'
            '        "native_pattern_declaration_map": extension_evidence["native_pattern"],\n',
        ),
    ]
    expected = old_bytes("scripts/verify.py")
    for old, new in changes:
        require(expected.count(old.encode()) == 1, "Ambiguous additive verifier edit")
        expected = expected.replace(old.encode(), new.encode(), 1)
    require((ROOT / "scripts/verify.py").read_bytes() == expected,
            "Verifier differs beyond the four reviewed additive manifest/mapping edits")
    return [{"old": old, "new": new} for old, new in changes]


def check_native_mapping(current: dict, audited: dict) -> dict:
    source_path = ROOT / "docs/native-pattern-source.json"
    map_path = ROOT / "verification/native-pattern-declarations.json"
    source, mapping = load(source_path), load(map_path)
    require(source["baseline_commit"] == BASE
            and source["kind"] == "supporting_continuation"
            and source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False,
            "Native source manifest changes the baseline or completed scope")
    modules = {item["module"]: item for item in source["modules"]}
    require(len(modules) == len(source["modules"]) == source["module_count"],
            "Native module inventory has duplicates or incorrect counts")
    public = {}
    for module, item in modules.items():
        require(item["path"] == module.replace(".", "/") + ".lean"
                and sha(ROOT / item["path"]) == item["sha256"],
                f"Native source path/hash mismatch: {module}")
        names = [entry["name"] for entry in item["public_proof_declarations"]]
        require(len(names) == len(set(names)) == item["public_theorem_count"],
                f"Native public-proof inventory mismatch: {module}")
        for name in names:
            require(name not in public and name in audited and audited[name][0] == module,
                    f"Native public proof missing, duplicated or audited elsewhere: {name}")
            public[name] = module
    require(set(public) == set(source["required_proof_declarations"])
            and len(public) == len(source["required_proof_declarations"])
            == source["public_theorem_count"], "Native required-public-proof map is incomplete")
    expected = {name: entry for name, entry in audited.items() if entry[0] in modules}
    actual = declaration_index(mapping["proof_declaration_map"], "native declaration map")
    require(actual == expected and {entry[0] for entry in actual.values()} == set(modules),
            "Native complete declaration map differs from the actual full audit")
    for item in mapping["proof_declaration_map"]:
        module = modules[item["module"]]
        require(item["source_path"] == module["path"]
                and item["source_sha256"] == module["sha256"],
                f"Native audited declaration has stale source binding: {item['name']}")
    summary = current["native_pattern_declaration_map"]
    require(summary["path"] == rel(map_path) and summary["sha256"] == sha(map_path),
            "Native result summary has a stale map path/hash")
    for key, value in [("module_count", len(modules)),
                       ("public_theorem_count", len(public)),
                       ("verified_declaration_count", len(actual)),
                       ("numbered_assertions_completed", 0)]:
        require(summary[key] == mapping[key] == value,
                f"Native result/map count mismatch: {key}")
    require(mapping["includes_private_and_generated_proofs"] is True,
            "Native declaration map excludes support proofs")
    return {"source_manifest_path": rel(source_path), "source_manifest_sha256": sha(source_path),
            "declaration_map_path": rel(map_path), "declaration_map_sha256": sha(map_path),
            "modules": modules, "public_names": sorted(public),
            "module_count": len(modules), "public_theorem_count": len(public),
            "audited_declaration_count": len(actual), "scope": source["scope"]}


def command_evidence() -> list[dict]:
    records = []
    for path in sorted(RUN.rglob("command.json")):
        data = load(path)
        require(isinstance(data.get("command"), list), f"Malformed command record: {rel(path)}")
        log_path = path.parent / "output.log"
        require(log_path.is_file(), f"Missing real command output: {rel(path)}")
        for source, expected in data.get("source_sha256", {}).items():
            snapshot = path.parent / Path(source).name
            require(snapshot.is_file() and sha(snapshot) == expected,
                    f"Recorded development source snapshot differs: {rel(snapshot)}")
        code = data.get("exit_code")
        if code is None:
            status = "incomplete"
        else:
            require(type(code) is int, f"Invalid command exit code: {rel(path)}")
            status = "passed" if code == 0 else "failed"
            require(data.get("status") == status, f"Command status/exit code disagree: {rel(path)}")
            require(datetime.fromisoformat(data["started_at_utc"]) <=
                    datetime.fromisoformat(data["finished_at_utc"]),
                    f"Command completion precedes its start: {rel(path)}")
        records.append({"metadata_path": rel(path), "metadata_sha256": sha(path),
                        "command": data["command"], "status": status, "exit_code": code,
                        "log_path": rel(log_path), "log_sha256": sha(log_path),
                        "source_snapshot_count": len(data.get("source_sha256", {}))})
    setup_path = RUN / "setup-commands.json"
    if setup_path.exists():
        for index, data in enumerate(load(setup_path)):
            log_path = RUN / data["log"]
            require(log_path.is_file() and type(data.get("exit_code")) is int,
                    "Setup command lacks its real output or exit status")
            records.append({"metadata_path": rel(setup_path), "metadata_sha256": sha(setup_path),
                            "metadata_array_index": index, "command": data["command"],
                            "status": "passed" if data["exit_code"] == 0 else "failed",
                            "exit_code": data["exit_code"], "log_path": rel(log_path),
                            "log_sha256": sha(log_path), "source_snapshot_count": 0})
    return records


def main() -> None:
    # No success report or copied evidence is written until every check below passes.
    command = load(RUN / "verification-command.json")
    require(command.get("command") == ["python3", "scripts/verify.py"]
            and command.get("status") == "passed" and command.get("exit_code") == 0
            and command.get("all_frozen_inputs_unchanged") is True,
            "Fresh complete frozen verifier has not passed")
    run = load(RUN / "run.json")
    require(run["base_commit"] == BASE, "Run metadata identifies another baseline")
    started = datetime.fromisoformat(run["started_at_utc"])
    require(started <= datetime.fromisoformat(command["started_at_utc"]) <=
            datetime.fromisoformat(command["completed_at_utc"]),
            "Fresh verification timestamps do not belong to this run")

    previous = json.loads(old_bytes("verification/results.json"))
    current = load(ROOT / "verification/results.json")
    require(current["lean_build_passed"] is True and current["axiom_audit_passed"] is True
            and current["status"] == "partial_formalization"
            and current["main_theorem_verified"] is False,
            "Fresh verification status or main-theorem scope is incorrect")
    require(current["toolchain"] == previous["toolchain"] == "leanprover/lean4:v4.24.0"
            and current["mathlib_revision"] == previous["mathlib_revision"]
            == "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
            and current["dependency_source_revisions"] == previous["dependency_source_revisions"],
            "Pinned Lean/mathlib/dependency sources changed")
    require(set(current["allowed_logical_axioms"]) == ALLOWED_AXIOMS,
            "Logical axiom allowance changed")
    before = declaration_index(previous["verified_declarations"], "baseline result")
    after = declaration_index(current["verified_declarations"], "fresh result")
    require(len(before) == previous["verified_declaration_count"] == BASE_DECLARATION_COUNT,
            "Unexpected authoritative baseline declaration count")
    require(len(after) == current["verified_declaration_count"]
            and all(after.get(name) == entry for name, entry in before.items()),
            "A prior audited name, source module or axiom set changed")
    require(all(axioms <= ALLOWED_AXIOMS for _, axioms in after.values()),
            "Fresh declaration audit has an unapproved axiom")
    require(all(current["completed_results"].get(name) == value
                for name, value in previous["completed_results"].items()),
            "A previous completed-result declaration mapping changed")

    baseline_paths = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", BASE], cwd=ROOT, text=True).splitlines())
    baseline_sources = {path for path in baseline_paths
                        if path in {"Audit.lean", "Overfull.lean"}
                        or path.startswith("Overfull/") and path.endswith(".lean")}
    require(set(previous["source_sha256"]) == baseline_sources,
            "Authoritative source inventory is incomplete")
    for path in sorted(baseline_sources):
        original = old_bytes(path)
        require(digest(original) == previous["source_sha256"][path],
                f"Authoritative source hash disagrees with its actual bytes: {path}")
        if path != "Overfull.lean":
            require((ROOT / path).read_bytes() == original,
                    f"Prior nonroot proof source changed: {path}")
    root_bytes = (ROOT / "Overfull.lean").read_bytes()
    for added in ADDED_IMPORTS:
        require(root_bytes.count(added) == 1, "New root import missing or duplicated")
        root_bytes = root_bytes.replace(added, b"", 1)
    require(root_bytes == old_bytes("Overfull.lean"), "Proof root changed beyond declared imports")
    verifier_edits = check_verifier_extension()

    sources, inputs = current_paths()
    require(set(current["source_sha256"]) == sources
            and set(current["verification_input_sha256"]) == inputs
            and sources.isdisjoint(inputs), "Current source/input path inventory is stale")
    actual_hashes = {path: sha(ROOT / path) for path in sorted(sources | inputs)}
    recorded_hashes = {**current["source_sha256"], **current["verification_input_sha256"]}
    frozen = load(RUN / "frozen-candidate-inputs.json")
    require(actual_hashes == recorded_hashes == frozen,
            "Current files, complete verifier results and frozen inputs disagree")
    require(command["candidate_input_hash_count"] == len(frozen), "Frozen input count differs")

    old_coverage = json.loads(old_bytes("docs/coverage.json"))
    coverage = load(ROOT / "docs/coverage.json")
    assertions = coverage["numbered_assertions"]
    require(assertions == old_coverage["numbered_assertions"]
            and len(assertions) == coverage["numbered_assertion_count"] == 69,
            "One of the 69 complete numbered assertion records changed")
    complete = [item for item in assertions if item["full_assertion_verified"]]
    require(len(complete) == 47 and coverage["main_theorem_verified"] is False
            and current["fully_verified_numbered_assertion_count"] == 47
            and current["fully_verified_numbered_assertions"] == [item["number"] for item in complete]
            == previous["fully_verified_numbered_assertions"],
            "Preserved 47/69 assertion scope changed")

    old_maps = {}
    for key, summary in previous.items():
        if key.endswith("_declaration_map"):
            path = summary["path"]
            require((ROOT / path).read_bytes() == old_bytes(path)
                    and current[key] == summary and sha(ROOT / path) == summary["sha256"],
                    f"Prior declaration map or its metadata changed: {path}")
            old_maps[key] = {"path": path, "sha256": sha(ROOT / path)}
    native = check_native_mapping(current, after)
    require(sources - baseline_sources == {item["path"] for item in native["modules"].values()}
            and baseline_sources <= sources, "New proof source inventory differs from native manifest")
    require(set(native["public_names"]).isdisjoint(before), "New public proof reused a baseline name")
    require(set(native["modules"]) <= set(current["imported_project_modules"])
            and set(previous["imported_project_modules"]) <= set(current["imported_project_modules"]),
            "A new or existing project module is missing from the checked root")

    audit_text = (ROOT / "verification/axioms.log").read_text()
    audit_records = [json.loads(line) for line in re.findall(r"VERIFIED_DECLARATION ([^\n]+)", audit_text)]
    require(declaration_index(audit_records, "actual full axiom log") == after
            and re.findall(r"OVERFULL_AXIOM_AUDIT_OK (\d+)", audit_text) == [str(len(after))],
            "Actual full axiom log differs from the fresh result declarations")
    build_text = (ROOT / "verification/build.log").read_text()
    build_counts = re.findall(r"Build completed successfully \((\d+) jobs\)", build_text)
    require(len(build_counts) == 1, "Actual fresh strict build lacks one final success marker")
    jobs = int(build_counts[0])
    console = (RUN / "verification-console.log").read_text()
    require(f"OVERFULL_AXIOM_AUDIT_OK {len(after)}" in console
            and f"Checked {len(after)} project declarations; full manuscript status: unverified." in console,
            "Fresh complete verifier console lacks its matching audit/final output")

    historical_paths = sorted(path for path in baseline_paths
                              if path.startswith(("verification/runs/", "recovery/")))
    for path in historical_paths:
        require((ROOT / path).read_bytes() == old_bytes(path),
                f"Historical run or recovery evidence changed: {path}")
    checks = command_evidence()
    failures = [item for item in checks if item["status"] == "failed"]
    successes = [item for item in checks if item["status"] == "passed"]
    incomplete = [item for item in checks if item["status"] == "incomplete"]

    # Exact copies of current outputs: no synthetic or replayed verification logs.
    copy_names = ["vizing-source.log", "lean-version.log", "build.log", "axioms.log",
                  "results.json", "native-pattern-declarations.json"]
    final_dir = RUN / "final"
    final_dir.mkdir(exist_ok=True)
    copied = {}
    for name in copy_names:
        origin, destination = ROOT / "verification" / name, final_dir / name
        shutil.copyfile(origin, destination)
        require(destination.read_bytes() == origin.read_bytes(), f"Evidence copy differs: {name}")
        copied[rel(destination)] = {"copied_from": rel(origin), "sha256": sha(destination)}

    now = datetime.now(timezone.utc)
    new_names = sorted(set(after) - set(before))
    evidence_paths = {rel(path) for path in RUN.rglob("*") if path.is_file()
                      and path.name not in OUTPUT_NAMES
                      and "__pycache__" not in path.parts and path.suffix != ".pyc"}
    evidence_paths |= {"verification/results.json", "verification/build.log", "verification/axioms.log",
                       native["source_manifest_path"], native["declaration_map_path"],
                       "docs/native-pattern-verification.md", "docs/native-pattern-semantic-review.md",
                       "docs/continuation-handoff.md", *(item["path"] for item in old_maps.values())}
    record = {
        "schema_version": 1, "status": "verification_and_preservation_passed",
        "run_id": RUN.name, "run_started_at_utc": run["started_at_utc"],
        "recorded_at_utc": now.isoformat(), "baseline_commit": BASE,
        "verification_command": command, "strict_build_jobs": jobs,
        "verified_declaration_count": len(after), "previous_verified_declarations_preserved": len(before),
        "new_verified_declaration_count": len(new_names), "new_verified_declarations": new_names,
        "all_prior_declaration_names_modules_and_axiom_sets_preserved": True,
        "previous_completed_result_mappings_preserved": len(previous["completed_results"]),
        "byte_identical_previous_nonroot_lean_source_count": len(baseline_sources) - 1,
        "all_previous_nonroot_lean_sources_byte_identical": True,
        "root_added_imports_only": [line.decode().strip() for line in ADDED_IMPORTS],
        "stock_audit_byte_identical": True,
        "verifier_previous_gates_byte_preserved_after_four_declared_extensions": True,
        "verifier_exact_additive_edits": verifier_edits,
        "previous_declaration_maps_byte_identical": old_maps,
        "all_69_original_numbered_assertion_records_and_statement_hashes_preserved": True,
        "all_47_completed_assertion_records_preserved": True,
        "fully_verified_numbered_assertion_count": 47, "remaining_numbered_assertion_count": 22,
        "numbered_assertions_completed_in_this_run": 0, "main_theorem_verified": False,
        "source_hash_count": len(sources), "verification_input_hash_count": len(inputs),
        "frozen_input_count": len(frozen), "all_source_and_input_hashes_match_frozen_candidate": True,
        "imported_project_module_count": len(current["imported_project_modules"]),
        "allowed_logical_axioms": current["allowed_logical_axioms"],
        "native_pattern": native, "preserved_historical_evidence_paths": historical_paths,
        "retained_command_count": len(checks), "successful_command_count": len(successes),
        "failed_command_count": len(failures), "incomplete_command_count": len(incomplete),
        "command_evidence": checks, "copied_fresh_outputs": copied,
        "evidence_sha256": {path: sha(ROOT / path) for path in sorted(evidence_paths)},
        "publication": {"repository": "fly31415926/overfull-lean",
                        "target_branches": ["main", "verified-bipartite-continuation-2026-11-21"],
                        "status": "pending_verified_branch_updates",
                        "note": "This report precedes branch updates and makes no claim that those updates succeeded."},
    }
    module_rows = "\n".join(f"| `{name}` | {item['public_theorem_count']} |"
                            for name, item in native["modules"].items())
    failure_rows = "\n".join(
        f"| `{item['metadata_path']}`"
        f"{(' entry ' + str(item['metadata_array_index'])) if 'metadata_array_index' in item else ''}"
        f" | {item['exit_code']} | `{item['log_path']}` |" for item in failures)
    report = f"""# Native matching patterns: final verification and preservation

**The complete frozen candidate passed strict Lean verification and the unchanged full axiom audit.**
This run began at `{run['started_at_utc']}`. The preservation report was written at
`{now.isoformat()}` against authoritative baseline `{BASE}`.

## Checked mathematical progress

{native['scope']}

The native distribution keeps every parallel edge copy distinct. With at most two
exceptions, at most five assignment signatures suffice; a positive-weight actual
representative has signature weight at least `k/5`. Equal signatures retain the
actual assigned parts and old-core crossing parity. The internal-pair signature
has weight exactly the original internal-copy multiplicity. The corresponding
exceptional-to-core and odd cross-core pools satisfy the proved capacity bounds.
Boundary compression retains all selected exceptional copies and the required
crossing parity, with the original representative retained throughout.

| New module | Public theorem proofs |
| --- | ---: |
{module_rows}

The native manifest has **{native['public_theorem_count']} public theorem proofs**
in **{native['module_count']} modules**, covering
**{native['audited_declaration_count']} audited declarations** including generated
and private support proofs. This is supporting progress toward Corollary 4.6.
**No numbered manuscript assertion is newly complete: coverage remains 47/69,
with 22 assertions, including the main theorem, incomplete.**

## Actual verification evidence

| Check | Result |
| --- | --- |
| Complete `python3 scripts/verify.py` | Exit 0; frozen inputs unchanged |
| Strict `lake build --wfail` | {jobs:,} jobs passed |
| Stock complete `Audit.lean` | {len(after):,} declarations passed |
| Prior declaration names, modules and axiom sets | All {len(before):,} preserved |
| Newly audited declarations | {len(new_names):,} |
| Prior nonroot proof files, including `Audit.lean` | {len(baseline_sources)-1} byte-identical |
| Previous declaration maps | All {len(old_maps)} byte-identical |
| Previous completed-result mappings | All {len(previous['completed_results']):,} retained |
| Numbered assertion records and statement hashes | All 69 unchanged; all 47 complete records preserved |
| Current proof source paths and SHA256 values | {len(sources)} files; exact match |
| Other current verification-input paths and SHA256 values | {len(inputs)} files; exact match |
| Frozen source/input inventory | {len(frozen)} paths; exact match at verification and recording |

The permitted logical axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
The preserved Lean pin is `leanprover/lean4:v4.24.0`; mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, with all other dependency source
revisions unchanged. The actual axiom-log declarations were compared with every
declaration in the fresh result. Removing the declared new root import reproduces
the old root bytes. The verifier differs by precisely the four checked native
manifest/mapping extensions; every previous gate is preserved.

The [`final/`](final/) directory contains byte-for-byte copies of the actual
fresh build, complete axiom log, result report, native declaration map, Lean
version log and Vizing-source log. The full console remains in
[`verification-console.log`](verification-console.log). No old verification log
was replayed or rewritten as a fresh compiler result. Exact copies, source
snapshots and evidence hashes are recorded in [`preservation.json`](preservation.json).

## Retained development and setup failures

The run retains {len(successes)} successful, {len(failures)} failed and
{len(incomplete)} incomplete command records. These are separate from the completed
full verification above. Every recorded source snapshot was checked against its
recorded SHA256; every command has its actual output log. Failed intermediate
commands remain marked failed, including setup/download errors and intermediate
Lean diagnostics. No failure is relabeled as a successful check.

| Failed command record | Exit code | Actual output |
| --- | ---: | --- |
{failure_rows or '| None | — | — |'}

## Remaining proof work and publication

Actual copy capacities do not by themselves provide simultaneous disjoint
reserves, enough distinct neighbors, or a residual graph with no overfull set.
Reserve selection, residual safety, palette grouping, robust completion and
the full factorization in Corollary 4.6 remain separate obligations. The exact
same representative must be used when connecting these new results to them.

This report is generated before publication to the verified branches and does
not claim that publication has succeeded. The containing checkpoint must be
published to both `main` and `verified-bipartite-continuation-2026-11-21`, preserving
concurrent work, followed by an actual read-back of both remote heads and the
published commit/tree.
"""
    (RUN / "preservation.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    (RUN / "final-report.md").write_text(report, encoding="utf-8")
    print(json.dumps({key: record[key] for key in [
        "status", "strict_build_jobs", "verified_declaration_count",
        "previous_verified_declarations_preserved", "new_verified_declaration_count",
        "source_hash_count", "verification_input_hash_count", "failed_command_count",
        "fully_verified_numbered_assertion_count", "main_theorem_verified",
    ]}, indent=2))


if __name__ == "__main__":
    main()
