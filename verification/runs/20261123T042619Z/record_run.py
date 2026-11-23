#!/usr/bin/env python3
"""Record this run only after the fresh complete verifier has passed.

This supplements the unchanged Audit.lean; it never substitutes historical
chat reports for current verification. Capture stdout outside this run folder:
the script hashes all finalized evidence files before writing its two reports.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
RUN = Path(__file__).resolve().parent
BASE = "5f46a36d87f9ca1cee382f46687d9d155b9b5bc2"
RECOVERED = "28edc7b555d459b93a00d15258ca374abf5f0bb0"
EARLY = "b6356191c948cac240f77ca3560c1910de42112e"
START = "2026-11-23T04:26:19+00:00"
ADDED_IMPORTS = [
    b"import Overfull.CompatibleCircuits.TwoOddDecomposition\n",
    b"import Overfull.AssignedParts.JoiningConstruction\n",
]
OLD_MAPS = {
    "four_odd_declaration_map": "four-odd-declarations.json",
    "residual_factorization_declaration_map": "residual-factorization-declarations.json",
    "boundary_extension_declaration_map": "boundary-extension-full-declarations.json",
    "ordinary_factorization_declaration_map": "ordinary-factorization-full-declarations.json",
    "few_exception_declaration_map": "few-exception-declarations.json",
    "three_label_circuit_declaration_map": "three-label-circuit-declarations.json",
}
JOINING_MODULES = {
    "Overfull.CompatibleCircuits.QuotientCuts",
    "Overfull.CompatibleCircuits.PairAugmentation",
    "Overfull.CompatibleCircuits.JoiningPartitions",
    "Overfull.CompatibleCircuits.TwoOddQuotient",
    "Overfull.CompatibleCircuits.TwoOddDecomposition",
}
ASSIGNED_MODULES = {
    "Overfull.AssignedParts.PairFiberParity",
    "Overfull.AssignedParts.ThreePartLabels",
    "Overfull.AssignedParts.Basic",
    "Overfull.AssignedParts.MatchedCuts",
    "Overfull.AssignedParts.JoiningConstruction",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def old_bytes(path: str, commit: str = BASE) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def index(records: list[dict], description: str) -> dict:
    data = {d["name"]: (d["module"], frozenset(d["axioms"])) for d in records}
    require(len(data) == len(records), f"Duplicate declaration in {description}")
    return data


def current_paths() -> tuple[set[str], set[str]]:
    sources = {"Overfull.lean", "Audit.lean"} | {
        rel(p) for p in (ROOT / "Overfull").rglob("*.lean")
    }
    inputs = {rel(p) for p in [
        ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
        ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
        *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
        *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
        ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
        ROOT / "LICENSE_BMATCHING.txt",
    ]}
    return sources, inputs


def check_group(basename: str, result_key: str, expected_modules: set[str],
                current: dict, after: dict) -> dict:
    source_path = ROOT / "docs" / f"{basename}-source.json"
    map_path = ROOT / "verification" / f"{basename}-declarations.json"
    source, mapping = load(source_path), load(map_path)
    modules = {m["module"]: m for m in source["modules"]}
    require(set(modules) == expected_modules
            and len(modules) == len(source["modules"]) == source["module_count"],
            f"Unexpected {basename} module inventory")
    require(source["baseline_commit"] == BASE
            and source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False,
            f"Unexpected {basename} source scope")
    public = {}
    for module, item in modules.items():
        require(item["path"] == module.replace(".", "/") + ".lean"
                and sha(ROOT / item["path"]) == item["sha256"],
                f"Source identity mismatch for {module}")
        names = [d["name"] for d in item["public_proof_declarations"]]
        require(len(names) == len(set(names)) == item["public_theorem_count"],
                f"Public proof inventory mismatch for {module}")
        for name in names:
            require(name not in public and name in after and after[name][0] == module,
                    f"Public proof absent, duplicated or audited in wrong module: {name}")
            public[name] = module
    require(set(public) == set(source["required_proof_declarations"])
            and len(public) == source["public_theorem_count"]
            == len(source["required_proof_declarations"]),
            f"Incomplete {basename} required-public-proof mapping")
    mapped = index(mapping["proof_declaration_map"], basename)
    expected = {n: v for n, v in after.items() if v[0] in modules}
    require(mapped == expected and {v[0] for v in mapped.values()} == set(modules),
            f"Incomplete {basename} complete audited declaration map")
    for item in mapping["proof_declaration_map"]:
        spec = modules[item["module"]]
        require(item["source_path"] == spec["path"]
                and item["source_sha256"] == spec["sha256"],
                f"Incorrect source binding for {item['name']}")
    summary = current[result_key]
    require(summary["path"] == rel(map_path) and summary["sha256"] == sha(map_path),
            f"Summary hash mismatch for {basename}")
    for key, count in [("module_count", len(modules)),
                       ("public_theorem_count", len(public)),
                       ("verified_declaration_count", len(mapped)),
                       ("numbered_assertions_completed", 0)]:
        require(mapping[key] == summary[key] == count,
                f"Summary count mismatch for {basename}: {key}")
    require(mapping["includes_private_and_generated_proofs"] is True,
            f"Incomplete audited scope for {basename}")
    return {"source_path": rel(source_path), "declaration_map_path": rel(map_path),
            "source": source, "modules": modules, "public_names": sorted(public),
            "module_count": len(modules), "public_theorem_count": len(public),
            "audited_declaration_count": len(mapped), "result_summary": summary}


def publication_record(filename: str, required: bool = False) -> dict | None:
    path = RUN / filename
    if not path.exists():
        require(not required, f"Missing required publication record: {filename}")
        return None
    data = load(path)
    require(data["baseline_commit"] == BASE
            and data["branch"] == f"continuation-attempt/{RUN.name}",
            f"Unexpected publication provenance in {filename}")
    for key in ("commit", "tree"):
        require(isinstance(data.get(key), str)
                and re.fullmatch(r"[0-9a-f]{40}", data[key]) is not None,
                f"Invalid {key} in {filename}")
    require(data["verified_remote_head"] == data["commit"],
            f"Publication record lacks matching observed head: {filename}")
    datetime.fromisoformat(data["recorded_at_utc"].replace("Z", "+00:00"))
    return data


def targeted_checks() -> list[dict]:
    records = []
    for path in sorted(RUN.glob("*.json")):
        if path.name in {"verification-command.json", "run.json"}:
            continue
        data = load(path)
        if not isinstance(data.get("command"), list) or type(data.get("exit_code")) is not int:
            continue
        # Actual development and public-name commands have a retained log.
        log = RUN / data.get("log", path.with_suffix(".log").name)
        require(log.is_file(), f"Missing actual command log: {path.name}")
        snapshot = data.get("source_snapshot")
        if snapshot is not None:
            snapshot_path = RUN / snapshot
            require(snapshot_path.is_file(), f"Missing source snapshot: {snapshot}")
            if "source_sha256" in data:
                require(sha(snapshot_path) == data["source_sha256"],
                        f"Source snapshot hash mismatch: {snapshot}")
        passed = (data["exit_code"] == 0
                  and data.get("source_unchanged_during_check") is not False)
        records.append({"metadata_path": rel(path), "metadata_sha256": sha(path),
                        "command_record": data, "log_path": rel(log),
                        "log_sha256": sha(log),
                        "status": "passed" if passed else "failed"})
    return records


def main() -> None:
    command = load(RUN / "verification-command.json")
    require(command.get("command") == ["python3", "scripts/verify.py"]
            and command.get("status") == "passed" and command.get("exit_code") == 0,
            "Fresh complete verifier has not passed")
    require(command.get("all_frozen_inputs_unchanged") is True,
            "Complete verifier did not confirm unchanged frozen inputs")
    started = datetime.fromisoformat(command["started_at_utc"])
    ended = datetime.fromisoformat(command["completed_at_utc"])
    require(datetime.fromisoformat(START) <= started <= ended,
            "Invalid fresh verification timestamps")

    current = load(ROOT / "verification/results.json")
    previous = json.loads(old_bytes("verification/results.json"))
    require(current["lean_build_passed"] and current["axiom_audit_passed"]
            and current["status"] == "partial_formalization"
            and current["main_theorem_verified"] is False,
            "Unexpected fresh verification status")
    require(current["toolchain"] == previous["toolchain"] == "leanprover/lean4:v4.24.0"
            and current["mathlib_revision"] == previous["mathlib_revision"]
            == "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
            and current["dependency_source_revisions"] == previous["dependency_source_revisions"],
            "Pinned toolchain or dependency sources changed")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(set(current["allowed_logical_axioms"]) == allowed,
            "Allowed logical axioms changed")
    before = index(previous["verified_declarations"], "baseline results")
    after = index(current["verified_declarations"], "fresh results")
    require(len(before) == previous["verified_declaration_count"] == 11727,
            "Unexpected published baseline declaration count")
    require(len(after) == current["verified_declaration_count"],
            "Fresh declaration count mismatch")
    require(set(before) <= set(after)
            and all(after[n] == value for n, value in before.items()),
            "A previous declaration name, module or axiom set changed")
    require(all(axioms <= allowed for _, axioms in after.values()),
            "Unapproved axiom in fresh declaration evidence")

    baseline_paths = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", BASE], cwd=ROOT, text=True).splitlines())
    baseline_sources = {p for p in baseline_paths if p in {"Overfull.lean", "Audit.lean"}
                        or p.startswith("Overfull/") and p.endswith(".lean")}
    require(set(previous["source_sha256"]) == baseline_sources,
            "Baseline source inventory is incomplete")
    preserved_sources = []
    for path, old_hash in previous["source_sha256"].items():
        original = old_bytes(path)
        require(digest(original) == old_hash, f"Baseline recorded hash mismatch: {path}")
        if path != "Overfull.lean":
            require((ROOT / path).read_bytes() == original,
                    f"Previous nonroot Lean source changed: {path}")
            preserved_sources.append(path)
    require(len(preserved_sources) == 493, "Unexpected prior nonroot source count")
    root_bytes = (ROOT / "Overfull.lean").read_bytes()
    for added in ADDED_IMPORTS:
        require(root_bytes.count(added) == 1, "Missing or duplicated new root import")
        root_bytes = root_bytes.replace(added, b"", 1)
    require(root_bytes == old_bytes("Overfull.lean"),
            "Root changed beyond the two declared imports")

    sources, inputs = current_paths()
    require(set(current["source_sha256"]) == sources
            and set(current["verification_input_sha256"]) == inputs
            and sources.isdisjoint(inputs), "Source/input inventory is incomplete or stale")
    actual_hashes = {p: sha(ROOT / p) for p in sorted(sources | inputs)}
    recorded_hashes = {**current["source_sha256"], **current["verification_input_sha256"]}
    frozen = load(RUN / "frozen-candidate-inputs.json")
    require(actual_hashes == recorded_hashes == frozen,
            "Fresh results or frozen source/input hashes differ from current files")
    require(command["candidate_input_hash_count"] == len(frozen),
            "Frozen input count mismatch")

    old_coverage = json.loads(old_bytes("docs/coverage.json"))
    coverage = load(ROOT / "docs/coverage.json")
    old_assertions, assertions = old_coverage["numbered_assertions"], coverage["numbered_assertions"]
    require(len(old_assertions) == len(assertions) == coverage["numbered_assertion_count"] == 69,
            "Numbered assertion inventory changed")
    signatures = lambda items: [(a["number"], a["statement_sha256"]) for a in items]
    require(signatures(old_assertions) == signatures(assertions),
            "An original numbered statement hash changed")
    old_complete = [a for a in old_assertions if a["full_assertion_verified"]]
    complete = [a for a in assertions if a["full_assertion_verified"]]
    require(old_complete == complete and len(complete) == 47
            and coverage["main_theorem_verified"] is False,
            "Completed numbered assertion records or main-theorem scope changed")
    require(current["fully_verified_numbered_assertion_count"] == len(complete)
            and current["fully_verified_numbered_assertions"] == [a["number"] for a in complete],
            "Fresh coverage result disagrees with the preserved inventory")
    for key, filename in OLD_MAPS.items():
        path = f"verification/{filename}"
        require((ROOT / path).read_bytes() == old_bytes(path)
                and current[key] == previous[key]
                and current[key]["sha256"] == sha(ROOT / path),
                f"Prior declaration mapping changed: {path}")

    joining = check_group("joining-circuit", "joining_circuit_declaration_map",
                          JOINING_MODULES, current, after)
    assigned = check_group("assigned-part", "assigned_part_declaration_map",
                           ASSIGNED_MODULES, current, after)
    require(joining["public_theorem_count"] == 75, "Recovered joining public inventory changed")
    expected_new_sources = {m["path"] for group in (joining, assigned)
                            for m in group["modules"].values()}
    require(baseline_sources <= sources and sources - baseline_sources == expected_new_sources,
            "Unexpected added or removed mathematical source")
    recovered_sources = []
    for item in joining["modules"].values():
        require((ROOT / item["path"]).read_bytes() == old_bytes(item["path"], RECOVERED),
                f"Recovered joining source differs from published attempt: {item['path']}")
        recovered_sources.append({"path": item["path"], "sha256": sha(ROOT / item["path"])})
    required_entries = {
        "Overfull.AssignedParts.exists_two_core_assigned_labels",
        "Overfull.AssignedParts.assignedLabel_parity_eq_core_crossing",
        "Overfull.AssignedParts.assignedLabel_joining_decomposition",
        "Overfull.AssignedParts.assignedLabel_joining_decomposition_in_host",
    }
    require(required_entries <= set(assigned["public_names"]),
            "An announced assigned-part entry point is absent from the fresh mapping")
    public_new = set(joining["public_names"]) | set(assigned["public_names"])
    require(public_new.isdisjoint(before), "A new public proof reuses a baseline declaration name")

    audit = (ROOT / "verification/axioms.log").read_text()
    actual_declarations = [json.loads(x) for x in re.findall(r"VERIFIED_DECLARATION ([^\n]+)", audit)]
    require(index(actual_declarations, "actual axiom log") == after
            and re.findall(r"OVERFULL_AXIOM_AUDIT_OK (\d+)", audit) == [str(len(after))],
            "Actual complete audit log disagrees with fresh results")
    build = (ROOT / "verification/build.log").read_text()
    build_jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", build)
    require(bool(build_jobs), "Fresh strict build log has no success marker")
    jobs = int(build_jobs[-1])
    console = (RUN / "verification-console.log").read_text()
    require(f"OVERFULL_AXIOM_AUDIT_OK {len(after)}" in console
            and f"Checked {len(after)} project declarations; full manuscript status: unverified." in console,
            "Current full-verifier console lacks its matching final output")

    recovery = load(RUN / "recovery.json")
    require(recovery["baseline_commit"] == BASE and recovery["recovered_attempt_commit"] == RECOVERED,
            "Recovery record identifies a different baseline")
    preserved_history = []
    for path in sorted(baseline_paths):
        if path.startswith(("verification/runs/", "recovery/")):
            require((ROOT / path).read_bytes() == old_bytes(path),
                    f"Historical baseline evidence changed: {path}")
            preserved_history.append(path)
    recovered_history = []
    for path in recovery["recovered_paths"]:
        if path.startswith("verification/runs/"):
            require((ROOT / path).read_bytes() == old_bytes(path, RECOVERED),
                    f"Recovered historical run evidence changed: {path}")
            recovered_history.append(path)
    early = publication_record("early-publication.json", required=True)
    require(early["commit"] == EARLY, "Early recovery checkpoint differs from the observed record")
    interim = publication_record("interim-publication.json")
    checks = targeted_checks()
    failures = [r for r in checks if r["status"] == "failed"]
    successes = [r for r in checks if r["status"] == "passed"]

    evidence = {rel(p) for p in RUN.rglob("*") if p.is_file()
                and p.name not in {"run.json", "REPORT.md", "report.md"}
                and "__pycache__" not in p.parts and p.suffix != ".pyc"}
    evidence |= {"verification/results.json", "verification/build.log", "verification/axioms.log",
                 "docs/continuation-handoff.md", "docs/assigned-part-semantic-review.md",
                 "docs/assigned-part-verification.md", "docs/joining-circuit-verification.md",
                 joining["source_path"], joining["declaration_map_path"],
                 assigned["source_path"], assigned["declaration_map_path"],
                 *(f"verification/{p}" for p in OLD_MAPS.values())}
    finished = datetime.now(timezone.utc)
    new_names = sorted(set(after) - set(before))
    record = {
        "schema_version": 1,
        "status": "verification_passed",
        "run_id": RUN.name,
        "run_started_at_utc": START,
        "recorded_at_utc": finished.isoformat(),
        "elapsed_seconds_to_record": round((finished - datetime.fromisoformat(START)).total_seconds(), 3),
        "baseline_commit": BASE,
        "recovered_attempt_commit": RECOVERED,
        "early_publication": early,
        "interim_publication": interim,
        "verification_command": command,
        "strict_build_jobs": jobs,
        "verified_declaration_count": len(after),
        "previous_verified_declarations_preserved": len(before),
        "new_verified_declaration_count": len(new_names),
        "new_verified_declarations": new_names,
        "all_prior_declaration_names_modules_and_axiom_sets_preserved": True,
        "all_previous_nonroot_lean_sources_byte_identical": True,
        "byte_identical_previous_nonroot_lean_source_count": len(preserved_sources),
        "root_change": "Exactly two added imports; removing them reproduces the baseline root bytes.",
        "stock_audit_byte_identical": True,
        "source_hash_count": len(sources),
        "verification_input_hash_count": len(inputs),
        "imported_project_module_count": len(current["imported_project_modules"]),
        "frozen_input_count": len(frozen),
        "all_current_source_and_input_paths_and_hashes_match_frozen_verification": True,
        "all_69_original_statement_hashes_preserved": True,
        "all_47_previous_completed_assertion_records_preserved": True,
        "fully_verified_numbered_assertion_count": len(complete),
        "remaining_numbered_assertion_count": len(assertions) - len(complete),
        "main_theorem_verified": False,
        "recovered_joining_module_count": joining["module_count"],
        "recovered_joining_public_theorem_count": joining["public_theorem_count"],
        "recovered_joining_audited_declaration_count": joining["audited_declaration_count"],
        "recovered_joining_sources_byte_identical": recovered_sources,
        "recreated_and_new_assigned_module_count": assigned["module_count"],
        "recreated_and_new_assigned_public_theorem_count": assigned["public_theorem_count"],
        "recreated_and_new_assigned_audited_declaration_count": assigned["audited_declaration_count"],
        "assigned_sources_not_claimed_byte_identical_to_lost_unpublished_drafts": True,
        "separate_host_composition_new_in_this_run": True,
        "historical_prior_check_report": recovery.get("prior_observed_full_check"),
        "lost_prior_full_logs_not_recreated_or_replayed_as_evidence": True,
        "previous_declaration_maps_preserved": list(OLD_MAPS.values()),
        "baseline_historical_evidence_preserved": preserved_history,
        "recovered_historical_evidence_preserved": recovered_history,
        "allowed_logical_axioms": current["allowed_logical_axioms"],
        "targeted_check_count": len(checks),
        "successful_targeted_check_count": len(successes),
        "failed_targeted_check_count": len(failures),
        "targeted_checks": checks,
        "evidence_sha256": {p: sha(ROOT / p) for p in sorted(evidence)},
        "publication": {
            "repository": "fly31415926/overfull-lean",
            "target_branches": ["main", "verified-bipartite-continuation-2026-11-21"],
            "status": "pending_verified_branch_updates",
            "note": "This record precedes branch updates. The containing commit identifies the candidate; subsequent remote-head verification confirms publication.",
        },
        "scope": assigned["source"]["scope"],
    }
    check_rows = "\n".join(
        f"| `{Path(r['metadata_path']).name}` | {r['command_record']['exit_code']} | {r['status']} |"
        for r in checks)
    interim_note = (f"A later frozen-candidate recovery commit is `{interim['commit']}`."
                    if interim else "No later interim publication record was present when this report was generated.")
    report = f"""# Recovery and continuation: actual assigned parts and joining proofs

**Fresh complete verification passed for the exact frozen candidate.**
The run began at `{START}`; this record was generated at
`{finished.isoformat()}`. The verified baseline is `{BASE}`.
The early recovery snapshot is `{early['commit']}`. {interim_note}

## What was recovered and what was proved now

Five joining modules, with {joining['public_theorem_count']} public theorems,
were recovered byte-for-byte from published attempt `{RECOVERED}`. They prove
the original-host joining decomposition for a supplied assignment to at most
three labels. All-even fibers yield exact matching partitions; exactly two
odd fibers yield exactly `h` primary matchings plus surplus matchings, retaining
all original joining copies and their cut footprints.

The unpublished assigned-part drafts were lost when the workspace was
replaced. The {assigned['module_count']} current assigned-part modules were
recreated and freshly checked; byte identity with those lost drafts is not
claimed. Their {assigned['public_theorem_count']} public theorems construct
actual labels from a specified perfect matching, prove the exact assigned
fibers and selected cuts, derive their parity, and compose the construction
with joining decomposition. With at most two exceptions, the optional pair
fiber has zero or two vertices and contains at most one selected internal copy.

The new `assignedLabel_joining_decomposition_in_host` refinement uses the
representative in one graph `G` to construct labels for another host `H` on
the same vertices. The representative need not survive in `H`; the output
retains `H`'s own actual edge copies. Regularity and absence of overfull sets
for `H` remain explicit residual-stage hypotheses, not consequences falsely
attributed to reserve removal.

The supplied perfect-matching representative is preserved. Generic interfaces
can aggregate multiple internal pairs into one even fiber; the source-specific
single optional pair interpretation uses the explicit two-exception bound.
The native multigraph proofs do not assume the original host is simple.

## Actual verification and preservation

| Check | Result |
| --- | --- |
| Fresh `python3 scripts/verify.py` | Exit 0; recorder status passed |
| Strict `lake build --wfail` | {jobs:,} jobs passed |
| Unchanged complete `Audit.lean` | {len(after):,} declarations passed |
| Prior declaration names/modules/axiom sets | All {len(before):,} preserved |
| New audited declarations relative to verified baseline | {len(new_names):,} |
| Prior nonroot Lean files | {len(preserved_sources)} byte-identical, including stock audit |
| Prior declaration maps | All {len(OLD_MAPS)} byte-identical |
| Recovered joining public/audited declarations | {joining['public_theorem_count']} / {joining['audited_declaration_count']} |
| Recreated and new assigned public/audited declarations | {assigned['public_theorem_count']} / {assigned['audited_declaration_count']} |
| Exact Lean source path/hash inventory | {len(sources)} files |
| Exact other verification-input path/hash inventory | {len(inputs)} files |
| Frozen source/input inventory | {len(frozen)} paths; unchanged through checking and recording |
| Numbered manuscript assertions | {len(complete)}/{len(assertions)} complete; {len(assertions)-len(complete)} remain |

The only allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Lean remains pinned to `leanprover/lean4:v4.24.0`, with mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; all dependency source revisions
match the verified baseline. The actual complete audit log is compared to
every declaration record in the fresh results. Removing the two new imports
reproduces the baseline root file exactly. All 69 original statement hashes
and all 47 previously complete assertion records are unchanged.

`run.json` records exact evidence hashes, complete group mappings, the frozen
input identity and genuine current command results. Full logs are in
`verification/build.log`, `verification/axioms.log` and this run's
`verification-console.log`. Source and declaration maps separately identify
the recovered joining group and the recreated/new assigned group.

## Recovery and diagnostic honesty

The earlier conversation reported a complete joining audit, but its final
raw outputs were not preserved in the referenced recovery commit. They are
not fabricated, replayed or used as current verification evidence here.
This report relies on the new complete verifier run. The published prior
targeted diagnostics and historical recovery evidence remain byte-identical.
The two manuscript documents already authorized and published in the
baseline remain preserved; no new source-release restriction is introduced.

Current retained targeted records contain {len(successes)} successes and
{len(failures)} failures. A failed check remains a failed check. Actual logs
and captured source snapshots are retained, including heartbeat or warning
failures where they occurred during recreation.

| Current command record | Exit code | Actual result |
| --- | ---: | --- |
{check_rows}

The earlier `cb05ef5` reconstruction evidence remains historical. Neither
this run nor the recovered joining attempt is described as that unavailable
original commit/tree.

## Remaining proof target

The assigned parts, exact selected cuts and joining-stage composition are
now checked supporting results. The native multigraph heavy-pattern and
reserve construction, reserve-degree estimates, residual safety, palette
grouping, robust completions, auxiliary graphs and original-host factorization
remain unfinished. Existing simple-graph pattern/reserve APIs do not supply
those multigraph steps. The exact old-core crossing count has not silently
been identified with an unrelated pattern-code statistic.

Full 4.4/4.5/4.6, the remaining 4.16 branches, general Section 6, structural
inputs and the main theorem remain incomplete. No numbered assertion is
newly counted complete. Continue from `docs/continuation-handoff.md`,
`docs/next-verification-target.md` and the source/proof maps.

## Publication boundary

This report was generated before the verified branch updates. It does not
claim those updates have happened. Publication must preserve concurrent
work, update both verified branches to the same checked source checkpoint,
and confirm the commit/tree and both remote heads afterward.
"""
    (RUN / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    (RUN / "REPORT.md").write_text(report)
    print(json.dumps({k: record[k] for k in [
        "status", "verified_declaration_count", "previous_verified_declarations_preserved",
        "new_verified_declaration_count", "source_hash_count", "verification_input_hash_count",
        "recovered_joining_public_theorem_count", "recreated_and_new_assigned_public_theorem_count",
        "failed_targeted_check_count",
    ]}, indent=2))


if __name__ == "__main__":
    main()
