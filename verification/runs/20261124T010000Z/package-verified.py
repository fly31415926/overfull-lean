#!/usr/bin/env python3
"""Commit and package only the genuinely verified local integration; no network."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
RELEASE = ROOT.parent / "native-integration-release"
BASELINE = "d2e7b1274d280ef6567cb2b562ec6e94eec2dda0"
BASELINE_TREE = "9850008a20bfd828d8ab9da4c5e8d1bf50240570"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def main():
    report = json.loads((RUN / "preservation.json").read_text())
    result = json.loads((ROOT / "verification/results.json").read_text())
    command = json.loads((RUN / "verification-command.json").read_text())
    frozen = json.loads((RUN / "frozen-candidate-inputs.json").read_text())
    source = json.loads((ROOT / "docs/native-integration-source.json").read_text())
    require(report["status"] == "verification_and_preservation_passed"
            and report["actual_preceding_verified_commit"] == BASELINE
            and report["actual_preceding_verified_tree"] == BASELINE_TREE
            and report["previous_verified_declarations_preserved"] == 12951
            and report["previous_completed_result_mappings_preserved"] == 2063
            and report["baseline_frozen_input_count"] == 670,
            "The exact baseline preservation check has not passed")
    preservation = json.loads((RUN / "record-final-command.json").read_text())
    require(preservation["status"] == "passed" and preservation["exit_code"] == 0
            and preservation["checker_sha256"] == digest((RUN / "record-final.py").read_bytes())
            and preservation["output_sha256"] == digest((RUN / "record-final-output.log").read_bytes())
            and preservation["preservation_report_sha256"] == digest((RUN / "preservation.json").read_bytes()),
            "Actual supplementary preservation command/source/output identity disagrees")
    supplement = json.loads((RUN / "supplementary-evidence-after-freeze.json").read_text())
    require(supplement["preservation_report_sha256"] == digest((RUN / "preservation.json").read_bytes()),
            "Supplementary post-check evidence points to a different report")
    for path, expected in supplement["files"].items():
        require(digest((ROOT / path).read_bytes()) == expected, "Supplementary bytes changed: " + path)
    require(command["status"] == "passed" and command["exit_code"] == 0
            and command["all_frozen_inputs_unchanged"] is True,
            "The complete frozen verifier has not passed")
    terminal = json.loads((RUN / "execution-terminal.json").read_text())
    require(terminal["actual_terminal_exit_code"] == 0
            and terminal["attempt"] == command["attempt"]
            and terminal["status"] == "passed" and terminal["exit_code"] == 0,
            "The actual supervised full-verifier exit was not observed as successful")
    require(result["lean_build_passed"] and result["axiom_audit_passed"]
            and not result["main_theorem_verified"]
            and result["fully_verified_numbered_assertion_count"] == 47,
            "Wrong verification or manuscript scope")
    for path, expected in {**frozen, **report["evidence_sha256"]}.items():
        require(digest((ROOT / path).read_bytes()) == expected, "Checked bytes changed: " + path)
    require(git("rev-parse", "HEAD").decode().strip() == BASELINE,
            "Worktree advanced after the pinned baseline")
    require(source["module_count"] == report["native_integration"]["module_count"]
            and source["public_theorem_count"] == report["native_integration"]["public_theorem_count"],
            "Source counts disagree with the actual preservation report")
    git("diff", "--check")
    bundle = RELEASE / "overfull-native-integration-20261124.bundle"
    archive = RELEASE / "overfull-native-integration-20261124.zip"
    require(not bundle.exists() and not archive.exists(), "Release artifact paths already exist")
    git("add", "--all")
    identity = git("show", "-s", "--format=%an%x00%ae", BASELINE).decode().strip().split("\0")
    new_count = result["verified_declaration_count"] - 12951
    message = (
        "Verify native weighted assembly and bounded two-core completion\n\n"
        f"{source['module_count']} new modules contain {source['public_theorem_count']} public theorem proofs. "
        f"The strict complete build and unchanged axiom audit passed for {result['verified_declaration_count']} "
        f"declarations, adding {new_count} while preserving all 12,951 preceding names, module owners and axiom sets. "
        "All 2,063 preceding completed-result mappings, 670 baseline frozen inputs and 69 assertion records were checked.\n\n"
        + source["scope"] + "\n\n"
        "The exact native-star checkpoint d2e7b127 is the verified local baseline. "
        "Every genuine failed focused attempt and full raw audit is retained. Publication is recorded separately. "
        "Numbered coverage remains 47/69 and the main theorem remains unproved."
    )
    git("-c", "user.name=" + identity[0], "-c", "user.email=" + identity[1], "commit", "-m", message)
    commit = git("rev-parse", "HEAD").decode().strip()
    tree = git("rev-parse", "HEAD^{tree}").decode().strip()
    branch = git("branch", "--show-current").decode().strip()
    require(bool(branch) and not git("status", "--porcelain").strip(), "Committed worktree is detached or dirty")
    for path, expected in {**frozen, **report["evidence_sha256"], **supplement["files"]}.items():
        require(digest(git("show", commit + ":" + path)) == expected,
                "Committed checked bytes differ: " + path)
    RELEASE.mkdir(exist_ok=True)
    git("bundle", "create", str(bundle), "HEAD", "refs/heads/" + branch)
    check = subprocess.run(["git", "bundle", "verify", str(bundle)], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (RELEASE / "bundle-verification.log").write_text(check.stdout)
    require(check.returncode == 0, "Bundle verification failed")
    git("archive", "--format=zip", "--output=" + str(archive), commit)
    entries = {}
    for item in git("ls-tree", "-rz", commit).split(b"\0"):
        if not item:
            continue
        meta, path = item.split(b"\t", 1)
        mode, kind, sha = meta.decode().split()
        require(kind == "blob", "Unexpected nonblob committed entry")
        entries[path.decode()] = sha
    with zipfile.ZipFile(archive) as archive_zip:
        require(archive_zip.testzip() is None, "ZIP CRC check failed")
        require({name for name in archive_zip.namelist() if not name.endswith("/")} == set(entries),
                "ZIP file inventory differs from the exact committed tree")
        for name, expected in entries.items():
            data = archive_zip.read(name)
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(blob == expected, "ZIP bytes differ from committed blob: " + name)
    report_copy = RELEASE / "overfull-native-integration-verification-report-20261124.md"
    shutil.copyfile(RUN / "final-report.md", report_copy)
    run = json.loads((RUN / "run.json").read_text())
    manifest = {"created_at_utc": datetime.now(timezone.utc).isoformat(),
                "commit": commit, "tree": tree, "branch": branch,
                "baseline_local_verified_commit": BASELINE, "baseline_local_verified_tree": BASELINE_TREE,
                "baseline_public_commit_at_input_freeze": None,
                "last_observed_public_main_at_input_freeze": run["observed_public_main"],
                "last_observed_public_continuation_at_input_freeze": run["observed_public_continuation"],
                "tracked_file_count": len(entries), "strict_build_jobs": report["strict_build_jobs"],
                "verified_declaration_count": result["verified_declaration_count"],
                "preceding_declarations_preserved": 12951, "preceding_completed_mappings_preserved": 2063,
                "preceding_frozen_input_count": 670, "new_verified_declarations": new_count,
                "new_modules": source["module_count"], "new_public_theorem_proofs": source["public_theorem_count"],
                "numbered_assertions_complete": 47, "numbered_assertions_total": 69,
                "main_theorem_verified": False,
                "baseline_publication_status_at_input_freeze": "verified_local_publication_blocked_by_automatic_review_at_input_freeze",
                "new_continuation_publication_status": "local_verified_checkpoint",
                "bundle_verification_exit_code": check.returncode,
                "zip_crc_and_all_committed_blob_bytes_verified": True,
                "files": [{"path": str(p), "bytes": p.stat().st_size, "sha256": digest(p.read_bytes())}
                          for p in [bundle, archive, report_copy]]}
    (RELEASE / "checkpoint-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
