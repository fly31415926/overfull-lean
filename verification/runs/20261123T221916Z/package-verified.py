#!/usr/bin/env python3
"""Commit and package only an actually verified and preserved local candidate.

This script performs no network publication. The public upload remains
subject to the recorded automatic approval review. The bundle contains
the exact Git history; the ZIP contains the complete committed snapshot.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
RELEASE = ROOT.parent / "release"
BASELINE = "1b5663a8fb472e42e698f4e09fcfc55497393815"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise SystemExit(message)


report = json.loads((RUN / "preservation.json").read_text())
results = json.loads((ROOT / "verification/results.json").read_text())
command = json.loads((RUN / "verification-command.json").read_text())
frozen = json.loads((RUN / "frozen-candidate-inputs.json").read_text())
require(report["status"] == "verification_and_preservation_passed",
        "The complete preservation checker has not passed")
require(command["status"] == "passed" and command["exit_code"] == 0
        and command["all_frozen_inputs_unchanged"] is True,
        "The latest full verifier has not passed unchanged")
require(results["lean_build_passed"] and results["axiom_audit_passed"]
        and results["main_theorem_verified"] is False
        and results["fully_verified_numbered_assertion_count"] == 47,
        "Verification result or manuscript scope is incorrect")
for path, expected in frozen.items():
    require(sha((ROOT / path).read_bytes()) == expected, f"Frozen input changed: {path}")
for path, expected in report["evidence_sha256"].items():
    require(sha((ROOT / path).read_bytes()) == expected, f"Checked evidence changed: {path}")
require(git("rev-parse", "HEAD").decode().strip() == BASELINE,
        "The worktree advanced after the checked baseline; inspect before committing")
git("diff", "--check")
git("add", "--all")
new_count = results["verified_declaration_count"] - 12559
message = (
    "Verify exceptional pair coloring and complete protected reserve classes\n\n"
    "Ten new modules contain 79 mapped public theorem proofs. The complete\n"
    f"strict build and unchanged full axiom audit passed for {results['verified_declaration_count']}\n"
    f"declarations, adding {new_count} and preserving all 12,559 preceding\n"
    "declaration names, module labels and axiom sets. Preserve all 1,859\n"
    "preceding completed-result mappings, source manifests and actual logs.\n\n"
    "Construct exact exceptional-pair free palettes and prescribed-copy\n"
    "coloring, all-even palettes with reserved empty colors, and native\n"
    "odd/even extensions to whole surviving original reserve boundaries.\n\n"
    "Coverage remains 47/69; Corollary 4.6 and the main theorem are unproved.\n"
    "Complete public publication remains blocked by automatic approval review.\n"
)
git("commit", "-m", message)
commit = git("rev-parse", "HEAD").decode().strip()
tree = git("rev-parse", "HEAD^{tree}").decode().strip()
branch = git("branch", "--show-current").decode().strip()
require(not git("status", "--porcelain").strip(), "The committed worktree is not clean")
for path, expected in frozen.items():
    require(sha(git("show", f"{commit}:{path}")) == expected,
            f"Committed frozen input differs: {path}")
RELEASE.mkdir(exist_ok=True)
bundle = RELEASE / "overfull-verified-20261123.bundle"
archive = RELEASE / "overfull-verified-20261123.zip"
require(not bundle.exists() and not archive.exists(), "Release paths already exist; inspect first")
git("bundle", "create", str(bundle), "HEAD", f"refs/heads/{branch}")
bundle_check = subprocess.run(["git", "bundle", "verify", str(bundle)], cwd=ROOT,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(RELEASE / "bundle-verification.log").write_text(bundle_check.stdout)
require(bundle_check.returncode == 0, "Git bundle verification failed")
git("archive", "--format=zip", f"--output={archive}", commit)
report_copy = RELEASE / "overfull-verification-report-20261123.md"
shutil.copyfile(RUN / "final-report.md", report_copy)
manifest = {
    "created_at_utc": datetime.now(timezone.utc).isoformat(),
    "commit": commit, "tree": tree, "branch": branch,
    "preceding_local_verified_commit": BASELINE,
    "tracked_file_count": len(git("ls-tree", "-rz", "--name-only", commit).split(b"\0")) - 1,
    "full_verification_run": str(RUN.relative_to(ROOT)),
    "full_verifier_exit_code": command["exit_code"],
    "strict_build_jobs": report["strict_build_jobs"],
    "verified_declaration_count": results["verified_declaration_count"],
    "preceding_declarations_preserved": 12559,
    "new_verified_declarations": new_count,
    "new_modules": 10, "new_public_theorem_proofs": 79,
    "numbered_assertions_complete": 47, "numbered_assertions_total": 69,
    "main_theorem_verified": False,
    "publication_status": "blocked_by_automatic_approval_review",
    "public_destination": "https://github.com/fly31415926/overfull-lean",
    "public_branches_updated_by_this_run": False,
    "files": [{"path": str(p), "bytes": p.stat().st_size, "sha256": sha(p.read_bytes())}
              for p in [bundle, archive, report_copy]],
}
(RELEASE / "publication-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
