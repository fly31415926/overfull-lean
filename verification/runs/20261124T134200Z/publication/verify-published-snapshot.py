#!/usr/bin/env python3
"""Check fetched published bytes against the immutable full-verification evidence."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from prepare import BASELINE_COMMIT, DEFAULT_BASELINE_TREE, EXPECTED_FROZEN_INPUTS

ap = argparse.ArgumentParser()
ap.add_argument("--commit", required=True)
ap.add_argument("--tree", required=True)
ap.add_argument("--parent", required=True)
ap.add_argument("--output", required=True)
args = ap.parse_args()
ROOT = Path(__file__).resolve().parents[4]
RUN = Path("verification/runs/20261124T134200Z")
GIT_ENV = {**os.environ, "GIT_NO_LAZY_FETCH": "1", "GIT_OPTIONAL_LOCKS": "0"}
def git(*argv):
    return subprocess.check_output(["git", *argv], cwd=ROOT, env=GIT_ENV)
def require(value, message):
    if not value:
        raise RuntimeError(message)
def sha(data):
    return hashlib.sha256(data).hexdigest()
commit = git("rev-parse", args.commit + "^{commit}").decode().strip()
tree = git("rev-parse", commit + "^{tree}").decode().strip()
parents = git("show", "-s", "--format=%P", commit).decode().strip().split()
require(commit == args.commit, "Commit differs from the exact requested object")
require(tree == args.tree, ("Tree mismatch", tree, args.tree))
require(parents == [args.parent], ("Parent mismatch", parents))
entries = {}
for entry in git("ls-tree", "-r", "-z", commit).split(b"\0"):
    if entry:
        meta, path = entry.split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        entries[path.decode()] = (mode, kind, oid)
reader = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=GIT_ENV)
cache = {}
def read(path):
    mode, kind, oid = entries[str(path)]
    require(kind == "blob", ("Expected blob", path, kind))
    if oid not in cache:
        reader.stdin.write((oid + "\n").encode())
        reader.stdin.flush()
        header = reader.stdout.readline().decode().strip().split()
        require(header[:2] == [oid, "blob"], ("Unexpected cat-file header", header))
        data = reader.stdout.read(int(header[2]))
        require(len(data) == int(header[2]), "Truncated blob read")
        require(reader.stdout.read(1) == b"\n", "Missing blob separator")
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(actual == oid, ("Blob hash mismatch", oid, actual))
        cache[oid] = data
    return cache[oid]
def parsed(path):
    return json.loads(read(path))
frozen_path = RUN / "full-01/frozen-inputs.json"
controls_path = RUN / "full-01/frozen-controls.json"
terminal_path = RUN / "full-01/terminal.json"
frozen = parsed(frozen_path)
controls = parsed(controls_path)
terminal = parsed(terminal_path)
require(len(frozen) == EXPECTED_FROZEN_INPUTS and controls, "Unexpected frozen inputs or empty controls")
require(terminal["baseline_commit"] == BASELINE_COMMIT and terminal["baseline_tree"] == DEFAULT_BASELINE_TREE,
        "Terminal baseline differs from the verified continuation baseline")
require(terminal["frozen_input_count"] == len(frozen) and terminal["control_sha256"] == controls,
        "Terminal inventories differ from the frozen manifests")
require(terminal["status"] == "passed" and terminal["exit_code"] == 0 and terminal["wrapper_exit_code"] == 0
        and terminal["preflight_passed"] is True and terminal["verifier_launched"] is True
        and terminal["inputs_unchanged"] is True and terminal["controls_unchanged"] is True
        and terminal["wrapper_errors"] == [] and terminal["missing_principal_outputs"] == [],
        "The complete frozen verifier did not pass")
require(read(terminal_path) == read(RUN / "full-01/command.json"), "Command and terminal receipts differ")
require(read(frozen_path) == (ROOT / frozen_path).read_bytes(), "Published frozen-input manifest differs")
require(read(controls_path) == (ROOT / controls_path).read_bytes(), "Published frozen-control manifest differs")
require(sha(read(RUN / "full-01/output.log")) == terminal["output_sha256"], "Full-run output log differs")
checks = []
def check(path, expected, size=None):
    data = read(path)
    actual = sha(data)
    require(actual == expected, ("Content digest mismatch", str(path), expected, actual))
    if size is not None:
        require(len(data) == size, ("Content size mismatch", str(path)))
    checks.append({"path": str(path), "sha256": actual, "bytes": len(data)})
for name, digest in frozen.items():
    check(name, digest)
    check(RUN / "full-01/input" / name, digest)
    require(sha((ROOT / name).read_bytes()) == digest, ("Working frozen input changed", name))
for name, digest in controls.items():
    check(RUN / name, digest)
    check(RUN / "full-01/control" / name, digest)
    require(sha((ROOT / RUN / name).read_bytes()) == digest, ("Working frozen control changed", name))
for output in terminal["outputs"]:
    check(output["path"], output["sha256"], output["bytes"])
    check(RUN / "full-01/artifacts" / output["path"], output["sha256"], output["bytes"])
output_paths = {output["path"] for output in terminal["outputs"]}
require(len(output_paths) == len(terminal["outputs"]) and output_paths, "Duplicate or empty output inventory")
scope = parsed(RUN / "verification-scope.json")
require({"verification/results.json", "verification/build.log", "verification/axioms.log",
         scope["declaration_map"]} <= output_paths, "Principal verifier output is missing")
artifact_prefix = str(RUN / "full-01/artifacts") + "/"
require({name.removeprefix(artifact_prefix) for name in entries if name.startswith(artifact_prefix)} == output_paths,
        "Published archived-output inventory differs from terminal receipt")
run_paths = [name for name in entries
             if name.startswith(str(RUN) + "/")
             and not name.startswith(str(RUN / "publication") + "/")]
local_run_paths = {p.relative_to(ROOT).as_posix() for p in (ROOT / RUN).rglob("*")
                   if p.is_file() and ROOT / RUN / "publication" not in p.parents
                   and "__pycache__" not in p.parts and p != ROOT / RUN / "build.lock"}
require(set(run_paths) == local_run_paths, "Published nonpublication run inventory differs from local evidence")
for name in run_paths:
    require(read(name) == (ROOT / name).read_bytes(), ("Published run evidence differs", name))
reader.stdin.close()
require(reader.wait() == 0, "git cat-file failed")
result = {
    "schema_version": 1,
    "kind": "fetched_public_commit_integrity",
    "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "commit": commit,
    "tree": tree,
    "parent": parents[0],
    "tracked_file_count": len(entries),
    "continuation_baseline_commit": BASELINE_COMMIT,
    "continuation_baseline_tree": DEFAULT_BASELINE_TREE,
    "frozen_input_count": len(frozen),
    "frozen_control_count": len(controls),
    "archived_output_count": len(terminal["outputs"]),
    "nonpublication_run_file_count": len(run_paths),
    "explicit_digest_checks": len(checks),
    "unique_blob_bytes_checked": len(cache),
    "all_published_and_frozen_bytes_match": True,
    "all_nonpublication_run_files_match_working_evidence": True,
    "command_and_terminal_identical": True,
    "full_verifier_exit_code": terminal["exit_code"],
    "full_wrapper_exit_code": terminal["wrapper_exit_code"],
    "passed": True,
    "checks": checks,
}
destination = ROOT / args.output
destination.open("x").write(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))
