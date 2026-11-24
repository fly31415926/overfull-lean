#!/usr/bin/env python3
"""Check fetched published bytes against the immutable full-verification evidence."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument("--commit", required=True)
ap.add_argument("--tree", required=True)
ap.add_argument("--parent", required=True)
ap.add_argument("--output", required=True)
args = ap.parse_args()
ROOT = Path(__file__).resolve().parents[4]
RUN = Path("verification/runs/20261124T120200Z")
def git(*argv):
    return subprocess.check_output(["git", *argv], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
commit = git("rev-parse", args.commit + "^{commit}").decode().strip()
tree = git("rev-parse", commit + "^{tree}").decode().strip()
parents = git("show", "-s", "--format=%P", commit).decode().strip().split()
assert commit == args.commit
assert tree == args.tree, (tree, args.tree)
assert parents == [args.parent], parents
entries = {}
for entry in git("ls-tree", "-r", "-z", commit).split(b"\0"):
    if entry:
        meta, path = entry.split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        entries[path.decode()] = (mode, kind, oid)
reader = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE)
cache = {}
def read(path):
    mode, kind, oid = entries[str(path)]
    assert kind == "blob", (path, kind)
    if oid not in cache:
        reader.stdin.write((oid + "\n").encode())
        reader.stdin.flush()
        header = reader.stdout.readline().decode().strip().split()
        assert header[:2] == [oid, "blob"], header
        data = reader.stdout.read(int(header[2]))
        assert len(data) == int(header[2])
        assert reader.stdout.read(1) == b"\n"
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert actual == oid
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
assert len(frozen) == 794 and len(controls) == 16
assert terminal["exit_code"] == 0 and terminal["wrapper_exit_code"] == 0
assert read(terminal_path) == read(RUN / "full-01/command.json")
assert read(frozen_path) == (ROOT / frozen_path).read_bytes()
assert read(controls_path) == (ROOT / controls_path).read_bytes()
checks = []
def check(path, expected, size=None):
    data = read(path)
    actual = sha(data)
    assert actual == expected, (str(path), expected, actual)
    if size is not None:
        assert len(data) == size
    checks.append({"path": str(path), "sha256": actual, "bytes": len(data)})
for name, digest in frozen.items():
    check(name, digest)
    check(RUN / "full-01/input" / name, digest)
    assert sha((ROOT / name).read_bytes()) == digest
for name, digest in controls.items():
    check(RUN / name, digest)
    check(RUN / "full-01/control" / name, digest)
    assert sha((ROOT / RUN / name).read_bytes()) == digest
for output in terminal["outputs"]:
    check(output["path"], output["sha256"], output["bytes"])
    check(RUN / "full-01/artifacts" / output["path"], output["sha256"], output["bytes"])
assert len(terminal["outputs"]) == 24
run_paths = [name for name in entries
             if name.startswith(str(RUN) + "/")
             and not name.startswith(str(RUN / "publication") + "/")]
for name in run_paths:
    assert read(name) == (ROOT / name).read_bytes(), name
reader.stdin.close()
assert reader.wait() == 0
result = {
    "schema_version": 1,
    "kind": "fetched_public_commit_integrity",
    "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "commit": commit,
    "tree": tree,
    "parent": parents[0],
    "tracked_file_count": len(entries),
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
