#!/usr/bin/env python3
"""Export an exact Git tree and raw changed blobs, without committing or publishing.

Example (explicit parent must be an existing full commit or tree SHA):
  python3 verification/runs/20261123T042619Z/publication_snapshot.py \
    --parent <40-hex-SHA> --phase interim-01 --mode interim

Outputs are <phase>-metadata.json and <phase>-blobs/<Git-blob-SHA> outside
the checkout. Never decode/re-encode the exported blobs for upload: use their
raw bytes or base64 and compare the returned Git SHA. The temporary index is
outside the repository and the real index, worktree and refs are untouched.
Capture stdout outside the checkout so it is not part of its own snapshot.

Interim mode omits three top-level verification outputs entirely from the
constructed tree; existing parent versions become explicit deletions. It
allows append-only growth of current-run .log files and reports those captures
as pending. Final mode omits no eligible tracked/unignored file and requires
a stable capture. Neither mode performs or certifies Lean verification.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tempfile


DEFAULT_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_OUTPUT = DEFAULT_ROOT.parent / "current-publication"
DEFAULT_RUN_ID = Path(__file__).resolve().parent.name
INTERIM_OMISSIONS = {
    "verification/results.json", "verification/axioms.log", "verification/build.log",
}
FORBIDDEN_PARTS = {
    ".git", ".lake", "node_modules", "__pycache__", ".cache", ".venv",
    "venv", "lean-runtime", ".ssh", ".aws", ".gnupg",
}
FORBIDDEN_SUFFIXES = {
    ".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".dll", ".exe",
    ".pyc", ".pyo", ".class", ".obj", ".lib", ".pdb", ".swp",
}
SECRET_PATTERNS = {
    "private-key header": re.compile(rb"-----BEGIN (?:RSA |EC |DSA |OPENSSH |ENCRYPTED )?PRIVATE KEY-----"),
    "GitHub token": re.compile(rb"\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,})\b"),
    "AWS access-key identifier": re.compile(rb"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b"),
    "API secret token": re.compile(rb"\bsk-(?:(?:proj|svcacct)-)?[A-Za-z0-9_-]{24,}\b"),
    "credential-bearing URL": re.compile(rb"https?://[^\s/:@]+:[^\s/@]+@"),
}


class SnapshotError(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SnapshotError(message)


def git(root: Path, args: list[str], env: dict[str, str], data: bytes | None = None) -> bytes:
    result = subprocess.run(["git", *args], cwd=root, env=env, input=data,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0,
            f"Git plumbing command {args[0]!r} failed with exit {result.returncode}; no publication occurred")
    return result.stdout


def oid(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def fingerprint(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None


def tree_entries(root: Path, tree: str, env: dict[str, str]) -> dict[str, dict[str, str]]:
    entries = {}
    for record in git(root, ["ls-tree", "-r", "-z", tree], env).split(b"\0"):
        if not record:
            continue
        header, raw_path = record.split(b"\t", 1)
        mode, kind, sha = header.decode("ascii").split()
        path = raw_path.decode("utf-8")
        require(path not in entries, "Duplicate path in parent tree")
        entries[path] = {"path": path, "mode": mode, "type": kind, "sha": sha}
    return entries


def current_paths(root: Path, env: dict[str, str], omitted: set[str]) -> set[str]:
    paths = set()
    raw = git(root, ["ls-files", "--cached", "--others", "--exclude-standard", "-z"], env)
    for item in raw.split(b"\0"):
        if not item:
            continue
        name = item.decode("utf-8")
        p = PurePosixPath(name)
        require(not p.is_absolute() and ".." not in p.parts
                and not any(ord(c) < 32 or ord(c) == 127 for c in name),
                "Unsafe repository path encountered")
        if name in omitted:
            continue
        path = root / name
        try:
            info = path.lstat()
        except FileNotFoundError:
            continue
        if stat.S_ISDIR(info.st_mode):
            continue  # A parent file replaced by a directory is a deletion plus child additions.
        require(stat.S_ISREG(info.st_mode), f"Symlink or nonregular file refused: {name}")
        require(path.resolve().is_relative_to(root), f"Path escapes checkout: {name}")
        paths.add(name)
    return paths


def screen(path: str, data: bytes, unchanged_parent_blob: bool) -> bool:
    """Return True only for a retained, byte-identical historical binary blob."""
    p = PurePosixPath(path)
    lower_parts = [part.lower() for part in p.parts]
    require(not set(lower_parts) & FORBIDDEN_PARTS, f"Cache/private path refused: {path}")
    require(p.suffix.lower() not in FORBIDDEN_SUFFIXES, f"Generated/binary artifact refused: {path}")
    name = p.name.lower()
    require(not (name == ".env" or name.startswith(".env.")
                 or name in {".netrc", ".npmrc", ".pypirc", ".git-credentials", "credentials",
                             "credentials.json", "token.json", "tokens.json", "id_rsa", "id_ed25519"}
                 or name.endswith((".pem", ".key", ".p12", ".pfx"))),
            f"Credential/private-file name refused: {path}")
    try:
        data.decode("utf-8")
        is_text = b"\0" not in data
    except UnicodeDecodeError:
        is_text = False
    if not is_text:
        require(unchanged_parent_blob, f"New or changed non-UTF-8/binary blob refused: {path}")
        return True
    for description, pattern in SECRET_PATTERNS.items():
        require(pattern.search(data) is None, f"Possible {description} refused in {path}; value not printed")
    return False


def check_capture(root: Path, env: dict[str, str], omitted: set[str], captured: dict,
                  mode_name: str, run_id: str) -> list[dict]:
    require(current_paths(root, env, omitted) == set(captured),
            "Eligible file inventory changed while capturing; retry with a new phase")
    growing = []
    for path, item in captured.items():
        file = root / path
        now = file.read_bytes()
        mode = "100755" if file.stat().st_mode & 0o111 else "100644"
        require(mode == item["mode"], f"File mode changed during capture: {path}")
        if now != item["data"]:
            pending_log = (mode_name == "interim"
                           and path.startswith(f"verification/runs/{run_id}/")
                           and path.endswith(".log") and now.startswith(item["data"]))
            require(pending_log, f"File changed during capture: {path}")
            growing.append({"path": path, "captured_size": len(item["data"]),
                            "later_observed_size": len(now), "status": "pending_prefix_snapshot"})
    return growing


def snapshot(args: argparse.Namespace) -> dict:
    root = args.repo.resolve()
    output = args.output_dir.resolve()
    require(root.is_dir(), "Repository directory does not exist")
    require(not output.is_relative_to(root), "Export directory must be outside the repository")
    require(re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9_.-]*", args.phase) is not None,
            "Phase must be a simple filename label")
    require(re.fullmatch(r"[0-9a-f]{40}", args.parent) is not None,
            "Parent must be an explicit full lowercase 40-hex commit or tree SHA")
    require(re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9_.-]*", args.run_id) is not None,
            "Run ID must be a simple filename label")
    output.mkdir(parents=True, exist_ok=True)
    metadata_path = output / f"{args.phase}-metadata.json"
    blobs_path = output / f"{args.phase}-blobs"
    require(not metadata_path.exists() and not blobs_path.exists(),
            "Phase export already exists; choose a new phase instead of overwriting evidence")
    lock_path = output / f"{args.phase}-lock"
    try:
        lock = lock_path.open("xb")
    except FileExistsError as exc:
        raise SnapshotError("Phase export is already locked") from exc
    lock.close()
    try:
        require(not metadata_path.exists() and not blobs_path.exists(),
                "Phase export appeared before lock acquisition; choose a new phase")
        started = datetime.now(timezone.utc).isoformat()
        env = os.environ.copy()
        env.pop("GIT_INDEX_FILE", None)
        env["GIT_OPTIONAL_LOCKS"] = "0"
        require(git(root, ["rev-parse", "--show-toplevel"], env).decode().strip() == str(root),
                "Repository argument must be its top-level checkout")
        require(git(root, ["rev-parse", "--show-object-format"], env).strip() == b"sha1",
                "This GitHub export helper requires SHA-1 Git object IDs")
        parent_type = git(root, ["cat-file", "-t", args.parent], env).decode().strip()
        require(parent_type in {"commit", "tree"}, "Parent object must be a commit or tree")
        base_tree = git(root, ["rev-parse", f"{args.parent}^{{tree}}"], env).decode().strip()
        frozen_path = root / "verification" / "runs" / args.run_id / "frozen-candidate-inputs.json"
        frozen_bytes = frozen_path.read_bytes()
        frozen = json.loads(frozen_bytes)
        require(isinstance(frozen, dict) and bool(frozen)
                and all(isinstance(p, str) and isinstance(h, str)
                        and re.fullmatch(r"[0-9a-f]{64}", h) is not None for p, h in frozen.items()),
                "Invalid or empty frozen-candidate input manifest")
        original_index = Path(git(root, ["rev-parse", "--git-path", "index"], env).decode().strip())
        if not original_index.is_absolute():
            original_index = root / original_index
        original_index_hash = fingerprint(original_index)
        omitted = INTERIM_OMISSIONS if args.mode == "interim" else set()
        retained_binary = []
        captured = {}
        growing_logs = []
        with tempfile.TemporaryDirectory(prefix=f".{args.phase}-index-", dir=output) as temporary:
            env["GIT_INDEX_FILE"] = str(Path(temporary) / "index")
            git(root, ["read-tree", base_tree], env)
            parent = tree_entries(root, base_tree, env)
            require(all(e["type"] == "blob" and e["mode"] in {"100644", "100755"}
                        for e in parent.values()),
                    "Parent includes symlinks, submodules or unsupported file modes; review explicitly")
            paths = current_paths(root, env, omitted)
            for path in sorted(paths):
                file = root / path
                data = file.read_bytes()
                info = file.stat()
                mode = "100755" if info.st_mode & 0o111 else "100644"
                sha = oid(data)
                old = parent.get(path)
                same = old is not None and old["type"] == "blob" and old["sha"] == sha and old["mode"] == mode
                if screen(path, data, same):
                    retained_binary.append({"path": path, "sha": sha, "size": len(data)})
                captured[path] = {"data": data, "mode": mode, "sha": sha}

            require(all(p in captured and hashlib.sha256(captured[p]["data"]).hexdigest() == h
                        for p, h in frozen.items()),
                    "Snapshot omits or changes a frozen candidate input")
            require(captured.get(frozen_path.relative_to(root).as_posix(), {}).get("data") == frozen_bytes,
                    "Frozen-input manifest changed while capturing")

            growing_logs = check_capture(root, env, omitted, captured, args.mode, args.run_id)

            # Hash exact raw bytes. No git-add filters or newline conversion run.
            records = []
            for path, item in captured.items():
                actual = git(root, ["hash-object", "-w", "--no-filters", "--stdin"], env, item["data"]).decode().strip()
                require(actual == item["sha"], f"Raw Git blob hash mismatch: {path}")
                records.append(f"{item['mode']} {actual}\t{path}".encode("utf-8") + b"\0")
            git(root, ["read-tree", "--empty"], env)
            git(root, ["update-index", "-z", "--index-info"], env, b"".join(records))
            tree = git(root, ["write-tree"], env).decode().strip()
            actual_tree = tree_entries(root, tree, env)
            require(set(actual_tree) == paths, "Written tree inventory differs from captured inventory")
            require(all(actual_tree[p]["sha"] == d["sha"] and actual_tree[p]["mode"] == d["mode"]
                        and actual_tree[p]["type"] == "blob" for p, d in captured.items()),
                    "Written tree differs from exact captured files")
            require(fingerprint(original_index) == original_index_hash,
                    "Real Git index changed during capture; no export finalized")
            require(frozen_path.read_bytes() == frozen_bytes
                    and all(fingerprint(root / p) == h for p, h in frozen.items()),
                    "Frozen candidate input drifted before finalizing snapshot metadata")

            entries = []
            for path, item in sorted(captured.items()):
                old = parent.get(path)
                if old == actual_tree[path]:
                    continue
                entries.append({"path": path, "mode": item["mode"], "type": "blob",
                                "sha": item["sha"], "size": len(item["data"]),
                                "sha256": hashlib.sha256(item["data"]).hexdigest(),
                                "local_blob_path": str(blobs_path / item["sha"]),
                                "change": "added" if old is None else "modified",
                                "previous_mode": old["mode"] if old else None,
                                "previous_sha": old["sha"] if old else None})
            deletions = [{"path": p, "mode": parent[p]["mode"], "type": parent[p]["type"],
                          "sha": None, "previous_sha": parent[p]["sha"],
                          "previous_size": int(git(root, ["cat-file", "-s", parent[p]["sha"]], env)),
                          "reason": "interim_verification_output_omission" if p in omitted else "absent_from_worktree"}
                         for p in sorted(set(parent) - paths)]

        # The temporary index has been removed before exports are finalized.
        metadata = {
            "schema_version": 1, "parent": args.parent, "parent_type": parent_type,
            "base_tree": base_tree, "tree": tree, "files": len(captured),
            "phase": args.phase, "mode": args.mode, "run_id": args.run_id,
            "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
            "verification_status": "pending" if args.mode == "interim" else "not_asserted_by_snapshot_helper",
            "verification_note": "This is an exact publication snapshot, not a Lean verification result.",
            "repository_path": str(root), "temporary_index_outside_repository": True,
            "real_git_index_unchanged": True, "committed": False, "published": False,
            "frozen_inputs_manifest": frozen_path.relative_to(root).as_posix(),
            "frozen_inputs_manifest_sha256": hashlib.sha256(frozen_bytes).hexdigest(),
            "frozen_input_count": len(frozen), "all_frozen_inputs_match_snapshot_and_worktree": True,
            "entries": entries, "deletions": deletions,
            "omitted_paths": sorted(omitted), "concurrently_growing_log_snapshots": growing_logs,
            "safety": {"new_or_changed_blobs_are_utf8_text": True,
                       "selected_cache_or_private_paths": [],
                       "known_secret_patterns_detected": [],
                       "secret_pattern_checks": list(SECRET_PATTERNS),
                       "unchanged_historical_parent_binary_blobs": retained_binary},
            "blob_export_encoding": "raw_bytes_without_whitespace_or_newline_normalization",
        }
        with tempfile.TemporaryDirectory(prefix=f".{args.phase}-export-", dir=output) as staging:
            staged = Path(staging)
            staged_blobs = staged / "blobs"
            staged_blobs.mkdir()
            for item in entries:
                target = staged_blobs / item["sha"]
                if not target.exists():
                    target.write_bytes(captured[item["path"]]["data"])
                require(oid(target.read_bytes()) == item["sha"], "Exported blob hash differs from Git tree")
            # Recheck all evidence, including files outside the Lean input hash set,
            # immediately before finalizing exports. This index is also external.
            with tempfile.TemporaryDirectory(prefix=f".{args.phase}-check-index-", dir=output) as checkdir:
                env["GIT_INDEX_FILE"] = str(Path(checkdir) / "index")
                git(root, ["read-tree", tree], env)
                growing_logs = check_capture(root, env, omitted, captured, args.mode, args.run_id)
                require(frozen_path.read_bytes() == frozen_bytes
                        and all(fingerprint(root / p) == h for p, h in frozen.items()),
                        "Frozen candidate input drifted before export finalization")
                require(fingerprint(original_index) == original_index_hash,
                        "Real Git index changed before export finalization")
            metadata["concurrently_growing_log_snapshots"] = growing_logs
            metadata["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
            staged_metadata = staged / "metadata.json"
            staged_metadata.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
            staged_blobs.rename(blobs_path)
            staged_metadata.rename(metadata_path)
        return {"status": "snapshot_exported", "mode": args.mode, "phase": args.phase,
                "parent": args.parent, "base_tree": base_tree, "tree": tree,
                "files": len(captured), "changed_entries": len(entries), "deletions": len(deletions),
                "pending_growing_logs": len(growing_logs), "metadata_path": str(metadata_path),
                "blob_directory": str(blobs_path), "committed": False, "published": False}
    finally:
        lock_path.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--parent", required=True, help="Explicit full commit or tree SHA to diff against")
    parser.add_argument("--phase", required=True, help="Unique output prefix, e.g. interim-01 or final-01")
    parser.add_argument("--mode", choices=("interim", "final"), required=True)
    parser.add_argument("--repo", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    args = parser.parse_args()
    try:
        print(json.dumps(snapshot(args)))
    except (SnapshotError, OSError, UnicodeError, ValueError) as error:
        print(json.dumps({"status": "snapshot_failed", "error": str(error),
                          "committed": False, "published": False}), file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
