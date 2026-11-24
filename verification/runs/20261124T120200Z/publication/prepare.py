#!/usr/bin/env python3
"""Prepare verified Git-object transport; perform no Git or remote mutations.

Example:
  python prepare.py --target-tree <40-hex-tree-SHA> --output-dir ./prepared

Upload each content batch with GitHub create_tree, using its tree_elements
and no base tree. The temporary paths are blob/<expected-blob-SHA>. Large
UTF-8 blobs and binary blobs have exact raw files and ordered chunk metadata
for create_blob. Verify every returned blob SHA. Then apply final tree batches
in order, beginning with baseline_tree_sha and using each returned tree as
the next base. The final returned tree MUST equal target_tree_sha.

Only git rev-parse, ls-tree, cat-file and local output-file writes are used.
No index, ref, commit, worktree file, or remote repository is changed.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any


DEFAULT_REPO = "/workspace/scratch/77adbfc63087/overfull-lean"
DEFAULT_BASELINE_TREE = "9013f6d5c07676ba130d4bb794062d700bab6136"
BASELINE_COMMIT = "e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8"
SHA1 = re.compile(r"[0-9a-fA-F]{40}\Z")
ALLOWED_MODES = {
    "tree": {"040000"},
    "blob": {"100644", "100755", "120000"},
    "commit": {"160000"},
}


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8")


def write_json(path: Path, value: Any, *, pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    else:
        path.write_bytes(json_bytes(value))


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def object_sha(kind: str, data: bytes) -> str:
    return hashlib.sha1(kind.encode("ascii") + b" " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


class GitReader:
    def __init__(self, repo: Path):
        self.repo = repo

    def run(self, *args: str) -> bytes:
        result = subprocess.run(["git", "-C", str(self.repo), *args], capture_output=True, check=False)
        if result.returncode:
            raise RuntimeError(f"git {' '.join(args)} failed: {result.stderr.decode('utf-8', 'replace').strip()}")
        return result.stdout

    def check_tree(self, value: str) -> str:
        if not SHA1.fullmatch(value):
            raise ValueError(f"An immutable full 40-hex tree SHA is required, got {value!r}")
        value = value.lower()
        if self.run("cat-file", "-t", value).strip() != b"tree":
            raise ValueError(f"Object {value} is not a tree")
        return value

    def inventory(self, tree: str) -> list[dict[str, str]]:
        entries = []
        data = self.run("ls-tree", "-r", "-t", "-z", "--full-tree", tree)
        for raw in data.split(b"\0"):
            if not raw:
                continue
            header, raw_path = raw.split(b"\t", 1)
            mode, kind, digest = header.decode("ascii").split(" ")
            path = raw_path.decode("utf-8", errors="strict")
            if any(part in {"", ".", ".."} for part in path.split("/")):
                raise ValueError(f"Unsupported Git path for GitHub transport: {path!r}")
            if kind not in ALLOWED_MODES or mode not in ALLOWED_MODES[kind]:
                raise ValueError(f"Unsupported entry: mode={mode}, type={kind}, path={path!r}")
            entries.append({"path": path, "mode": mode, "type": kind, "sha": digest})
        if len({entry["path"] for entry in entries}) != len(entries):
            raise ValueError("Duplicate paths in Git tree inventory")
        return entries

    def blob_reader(self) -> subprocess.Popen[bytes]:
        return subprocess.Popen(
            ["git", "-C", str(self.repo), "cat-file", "--batch"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )


def empty_directories(entries: list[dict[str, str]]) -> set[str]:
    parents = {entry["path"].rpartition("/")[0] for entry in entries}
    return {entry["path"] for entry in entries if entry["type"] == "tree" and entry["path"] not in parents}


def tree_from_leaves(leaves: list[dict[str, str]], empty_dirs: set[str]) -> str:
    """Independently reconstruct raw Git tree hashes from exact names/modes/SHAs."""
    root: dict[str, Any] = {}
    for entry in leaves:
        parts = entry["path"].split("/")
        node = root
        for component in parts[:-1]:
            child = node.setdefault(component, {})
            if not isinstance(child, dict):
                raise ValueError(f"File/directory collision at {entry['path']!r}")
            node = child
        if parts[-1] in node:
            raise ValueError(f"Duplicate tree entry at {entry['path']!r}")
        node[parts[-1]] = (entry["mode"], entry["sha"])
    for directory in sorted(empty_dirs):
        node = root
        for component in directory.split("/"):
            child = node.setdefault(component, {})
            if not isinstance(child, dict):
                raise ValueError(f"File/directory collision at {directory!r}")
            node = child
        if node:
            raise ValueError(f"Declared empty directory is nonempty: {directory!r}")

    def digest(node: dict[str, Any]) -> str:
        records = []
        for name, child in node.items():
            if isinstance(child, dict):
                mode, value = "40000", digest(child)
                sort_key = name.encode("utf-8") + b"/"
            else:
                mode, value = child
                mode = format(int(mode, 8), "o")
                sort_key = name.encode("utf-8")
            record = mode.encode("ascii") + b" " + name.encode("utf-8") + b"\0" + bytes.fromhex(value)
            records.append((sort_key, record))
        return object_sha("tree", b"".join(record for _, record in sorted(records)))

    return digest(root)


def read_blob(process: subprocess.Popen[bytes], digest: str) -> bytes:
    assert process.stdin is not None and process.stdout is not None
    process.stdin.write(digest.encode("ascii") + b"\n")
    process.stdin.flush()
    header = process.stdout.readline().rstrip(b"\n").split(b" ")
    if len(header) != 3 or header[0].decode("ascii") != digest or header[1] != b"blob":
        raise RuntimeError(f"Unexpected cat-file response for {digest}: {header!r}")
    size = int(header[2])
    chunks = []
    remaining = size
    while remaining:
        chunk = process.stdout.read(remaining)
        if not chunk:
            raise RuntimeError(f"Truncated cat-file output for {digest}")
        chunks.append(chunk)
        remaining -= len(chunk)
    if process.stdout.read(1) != b"\n":
        raise RuntimeError(f"Missing cat-file separator for {digest}")
    data = b"".join(chunks)
    actual = object_sha("blob", data)
    if actual != digest:
        raise RuntimeError(f"Blob verification failed: expected {digest}, found {actual}")
    return data


def utf8_chunks(data: bytes, limit: int):
    offset = 0
    while offset < len(data):
        end = min(offset + limit, len(data))
        while end < len(data) and (data[end] & 0xC0) == 0x80:
            end -= 1
        if end <= offset:
            raise ValueError("Chunk size cannot hold one UTF-8 character")
        part = data[offset:end]
        yield offset, part, part.decode("utf-8", errors="strict")
        offset = end


def write_blob_chunks(output: Path, digest: str, data: bytes, encoding: str, limit: int) -> list[dict[str, Any]]:
    directory = output / "chunks" / digest
    directory.mkdir(parents=True, exist_ok=False)
    if encoding == "utf-8":
        parts = utf8_chunks(data, limit)
    else:
        # Split the encoded string on multiples of four. Concatenate before decoding.
        encoded = base64.b64encode(data)
        width = max(4, limit // 4 * 4)
        parts = ((offset, encoded[offset:offset + width], encoded[offset:offset + width].decode("ascii"))
                 for offset in range(0, len(encoded), width))
    metadata = []
    joined: list[str] = []
    for index, (offset, raw, content) in enumerate(parts):
        suffix = "utf8" if encoding == "utf-8" else "base64"
        text_file = directory / f"{index:04d}.{suffix}"
        json_file = directory / f"{index:04d}.json"
        text_file.write_bytes(raw)
        write_json(json_file, {"blob_sha": digest, "index": index, "encoding": encoding, "content": content})
        metadata.append({
            "index": index,
            "offset_bytes" if encoding == "utf-8" else "offset_base64_chars": offset,
            "size_bytes": len(raw),
            "sha256": sha256(raw),
            "text_file": str(text_file.relative_to(output)),
            "json_file": str(json_file.relative_to(output)),
            "json_sha256": sha256(json_file.read_bytes()),
        })
        joined.append(content)
    reconstructed = "".join(joined).encode("utf-8") if encoding == "utf-8" else base64.b64decode("".join(joined), validate=True)
    if reconstructed != data:
        raise RuntimeError(f"Chunk round trip failed for blob {digest}")
    return metadata


def write_batches(output: Path, prefix: str, entries: list[dict[str, Any]], maximum: int) -> list[dict[str, Any]]:
    """Every emitted payload is directly suitable as create_tree tree_elements."""
    batches = []
    current: list[dict[str, Any]] = []

    def flush() -> None:
        if not current:
            return
        path = output / "batches" / f"{prefix}-{len(batches):04d}.json"
        payload = {"tree_elements": list(current)}
        raw = json_bytes(payload)
        if len(raw) > maximum:
            raise RuntimeError("Internal batch sizing error")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        batches.append({"file": str(path.relative_to(output)), "size_bytes": len(raw),
                        "sha256": sha256(raw), "entries": len(current)})
        current.clear()

    for entry in entries:
        if len(json_bytes({"tree_elements": [entry]})) > maximum:
            raise ValueError(f"Single tree element exceeds batch limit: {entry['path']!r}")
        if current and len(json_bytes({"tree_elements": [*current, entry]})) > maximum:
            flush()
        current.append(entry)
    flush()
    return batches


def deletion_roots(baseline: dict[str, dict[str, str]], target: dict[str, dict[str, str]]) -> list[dict[str, Any]]:
    """Delete whole absent/replaced subtrees once, before any upserts."""
    result: list[dict[str, Any]] = []
    removed: set[str] = set()
    for path in sorted(baseline, key=lambda item: (item.count("/"), item.encode("utf-8"))):
        if any(parent in removed for parent in ancestors(path)):
            continue
        old = baseline[path]
        new = target.get(path)
        if new is None or new["type"] != old["type"]:
            result.append({"path": path, "mode": old["mode"], "type": old["type"], "sha": None})
            removed.add(path)
    return result


def ancestors(path: str) -> list[str]:
    parts = path.split("/")
    return ["/".join(parts[:index]) for index in range(1, len(parts))]


def prepare(args: argparse.Namespace) -> dict[str, Any]:
    repo = Path(args.repo).resolve(strict=True)
    git = GitReader(repo)
    if git.run("rev-parse", "--show-object-format").strip() != b"sha1":
        raise ValueError("GitHub transport requires a SHA-1 repository")
    worktree = Path(git.run("rev-parse", "--show-toplevel").decode("utf-8").strip()).resolve()
    target_tree = git.check_tree(args.target_tree)
    baseline_tree = git.check_tree(args.baseline_tree)
    output = Path(args.output_dir or (Path(__file__).resolve().parent / f"prepared-{target_tree[:12]}")).resolve()
    if output == worktree or worktree in output.parents:
        raise ValueError("Output must be outside the source repository")
    if args.max_batch_bytes < 1024 or args.chunk_bytes < 4:
        raise ValueError("Batch limit must be at least 1024; chunk limit at least 4")
    if output.exists():
        raise FileExistsError(f"Output already exists; choose a fresh directory: {output}")

    baseline_entries = git.inventory(baseline_tree)
    target_entries = git.inventory(target_tree)
    baseline = {entry["path"]: entry for entry in baseline_entries}
    target = {entry["path"]: entry for entry in target_entries}
    baseline_leaves = [entry for entry in baseline_entries if entry["type"] != "tree"]
    target_leaves = [entry for entry in target_entries if entry["type"] != "tree"]
    baseline_empty = empty_directories(baseline_entries)
    target_empty = empty_directories(target_entries)
    if tree_from_leaves(baseline_leaves, baseline_empty) != baseline_tree:
        raise ValueError("Baseline inventory does not reconstruct its exact tree SHA")
    if tree_from_leaves(target_leaves, target_empty) != target_tree:
        raise ValueError("Target inventory does not reconstruct its exact tree SHA")

    baseline_blobs = {entry["sha"] for entry in baseline_leaves if entry["type"] == "blob"}
    blob_paths: dict[str, list[dict[str, str]]] = defaultdict(list)
    for entry in target_leaves:
        if entry["type"] == "blob":
            blob_paths[entry["sha"]].append(entry)
    new_blobs = sorted(set(blob_paths) - baseline_blobs)
    reused = sorted(set(blob_paths) & baseline_blobs)
    deletions = deletion_roots(baseline, target)
    upserts = [entry for entry in target_leaves if baseline.get(entry["path"]) != entry]
    upserts += [target[path] for path in sorted(target_empty) if baseline.get(path) != target[path]]
    upserts.sort(key=lambda entry: entry["path"].encode("utf-8"))

    # Independently check that the complete final plan has no omitted leaf or mode.
    simulated = {entry["path"]: entry for entry in baseline_leaves}
    simulated_empty = set(baseline_empty)
    for entry in deletions:
        path = entry["path"]
        simulated = {key: value for key, value in simulated.items() if key != path and not key.startswith(path + "/")}
        simulated_empty = {key for key in simulated_empty if key != path and not key.startswith(path + "/")}
    for entry in upserts:
        path = entry["path"]
        simulated = {key: value for key, value in simulated.items() if key != path and not key.startswith(path + "/")}
        simulated_empty = {key for key in simulated_empty if key != path and not key.startswith(path + "/") and key not in ancestors(path)}
        if entry["type"] == "tree":
            simulated_empty.add(path)
        else:
            simulated[path] = entry
    if tree_from_leaves(list(simulated.values()), simulated_empty) != target_tree:
        raise ValueError("Final tree plan does not reconstruct target tree exactly")

    changes = []
    old_leaves = {entry["path"]: entry for entry in baseline_leaves}
    new_leaves = {entry["path"]: entry for entry in target_leaves}
    for path in sorted(set(old_leaves) | set(new_leaves), key=lambda item: item.encode("utf-8")):
        old, new = old_leaves.get(path), new_leaves.get(path)
        if old != new:
            changes.append({"path": path, "change": "add" if old is None else "delete" if new is None else "modify",
                            "before": old, "after": new})

    output.mkdir(parents=True, exist_ok=False)
    (output / "blobs").mkdir()
    write_json(output / "baseline-tree-inventory.json", {"tree_sha": baseline_tree, "entries": baseline_entries})
    write_json(output / "target-tree-inventory.json", {"tree_sha": target_tree, "entries": target_entries})
    write_json(output / "file-changes.json", changes)
    write_json(output / "final-tree-elements.json", {
        "base_tree_sha": baseline_tree, "expected_tree_sha": target_tree,
        "deletions": deletions, "upserts": upserts, "tree_elements": [*deletions, *upserts],
        "instruction": "Apply deletion batches before upsert batches; verify the final tree SHA.",
    })

    blob_metadata = []
    inline_elements = []
    process = git.blob_reader()
    try:
        for digest in new_blobs:
            data = read_blob(process, digest)
            raw_path = output / "blobs" / f"{digest}.bytes"
            raw_path.write_bytes(data)
            metadata: dict[str, Any] = {
                "sha": digest, "size_bytes": len(data), "sha256": sha256(data),
                "raw_file": str(raw_path.relative_to(output)),
                "representative_path": f"blob/{digest}", "target_entries": blob_paths[digest],
            }
            try:
                content = data.decode("utf-8", errors="strict")
            except UnicodeDecodeError:
                metadata["transport"] = "create_blob_base64_chunks"
                metadata["encoding"] = "base64"
                metadata["chunks"] = write_blob_chunks(output, digest, data, "base64", args.chunk_bytes)
            else:
                if content.encode("utf-8") != data:
                    raise RuntimeError(f"UTF-8 round trip failed for {digest}")
                element = {"path": f"blob/{digest}", "mode": "100644", "type": "blob", "content": content}
                if len(json_bytes({"tree_elements": [element]})) <= args.max_batch_bytes:
                    inline_elements.append(element)
                    metadata["transport"] = "create_tree_content_batch"
                    metadata["encoding"] = "utf-8"
                else:
                    metadata["transport"] = "create_blob_utf8_chunks"
                    metadata["encoding"] = "utf-8"
                    metadata["chunks"] = write_blob_chunks(output, digest, data, "utf-8", args.chunk_bytes)
            blob_metadata.append(metadata)
    finally:
        if process.stdin is not None:
            process.stdin.close()
        if process.stdout is not None:
            process.stdout.close()
        errors = process.stderr.read() if process.stderr is not None else b""
        code = process.wait()
        if code:
            raise RuntimeError(f"git cat-file --batch failed ({code}): {errors.decode('utf-8', 'replace')}")

    content_batches = write_batches(output, "content", inline_elements, args.max_batch_bytes)
    delete_batches = write_batches(output, "final-delete", deletions, args.max_batch_bytes)
    upsert_batches = write_batches(output, "final-upsert", upserts, args.max_batch_bytes)
    baseline_trees = {baseline_tree} | {entry["sha"] for entry in baseline_entries if entry["type"] == "tree"}
    empty_trees_needed = sorted({target[path]["sha"] for path in target_empty} - baseline_trees)
    for digest in empty_trees_needed:
        if digest != object_sha("tree", b""):
            raise RuntimeError("Nonempty tree unexpectedly marked empty")
    manifest = {
        "format_version": 1,
        "repo": str(worktree), "output_dir": str(output),
        "baseline_commit_reference": BASELINE_COMMIT if baseline_tree == DEFAULT_BASELINE_TREE else None,
        "baseline_tree_sha": baseline_tree, "target_tree_sha": target_tree,
        "object_format": "sha1", "batch_limit_bytes": args.max_batch_bytes,
        "chunk_limit_bytes": args.chunk_bytes,
        "verification": {
            "baseline_inventory_reconstructs_tree": True,
            "target_inventory_reconstructs_tree": True,
            "final_plan_reconstructs_target_tree": True,
            "every_extracted_blob_git_sha_verified": True,
            "every_chunked_blob_roundtrip_verified": True,
        },
        "counts": {
            "baseline_leaf_paths": len(baseline_leaves), "target_leaf_paths": len(target_leaves),
            "target_blob_paths": sum(len(paths) for paths in blob_paths.values()),
            "target_unique_blob_shas": len(blob_paths), "baseline_unique_blob_shas": len(baseline_blobs),
            "unique_new_blobs": len(new_blobs), "unique_reused_baseline_blobs": len(reused),
            "duplicate_target_blob_paths": sum(len(paths) - 1 for paths in blob_paths.values()),
            "new_blob_bytes": sum(item["size_bytes"] for item in blob_metadata),
            "changed_leaf_paths": len(changes), "deletion_entries": len(deletions), "upsert_entries": len(upserts),
            "content_batches": len(content_batches),
            "chunked_blobs": sum("chunks" in item for item in blob_metadata),
        },
        "inventory_files": {"baseline": "baseline-tree-inventory.json", "target": "target-tree-inventory.json",
                            "file_changes": "file-changes.json", "final_tree_elements": "final-tree-elements.json"},
        "new_blobs": blob_metadata,
        "reused_baseline_blobs": [{"sha": digest, "target_entries": blob_paths[digest]} for digest in reused],
        "content_batches": content_batches,
        "empty_tree_objects_to_create": [{"expected_sha": digest, "tree_elements": []} for digest in empty_trees_needed],
        "final_tree_batches": [
            *[{**batch, "phase": "delete"} for batch in delete_batches],
            *[{**batch, "phase": "upsert"} for batch in upsert_batches],
        ],
        "gitlinks": [entry for entry in target_leaves if entry["type"] == "commit"],
        "instructions": [
            "No operation has staged, committed, updated a ref, or contacted GitHub.",
            "Content batches: parse JSON; pass tree_elements to GitHub create_tree with no base tree.",
            "Check returned representative blob/<sha> entries against the expected blob SHA in the path.",
            "Chunked blobs: read each chunks[].json in index order and concatenate content exactly, with no separators.",
            "Use create_blob with the manifest encoding (utf-8 or base64); verify its returned SHA equals new_blobs[].sha.",
            "Raw blobs/<sha>.bytes are exact backups. Chunk offsets for UTF-8 refer to raw bytes; base64 offsets refer to encoded characters.",
            "If listed, materialize the empty tree object before applying final tree batches; verify its SHA.",
            "Apply final_tree_batches in listed order. The first base_tree_sha is baseline_tree_sha; later bases are prior returned tree SHAs.",
            "Final upserts use complete destination paths, original modes and verified object SHAs. Deletions precede upserts for type replacements.",
            "The last returned tree SHA must equal target_tree_sha before any commit or ref update.",
            "If final_tree_batches is empty, baseline and target are identical and no final tree request is necessary.",
        ],
    }
    write_json(output / "manifest.json", manifest, pretty=True)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", default=DEFAULT_REPO, help="Source Git worktree; read only")
    parser.add_argument("--target-tree", required=True, help="Exact full target tree SHA")
    parser.add_argument("--baseline-tree", default=DEFAULT_BASELINE_TREE, help="Exact full baseline tree SHA")
    parser.add_argument("--output-dir", help="Fresh output directory outside the source worktree")
    parser.add_argument("--max-batch-bytes", type=int, default=120000, help="Maximum serialized JSON bytes per create_tree batch")
    parser.add_argument("--chunk-bytes", type=int, default=24000, help="Maximum raw UTF-8/base64 bytes per chunk")
    args = parser.parse_args()
    try:
        manifest = prepare(args)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"manifest": str(Path(manifest["output_dir"]) / "manifest.json"),
                      "baseline_tree_sha": manifest["baseline_tree_sha"],
                      "target_tree_sha": manifest["target_tree_sha"],
                      "counts": manifest["counts"], "verification": manifest["verification"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
