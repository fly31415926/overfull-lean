#!/usr/bin/env python3
"""Fetch the pinned Vizing proof and apply its Lean 4.24 compatibility patch.

No upstream source files are distributed in this repository. Every downloaded
file is checked against the pinned Git blob and SHA256 manifest before patching,
and against the expected SHA256 afterwards. An existing modified checkout is
never overwritten. Use --source with a pristine local checkout for offline setup.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/vizing-source.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def safe_relative_path(value: str) -> Path:
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise RuntimeError(f"Invalid source path in manifest: {value}")
    return Path(*path.parts)


def verify_file(data: bytes, entry: dict, *, patched: bool) -> None:
    key = "ported_sha256" if patched else "upstream_sha256"
    if sha256(data) != entry[key]:
        raise RuntimeError(f"SHA256 mismatch: {entry['path']}")
    if not patched and (len(data) != entry["size"] or git_blob_sha(data) != entry["sha"]):
        raise RuntimeError(f"Pinned Git blob mismatch: {entry['path']}")


def verify_checkout(directory: Path, entries: list[dict], *, patched: bool,
                    installed: bool = False) -> None:
    for entry in entries:
        path = directory / safe_relative_path(entry["path"])
        if installed and not entry.get("installed", True):
            if path.exists():
                raise RuntimeError(f"Upstream dependency manifest must be omitted: {path}")
            continue
        if not path.is_file() or path.is_symlink():
            raise RuntimeError(f"Missing or nonregular source file: {path}")
        verify_file(path.read_bytes(), entry, patched=patched)


def obtain_source(manifest: dict, source: Path | None) -> dict[str, bytes]:
    entries = manifest["files"]
    if source is not None:
        verify_checkout(source, entries, patched=False)
        return {entry["path"]: (source / safe_relative_path(entry["path"])).read_bytes()
                for entry in entries}

    archive_url = f"{manifest['repository']}/archive/{manifest['commit']}.tar.gz"
    request = urllib.request.Request(archive_url, headers={"User-Agent": "overfull-lean-setup"})
    with urllib.request.urlopen(request, timeout=60) as response:
        archive_data = response.read(10_000_001)
    if len(archive_data) > 10_000_000:
        raise RuntimeError("Upstream archive exceeds the expected small source size")

    with tarfile.open(fileobj=io.BytesIO(archive_data), mode="r:gz") as archive:
        members = archive.getmembers()
        prefixes = {PurePosixPath(member.name).parts[0] for member in members
                    if PurePosixPath(member.name).parts}
        if len(prefixes) != 1:
            raise RuntimeError("Upstream archive has an unexpected directory structure")
        prefix = prefixes.pop()
        files = {}
        for entry in entries:
            relative = safe_relative_path(entry["path"]).as_posix()
            member = archive.getmember(f"{prefix}/{relative}")
            if not member.isfile() or member.size != entry["size"]:
                raise RuntimeError(f"Unexpected upstream archive member: {relative}")
            stream = archive.extractfile(member)
            if stream is None:
                raise RuntimeError(f"Unreadable upstream archive member: {relative}")
            data = stream.read()
            verify_file(data, entry, patched=False)
            files[relative] = data
        return files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path,
                        help="Pristine local checkout of the exact pinned commit (offline setup)")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    target = ROOT / safe_relative_path(manifest["dependency_directory"])
    patch = ROOT / safe_relative_path(manifest["compatibility_patch"])
    if sha256(patch.read_bytes()) != manifest["compatibility_patch_sha256"]:
        raise RuntimeError("Compatibility patch does not match the provenance manifest")

    if target.exists():
        try:
            verify_checkout(target, manifest["files"], patched=True, installed=True)
        except RuntimeError as error:
            raise RuntimeError(
                f"Existing Vizing source differs from the pinned port; it was not overwritten. {error}"
            ) from error
        print(f"Vizing source verified: {manifest['commit']}")
        return 0

    patch_program = shutil.which("patch")
    if patch_program is None:
        raise RuntimeError("The standard 'patch' command is required for the compatibility patch")
    source_files = obtain_source(manifest, args.source)
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="vizing-setup-", dir=target.parent) as temporary:
        candidate = Path(temporary) / "source"
        candidate.mkdir()
        for relative, data in source_files.items():
            path = candidate / safe_relative_path(relative)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        verify_checkout(candidate, manifest["files"], patched=False)
        subprocess.run([patch_program, "-p1", "--batch", "--forward", "--fuzz=0",
                        "--input", str(patch)], cwd=candidate, check=True)
        verify_checkout(candidate, manifest["files"], patched=True)
        # Upstream pins older mathlib dependencies. Root pins must remain authoritative.
        for entry in manifest["files"]:
            if not entry.get("installed", True):
                (candidate / safe_relative_path(entry["path"])).unlink()
        verify_checkout(candidate, manifest["files"], patched=True, installed=True)
        candidate.rename(target)
    print(f"Vizing source prepared and verified: {manifest['commit']}")
    print("The main project's pinned Lean and mathlib versions are used to build Vizing.Main.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"Vizing setup failed: {error}", file=sys.stderr)
        raise SystemExit(1)
