#!/usr/bin/env python3
"""Restore all exact original readback JSON/log bytes after verifying every hash."""
from __future__ import annotations
import argparse, base64, gzip, hashlib, json, pathlib
EXPECTED_MANIFEST_SHA256 = "444c4cea13e0cf6913e95bfd37bd32c6bd8d837f3b667c53cc457aef65b9f4a0"

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def blob_sha(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()

def checked(data, record, label):
    require(len(data) == record["bytes"], label + ": byte length mismatch")
    require(digest(data) == record["sha256"], label + ": SHA-256 mismatch")
    require(blob_sha(data) == record["git_blob_sha1"], label + ": Git blob SHA-1 mismatch")
    return data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, help="Directory for all restored originals; existing files are refused")
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent
    raw = (root / "archive-manifest.json").read_bytes()
    require(digest(raw) == EXPECTED_MANIFEST_SHA256, "Exact archive manifest SHA-256 mismatch")
    manifest = json.loads(raw)
    require(manifest["schema_version"] == 1 and manifest["kind"] == "lossless_public_proof_readback_archive",
            "Unexpected archive schema")
    originals = {}
    for item in manifest["files"]:
        name, storage = item["name"], item["storage"]
        require(pathlib.PurePosixPath(name).name == name and name not in ["", ".", ".."]
                and name not in originals, "Unexpected or repeated original filename")
        if storage["kind"] == "exact_utf8":
            require(storage["path"] == name, "Unexpected readable source path")
            original = (root / name).read_bytes()
            original.decode("utf-8")
        elif storage["kind"] == "gzip_base64_parts":
            require(storage["compression"] == "gzip" and storage["mtime"] == 0
                    and storage["filename_header"] == "" and storage["compression_level"] == 9,
                    "Unexpected gzip metadata")
            require(len(storage["parts"]) == storage["part_count"] and storage["part_limit_bytes"] == 45000,
                    "Unexpected part inventory")
            parts = []
            for number, part in enumerate(storage["parts"], start=1):
                expected = f"encoded/{name}.gz.part-{number:06d}.b64"
                require(part["number"] == number and part["path"] == expected, "Unexpected part path or order")
                data = checked((root / expected).read_bytes(), part, expected)
                require(len(data) <= 45000, "Part exceeds declared bound")
                data.decode("ascii")
                parts.append(data)
            encoded = checked(b"".join(parts), storage["encoded"], name + " encoded")
            compressed = base64.b64decode(encoded, validate=True)
            require(base64.b64encode(compressed) == encoded, "Noncanonical base64")
            checked(compressed, storage["compressed"], name + " gzip")
            require(compressed[:4] == b"\x1f\x8b\x08\x00" and compressed[4:8] == b"\0\0\0\0",
                    "Gzip header is not the declared deterministic form")
            original = gzip.decompress(compressed)
        else:
            raise RuntimeError("Unknown storage kind")
        originals[name] = checked(original, item["original"], name + " original")
    require(len(originals) == manifest["source_file_count"], "Source file count mismatch")
    require(sum(map(len, originals.values())) == manifest["source_total_bytes"], "Total original byte length mismatch")
    for derivative in manifest["generated_derivatives"]:
        require(derivative["path"] == "snapshot-integrity-summary.json", "Unexpected derivative path")
        checked((root / derivative["path"]).read_bytes(), derivative, derivative["path"])
    out = pathlib.Path(args.output_dir).resolve()
    require(all(not (out / name).exists() for name in originals), "Refusing to replace an existing restored file")
    out.mkdir(parents=True, exist_ok=True)
    for name, data in originals.items():
        with (out / name).open("xb") as stream:
            stream.write(data)
    print(json.dumps({"status": "passed", "manifest_sha256": EXPECTED_MANIFEST_SHA256,
                      "restored_files": len(originals), "restored_bytes": sum(map(len, originals.values())),
                      "output_directory": str(out)}, indent=2))

if __name__ == "__main__":
    main()
