#!/usr/bin/env python3
"""Verify one fixed archive; publish its exact proof ref only with --publish.

This file is an inert proposal until separately approved. The default invocation
performs local verification and imports bundle objects without updating refs.
It makes no network calls. --publish is reserved for the reviewed GitHub job.
"""
from __future__ import annotations

import argparse
import base64
import datetime
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile
import time

REPOSITORY = "fly31415926/overfull-lean"
PROOF = "db841575ca2c427e230387c1c95fa74bedb463d6"
PROOF_TREE = "a7e59e8303f670fab6c95348cd100acd1aaa5899"
BASELINE = "1c9404a454c99fe5c11ba8d774cb9c259f291f20"
BASELINE_TREE = "087e26b5f004af1f9423a6f2b137d805f5991f1a"
BUNDLE_SHA256 = "b28ad8fdf21678b583458683c58d04ce7cb823c9dc08b7932b988f22aa54d57e"
BUNDLE_BYTES = 2101917
MANIFEST_SHA256 = "7fac099d28d334ae8cb104dfd52a2e95533d40c515db310fbadb3cdc5949ec61"
TRANSFER_BRANCH = "reconstruction-four-core-2026-11-24-2130"
PROOF_BRANCH = "publication-four-core-proof-2026-11-24-2130"
SOURCE_BRANCHES = ["main", "verified-bipartite-continuation-2026-11-21"]
ARCHIVE_PREFIX = "publication-transfer/verified-db841575"
RUN = "verification/runs/20261124T213000Z/"
SHA = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
GIT = ["git", "--no-replace-objects", "-c", "core.hooksPath=/dev/null",
       "-c", "protocol.allow=never"]
REMOTE_GIT = GIT + ["-c", "protocol.https.allow=always"]
ROOT = pathlib.Path.cwd()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def blob_digest(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def execute(receipt, argv, check=True):
    tick = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=300)
    output = result.stdout.decode("utf-8", "replace")
    receipt["commands"].append({"argv": argv, "exit_code": result.returncode,
                                "elapsed_seconds": time.monotonic() - tick,
                                "output": output, "output_sha256": digest(result.stdout)})
    if check:
        require(result.returncode == 0, f"Command failed with actual exit {result.returncode}: {argv!r}")
    return output


def read_object(receipt, path):
    result = subprocess.run(GIT + ["show", f"{PROOF}:{path}"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=300)
    require(result.returncode == 0, f"Could not read exact committed evidence: {path}")
    data = result.stdout
    receipt["evidence_reads"].append({"path": path, "bytes": len(data),
                                     "sha256": digest(data), "git_blob_sha1": blob_digest(data)})
    return data


def verify_archive(receipt):
    archive = ROOT / ARCHIVE_PREFIX
    raw_manifest = (archive / "manifest.json").read_bytes()
    require(digest(raw_manifest) == MANIFEST_SHA256, "Exact reviewed manifest hash mismatch")
    manifest = json.loads(raw_manifest)
    require(manifest["schema_version"] == 1
            and manifest["kind"] == "incremental_git_bundle_archive"
            and manifest["commit"] == PROOF and manifest["tree"] == PROOF_TREE
            and manifest["parent"] == BASELINE and manifest["prerequisite_commit"] == BASELINE,
            "Manifest commit, tree, baseline, or schema mismatch")
    expected_bundle = {"path": f"verified-{PROOF}.bundle", "format": "git bundle v2",
                       "bytes": BUNDLE_BYTES, "sha256": BUNDLE_SHA256,
                       "heads": [{"commit": PROOF, "ref": "HEAD"}]}
    require(manifest["bundle"] == expected_bundle, "Manifest bundle identity mismatch")
    require(manifest["part_count"] == len(manifest["parts"]) == 63
            and manifest["part_character_limit"] == 45000
            and manifest["encoded_bytes"] == 2802556, "Manifest part inventory mismatch")
    chunks = []
    for index, part in enumerate(manifest["parts"], start=1):
        expected_name = f"bundle.part-{index:06d}.b64"
        require(part["number"] == index and part["path"] == expected_name
                and SHA256.fullmatch(part["sha256"]) and SHA.fullmatch(part["git_blob_sha1"]),
                "Unexpected part path, number, or hash")
        content = (archive / expected_name).read_bytes()
        require(len(content) == part["bytes"] and len(content) <= 45000
                and digest(content) == part["sha256"] and blob_digest(content) == part["git_blob_sha1"],
                f"Exact part bytes or hashes mismatch: {expected_name}")
        chunks.append(content)
    encoded = b"".join(chunks)
    require(len(encoded) == 2802556, "Encoded bundle length mismatch")
    bundle = base64.b64decode(encoded, validate=True)
    require(base64.b64encode(bundle) == encoded, "Bundle encoding is not canonical base64")
    require(len(bundle) == BUNDLE_BYTES and digest(bundle) == BUNDLE_SHA256,
            "Exact decoded bundle bytes or hash mismatch")
    baseline_tree = execute(receipt, GIT + ["rev-parse", f"{BASELINE}^{{tree}}"] ).strip()
    require(baseline_tree == BASELINE_TREE, "Exact prerequisite baseline tree mismatch")
    with tempfile.TemporaryDirectory(prefix="overfull-reviewed-bundle-") as temporary:
        bundle_path = pathlib.Path(temporary) / "proof.bundle"
        bundle_path.write_bytes(bundle)
        execute(receipt, GIT + ["bundle", "verify", str(bundle_path)])
        heads = execute(receipt, GIT + ["bundle", "list-heads", str(bundle_path)]).splitlines()
        require(len(heads) == 1 and heads[0].split() == [PROOF, "HEAD"], "Exact bundle head mismatch")
        # Local bundle only. No worktree, index, FETCH_HEAD, tag, or branch update.
        execute(receipt, GIT + ["-c", "protocol.file.allow=always",
                               "fetch", "--no-write-fetch-head", "--no-tags", "--recurse-submodules=no",
                               str(bundle_path), "HEAD"])
    actual_tree = execute(receipt, GIT + ["rev-parse", f"{PROOF}^{{tree}}"] ).strip()
    parents = execute(receipt, GIT + ["show", "-s", "--format=%P", PROOF]).strip().split()
    require(actual_tree == PROOF_TREE and parents == [BASELINE], "Exact proof tree or sole parent mismatch")
    expected_paths = {"terminal": RUN + "full-01/terminal.json",
                      "preservation": RUN + "preservation.json",
                      "results": "verification/results.json",
                      "full_output_log": RUN + "full-01/output.log",
                      "frozen_inputs": RUN + "full-01/frozen-inputs.json",
                      "frozen_controls": RUN + "full-01/frozen-controls.json"}
    evidence = {}
    for name, expected_path in expected_paths.items():
        record = manifest["verification"][name]
        require(record["path"] == expected_path, f"Unexpected committed evidence path: {name}")
        data = read_object(receipt, expected_path)
        require(len(data) == record["bytes"] and digest(data) == record["sha256"]
                and blob_digest(data) == record["git_blob_sha1"], f"Committed evidence bytes changed: {name}")
        evidence[name] = data
    terminal = json.loads(evidence["terminal"])
    preservation = json.loads(evidence["preservation"])
    require(terminal.get("status") == "passed" and terminal.get("exit_code") == 0
            and terminal.get("wrapper_exit_code") == 0
            and terminal.get("command") == ["python3", "scripts/verify.py"]
            and terminal.get("attempt") == "full-01"
            and terminal.get("baseline_commit") == BASELINE
            and terminal.get("baseline_tree") == BASELINE_TREE
            and terminal.get("verifier_launched") is True
            and terminal.get("preflight_passed") is True
            and terminal.get("inputs_unchanged") is True
            and terminal.get("controls_unchanged") is True
            and terminal.get("changed_inputs") == [] and terminal.get("changed_controls") == []
            and terminal.get("wrapper_errors") == [] and terminal.get("missing_principal_outputs") == [],
            "Fresh full verification did not pass its exact frozen-input gates")
    require(read_object(receipt, RUN + "full-01/command.json") == evidence["terminal"],
            "Command and terminal receipts differ")
    require(digest(evidence["full_output_log"]) == terminal.get("output_sha256"),
            "Actual full-run output differs from its genuine receipt")
    coverage = preservation.get("coverage", {})
    require(preservation.get("status") == "passed" and preservation.get("actual_full_verifier_exit") == 0
            and preservation.get("full_verifier_attempt") == "full-01"
            and preservation.get("baseline_commit") == BASELINE
            and preservation.get("baseline_tree") == BASELINE_TREE
            and preservation.get("genuine_command_receipt_sha256") == digest(evidence["terminal"])
            and preservation.get("all_previous_declarations_owners_axiom_sets_preserved") is True
            and preservation.get("all_previous_completed_result_mappings_preserved") is True
            and preservation.get("all_previous_source_declaration_maps_preserved") is True
            and coverage.get("numbered_assertions") == 69
            and coverage.get("previous_complete") == 49 and coverage.get("current_complete") == 51
            and coverage.get("promoted_assertions") == ["4.16", "4.17"]
            and coverage.get("all_69_statement_identities_identical") is True
            and coverage.get("all_unpromoted_records_identical") is True
            and coverage.get("main_theorem_verified") is False,
            "Preservation did not pass the exact baseline and scope gates")
    receipt.update(archive_verified=True, proof_commit=PROOF, proof_tree=PROOF_TREE,
                   parent_commit=BASELINE, manifest_sha256=MANIFEST_SHA256,
                   bundle_sha256=BUNDLE_SHA256, bundle_bytes=BUNDLE_BYTES, part_count=63,
                   full_verifier_exit_code=0, main_theorem_verified=False)


def remote_snapshot(receipt):
    refs = [f"refs/heads/{name}" for name in [PROOF_BRANCH] + SOURCE_BRANCHES]
    output = execute(receipt, REMOTE_GIT + ["ls-remote", "--refs", "origin"] + refs)
    snapshot = {}
    for line in output.splitlines():
        fields = line.split()
        require(len(fields) == 2 and SHA.fullmatch(fields[0]) and fields[1] in refs
                and fields[1] not in snapshot, "Unexpected remote ref readback")
        snapshot[fields[1]] = fields[0]
    return snapshot


def publish_proof_ref(receipt):
    require(os.environ.get("GITHUB_ACTIONS") == "true"
            and os.environ.get("GITHUB_EVENT_NAME") == "push"
            and os.environ.get("GITHUB_REPOSITORY") == REPOSITORY
            and os.environ.get("GITHUB_REF_NAME") == TRANSFER_BRANCH
            and os.environ.get("GITHUB_REF") == f"refs/heads/{TRANSFER_BRANCH}",
            "Publication is restricted to the reviewed repository and recovery-branch push job")
    event_commit = os.environ.get("GITHUB_SHA", "")
    require(SHA.fullmatch(event_commit), "Invalid workflow event commit")
    require(execute(receipt, GIT + ["rev-parse", "HEAD"]).strip() == event_commit,
            "Checkout differs from the workflow event commit")
    # Read only the configured URL; do not put unexpected URL credentials in logs.
    origins = subprocess.check_output(GIT + ["remote", "get-url", "--push", "--all", "origin"],
                                      cwd=ROOT, timeout=30).decode("utf-8").splitlines()
    require(len(origins) == 1 and origins[0] in [f"https://github.com/{REPOSITORY}",
                                              f"https://github.com/{REPOSITORY}.git"],
            "Unexpected origin push destination")
    receipt["network_commands_requested"] = True
    before = remote_snapshot(receipt)
    receipt["branch_refs_before"] = before
    proof_ref = f"refs/heads/{PROOF_BRANCH}"
    require(before.get(proof_ref) in [None, PROOF], "Proof branch already has a different commit")
    if proof_ref not in before:
        receipt["proof_ref_push_attempted"] = True
        # Ordinary nonforce push of one exact commit to one exact proof ref.
        execute(receipt, REMOTE_GIT + ["push", "--no-follow-tags", "origin", f"{PROOF}:{proof_ref}"])
        receipt["proof_ref_push_completed"] = True
    after = remote_snapshot(receipt)
    receipt["branch_refs_after"] = after
    require(after.get(proof_ref) == PROOF, "Proof publication readback mismatch")
    require(all(before.get(f"refs/heads/{name}") == after.get(f"refs/heads/{name}")
                for name in SOURCE_BRANCHES), "A source publication ref changed during the job")
    receipt.update(proof_ref_published=True, source_publication_refs_unchanged=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--publish", action="store_true",
                        help="After separate approval, publish only the fixed proof ref from the reviewed job")
    arguments = parser.parse_args()
    started = time.monotonic()
    receipt = {"schema_version": 1, "kind": "exact_verified_bundle_publication",
               "mode": "publish" if arguments.publish else "verify_only",
               "repository": REPOSITORY, "proof_branch": PROOF_BRANCH,
               "transfer_branch": TRANSFER_BRANCH, "archive_prefix": ARCHIVE_PREFIX,
               "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "github_run_id": os.environ.get("GITHUB_RUN_ID"),
               "github_sha": os.environ.get("GITHUB_SHA"),
               "commands": [], "evidence_reads": [], "status": "running",
               "network_commands_requested": False, "proof_ref_push_attempted": False,
               "proof_ref_push_completed": False, "proof_ref_published": False,
               "requested_publication_branches_advanced": False,
               "later_connector_publication_refs": [f"refs/heads/{name}" for name in SOURCE_BRANCHES]}
    try:
        verify_archive(receipt)
        if arguments.publish:
            publish_proof_ref(receipt)
        receipt["status"] = "passed"
    except BaseException as error:
        receipt.update(status="failed", error=repr(error))
    finally:
        receipt["finished_at_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        receipt["elapsed_seconds"] = time.monotonic() - started
        output = ROOT / "publication-transfer/publication-receipt-db841575.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        print("OVERFULL_PUBLICATION_RECEIPT=" + json.dumps(receipt, separators=(",", ":")), flush=True)
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            with open(summary, "a", encoding="utf-8") as stream:
                stream.write("## Exact verified bundle publication\n\n")
                stream.write(f"Mode: **{receipt['mode']}**. Status: **{receipt['status']}**.\n\n")
                stream.write(f"Fixed proof commit: `{PROOF}`.\n\n")
                stream.write(f"Proof ref published: **{receipt['proof_ref_published']}**.\n\n")
                stream.write("Main and the verified continuation branch are reserved for later ordinary connector updates.\n")
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
