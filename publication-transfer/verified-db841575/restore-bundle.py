#!/usr/bin/env python3
"""Reassemble an exact incremental Git bundle from hash-checked ASCII parts.

This script writes only the requested new bundle file. It does not fetch,
unbundle, check out a commit, or change repository refs. Optional --verify-repo
runs read-only `git bundle verify` against a repository containing the baseline.
"""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile


def require(value, message):
    if not value:
        raise RuntimeError(message)


def git_blob_sha(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=Path(__file__).with_name('manifest.json'))
    parser.add_argument('--output', type=Path, required=True, help='A new output bundle path; never overwritten')
    parser.add_argument('--verify-repo', type=Path, help='Optional existing repository containing the prerequisite')
    args = parser.parse_args()
    manifest_path = args.manifest.resolve(strict=True)
    manifest = json.loads(manifest_path.read_bytes())
    require(manifest['schema_version'] == 1 and manifest['kind'] == 'incremental_git_bundle_archive',
            'Unsupported archive manifest')
    require(hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == manifest['restore_script']['sha256'],
            'Restore script differs from the archive manifest')
    for name in ('commit', 'tree', 'parent', 'prerequisite_commit'):
        require(re.fullmatch(r'[0-9a-f]{40}', manifest[name]), f'Invalid {name} object ID')
    require(manifest['parent'] == manifest['prerequisite_commit'], 'Parent/prerequisite mismatch')
    parts = manifest['parts']
    require(parts and manifest['part_count'] == len(parts), 'Empty or inconsistent part inventory')
    require(manifest['part_character_limit'] == 45000, 'Unexpected part size limit')
    output = args.output.resolve()
    require(not output.exists(), 'Refusing to overwrite an existing output file')
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix='restore-partial-', dir=output.parent)
    temporary = Path(name)
    total, digest, seen = 0, hashlib.sha256(), set()
    try:
        with os.fdopen(fd, 'wb') as destination:
            for number, part in enumerate(parts, 1):
                require(part['number'] == number, 'Parts are missing or out of order')
                filename = part['path']
                require(re.fullmatch(r'bundle\.part-[0-9]{6}\.b64', filename)
                        and filename not in seen, 'Unexpected or duplicate part filename')
                seen.add(filename)
                path = manifest_path.parent / filename
                require(stat.S_ISREG(path.lstat().st_mode), 'Part is not a regular file')
                data = path.read_bytes()
                require(0 < len(data) <= 45000 and len(data) == part['bytes'], 'Part length mismatch')
                require(hashlib.sha256(data).hexdigest() == part['sha256'], 'Part SHA-256 mismatch')
                require(git_blob_sha(data) == part['git_blob_sha1'], 'Part Git blob SHA-1 mismatch')
                decoded = base64.b64decode(data, validate=True)
                require(base64.b64encode(decoded) == data, 'Noncanonical base64 part')
                digest.update(decoded)
                total += len(decoded)
                require(total <= manifest['bundle']['bytes'], 'Decoded bundle exceeds expected length')
                destination.write(decoded)
        require(total == manifest['bundle']['bytes'], 'Reassembled bundle length mismatch')
        require(digest.hexdigest() == manifest['bundle']['sha256'], 'Reassembled bundle SHA-256 mismatch')
        os.link(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    git_verified = False
    if args.verify_repo is not None:
        env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0'}
        result = subprocess.run(['git', '-C', str(args.verify_repo.resolve(strict=True)),
                                 'bundle', 'verify', str(output)], env=env, capture_output=True)
        require(result.returncode == 0, 'Git bundle verification failed: '
                + result.stdout.decode(errors='replace') + result.stderr.decode(errors='replace'))
        heads = subprocess.check_output(['git', '-C', str(args.verify_repo.resolve(strict=True)),
                                         'bundle', 'list-heads', str(output)], env=env).decode().splitlines()
        require(heads == [manifest['commit'] + ' HEAD'], 'Bundle head differs from the exact archived commit')
        git_verified = True
    print(json.dumps({'status': 'passed', 'output': str(output), 'bytes': total,
                      'sha256': digest.hexdigest(), 'part_count': len(parts),
                      'commit': manifest['commit'], 'prerequisite_commit': manifest['prerequisite_commit'],
                      'git_bundle_verified': git_verified, 'refs_changed': False}, indent=2))


if __name__ == '__main__':
    main()
