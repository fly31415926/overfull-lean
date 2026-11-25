#!/usr/bin/env python3
"""Read a bounded base64 body chunk from an immutable prepared upload snapshot.

The payload is checked against its Git blob SHA-1, SHA-256, and byte length on
 every read. No files or Git state are changed. Use exec_command with an output
budget of 100000 tokens for 128000-character chunks, parse the returned JSON,
and reject truncation or inconsistent offsets before assembling the payload.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def read_chunk(snapshot: Path, sha: str, offset: int, limit: int) -> dict:
    if not re.fullmatch(r'[0-9a-f]{40}', sha):
        raise ValueError('Expected a lowercase 40-character Git blob SHA.')
    if offset < 0 or not 1 <= limit <= 128000:
        raise ValueError('Require offset >= 0 and 1 <= limit <= 128000.')
    folder = snapshot.resolve(strict=True)
    manifest = json.loads((folder / 'manifest.json').read_text(encoding='utf-8'))
    matches = [entry for entry in manifest['blobs'] if entry['sha'] == sha]
    if len(matches) != 1 or matches[0].get('type') != 'blob':
        raise ValueError('Expected exactly one matching blob in the snapshot manifest.')
    entry = matches[0]
    relative = PurePosixPath(entry['payload'])
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('The payload reference must stay inside the snapshot.')
    path = (folder / relative).resolve(strict=True)
    if not path.is_relative_to(folder) or not path.is_file():
        raise ValueError('The payload is not a regular file inside the snapshot.')
    body = path.read_bytes()
    actual_sha = hashlib.sha1(f'blob {len(body)}\0'.encode('ascii') + body).hexdigest()
    digest = hashlib.sha256(body).hexdigest()
    if actual_sha != sha or digest != entry['sha256'] or len(body) != entry['size']:
        raise ValueError('Payload bytes do not match the prepared Git SHA, SHA-256, or size.')
    encoded = base64.b64encode(body).decode('ascii')
    if offset > len(encoded):
        raise ValueError('Offset exceeds the encoded payload length.')
    end = min(offset + limit, len(encoded))
    return {'sha': sha, 'type': 'blob', 'byte_size': len(body), 'sha256': digest,
            'encoding': 'base64', 'offset': offset, 'next_offset': end,
            'total_characters': len(encoded), 'done': end == len(encoded),
            'content': encoded[offset:end]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', type=Path, required=True)
    parser.add_argument('--sha', required=True)
    parser.add_argument('--offset', type=int, default=0)
    parser.add_argument('--limit', type=int, default=64000)
    args = parser.parse_args()
    print(json.dumps(read_chunk(args.snapshot, args.sha, args.offset, args.limit),
                     separators=(',', ':')))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(f'Upload chunk read failed: {error}', file=sys.stderr)
        raise SystemExit(1)
