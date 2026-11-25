#!/usr/bin/env python3
"""Prepare checked inline/blob requests from an immutable Git snapshot."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--snapshot', type=Path, required=True)
a = parser.parse_args()
folder = a.snapshot.resolve(strict=True)
manifest = json.loads((folder / 'manifest.json').read_text())
inline, uploads, identities = {}, [], []
for entry in manifest['blobs']:
    p = (folder / entry['payload']).resolve(strict=True)
    assert p.is_relative_to(folder) and p.is_file()
    body = p.read_bytes()
    assert len(body) == entry['size']
    assert hashlib.sha1(f'blob {len(body)}\0'.encode() + body).hexdigest() == entry['sha']
    assert hashlib.sha256(body).hexdigest() == entry['sha256']
    try:
        text = body.decode('utf-8')
        encoding = 'utf-8'
    except UnicodeDecodeError:
        text, encoding = None, 'base64'
    identity = {k: entry[k] for k in ('sha', 'sha256', 'size', 'paths')}
    if text is not None and len(body) <= 128000:
        inline[entry['sha']] = text
        identities.append(identity)
    else:
        uploads.append({**identity, 'encoding': encoding})
request = json.loads((folder / manifest['root_tree_request']).read_text())
for entry in request['tree_elements']:
    if entry.get('sha') in inline:
        entry['content'] = inline[entry.pop('sha')]
plan = {
    'repository_full_name': manifest['repository_full_name'],
    'baseline_commit': manifest['baseline_commit'],
    'baseline_tree': manifest['baseline_tree'],
    'expected_tree': manifest['expected_tree'],
    'changed_path_count': manifest['changed_path_count'],
    'inline_blob_count': len(inline),
    'inline_blobs': identities,
    'uploads': uploads,
}
for name, value in [('inline-tree-request.json', request), ('upload-plan.json', plan)]:
    data = (json.dumps(value, ensure_ascii=True, separators=(',', ':')) + '\n').encode()
    with (folder / name).open('xb') as output:
        output.write(data)
    print(json.dumps({'path': str(folder / name), 'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest()}))
print(json.dumps({'inline_blobs': len(inline), 'individual_uploads': len(uploads),
                  'expected_tree': manifest['expected_tree']}))
