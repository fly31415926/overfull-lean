#!/usr/bin/env python3
"""Read checked immutable upload bytes in bounded JSON text/base64 chunks."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('--snapshot', type=Path, required=True)
p.add_argument('--sha', required=True)
p.add_argument('--encoding', choices=['utf-8', 'base64'], required=True)
p.add_argument('--offset', type=int, default=0)
p.add_argument('--limit', type=int, default=128000)
a = p.parse_args()
assert re.fullmatch('[0-9a-f]{40}', a.sha)
assert a.offset >= 0 and 1 <= a.limit <= 128000
folder = a.snapshot.resolve(strict=True)
manifest = json.loads((folder / 'manifest.json').read_text())
matches = [x for x in manifest['blobs'] if x['sha'] == a.sha]
assert len(matches) == 1
entry = matches[0]
path = (folder / entry['payload']).resolve(strict=True)
assert path.is_relative_to(folder) and path.is_file()
body = path.read_bytes()
assert len(body) == entry['size']
assert hashlib.sha1(f'blob {len(body)}\0'.encode() + body).hexdigest() == a.sha
assert hashlib.sha256(body).hexdigest() == entry['sha256']
content = body.decode('utf-8') if a.encoding == 'utf-8' else base64.b64encode(body).decode('ascii')
assert a.offset <= len(content)
end = min(a.offset + a.limit, len(content))
print(json.dumps({'sha': a.sha, 'sha256': entry['sha256'], 'byte_size': len(body),
                  'encoding': a.encoding, 'offset': a.offset, 'next_offset': end,
                  'total_characters': len(content), 'done': end == len(content),
                  'content': content[a.offset:end]}, ensure_ascii=True, separators=(',', ':')))
