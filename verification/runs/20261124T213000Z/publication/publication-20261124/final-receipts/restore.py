#!/usr/bin/env python3
"""Restore the exact publication observation archive with complete hash checks."""
from pathlib import Path
import argparse,base64,gzip,hashlib,io,json,tarfile
p=argparse.ArgumentParser();p.add_argument("destination");a=p.parse_args()
root=Path(__file__).resolve().parent; dest=Path(a.destination)
if dest.exists(): raise SystemExit("Use a new destination directory")
m=json.loads((root/"manifest.json").read_text()); data=[]
for part in m["parts"]:
 raw=(root/part["path"]).read_bytes()
 assert len(raw)==part["bytes"] and hashlib.sha256(raw).hexdigest()==part["sha256"]
 data.append(raw)
encoded=b"".join(data);assert len(encoded)==m["encoded_bytes"]
compressed=base64.b64decode(encoded,validate=True)
assert base64.b64encode(compressed)==encoded
assert len(compressed)==m["gzip_bytes"] and hashlib.sha256(compressed).hexdigest()==m["gzip_sha256"]
with tarfile.open(fileobj=io.BytesIO(gzip.decompress(compressed)),mode="r:") as archive:
 names=archive.getnames();assert len(names)==len(set(names))
 inventory_raw=archive.extractfile(m["inventory_path"]).read()
 assert hashlib.sha256(inventory_raw).hexdigest()==m["inventory_sha256"]
 inv=json.loads(inventory_raw); records={v["path"]:v for v in inv["files"]}
 assert len(records)==m["original_file_count"]
 assert set(names)==set(records)|{m["inventory_path"]}
 restored={}
 for member in archive.getmembers():
  assert member.isfile() and not member.name.startswith("/") and ".." not in Path(member.name).parts
  raw=archive.extractfile(member).read()
  if member.name in records:
   r=records[member.name];assert len(raw)==r["bytes"] and hashlib.sha256(raw).hexdigest()==r["sha256"]
  restored[member.name]=raw
 dest.mkdir(parents=True)
 for name,raw in restored.items():
  path=dest/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
 print(json.dumps({"status":"passed","original_files_restored":len(records),"bytes":sum(v["bytes"] for v in records.values()),"canonical_commit":m["canonical_commit"]}))
