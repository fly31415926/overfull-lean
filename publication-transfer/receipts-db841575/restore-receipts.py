#!/usr/bin/env python3
"""Validate and restore receipt files as data; never execute archived code."""
import argparse,base64,hashlib,io,json,os,stat,tarfile
from pathlib import Path,PurePosixPath
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(d):return hashlib.sha256(d).hexdigest()
def blob(d):return hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
def safe(name):
    p=PurePosixPath(name)
    need(name and not p.is_absolute() and '\\' not in name and all(x not in ('','.','..') for x in name.split('/')),'Unsafe path')
    return p
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--manifest',type=Path,default=Path(__file__).with_name('manifest.json'))
ap.add_argument('--output-dir',type=Path,required=True)
a=ap.parse_args();mp=a.manifest.resolve(strict=True);m=json.loads(mp.read_bytes())
need(m['schema_version']==1 and m['kind']=='publication_receipt_archive','Wrong manifest')
need(sha(Path(__file__).read_bytes())==m['restore_helper']['sha256'],'Restore helper differs')
need(len(m['parts'])==m['part_count'] and m['part_count']>0,'Invalid part count')
chunks=[]
for n,p in enumerate(m['parts'],1):
    need(p['number']==n and p['path']==f'receipts.part-{n:06d}.b64','Part name/order mismatch')
    source=mp.parent/p['path'];need(stat.S_ISREG(source.lstat().st_mode),'Part is not regular')
    d=source.read_bytes()
    need(0<len(d)<=45000 and len(d)==p['bytes'] and sha(d)==p['sha256'] and blob(d)==p['git_blob_sha1'],'Part mismatch')
    decoded=base64.b64decode(d,validate=True);need(base64.b64encode(decoded)==d,'Noncanonical base64');chunks.append(decoded)
archive=b''.join(chunks)
need(len(archive)==m['archive']['bytes'] and sha(archive)==m['archive']['sha256'],'Archive mismatch')
with tarfile.open(fileobj=io.BytesIO(archive),mode='r:gz') as tar:
    members=tar.getmembers();need(len(members)==m['file_count']+1,'Member count mismatch')
    first=members[0]
    need(first.name=='inventory.json' and first.isfile() and first.size==m['inner_inventory']['bytes'],'Invalid inventory')
    raw=tar.extractfile(first).read();need(sha(raw)==m['inner_inventory']['sha256'],'Inventory hash mismatch')
    inv=json.loads(raw);records=inv['files'];need(len(records)==m['file_count']==inv['file_count'],'Inventory count mismatch')
    expected={e['path']:e for e in records};need(len(expected)==len(records) and 'inventory.json' not in expected,'Duplicate path')
    need(sum(e['bytes'] for e in records)==m['payload_bytes']==inv['payload_bytes'],'Payload size mismatch')
    checked={'inventory.json':raw};seen=set()
    for member in members[1:]:
        name=member.name;safe(name)
        need(member.isfile() and name in expected and name not in seen,'Unexpected member, duplicate, or link')
        e=expected[name];need(member.size==e['bytes'],'Member size mismatch');d=tar.extractfile(member).read()
        need(len(d)==e['bytes'] and sha(d)==e['sha256'] and blob(d)==e['git_blob_sha1'],'Member hash mismatch')
        checked[name]=d;seen.add(name)
    need(seen==set(expected),'Missing member')
destination=a.output_dir.absolute();need(not destination.exists(),'Output directory must be new')
destination.mkdir(parents=True,mode=0o700);root=destination.resolve()
for name,d in checked.items():
    target=root.joinpath(*safe(name).parts);target.parent.mkdir(parents=True,exist_ok=True)
    need(target.resolve().is_relative_to(root),'Path escapes output')
    with target.open('xb') as f:f.write(d)
    os.chmod(target,0o644)
print(json.dumps({'status':'passed','files_restored':len(seen),'archive_sha256':m['archive']['sha256'],'cutoff_utc':m['cutoff_utc'],'archived_code_executed':False},indent=2))
