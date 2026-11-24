#!/usr/bin/env python3
"""Capture reviewed sources and completed development evidence without changing HEAD/index."""
from pathlib import Path
import subprocess,os,json,datetime
ROOT=Path('/workspace/scratch/05b9e46fe96b/overfull-lean')
OUT=Path('/workspace/scratch/05b9e46fe96b/recovery-20261124/preaudit-snapshot')
BASE='1c9404a454c99fe5c11ba8d774cb9c259f291f20'
RUN='verification/runs/20261124T213000Z'
OUT.mkdir(exist_ok=False)
env={**os.environ,'GIT_INDEX_FILE':str(OUT/'index')}
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,env=env)
head=git('rev-parse','HEAD').decode().strip()
assert head==BASE
before=(ROOT/'.git/index').read_bytes()
git('read-tree',BASE)
git('add','-A','--','Overfull.lean','README.md','Overfull','docs','scripts',RUN,
    ':(exclude)'+RUN+'/full-01',
    ':(exclude)'+RUN+'/build.lock')
tree=git('write-tree').decode().strip()
assert (ROOT/'.git/index').read_bytes()==before
assert git('rev-parse','HEAD').decode().strip()==head
report={'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'purpose':'Immutable pre-audit data transport snapshot. Does not assert full verification.',
 'baseline':BASE,'tree':tree,'live_full_attempt_excluded':True,
 'working_head_and_index_unchanged':True,
 'entries':len([x for x in git('ls-tree','-r','-z',tree).split(bytes([0])) if x]),
 'changed_paths':git('diff','--name-only',BASE,tree).decode().splitlines()}
(OUT/'snapshot.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='changed_paths'},indent=2))
