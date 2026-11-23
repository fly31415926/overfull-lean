from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys
root=Path('/workspace/scratch/5d2e6f7b5492/overfull-lean')
work=Path('/workspace/scratch/96ddfd820f7d/uniform-work')
run=work/sys.argv[1]
run.mkdir()
source=work/'ReservedPrimary.lean'
data=source.read_bytes()
(run/source.name).write_bytes(data)
cmd=['/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin/lake','env','lean','-DwarningAsError=true',str(source)]
env=os.environ.copy()
env['PATH']='/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:'+env['PATH']
record={'command':cmd,'cwd':str(root),'started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':hashlib.sha256(data).hexdigest()}
(run/'command.json').write_text(json.dumps(record,indent=2)+'\n')
with (run/'output.log').open('w') as out:
    p=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
record['exit_code']=p.returncode
record['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(run/'command.json').write_text(json.dumps(record,indent=2)+'\n')
print((run/'output.log').read_text())
print(json.dumps(record,indent=2))
