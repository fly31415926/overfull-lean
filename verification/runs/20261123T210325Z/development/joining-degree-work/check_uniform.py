from pathlib import Path
from datetime import datetime, timezone
import os, subprocess, json, hashlib, shutil
work=Path(__file__).resolve().parent
repo=Path('/workspace/scratch/5d2e6f7b5492/overfull-lean')
binpath=Path('/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin')
lib=work/'checklib'
env=os.environ.copy(); env['PATH']=str(binpath)+os.pathsep+env['PATH']
base=subprocess.check_output([str(binpath/'lake'),'env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
env['LEAN_PATH']=str(lib)+os.pathsep+base
attempt=work/'uniform-check-02'; attempt.mkdir()
source=lib/'Overfull/ResidualPalette/UniformJoining.lean'
paths=[source,lib/'Overfull/ResidualPalette/JoiningBounds.lean',lib/'Overfull/ResidualPalette/UniformCompletion.lean']
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[str(binpath/'lean'),'-DwarningAsError=true','--root='+str(lib),str(source)]
meta={'command':cmd,'cwd':str(repo),'started_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':{str(p):sha(p) for p in paths},'status':'running'}
for p in paths: shutil.copyfile(p,attempt/p.name)
(attempt/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
with (attempt/'output.log').open('w') as out:
 cp=subprocess.run(cmd,cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT)
meta.update(exit_code=cp.returncode,status='passed' if cp.returncode==0 else 'failed',completed_at_utc=datetime.now(timezone.utc).isoformat(),output_sha256=sha(attempt/'output.log'))
(attempt/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
raise SystemExit(cp.returncode)
