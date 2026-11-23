from pathlib import Path
from datetime import datetime, timezone
import os, subprocess, json, hashlib, shutil, sys
work=Path(__file__).resolve().parent
repo=Path('/workspace/scratch/5d2e6f7b5492/overfull-lean')
binpath=Path('/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin')
lib=work/'checklib'
module=lib/'Overfull/ResidualPalette'
module.mkdir(parents=True,exist_ok=True)
for path in (repo/'.lake/build/lib/lean/Overfull').iterdir():
    target=lib/'Overfull'/path.name
    if not target.exists():
        target.symlink_to(path)
shared=Path('/workspace/scratch/96ddfd820f7d/joining-degree-work/checklib/Overfull/ResidualPalette')
for path in shared.iterdir():
    if path.suffix in ('.olean','.ilean','.lean') and path.name not in ('ReservedPrimary.lean','NativeReservedCrossings.lean','NativeProtectedPalette.lean'):
        shutil.copyfile(path,module/path.name)
shutil.copyfile(work/'ReservedPrimary.lean',module/'ReservedPrimary.lean')
shutil.copyfile(Path('/workspace/scratch/96ddfd820f7d/joining-degree-work/NativeReservedCrossings.lean'),module/'NativeReservedCrossings.lean')
shutil.copyfile(work/'NativeProtectedPalette.lean',module/'NativeProtectedPalette.lean')
env=os.environ.copy(); env['PATH']=str(binpath)+os.pathsep+env['PATH']
base=subprocess.check_output([str(binpath/'lake'),'env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
env['LEAN_PATH']=str(lib)+os.pathsep+base
attempt=work/sys.argv[1];attempt.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ('ReservedPrimary','NativeReservedCrossings','NativeProtectedPalette'):
    stage=attempt/name;stage.mkdir()
    source=module/(name+'.lean')
    cmd=[str(binpath/'lean'),'-DwarningAsError=true','--root='+str(lib),'-o',str(module/(name+'.olean')),str(source)]
    meta={'command':cmd,'cwd':str(repo),'started_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':sha(source),'dependency_source_sha256':{p.name:sha(p) for p in module.glob('*.lean')},'status':'running'}
    shutil.copyfile(source,stage/source.name)
    (stage/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
    with (stage/'output.log').open('w') as out:
        cp=subprocess.run(cmd,cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT)
    meta.update(exit_code=cp.returncode,status='passed' if cp.returncode==0 else 'failed',completed_at_utc=datetime.now(timezone.utc).isoformat(),output_sha256=sha(stage/'output.log'))
    (stage/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(name,cp.returncode)
    print((stage/'output.log').read_text())
    if cp.returncode:
        raise SystemExit(cp.returncode)
