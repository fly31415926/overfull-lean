from pathlib import Path
import datetime,json,subprocess,os,sys,shutil
root=Path('/workspace/scratch/0f64d20031b0/overfull-next')
work=Path('/workspace/scratch/0f64d20031b0/reserve-work')
module=sys.argv[1]
n=len(list(work.glob('attempt-*')))+1
out=work/f'attempt-{n:03}'
out.mkdir()
for p in (root/'Overfull/ExceptionalPalette').glob('Reserve*.lean'): shutil.copy2(p,out/p.name)
target=root/'.lake/build/lib/lean'/('Overfull/ExceptionalPalette/'+module+'.olean')
target.parent.mkdir(parents=True,exist_ok=True)
cmd=['lake','env','lean','-DwarningAsError=true','-o',str(target),'Overfull/ExceptionalPalette/'+module+'.lean']
env=os.environ.copy();env['PATH']='/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:'+env['PATH']
r={'command':cmd,'cwd':str(root),'started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':None}
(out/'command.json').write_text(json.dumps(r,indent=2)+'\n')
with (out/'output.log').open('w') as log: p=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
r.update(exit_code=p.returncode,finished_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(out/'command.json').write_text(json.dumps(r,indent=2)+'\n')
print(str(out));print((out/'output.log').read_text());sys.exit(p.returncode)
