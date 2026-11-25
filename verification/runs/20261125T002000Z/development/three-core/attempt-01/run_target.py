from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys
repo=Path('/workspace/scratch/0e01d9fcb296/overfull-lean')
base=Path('/workspace/scratch/0e01d9fcb296/three-core-attempts')
attempt=base / sys.argv[1]
attempt.mkdir()
source=repo/'Overfull/AuxiliarySimple/OrdinaryThree.lean'
shutil.copy2(source,attempt/'OrdinaryThree.lean')
runner=Path(__file__).resolve()
shutil.copy2(runner,attempt/'run_target.py')
command=['/home/agent/.elan/bin/lake','build','--wfail','Overfull.AuxiliarySimple.OrdinaryThree']
meta={'command':command,'cwd':str(repo),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runner_sha256':hashlib.sha256(runner.read_bytes()).hexdigest(),'environment':{'LEAN_NUM_THREADS':'2'}}
(attempt/'execution.json').write_text(json.dumps(meta,indent=2)+'\n')
env=os.environ.copy()
env['PATH']='/home/agent/.elan/bin:'+env['PATH']
env['LEAN_NUM_THREADS']='2'
with (attempt/'build.log').open('w') as log:
    result=subprocess.run(command,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT)
meta.update({'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'child_exit_code':result.returncode,'runner_sha256_after':hashlib.sha256(runner.read_bytes()).hexdigest(),'source_sha256_after':hashlib.sha256(source.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((attempt/'build.log').read_bytes()).hexdigest()})
drift=meta['source_sha256'] != meta['source_sha256_after'] or meta['runner_sha256'] != meta['runner_sha256_after']
meta['frozen_inputs_unchanged']=not drift
meta['wrapper_exit_code']=result.returncode if result.returncode else (3 if drift else 0)
(attempt/'execution.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2),flush=True)
print((attempt/'build.log').read_text()[-18000:],flush=True)
raise SystemExit(meta['wrapper_exit_code'])
