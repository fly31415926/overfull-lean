from pathlib import Path
from datetime import datetime,timezone
import os,json,re,subprocess,sys
root=Path('/workspace/scratch/4ffd54dab476/overfull-lean-current');logs=root.parent/'current-setup-logs'
env=dict(os.environ);env['PATH']=str(root.parent/'lean-runtime/lean-4.24.0-linux/bin')+':'+env['PATH']
phase=sys.argv[1]
if phase=='shared':
 modules=['Overfull.CriticalMultigraph','Overfull.CompatibleCircuits.Counting','Overfull.FourOdd.OriginalGraph']
elif phase=='existing':
 content=subprocess.check_output(['git','show','28edc7b555d459b93a00d15258ca374abf5f0bb0:Overfull.lean'],cwd=root,text=True)
 modules=re.findall(r'^import\s+(\S+)',content,re.MULTILINE)
else: raise SystemExit('Unknown phase')
command=['lake','build','--wfail',*modules];started=datetime.now(timezone.utc)
record={'command':command,'started_at_utc':started.isoformat(),'status':'running','module_target_count':len(modules),'source_of_targets':'three explicit baseline modules' if phase=='shared' else 'git show 28edc7b555d459b93a00d15258ca374abf5f0bb0:Overfull.lean','not_full_verification':True}
(logs/(phase+'-prerequisites-command.json')).write_text(json.dumps(record,indent=2)+'\n')
with (logs/(phase+'-prerequisites-build.log')).open('wb') as log:r=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc);record.update({'status':'passed' if r.returncode==0 else 'failed','finished_at_utc':finished.isoformat(),'elapsed_seconds':(finished-started).total_seconds(),'exit_code':r.returncode});(logs/(phase+'-prerequisites-command.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items() if k!='command'},indent=2));print((logs/(phase+'-prerequisites-build.log')).read_text()[-10000:]);raise SystemExit(r.returncode)
