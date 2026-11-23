from pathlib import Path
from datetime import datetime,timezone
import os,json,subprocess,time
root=Path('/workspace/scratch/4ffd54dab476/overfull-lean-current');logs=root.parent/'current-setup-logs'
env=dict(os.environ);env['PATH']=str(root.parent/'current-tools')+':'+str(root.parent/'lean-runtime/lean-4.24.0-linux/bin')+':'+env['PATH']
roots=json.loads((logs/'mathlib-cache-roots.json').read_text());command=['lake','exe','cache','get',*roots]
started=datetime.now(timezone.utc);record={'command':command,'started_at_utc':started.isoformat(),'status':'running','root_module_count':len(roots),'curl_parallel_max':2,'curl_request_rate':'5/s','backoff_seconds':10,'dependency_sources_modified':False};(logs/'mathlib-cache-retry-command.json').write_text(json.dumps(record,indent=2)+'\n')
time.sleep(10)
with (logs/'mathlib-cache-retry.log').open('wb') as log:r=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc);record.update({'status':'passed' if r.returncode==0 else 'failed','finished_at_utc':finished.isoformat(),'elapsed_seconds':(finished-started).total_seconds(),'exit_code':r.returncode});(logs/'mathlib-cache-retry-command.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='command'},indent=2));print((logs/'mathlib-cache-retry.log').read_text()[-8000:]);raise SystemExit(r.returncode)
