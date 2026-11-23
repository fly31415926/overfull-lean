from pathlib import Path
from datetime import datetime,timezone
import concurrent.futures,json,subprocess
root=Path('/workspace/scratch/4ffd54dab476/overfull-lean-current');logs=root.parent/'current-setup-logs'
packages=root/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
manifest=json.loads((root/'lake-manifest.json').read_text())
def restore(dep):
 name=dep['name'];path=packages/name;path.mkdir(exist_ok=True);started=datetime.now(timezone.utc);commands=[]
 with (logs/(name+'-fetch.log')).open('wb') as log:
  for cmd in [['git','init','-q',str(path)],['git','-C',str(path),'remote','add','origin',dep['url']],['git','-C',str(path),'fetch','--depth','1','origin',dep['rev']],['git','-C',str(path),'checkout','--detach','FETCH_HEAD']]:
   r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT);commands.append({'command':cmd,'exit_code':r.returncode})
   if r.returncode:return {'name':name,'status':'failed','started_at_utc':started.isoformat(),'completed_at_utc':datetime.now(timezone.utc).isoformat(),'commands':commands}
 actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
 clean=subprocess.run(['git','-C',str(path),'diff','--quiet','HEAD','--']).returncode==0
 return {'name':name,'status':'passed' if actual==dep['rev'] and clean else 'failed','expected_revision':dep['rev'],'actual_revision':actual,'tracked_sources_clean':clean,'started_at_utc':started.isoformat(),'completed_at_utc':datetime.now(timezone.utc).isoformat(),'commands':commands}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 results=list(pool.map(restore,[p for p in manifest['packages'] if p['type']=='git']))
(logs/'dependency-fetch-results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
raise SystemExit(0 if all(x['status']=='passed' for x in results) else 1)
