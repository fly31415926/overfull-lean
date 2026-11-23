from datetime import datetime, timezone
import hashlib,json,subprocess,time
from pathlib import Path
base=Path('/workspace/scratch/5d2e6f7b5492');logs=Path(__file__).resolve().parent;runtime=base/'lean-runtime';runtime.mkdir(exist_ok=True)
archive=runtime/'lean-4.24.0-linux.tar.zst'
url='https://github.com/leanprover/lean4/releases/download/v4.24.0/lean-4.24.0-linux.tar.zst'
started=datetime.now(timezone.utc)
records=[]
def run(command,name):
 start=datetime.now(timezone.utc)
 with (logs/name).open('wb') as log:
  r=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
 end=datetime.now(timezone.utc)
 item={'command':command,'started_at_utc':start.isoformat(),'finished_at_utc':end.isoformat(),'elapsed_seconds':(end-start).total_seconds(),'exit_code':r.returncode,'log':name};records.append(item)
 (logs/'lean-runtime-commands.json').write_text(json.dumps(records,indent=2)+'\n')
 if r.returncode: raise SystemExit(r.returncode)
run(['curl','-L','--fail','--retry','3','--retry-delay','2','-o',str(archive),url],'lean-runtime-download.log')
actual=hashlib.sha256(archive.read_bytes()).hexdigest()
assert actual=='b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec',actual
assert archive.stat().st_size==459625674,archive.stat().st_size
run(['tar','--zstd','-xf',str(archive),'-C',str(runtime)],'lean-runtime-extract.log')
run([str(runtime/'lean-4.24.0-linux/bin/lean'),'--version'],'lean-runtime-version.log')
record={'status':'runtime_restored','started_at_utc':started.isoformat(),'finished_at_utc':datetime.now(timezone.utc).isoformat(),'archive_url':url,'archive_bytes':archive.stat().st_size,'archive_sha256':actual,'runtime_bin':str(runtime/'lean-4.24.0-linux/bin'),'commands':records}
(logs/'lean-runtime-setup.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
