from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys

folder = Path(__file__).resolve().parent
source = folder / 'PaletteParity.lean'
attempt = folder / sys.argv[1]
attempt.mkdir(exist_ok=False)
shutil.copyfile(source, attempt/source.name)
env = os.environ.copy()
env['PATH'] = '/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:'+env['PATH']
command = ['lake','env','lean','-DwarningAsError=true',str(source)]
record = {'command':command, 'cwd':'/workspace/scratch/5d2e6f7b5492/overfull-lean',
          'started_at_utc':datetime.now(timezone.utc).isoformat(),
          'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
with (attempt/'output.log').open('wb') as log:
    result = subprocess.run(command, cwd=record['cwd'], env=env, stdout=log, stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode,status='passed' if result.returncode==0 else 'failed',
              finished_at_utc=datetime.now(timezone.utc).isoformat())
(attempt/'command.json').write_text(json.dumps(record,indent=2)+'\n')
print((attempt/'output.log').read_text())
print(json.dumps(record,indent=2))
sys.exit(result.returncode)
