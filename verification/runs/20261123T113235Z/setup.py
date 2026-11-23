from pathlib import Path
from datetime import datetime,timezone
import json, os, subprocess
root=Path(__file__).resolve().parents[3]
run=Path(__file__).resolve().parent
env=os.environ.copy(); env["PATH"]="/workspace/scratch/4ffd54dab476/lean-runtime/lean-4.24.0-linux/bin:"+env["PATH"]
steps=[("vizing",["python3","scripts/setup_vizing.py"]),("cache",["lake","exe","cache","get","Mathlib.Combinatorics.SimpleGraph.Matching","Mathlib.Combinatorics.SimpleGraph.Coloring","Mathlib.Combinatorics.SimpleGraph.Tutte","Mathlib.Tactic","Mathlib.Data.Real.Archimedean","Mathlib.Data.Nat.Choose.Basic","Mathlib.Analysis.Convex.Combination","Mathlib.Analysis.Normed.Operator.Banach","Mathlib.Analysis.Normed.Module.FiniteDimension","Mathlib.Combinatorics.Hall.Finite"]),("base-build",["lake","build","Overfull.AssignedParts.MatchedCuts","Overfull.CircuitPatterns.Weights","Overfull.MultigraphMatchingProbability"])]
records=[]
for name, cmd in steps:
 start=datetime.now(timezone.utc)
 print("Starting",name,flush=True)
 with (run/("setup-"+name+".log")).open("wb") as log:
  result=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 record={"command":cmd,"started_at_utc":start.isoformat(),"finished_at_utc":datetime.now(timezone.utc).isoformat(),"exit_code":result.returncode,"log":"setup-"+name+".log"}
 records.append(record);(run/"setup-commands.json").write_text(json.dumps(records,indent=2)+"\n")
 print(record,flush=True)
 if result.returncode: raise SystemExit(result.returncode)
