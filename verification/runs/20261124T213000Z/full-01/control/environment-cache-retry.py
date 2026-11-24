#!/usr/bin/env python3
"""Retry the pinned dependency cache with a modest documented curl rate."""
from pathlib import Path
import os,subprocess,json
ROOT=Path(__file__).resolve().parents[3]
settings=ROOT.parent/'cache-curl-config'
settings.mkdir(exist_ok=True)
config='parallel-max = 4\nrate = "4/s"\n'
(settings/'.curlrc').write_text(config)
env=os.environ.copy()
env['CURL_HOME']=str(settings)
modules=['Mathlib.Combinatorics.SimpleGraph.Matching','Mathlib.Combinatorics.SimpleGraph.Coloring','Mathlib.Combinatorics.SimpleGraph.Tutte','Mathlib.Tactic','Mathlib.Data.Real.Archimedean','Mathlib.Data.Nat.Choose.Basic','Mathlib.Analysis.Convex.Combination','Mathlib.Analysis.Normed.Operator.Banach','Mathlib.Analysis.Normed.Module.FiniteDimension','Mathlib.Combinatorics.Hall.Finite']
print(json.dumps({'curl_configuration_directory':str(settings),'curl_configuration':config,'reason':'Actual prior HTTP429 responses; retry with lower request rate and concurrency.'}),flush=True)
raise SystemExit(subprocess.run(['lake','exe','cache','get',*modules],cwd=ROOT,env=env).returncode)
