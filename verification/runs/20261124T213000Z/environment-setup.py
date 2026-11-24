#!/usr/bin/env python3
"""Install exact official Lean archive after SHA256 verification."""
from pathlib import Path
import hashlib,json,subprocess,urllib.request
ROOT=Path(__file__).resolve().parents[3]
DEST=ROOT.parent/'toolchain'
URL='https://github.com/leanprover/lean4/releases/download/v4.24.0/lean-4.24.0-linux.tar.zst'
EXPECTED='b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec'
DEST.mkdir(exist_ok=True)
archive=DEST/'lean-4.24.0-linux.tar.zst'
if not archive.exists():
    subprocess.run(['curl','--fail','--location','--retry','2','--max-time','300','--output',str(archive),URL],check=True)
digest=hashlib.sha256(archive.read_bytes()).hexdigest()
assert digest==EXPECTED,(digest,EXPECTED)
print(json.dumps({'url':URL,'bytes':archive.stat().st_size,'sha256':digest,'sha256_matches_official_release':True}),flush=True)
subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(DEST)],check=True)
subprocess.run([str(DEST/'lean-4.24.0-linux/bin/lean'),'--version'],check=True)
