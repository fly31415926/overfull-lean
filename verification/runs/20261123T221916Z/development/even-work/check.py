from pathlib import Path
import subprocess,json,datetime,os,sys,hashlib
root=Path("/workspace/scratch/0f64d20031b0/overfull-next")
module=sys.argv[1] if len(sys.argv)>1 else "EvenColors"
base=Path("/workspace/scratch/0f64d20031b0/even-work")
a=1
while (base/f"{module}-{a:02}").exists(): a+=1
out=base/f"{module}-{a:02}"
out.mkdir()
src=root/f"Overfull/ExceptionalPalette/{module}.lean"
(out/src.name).write_bytes(src.read_bytes())
bin=Path("/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin")
obj=root/f".lake/build/lib/lean/Overfull/ExceptionalPalette/{module}.olean"
obj.parent.mkdir(parents=True,exist_ok=True)
cmd=[str(bin/"lake"),"env","lean","-DwarningAsError=true","-o",str(obj),str(src)]
env=os.environ.copy();env["PATH"]=str(bin)+":"+env.get("PATH","")
meta={"command":cmd,"cwd":str(root),"started_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"source_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"status":"running"}
(out/"command.json").write_text(json.dumps(meta,indent=2)+"\n")
with (out/"output.log").open("w") as f: r=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
meta.update({"finished_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"exit_code":r.returncode,"status":"passed" if r.returncode==0 else "failed","output_sha256":hashlib.sha256((out/"output.log").read_bytes()).hexdigest()})
(out/"command.json").write_text(json.dumps(meta,indent=2)+"\n")
print(str(out));print((out/"output.log").read_text());print("exit",r.returncode)
sys.exit(r.returncode)
