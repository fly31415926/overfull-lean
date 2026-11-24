"""Package only the new genuinely verified continuation; no network publication."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
RELEASE = ROOT.parent / "weighted-release"
BASELINE = "c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)
def digest(data):
    return hashlib.sha256(data).hexdigest()
def require(ok, why):
    if not ok:
        raise SystemExit(why)

report = json.loads((RUN/"preservation.json").read_text())
result = json.loads((ROOT/"verification/results.json").read_text())
command = json.loads((RUN/"verification-command.json").read_text())
frozen = json.loads((RUN/"frozen-candidate-inputs.json").read_text())
source = json.loads((ROOT/"docs/weighted-palette-source.json").read_text())
require(report["status"] == "verification_and_preservation_passed", "Preservation has not passed")
preservation = json.loads((RUN/"record-final-command.json").read_text())
require(preservation["status"] == "passed" and preservation["exit_code"] == 0
        and preservation["checker_sha256"] == digest((RUN/"record-final.py").read_bytes())
        and preservation["output_sha256"] == digest((RUN/"record-final-output.log").read_bytes())
        and preservation["preservation_report_sha256"] == digest((RUN/"preservation.json").read_bytes()),
        "Supplementary preservation receipt or source/output identity disagrees")
require(command["status"] == "passed" and command["exit_code"] == 0
        and command["all_frozen_inputs_unchanged"] is True, "Complete frozen verification has not passed")
require(result["lean_build_passed"] and result["axiom_audit_passed"]
        and not result["main_theorem_verified"]
        and result["fully_verified_numbered_assertion_count"] == 47,
        "Wrong verification or manuscript scope")
for path, expected in {**frozen, **report["evidence_sha256"]}.items():
    require(digest((ROOT/path).read_bytes()) == expected, "Checked bytes changed: "+path)
require(git("rev-parse", "HEAD").decode().strip() == BASELINE, "Worktree advanced after pinned baseline")
git("diff", "--check")
git("add", "--all")
identity = git("show", "-s", "--format=%an%x00%ae", BASELINE).decode().strip().split("\0")
new_count = result["verified_declaration_count"] - 12738
message = (
    "Verify weighted matching palettes and asymmetric Hall choice\n\n"
    f"{source['module_count']} new modules contain {source['public_theorem_count']} public theorem proofs. "
    f"The strict complete build and unchanged axiom audit passed for {result['verified_declaration_count']} "
    f"declarations, adding {new_count} while preserving all 12,738 prior names, modules and axiom sets. "
    "All 1,938 prior completed-result mappings and 69 assertion records are retained.\n\n"
    "Construct actual matching groupings with protected seed unions and whole-class blocked-star "
    "weights at most h/8, deriving weighted budgets from actual multiplicities and incidences. "
    "Prove an asymmetric finite Hall criterion including its equality boundary.\n\n"
    "The baseline authorized checkpoints were published and both public branches independently "
    "read back at c28cec4 before this continuation. Coverage remains 47/69; exact actual star "
    "assembly, native wrappers, full Corollary 4.6 and the main theorem remain unproved."
)
git("-c", "user.name="+identity[0], "-c", "user.email="+identity[1], "commit", "-m", message)
commit = git("rev-parse", "HEAD").decode().strip()
tree = git("rev-parse", "HEAD^{tree}").decode().strip()
branch = git("branch", "--show-current").decode().strip()
require(not git("status", "--porcelain").strip(), "Committed worktree is not clean")
for path, expected in frozen.items():
    require(digest(git("show", commit+":"+path)) == expected, "Committed frozen bytes differ: "+path)
RELEASE.mkdir(exist_ok=True)
bundle = RELEASE/"overfull-weighted-20261123.bundle"
archive = RELEASE/"overfull-weighted-20261123.zip"
require(not bundle.exists() and not archive.exists(), "Release paths already exist")
git("bundle", "create", str(bundle), "HEAD", "refs/heads/"+branch)
check = subprocess.run(["git","bundle","verify",str(bundle)],cwd=ROOT,text=True,
                       stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(RELEASE/"bundle-verification.log").write_text(check.stdout)
require(check.returncode == 0, "Bundle verification failed")
git("archive","--format=zip","--output="+str(archive),commit)
entries = {}
for item in git("ls-tree","-rz",commit).split(b"\0"):
    if not item: continue
    meta, path = item.split(b"\t",1)
    mode, kind, sha = meta.decode().split()
    require(kind=="blob", "Unexpected nonblob entry")
    entries[path.decode()] = sha
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None, "ZIP CRC check failed")
    actual = {name for name in z.namelist() if not name.endswith("/")}
    require(actual == set(entries), "ZIP file inventory differs from commit")
    for name, expected in entries.items():
        data=z.read(name)
        blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        require(blob==expected, "ZIP bytes differ: "+name)
report_copy = RELEASE/"overfull-weighted-verification-report-20261123.md"
shutil.copyfile(RUN/"final-report.md",report_copy)
manifest = {
    "created_at_utc":datetime.now(timezone.utc).isoformat(),
    "commit":commit,"tree":tree,"branch":branch,"baseline_public_commit":BASELINE,
    "tracked_file_count":len(entries),"strict_build_jobs":report["strict_build_jobs"],
    "verified_declaration_count":result["verified_declaration_count"],
    "preceding_declarations_preserved":12738,"new_verified_declarations":new_count,
    "new_modules":source["module_count"],"new_public_theorem_proofs":source["public_theorem_count"],
    "numbered_assertions_complete":47,"numbered_assertions_total":69,"main_theorem_verified":False,
    "baseline_publication_status":"published_on_both_requested_branches_and_read_back",
    "new_continuation_publication_status":"local_verified_checkpoint",
    "bundle_verification_exit_code":check.returncode,
    "zip_crc_and_all_committed_blob_bytes_verified":True,
    "files":[{"path":str(p),"bytes":p.stat().st_size,"sha256":digest(p.read_bytes())}
             for p in [bundle,archive,report_copy]],
}
(RELEASE/"checkpoint-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps(manifest,indent=2))
