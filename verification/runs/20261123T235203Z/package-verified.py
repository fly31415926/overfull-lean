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
RELEASE = ROOT.parent / "native-star-release"
BASELINE = "af8dca22ef67d66d0de3f6d89954d31f06a4d2fa"

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
source = json.loads((ROOT/"docs/native-star-source.json").read_text())
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
new_count = result["verified_declaration_count"] - 12811
message = (
    "Verify native reserve-star balance and actual endpoint Hall choice\n\n"
    f"{source['module_count']} new modules contain {source['public_theorem_count']} public theorem proofs. "
    f"The strict complete build and unchanged axiom audit passed for {result['verified_declaration_count']} "
    f"declarations, adding {new_count} while preserving all 12,811 prior names, modules and axiom sets. "
    "All 1,979 prior completed-result mappings and 69 assertion records are retained.\n\n"
    "Construct distinct actual residual reserve-star copies, the native incidence partition and "
    "combined degree bound; prove common bundle colors, exact remaining star balance, and actual "
    "endpoint Hall choice with sequential star accounting.\n\n"
    "The verified local weighted checkpoint af8dca2 is the exact frozen baseline. Publication is recorded separately. "
    "Coverage remains 47/69; complete native weighted assembly, full Corollary 4.6, robust "
    "factorization and the main theorem remain unproved."
)
git("-c", "user.name="+identity[0], "-c", "user.email="+identity[1], "commit", "-m", message)
commit = git("rev-parse", "HEAD").decode().strip()
tree = git("rev-parse", "HEAD^{tree}").decode().strip()
branch = git("branch", "--show-current").decode().strip()
require(not git("status", "--porcelain").strip(), "Committed worktree is not clean")
for path, expected in frozen.items():
    require(digest(git("show", commit+":"+path)) == expected, "Committed frozen bytes differ: "+path)
RELEASE.mkdir(exist_ok=True)
bundle = RELEASE/"overfull-native-star-20261123.bundle"
archive = RELEASE/"overfull-native-star-20261123.zip"
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
report_copy = RELEASE/"overfull-native-star-verification-report-20261123.md"
shutil.copyfile(RUN/"final-report.md",report_copy)
manifest = {
    "created_at_utc":datetime.now(timezone.utc).isoformat(),
    "commit":commit,"tree":tree,"branch":branch,"baseline_local_verified_commit":BASELINE,
    "baseline_public_commit_at_input_freeze":None,
    "last_observed_public_commit_at_input_freeze":"c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2",
    "tracked_file_count":len(entries),"strict_build_jobs":report["strict_build_jobs"],
    "verified_declaration_count":result["verified_declaration_count"],
    "preceding_declarations_preserved":12811,"new_verified_declarations":new_count,
    "new_modules":source["module_count"],"new_public_theorem_proofs":source["public_theorem_count"],
    "numbered_assertions_complete":47,"numbered_assertions_total":69,"main_theorem_verified":False,
    "baseline_publication_status_at_input_freeze":"verified_local_publication_blocked_by_automatic_review_at_input_freeze",
    "new_continuation_publication_status":"local_verified_checkpoint",
    "bundle_verification_exit_code":check.returncode,
    "zip_crc_and_all_committed_blob_bytes_verified":True,
    "files":[{"path":str(p),"bytes":p.stat().st_size,"sha256":digest(p.read_bytes())}
             for p in [bundle,archive,report_copy]],
}
(RELEASE/"checkpoint-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps(manifest,indent=2))
