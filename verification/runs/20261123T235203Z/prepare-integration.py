"""Prepare additive native-star verification against the verified local baseline.

This records no verification claim. All old source and declaration maps stay
unchanged; the full stock audit must subsequently run on frozen inputs.
"""
from pathlib import Path
from datetime import datetime, timezone
import json
import pprint
import re
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
OLD = ROOT / "verification/runs/20261123T230808Z"
BASE = sys.argv[1]
TREE = "5ddefa9b77dfaf2d1cf09df1d7e2d4b541346a85"
LOCAL = "af8dca22ef67d66d0de3f6d89954d31f06a4d2fa"
if BASE != LOCAL:
    raise SystemExit("This run pins the verified local af8 checkpoint; publication is recorded separately")
SCOPE = (
    "Actual reserved-copy injection into unpaired assigned stars, a disjoint "
    "joining/star/internal-exception incidence partition, native combined degree "
    "bounds, common internal-bundle coloring, exact remaining star copy/color "
    "balance, and endpoint-conflict Hall choice with sequential star accounting. "
    "These supporting results do not yet assemble the complete native weighted "
    "odd/even palette, all protected prescriptions and parity conditions into "
    "the full two-core Corollary 4.6, final robust factorization, or main theorem."
)
EDITS = [
    {"old": '                          ("weighted_palette", "weighted-palette-source.json")):\n',
     "new": '                          ("weighted_palette", "weighted-palette-source.json"),\n'
            '                          ("native_star", "native-star-source.json")):\n'},
    {"old": '    # Every first-party mathematical file must be included in the library build.\n',
     "new": '    if extension_maps["native_star"][0]["numbered_assertions_completed"] != 0:\n'
            '        raise SystemExit("The native-star continuation completes no numbered manuscript assertion.")\n\n'
            '    # Every first-party mathematical file must be included in the library build.\n'},
    {"old": '                    "weighted_palette": "weighted-palette"}[key]\n',
     "new": '                    "weighted_palette": "weighted-palette",\n'
            '                    "native_star": "native-star"}[key]\n'},
    {"old": '        "weighted_palette_declaration_map": extension_evidence["weighted_palette"],\n',
     "new": '        "weighted_palette_declaration_map": extension_evidence["weighted_palette"],\n'
            '        "native_star_declaration_map": extension_evidence["native_star"],\n'},
]


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Expected one exact replacement: {old[:120]!r}")
    return text.replace(old, new, 1)


actual_tree = subprocess.check_output(["git", "rev-parse", BASE + "^{tree}"], cwd=ROOT).decode().strip()
if actual_tree != TREE:
    raise SystemExit("Published baseline does not reproduce the verified weighted tree")

verifier = (ROOT / "scripts/verify.py").read_text()
for edit in EDITS:
    verifier = replace_once(verifier, edit["old"], edit["new"])
(ROOT / "scripts/verify.py").write_text(verifier)
(RUN / "verifier-additions.json").write_text(json.dumps(EDITS, indent=2) + "\n")

manifest = (ROOT / "scripts/update_weighted_palette_manifest.py").read_text()
manifest = manifest.replace("WeightedPalette", "NativeStar")
manifest = manifest.replace("weighted_palette", "native_star").replace("weighted-palette", "native-star")
manifest = manifest.replace("c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2", BASE)
manifest = manifest.replace("6a9e73eee4e944b104ff98630b04655e8bfb959d", TREE)
manifest = re.sub(r"^        'scope': .*,\n", "        'scope': " + repr(SCOPE) + ",\n", manifest, flags=re.M)
(ROOT / "scripts/update_native_star_manifest.py").write_text(manifest)

runner = (OLD / "run-verifier.py").read_text().replace("Overfull/WeightedPalette", "Overfull/NativeStar")
(RUN / "run-verifier.py").write_text(runner)

checker = (OLD / "record-final.py").read_text()
checker = checker.replace("20261123T230808Z", RUN.name)
checker = checker.replace("c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2", BASE)
checker = checker.replace("6a9e73eee4e944b104ff98630b04655e8bfb959d", TREE)
checker = checker.replace("BASELINE_FILE_COUNT = 2355", "BASELINE_FILE_COUNT = 2507")
checker = checker.replace("BASELINE_DECLARATION_COUNT = 12738", "BASELINE_DECLARATION_COUNT = 12811")
checker = checker.replace("BASELINE_COMPLETED_MAPPING_COUNT = 1938", "BASELINE_COMPLETED_MAPPING_COUNT = 1979")
checker = checker.replace("WeightedPalette", "NativeStar")
checker = checker.replace("weighted_palette", "native_star").replace("weighted-palette", "native-star")
checker = checker.replace("Weighted palette", "Native star").replace("Weighted-palette", "Native-star")
checker = checker.replace("weighted continuation", "native star continuation")
checker = checker.replace('"exceptional_palette_declaration_map" in previous',
                          '"weighted_palette_declaration_map" in previous')
checker = checker.replace("preceding exceptional-palette verified result", "preceding weighted-palette verified result")
a = checker.index("VERIFIER_EDITS = [")
b = checker.index("\n\n\ndef require", a)
checker = checker[:a] + "VERIFIER_EDITS = " + pprint.pformat(EDITS, width=110, sort_dicts=False) + checker[b:]
checker = replace_once(checker,
    'It exactly reproduces local checkpoint `89678bc`; its parent exactly\n'
    'reproduces `1b5663a`. This report concerns the new local continuation.',
    'It exactly reproduces verified local checkpoint `af8dca2`. Its parent\n'
    'preserves the already published `89678bc` and `1b5663a` trees. This report\n'
    'concerns the new local native-star continuation.')
checker = checker.replace('"general_exceptional_to_core_incidence_and_final_robust_factorization_unproved"',
                          '"native_weighted_wrapper_and_full_exceptional_assembly_and_robust_factorization_unproved"')
(RUN / "record-final.py").write_text(checker)

package = (OLD / "package-verified.py").read_text()
package = package.replace("c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2", BASE)
package = package.replace("weighted-release", "native-star-release")
package = package.replace("weighted-palette", "native-star")
package = package.replace("overfull-weighted-", "overfull-native-star-")
package = package.replace("12738", "12811").replace("12,738", "12,811")
package = package.replace("1,938", "1,979")
a = package.index("message = (")
b = package.index('\ngit("-c",', a)
message = '''message = (
    "Verify native reserve-star balance and actual endpoint Hall choice\\n\\n"
    f"{source['module_count']} new modules contain {source['public_theorem_count']} public theorem proofs. "
    f"The strict complete build and unchanged axiom audit passed for {result['verified_declaration_count']} "
    f"declarations, adding {new_count} while preserving all 12,811 prior names, modules and axiom sets. "
    "All 1,979 prior completed-result mappings and 69 assertion records are retained.\\n\\n"
    "Construct distinct actual residual reserve-star copies, the native incidence partition and "
    "combined degree bound; prove common bundle colors, exact remaining star balance, and actual "
    "endpoint Hall choice with sequential star accounting.\\n\\n"
    "The weighted checkpoint af8dca2 was published with its exact checked tree before this run. "
    "Coverage remains 47/69; complete native weighted assembly, full Corollary 4.6, robust "
    "factorization and the main theorem remain unproved."
)'''
package = package[:a] + message + package[b:]
(RUN / "package-verified.py").write_text(package)

(RUN / "run.json").write_text(json.dumps({
    "run_id": RUN.name, "started_at_utc": "2026-11-23T23:52:03+00:00",
    "baseline_local_verified_commit": BASE, "baseline_local_verified_tree": TREE,
    "baseline_public_verified_commit": BASE,
    "baseline_publication_status": "published_and_independently_read_back",
    "baseline_corresponding_local_checkpoint": LOCAL,
    "baseline_verified_declaration_count": 12811, "baseline_completed_result_mapping_count": 1979,
    "numbered_assertions_completed_in_this_run": 0,
    "scope": SCOPE,
}, indent=2) + "\n")
# At input freeze, the previous checkpoint's publication was still blocked by automatic approval review.
# Correct the former published-baseline template without changing mathematical
# inputs, the four verifier substitutions, or any preservation requirement.
PENDING = "verified_local_publication_blocked_by_automatic_review_at_input_freeze"
LAST_PUBLIC = "c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2"
mapper_path = ROOT / "scripts/update_native_star_manifest.py"
mapper = replace_once(mapper_path.read_text(),
    "'baseline_publication_status': 'published'",
    "'baseline_publication_status': '" + PENDING + "'")
mapper_path.write_text(mapper)

checker_path = RUN / "record-final.py"
checker = checker_path.read_text()
checker = replace_once(checker,
    'source["baseline_publication_status"] == "published"',
    'source["baseline_publication_status"] == "' + PENDING + '"')
checker = replace_once(checker,
    '                        "baseline_status": "published_and_independently_read_back",\n'
    '                        "baseline_public_commit": BASELINE,\n'
    '                        "status": "local_continuation_after_published_baseline",\n'
    '                        "note": "Both public branches were verified at the baseline; this report does not claim the new continuation was published."',
    '                        "baseline_status_at_input_freeze": "' + PENDING + '",\n'
    '                        "baseline_local_verified_commit": BASELINE,\n'
    '                        "baseline_public_commit": None,\n'
    '                        "last_observed_public_commit_at_input_freeze": "' + LAST_PUBLIC + '",\n'
    '                        "status": "local_continuation_after_verified_local_baseline",\n'
    '                        "note": "Publication was blocked by automatic approval review at input freeze; separate receipts establish any later public commit and branch promotion."')
checker = replace_once(checker,
    'The preceding verified public commit is `{BASELINE}`, with tree\n'
    '`{BASELINE_TREE}` and {len(baseline_paths):,} files. Both public branches were\n'
    'independently read back at this commit before this continuation began.\n'
    'It exactly reproduces verified local checkpoint `af8dca2`. Its parent\n'
    'preserves the already published `89678bc` and `1b5663a` trees. This report\n'
    'concerns the new local native-star continuation.',
    'The preceding verified local commit is `{BASELINE}`, with tree\n'
    '`{BASELINE_TREE}` and {len(baseline_paths):,} files. It is the exact checked\n'
    'weighted checkpoint `af8dca2`. Its public parent `c28cec4` preserves the\n'
    'already published `89678bc` and `1b5663a` trees. Publication of `af8dca2`\n'
    'was blocked by automatic approval review at this run\'s input freeze; later publication receipts\n'
    'are separate from this local verification and preservation report.')
checker = replace_once(checker,
    'The authorized preceding checkpoints have been published, and both branch\n'
    'heads, exact trees and complete file inventories were independently read back.\n'
    'The retained baseline receipts record that successful publication. The new\n'
    'native star continuation is verified locally by this run; this report does not\n'
    'claim a later public branch promotion.',
    'The previously published checkpoints `89678bc` and `1b5663a` remain in the\n'
    'public history. At this run\'s input freeze, the verified local weighted\n'
    'checkpoint `af8dca2` was blocked by automatic approval review; the last observed public\n'
    'head was `c28cec4`. This report establishes local verification only. Exact\n'
    'public commits, trees and later branch promotions require their own receipts.')
checker_path.write_text(checker)

package_path = RUN / "package-verified.py"
package = package_path.read_text()
package = replace_once(package,
    '"The weighted checkpoint af8dca2 was published with its exact checked tree before this run. "',
    '"The verified local weighted checkpoint af8dca2 is the exact frozen baseline. Publication is recorded separately. "')
package = replace_once(package,
    '"commit":commit,"tree":tree,"branch":branch,"baseline_public_commit":BASELINE,',
    '"commit":commit,"tree":tree,"branch":branch,"baseline_local_verified_commit":BASELINE,\n'
    '    "baseline_public_commit_at_input_freeze":None,\n'
    '    "last_observed_public_commit_at_input_freeze":"' + LAST_PUBLIC + '",')
package = replace_once(package,
    '"baseline_publication_status":"published_on_both_requested_branches_and_read_back",',
    '"baseline_publication_status_at_input_freeze":"' + PENDING + '",')
package_path.write_text(package)

run_path = RUN / "run.json"
run_record = json.loads(run_path.read_text())
run_record.update({
    "baseline_public_verified_commit": None,
    "baseline_publication_status": PENDING,
    "last_observed_public_verified_commit_at_input_freeze": LAST_PUBLIC,
    "publication_note": "The verified local baseline and its exact tree are pinned. Public reconstruction is blocked by automatic approval review at freeze and will be documented by separate readback receipts.",
})
run_path.write_text(json.dumps(run_record, indent=2) + "\n")
print("Prepared four additive verifier edits and exact local-baseline verification/preservation tools; public status remains separately recorded.")
