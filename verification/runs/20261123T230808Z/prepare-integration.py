"""Prepare additive weighted-continuation verification infrastructure.

This does not run Lean, claim verification, or change earlier proof sources.
"""
from pathlib import Path
import json
import pprint
import re

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASE = "c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2"
TREE = "6a9e73eee4e944b104ff98630b04655e8bfb959d"
OLD = ROOT / "verification/runs/20261123T221916Z"
SCOPE = ("Weighted palette extension preserving prescribed seeds and protected colors, "
         "resource-load and actual blocked-star-copy estimates, and finite Hall choice "
         "with asymmetric conflict bounds. These supporting constructions do not establish "
         "the exact remaining-star copy/free-color balance, complete actual exceptional-star "
         "assembly, native weighted wrappers, final robust factorization, full Corollary 4.6 "
         "or the main theorem.")
EDITS = [
    {"old": '                          ("exceptional_palette", "exceptional-palette-source.json")):\n',
     "new": '                          ("exceptional_palette", "exceptional-palette-source.json"),\n'
            '                          ("weighted_palette", "weighted-palette-source.json")):\n'},
    {"old": '    # Every first-party mathematical file must be included in the library build.\n',
     "new": '    if extension_maps["weighted_palette"][0]["numbered_assertions_completed"] != 0:\n'
            '        raise SystemExit("The weighted-palette continuation completes no numbered manuscript assertion.")\n\n'
            '    # Every first-party mathematical file must be included in the library build.\n'},
    {"old": '                    "exceptional_palette": "exceptional-palette"}[key]\n',
     "new": '                    "exceptional_palette": "exceptional-palette",\n'
            '                    "weighted_palette": "weighted-palette"}[key]\n'},
    {"old": '        "exceptional_palette_declaration_map": extension_evidence["exceptional_palette"],\n',
     "new": '        "exceptional_palette_declaration_map": extension_evidence["exceptional_palette"],\n'
            '        "weighted_palette_declaration_map": extension_evidence["weighted_palette"],\n'},
]
def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Expected one exact replacement: {old[:120]!r}")
    return text.replace(old, new, 1)

verifier = (ROOT / "scripts/verify.py").read_text()
for edit in EDITS:
    verifier = replace_once(verifier, edit["old"], edit["new"])
(ROOT / "scripts/verify.py").write_text(verifier)
(RUN / "verifier-additions.json").write_text(json.dumps(EDITS, indent=2) + "\n")

manifest = (ROOT / "scripts/update_exceptional_palette_manifest.py").read_text()
manifest = manifest.replace("ExceptionalPalette", "WeightedPalette")
manifest = manifest.replace("exceptional_palette", "weighted_palette").replace("exceptional-palette", "weighted-palette")
manifest = manifest.replace("1b5663a8fb472e42e698f4e09fcfc55497393815", BASE)
manifest = manifest.replace("ab2dd45502da57ea7dfb1db046a9efc9ab0cf067", TREE)
manifest = manifest.replace("blocked_by_automatic_approval_review", "published")
manifest = re.sub(r"^        'scope': .*,\n", "        'scope': " + repr(SCOPE) + ",\n", manifest, flags=re.M)
(ROOT / "scripts/update_weighted_palette_manifest.py").write_text(manifest)

runner = (OLD / "run-verifier.py").read_text().replace("Overfull/ExceptionalPalette", "Overfull/WeightedPalette")
(RUN / "run-verifier.py").write_text(runner)

checker = (OLD / "record-final.py").read_text()
checker = checker.replace("20261123T221916Z", RUN.name)
checker = checker.replace("1b5663a8fb472e42e698f4e09fcfc55497393815", BASE)
checker = checker.replace("ab2dd45502da57ea7dfb1db046a9efc9ab0cf067", TREE)
checker = checker.replace("BASELINE_FILE_COUNT = 2196", "BASELINE_FILE_COUNT = 2355")
checker = checker.replace("BASELINE_DECLARATION_COUNT = 12559", "BASELINE_DECLARATION_COUNT = 12738")
checker = checker.replace("BASELINE_COMPLETED_MAPPING_COUNT = 1859", "BASELINE_COMPLETED_MAPPING_COUNT = 1938")
checker = checker.replace("ExceptionalPalette", "WeightedPalette")
checker = checker.replace("exceptional_palette", "weighted_palette").replace("exceptional-palette", "weighted-palette")
checker = checker.replace("Exceptional palette", "Weighted palette").replace("Exceptional-palette", "Weighted-palette")
a = checker.index("VERIFIER_EDITS = [")
b = checker.index("\n\n\ndef require", a)
checker = checker[:a] + "VERIFIER_EDITS = " + pprint.pformat(EDITS, width=110, sort_dicts=False) + checker[b:]
checker = checker.replace('source["baseline_publication_status"] == "blocked_by_automatic_approval_review"',
                          'source["baseline_publication_status"] == "published"')
checker = checker.replace('"residual_palette_declaration_map" in previous and "weighted_palette_declaration_map" not in previous',
                          '"exceptional_palette_declaration_map" in previous and "weighted_palette_declaration_map" not in previous')
checker = checker.replace("preceding residual-palette verified result", "preceding exceptional-palette verified result")
checker = replace_once(checker,
    '            snapshot = path.parent / Path(source).name\n',
    '            local(source)\n'
    '            nested = path.parent / "source" / source\n'
    '            snapshot = nested if nested.is_file() else path.parent / Path(source).name\n')
checker = checker.replace('len(data.get("dependency_source_sha256", {}))',
                          'len(data.get("input_sha256", data.get("dependency_source_sha256", {})))')
checker = checker.replace('"byte_identical_genuine_development_evidence"', '"genuine_development_evidence"')
checker = checker.replace('item["copied_from"]', 'item["recorded_at_path"]')
checker = replace_once(checker,
    '                        "status": "pending_verified_branch_updates_after_automatic_approval_rejection",\n'
    '                        "note": "This local verification report records no successful public publication or branch promotion."',
    '                        "baseline_status": "published_and_independently_read_back",\n'
    '                        "baseline_public_commit": BASELINE,\n'
    '                        "status": "local_continuation_after_published_baseline",\n'
    '                        "note": "Both public branches were verified at the baseline; this report does not claim the new continuation was published."')
checker = replace_once(checker,
    'The actual preceding verified local commit is `{BASELINE}`, with tree\n'
    '`{BASELINE_TREE}` and {len(baseline_paths):,} files. Its publication was blocked\n'
    'by automatic approval review. This report makes no claim that either it or\n'
    'the present continuation has reached the public verified branches.',
    'The preceding verified public commit is `{BASELINE}`, with tree\n'
    '`{BASELINE_TREE}` and {len(baseline_paths):,} files. Both public branches were\n'
    'independently read back at this commit before this continuation began.\n'
    'It exactly reproduces local checkpoint `89678bc`; its parent exactly\n'
    'reproduces `1b5663a`. This report concerns the new local continuation.')
checker = replace_once(checker,
    'Public verified-branch updates are pending after automatic approval review\n'
    'rejected publication. This report records local verification only. Preserve\n'
    'the exact checked sources and genuine evidence for the authorized publication;\n'
    'record actual remote commit/tree and branch readback after it succeeds.',
    'The authorized preceding checkpoints have been published, and both branch\n'
    'heads, exact trees and complete file inventories were independently read back.\n'
    'The retained baseline receipts record that successful publication. The new\n'
    'weighted continuation is verified locally by this run; this report does not\n'
    'claim a later public branch promotion.')
(RUN / "record-final.py").write_text(checker)
(RUN / "run.json").write_text(json.dumps({
    "run_id": RUN.name, "started_at_utc": "2026-11-23T23:08:08+00:00",
    "baseline_local_verified_commit": BASE, "baseline_local_verified_tree": TREE,
    "baseline_public_verified_commit": BASE, "baseline_publication_status": "published_and_independently_read_back",
    "baseline_corresponding_local_checkpoint": "89678bcf148d5dadb10c954b6a306f39fc941317",
    "baseline_verified_declaration_count": 12738, "baseline_completed_result_mapping_count": 1938,
    "numbered_assertions_completed_in_this_run": 0,
    "scope": SCOPE,
}, indent=2) + "\n")
print("Prepared four additive verifier edits, a new source mapper, frozen-input runner and preservation checker.")
