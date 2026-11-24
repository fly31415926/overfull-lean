#!/usr/bin/env python3
"""Prepare reviewable integration documentation without changing live inputs.

Default: write drafts under this run's docs-draft directory, using the actual
current source inventory. --archive-development additionally records every
genuine focused-attempt file, after acquiring the same build lock. Neither
mode changes Overfull.lean, scripts, or live docs, or invokes Lean/the verifier.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "d2e7b1274d280ef6567cb2b562ec6e94eec2dda0"
TREE = "9850008a20bfd828d8ab9da4c5e8d1bf50240570"
SOURCE_DIRS = ("NativeWeighted", "NativeAssembly", "NativeCore")
CONTRIBUTIONS = {
    "NativeWeighted.WeightedJoining": "Weighted even/odd joining grouping with actual primary seeds, protected colors and original-palette thresholds.",
    "NativeWeighted.EvenNative": "Native even reserve indices and protected empty joining seeds.",
    "NativeWeighted.OddNative": "Native odd crossing primaries, injective selected reserve indices and genuine small seed weights.",
    "NativeWeighted.NativePalette": "Both parity cases produce an actual weighted joining palette and exactly prescribed half-reserve extension.",
    "NativeWeighted.CoreBounds": "Derive integer degree/multiplicity bounds, weighted resources and quotient capacity from the actual two residual cores.",
    "NativeAssembly.BaseClasses": "Insert prescribed full reserve classes and the internal exceptional bundle while retaining exact available-color classes.",
    "NativeAssembly.NativeBundles": "Native internal bundle and boundary separation; actual star pool incidence facts.",
    "NativeAssembly.NativeTwoStars": "Construct the same-label two-exception completion with exact cuts, protected prescriptions and two-copy/four-vertex growth.",
    "NativeAssembly.OtherCases": "Construct the single-exception star completion from actual remaining pools and available colors.",
    "NativeAssembly.SeparateStars": "Construct distinct-label two-exception completion; the mutual copies are already joining copies.",
    "NativeAssembly.ZeroCase": "Construct the zero-exception completion on the actual prescribed reserve extension.",
    "NativeAssembly.Paired": "Construct the paired exceptional configuration with preserved native reserve classes.",
    "NativeAssembly.Unpaired": "Exhaustively assemble zero, one and both two-exception unpaired cases without assuming the final family.",
    "NativeCore.WeightedBudget": "Prove the uniform numerical margin, quotient capacity, support bounds and explicit star-load arithmetic.",
    "NativeCore.Incidence": "Obtain actual parallel-copy and whole-family load bounds from the complement of each embedded near-regular core.",
    "NativeCore.Coverage": "Use regularity and saturation of all exceptions to prove exact coverage of every external copy.",
    "NativeCore.Parity": "Transfer assigned-cut parity and exceptional saturation to even uncovered subsets of the original two cores.",
    "NativeCore.ExternalPalette": "Build the complete native external palette with exact half-reserve classes, parity, small support and actual global core loads.",
    "NativeCore.Completion": "Construct a uniformly bounded two-core perfect-matching prefix while retaining the exact residual cores.",
    "NativeCore.PrefixSelection": "Index every nonprotected color, identify the exact protected external remainder, and prove half-reserve rounding room.",
    "NativeCore.NativePrefix": "Choose host-independent positive parameters and construct every nonprotected perfect matching, leaving an exactly half-reserve-regular robust residual.",
    "NativeCore.IndependentExterior": "Construct complementary colorings and uniform one-core factorizations when exterior vertices are independent, without a no-overfull hypothesis.",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n")


def source_manifest() -> dict:
    spec = importlib.util.spec_from_file_location("integration_preservation_checker", RUN / "record-final.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    modules = []
    for path in sorted(p for name in SOURCE_DIRS for p in (ROOT / "Overfull" / name).glob("*.lean")):
        declarations = checker.source_public_proofs(path)
        modules.append({"module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
                        "path": path.relative_to(ROOT).as_posix(), "sha256": digest(path.read_bytes()),
                        "public_theorem_count": len(declarations), "public_proof_declarations": declarations})
    names = sorted(d["name"] for module in modules for d in module["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate public theorem in the actual new sources")
    updater = ast.parse((ROOT / "scripts/update_native_integration_manifest.py").read_text())
    scopes = [ast.literal_eval(value) for node in ast.walk(updater) if isinstance(node, ast.Dict)
              for key, value in zip(node.keys, node.values)
              if isinstance(key, ast.Constant) and key.value == "scope"]
    if len(scopes) != 1 or not isinstance(scopes[0], str):
        raise SystemExit("Manifest updater does not have one exact literal scope")
    return {"schema_version": 1, "kind": "supporting_continuation", "baseline_commit": BASELINE,
            "baseline_tree": TREE,
            "baseline_publication_status": "verified_local_publication_blocked_by_automatic_review_at_input_freeze",
            "numbered_assertions_completed": 0, "main_theorem_verified": False, "scope": scopes[0],
            "review": "docs/native-integration-semantic-review.md",
            "proof_map": "docs/native-integration-verification.md",
            "module_count": len(modules), "public_theorem_count": len(names), "modules": modules,
            "required_proof_declarations": names}


def archive_development() -> dict:
    with (RUN / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        files = [{"path": p.relative_to(ROOT).as_posix(), "recorded_at_path": str(p),
                  "sha256": digest(p.read_bytes()), "bytes": p.stat().st_size}
                 for p in sorted((RUN / "development").rglob("*")) if p.is_file()]
        record = {"kind": "genuine_development_evidence",
                  "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
                  "file_count": len(files), "files": files}
        write_json(RUN / "development-archive.json", record)
        return record


def prepare() -> dict:
    manifest = source_manifest()
    draft = RUN / "docs-draft"
    draft.mkdir(exist_ok=True)
    write_json(draft / "native-integration-source.json", manifest)
    imports = ["import " + item["module"] + "\n" for item in manifest["modules"]]
    write_json(draft / "candidate-root-added-imports.json", imports)
    scope = manifest["scope"] + " The unchanged assertion records retain 47 of 69 complete numbered assertions."
    write_json(draft / "coverage-scope.json", {"scope": scope})
    rows = "\n".join(
        f"| `{item['module'].removeprefix('Overfull.')}` | {item['public_theorem_count']} | "
        f"{CONTRIBUTIONS.get(item['module'].removeprefix('Overfull.'), 'New supporting module; inspect its exact public declarations below.')} |"
        for item in manifest["modules"])
    inventory = "\n\n".join(
        f"### `{item['module']}`\n\nSource: `{item['path']}`. SHA-256: `{item['sha256']}`.\n\n" +
        "\n".join(f"- `{proof['name']}` (source line {proof['source_line']})."
                  for proof in item["public_proof_declarations"])
        for item in manifest["modules"])
    verification = f"""# Native integration: exact proof map and verification scope

This supporting continuation adds {manifest['module_count']} source modules and
{manifest['public_theorem_count']} explicitly named public theorem/lemma proofs.
The exact manifest is `docs/native-integration-source.json`. Its source hashes,
names and lines describe the candidate source; they do not certify a full run.

The full unchanged `Audit.lean` enumerates every proof declaration actually
imported, including private and generated support proofs. Its successful run
produces `verification/native-integration-declarations.json`, which ties every
audited new declaration to the source path and hash. The current run's genuine
command receipt, full raw logs and `preservation.json` determine whether full
verification and preservation have completed. No count of audited declarations
is inferred from this lexical source map or from a focused compiler pass.

## Baseline and scope

The baseline is `{BASELINE}`, tree `{TREE}`: 2,752 committed files, 12,951 audited
declarations, 2,063 completed-result mappings and 670 frozen source/input hashes.
Every prior nonroot mathematical source, declaration name/owner/axiom set, old
declaration map, all 69 numbered-assertion records and their statement hashes
must be preserved. Root imports are only appended after the complete old prefix;
the verifier admits exactly the four reviewed additive integration edits.

{manifest['scope']}

**No numbered assertion is completed by this continuation. Coverage remains
47 of 69. Full two-core Corollary 4.6 and the main theorem remain unproved.**

## Source modules

| Module | Public proofs | Contribution |
| --- | ---: | --- |
{rows}

## Complete explicit public inventory

{inventory}

## Required full verification

The actual full command is `python3 scripts/verify.py`, running the unchanged
strict `lake build --wfail` and complete `lake env lean Audit.lean` gates under
Lean 4.24.0 and pinned mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed logical axioms.
All genuine failed focused attempts remain archived with their original source
snapshots, command metadata and logs. Each full attempt has a separate immutable
directory, complete frozen input snapshots, exact output copies and raw audit
byte segments. The supplementary preservation checker cannot replace the build
or audit and reports success only after every checked consistency gate passes.
"""
    (draft / "native-integration-verification.md").write_text(verification)
    review = f"""# Native integration: semantic review

## Scope and construction direction

{manifest['scope']}

The native external-palette theorem begins with the actual residual regular
multigraph, its two embedded old cores, an original perfect matching and native
reserve packing. It constructs the weighted joining palette, selected reserve
indices and colors, actual exceptional bundle/star copies and the final external
classes. The final external family is an existential conclusion. No assumption
that this final family, a full factorization or the main theorem already exists
is introduced. The original perfect matching and reserve packing remain explicit
native input hypotheses; this continuation does not construct them from nothing.

## Weighted native inputs

Both parity branches use the original palette size `h`. The odd branch retains
genuine injective count-one primary seeds; their small actual-copy star weights
are proved from old-core multiplicity bounds. The even branch uses protected
empty joining seeds. Exactly `r/2` reserve indices and color labels are selected
injectively. Their actual joining traces are preserved when full native reserve
boundaries are inserted.

The native integer error is `D = floor(max(a, h-r))`. Its joining-degree and
exceptional-to-old-core multiplicity bounds come from actual residual degree and
the two core deficits. The mutual exceptional bundle is handled by the native
combined joining-plus-bundle budget, without imposing an old-core multiplicity
bound on that exceptional-to-exception bundle. Weights control the union of both
original cores, so either assigned core inherits the same bound.

## Exceptional cases and exact coverage

The paired case and every unpaired cardinality-zero/one/two case have actual
constructors. The two-exception unpaired cases distinguish equal and distinct
assignment labels. They preserve original joining classes, all selected full
reserve classes, exact assigned cuts, matching and pairwise copy disjointness.
Each completed color saturates every exceptional vertex. Regularity then proves
that all exceptional incident copies occur in the palette. Together with joining
coverage and the external-copy inclusion, this yields exact equality of the
palette union with the joining and exceptional copy sets.

Hall row budgets are restricted to available colors, whose actual base classes
have the required equality with the bounded joining classes. Protected reserve
classes are outside that row budget. For the same-label case, bundle-used colors
receive no star; the verified per-class growth is at most two copies and four
support vertices. This is the reason the bound is `max(3L, |Z|+1)+2` copies and
`2 max(3L, |Z|+1)+4` vertices. With `|Z|≤2` and `L>0`, these reduce to `3L+2`
and `6L+4` respectively.

## Uniform quantitative budget

From `h≥αn/30`, `D≤δn`, `δ≤α/3840` and `2s≤h`, the exact integer gap satisfies
`128D≤h`, `h-s-32D>0`, `h/4≤h-s-32D` and `αn/120≤h-s-32D`.
The natural-number choice `L=(nD/2)/(h-s-32D)+1` gives positive capacity and
`nD≤2L(h-s-32D)`. Its support estimate is
`6L+4≤(360δ/α)n+10≤εn` under `δ≤εα/720` and `n≥20/ε`.
The quantified parameter theorem chooses a positive `δ` below an arbitrary
previous positive threshold and a host-order threshold before the host data.
The native external palette instantiates this budget with `s=r/2`.

The separate arithmetic `D+2b≤3δn` is not used as an unjustified global load
bound after protected insertion. Every final external class is disjoint from
each actual old-core edge set. Their pairwise disjointness and the degree deficit
therefore prove the stronger actual whole-family core load `≤a`, including all
protected classes. The same core-complement count proves actual parallel-copy
bounds used by the weighted construction.

## Core parity and bounded completion

Exceptional saturation identifies the uncovered assigned parts with uncovered
subsets of the original cores. Exact assigned cuts then transfer the joining
parity certificate, giving even uncovered subsets in both cores for every color.
The bounded-boundary completion theorem uses genuinely small support and the
actual global core load to construct a prefix of disjoint perfect matchings in
the two robust cores. It retains the exact residual core embeddings and their
proved invariants. Its length bounds and robustness hypotheses remain explicit.

The prefix-selection module indexes every color outside the protected image and
proves the exact selected/protected union partition. Under `r≥αn/30` and
`n≥120/α`, half-reserve rounding gives `(α/120)m≤r/2` for `m≤n`, hence the prefix
room required by the robust completion theorem.

`exists_uniform_native_unprotected_prefix` composes the actual native external
palette, complete nonprotected selection and robust two-core completion. Given
the displayed positive density, linear core-size and expansion parameters, it
chooses positive `δ, θ` and `n₀` before any host types, graph, cores or reserve
data. For every qualifying host it constructs all `h-r/2` nonprotected perfect
matchings, pairwise copy-disjoint and avoiding the selected protected union.
The remaining graph is exactly `r/2`-regular; its two embedded cores remain
robust `(θ,σ)` expanders with minimum degree at least `r/2-a`. The surviving
external copies are exactly the selected original reserve copies, both as a
difference in the pre-deletion copy type and as an equality/image in the actual
surviving copy type. This is a constructed partial factorization with a precise
residual; no terminal coloring is assumed or concluded.

## Independent-exterior ingredient and terminal gap

The separate independent-exterior theorem derives a complementary `k`-coloring
from actual regularity, independent exterior vertices and complementary core
degree at most `a` with `2a<k`. The existing one-core factorization theorem then
gives uniform colorings and exact perfect-matching partitions for a fixed bound
on the number of independent exterior vertices, allowing either original-core
parity. It needs neither an input complementary coloring nor a no-overfull
hypothesis. It does not construct the two terminal shore models, contractions
or palette alignment needed to apply it to the newly produced two-core residual.
The exact next route and its remaining obligations are recorded separately in
`verification/runs/{RUN.name}/independent-review/final-protected-route.md`.

## Verification boundary

The exact public source inventory is `docs/native-integration-source.json`; the
full proof map is generated only by the unchanged complete audit. Focused
compilation establishes each recorded attempt's own result. Only the final
frozen verifier and strict preservation report establish the whole continuation.
The checker preserves all 12,951 prior declaration names, owners and axiom sets,
all 2,063 old result mappings and all 69 numbered assertion records. **Coverage
stays 47/69. Final native factorization, full two-core Corollary 4.6 and the main
theorem remain unproved.**
"""
    (draft / "native-integration-semantic-review.md").write_text(review)
    latest = f"""## Latest continuation: native weighted assembly and bounded core completion

The native construction now supplies weighted odd/even joining palettes with
exact half-reserve prescriptions, constructs every paired/unpaired exceptional
case, and covers precisely all joining and exceptional edge copies. It derives
old-core parity, small support and actual whole-family core loads from the
embedded near-regular cores. The constants and natural quotient capacity are
proved uniformly from the native numerical hypotheses. Supporting robust core
completion and nonprotected-color selection now produce all `h-r/2` nonprotected
perfect matchings under constants fixed before the host. The remaining graph is
exactly `r/2`-regular, retains two robust cores, and has exactly the selected
reserve copies as its external edges. An independent-exterior one-core theorem
supplies a further ingredient for the terminal problem.

{manifest['scope']}

**Coverage remains 47/69. Full two-core Corollary 4.6 and the main theorem are
unproved.** The [source inventory](docs/native-integration-source.json),
[public proof map](docs/native-integration-verification.md),
[semantic review](docs/native-integration-semantic-review.md) and
[current-run evidence](verification/runs/{RUN.name}/) record the exact scope.
The final frozen verifier and preservation reports determine the actual full
verification state. Focused checks and source inventories alone do not certify
the full project.

"""
    (draft / "readme-latest-section.md").write_text(latest)
    handoff = f"""# Continuation handoff: native integration and bounded completion

## Exact baseline and evidence

The verified local predecessor is `{BASELINE}`, exact tree `{TREE}`, containing
2,752 committed files. Its unchanged full audit enumerated 12,951 declarations;
the result has 2,063 completed-result mappings and 670 frozen source/input hashes.
This run is `{RUN.name}` in `{ROOT}`. The actual full command, immutable attempt
logs, raw audit segments, all input snapshots and supplementary preservation
report determine the new verification state. New audited counts must be read
from those genuine results, never inferred from a focused pass or module count.

The last observed public heads are recorded in `run.json`. Publication of the
preceding local chain was blocked by the retained automatic review rejection.
Standing user instructions authorize complete verified sources, private/generated
declaration names, hashes and genuine diagnostics, but no publication workaround
may evade that rejection. Actual later public commit/tree/branch readbacks belong
in separate publication receipts. No branch promotion follows merely from a
local verified checkpoint or an unreferenced object upload.

## New formal constructions

{manifest['scope']}

See `docs/native-integration-source.json` and the source-linked semantic review
for the exact dynamic module inventory and theorem names. The construction now
produces the native weighted joining palette and half-reserve prescriptions;
all paired and zero/one/two unpaired exceptional completions; exact external copy
coverage; old-core parity; uniform support estimates; actual full-family load
from core deficits; and the selected/protected color and external-remainder
partition. The universal native prefix theorem chooses `δ, θ, n₀` before the
host and constructs all `h-r/2` nonprotected perfect matchings. It retains an
exactly `r/2`-regular residual with robust embedded cores and exact equality of
all surviving external copies with the selected native reserve union. The
independent-exterior module constructs a complementary coloring and one-core
factorization without a supplied complementary coloring or no-overfull condition.
These conclusions follow from their displayed hypotheses. No terminal two-core
coloring or full factorization is supplied as an assumed target.

## Remaining integration and terminal theorem

Construct the terminal shore restrictions or contractions, prove their
independent-exterior and robust-core hypotheses, align shared crossing-copy
labels, and lift/combine the resulting actual matchings. Terminal recoloring
need not preserve the selected reserve boundaries as whole color classes; the
proved prefix preserves their copy union. The independent-exterior theorem supplies a one-core factorization
ingredient, but it does not supply those two-core modeling and alignment steps.
The proposed next route is recorded in
`verification/runs/{RUN.name}/independent-review/final-protected-route.md`;
the independent prefix review records its exact source and focused status.
Keep the selected native reserve union in the actual surviving edge-copy type.
Then prove the terminal residual factorization and combine it with the already
constructed prefix. Check exact theorem signatures before claiming the full
manuscript conclusion.

The full two-core Corollary 4.6, remaining five-exception/final-factorization
obligations and the main theorem remain unproved. All 69 original assertion
records and statement hashes remain unchanged; **47 are complete and 22 are
incomplete**. Only the top-level coverage scope prose may change here.

## Numerical interface and key semantic constraints

Use the actual `D=floor(max(a,h-r))` and `s=r/2`. From `h≥αn/30`, `D≤δn`,
`δ≤α/3840`, `δ≤εα/720` and `n≥20/ε`, the new theorems prove `128D≤h`, positive
gap `h-s-32D≥h/4`, capacity `L=(nD/2)/(h-s-32D)+1` and support `6L+4≤εn`.
The available-color Hall budget remains restricted to its actual palette.
Whole-family load, including protected colors, is separately bounded by the
actual core deficit `a`; do not infer a generic global `D` bound from abstract
reserve-extension data. The half-reserve prefix room uses the explicit rounding
condition `n≥120/α` and reserve density `r≥αn/30`.

## Verification and restart

Preserve the unchanged `Audit.lean`, every prior nonroot source, all previous
declaration names/owners/axioms, all old mappings and all historical evidence.
Use only the four reviewed additive verifier edits recorded in
`verifier-additions.json`. Root imports must be appended after the complete old
prefix. Regenerate the live source manifest only after the candidate is stable;
the draft manifest is an inventory, not a verification result.

Run focused commands only through this run's `record-command.py`, retaining
failed attempts faithfully. Use Lean 4.24.0 at
`/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`
and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The full command is
`python3 -u verification/runs/{RUN.name}/supervise-verifier.py full-01`.
It stays attached to one observed child process and streams actual heartbeats
every 30 seconds. Await its actual exit; do not infer process completion from
a different tool namespace or stale session handle. Before launching, finish
live docs/root/manifest and archive all focused evidence. Do not edit frozen
inputs while the full verifier runs. After success, run the strict supplementary
checker with a genuine command/output receipt, then the local-only packaging
script. Publication is a distinct authorized action subject to the retained
automatic-review decision and exact remote readback.
"""
    (draft / "continuation-handoff.md").write_text(handoff)
    generated = {p.name: digest(p.read_bytes()) for p in sorted(draft.iterdir()) if p.is_file()}
    record = {"prepared_at_utc": datetime.now(timezone.utc).isoformat(),
              "kind": "reviewable_drafts_not_live_inputs_or_verification", "live_inputs_modified": False,
              "module_count": manifest["module_count"], "public_theorem_count": manifest["public_theorem_count"],
              "source_sha256": {item["path"]: item["sha256"] for item in manifest["modules"]},
              "draft_sha256": generated}
    write_json(RUN / "docs-draft-manifest.json", record)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-development", action="store_true")
    args = parser.parse_args()
    record = prepare()
    if args.archive_development:
        record["development_file_count"] = archive_development()["file_count"]
    print(json.dumps({key: record[key] for key in ["kind", "live_inputs_modified", "module_count",
                                                 "public_theorem_count"]}, indent=2))
    if args.archive_development:
        print("Archived genuine development files:", record["development_file_count"])


if __name__ == "__main__":
    main()
