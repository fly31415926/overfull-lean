# Continuation handoff: weighted palettes and actual star-copy bounds

## Published baseline and current local continuation

Publication of the preceding complete checkpoints is finished. Both `main`
and `verified-bipartite-continuation-2026-11-21` in
`fly31415926/overfull-lean` were independently read back at public commit
`c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2`. Its tree is exactly the tree
of local checkpoint `89678bcf148d5dadb10c954b6a306f39fc941317`.

| Stage | Original local checkpoint | Public commit | Exact tree |
|---|---|---|---|
| Native reserve | `b7be9966640e932ef7bbd030d3dae42f7bcb4638` | `347b6afe3b37dca8b5b8d9667db41b061b66677b` | `7b7c84d18ee0f7826e87829de5d175fd6eea7ff6` |
| Residual palette | `1b5663a8fb472e42e698f4e09fcfc55497393815` | `8c974c8a5ca3f7b2fcf557bee596e264480b4b81` | `ab2dd45502da57ea7dfb1db046a9efc9ab0cf067` |
| Exceptional palette | `89678bcf148d5dadb10c954b6a306f39fc941317` | `c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2` | `6a9e73eee4e944b104ff98630b04655e8bfb959d` |

The public residual-palette commit is the parent of the public
exceptional-palette commit. Publication recreated commit metadata while
preserving these complete source/evidence trees byte-for-byte. All source
files, documentation, complete mappings, private/generated declaration
names, paths, hashes, and genuine retained logs were included. The earlier
publication blocker is resolved; historical rejected-attempt records remain
unchanged. The current run's `baseline-remote-readback-final.json` records
the independently observed baseline.

The **new weighted continuation is local work from public `c28cec4`** in
run `20261123T230808Z`; this handoff does not claim it has been published.
Fetch and inspect both public branch heads before any later update, and
preserve concurrent remote changes. Publication status and local proof
verification status are recorded separately.

## Current proved ingredients

Five modules under `Overfull/WeightedPalette/` contain 41 public theorem
proofs and four definitions. Exact public names and source SHA-256 hashes
are in `docs/weighted-palette-source.json`. The proof map is
`docs/weighted-palette-verification.md`; the read-only semantic review is
`docs/weighted-palette-semantic-review.md`.

`Overfull.NativeReserve.exists_weighted_palette_extension` extends a
prescribed proper finite coloring while bounding both the number of pieces
and every whole-color resource weight. Resource totals include **all seed
pieces**. Seeds retain their labels; only surplus pieces must avoid the
protected set `Q`.

Actual star weights count original copies from `z` to its old-core set `U`
whose **old-core endpoint** is occupied by a joining piece. They retain
parallel multiplicities. A three-copy piece has weight at most `6b`, and
the family total is at most `D*h` under the stated actual incidence and
degree caps. The union lemma bounds the blocked copies of an entire grouped
class by the sum of its piece weights.

`Overfull.WeightedPalette.exists_star_weighted_matching_grouping` combines
these constructions. Its hypotheses include actual matching pieces of size
at most three, pairwise edge-disjointness inside a set of degree at most
`D`, at most two star resources, multiplicity at most `b`, exceptional degree
at most `h`, explicit seed properness/count/weight certificates, `0<h`,
`b<=D`, `128D<=h`, `2*|Q|<=h`, and capacity
`|I|<=L*(h-|Q|-32D)`. Its output preserves:

- prescribed seed labels and exact seed unions in protected colors;
- proper grouping, actual matching classes, and pairwise edge-disjointness;
- the exact union of the original pieces;
- whole-class blocked-star-copy weight at most `h/8` for each resource;
- at most `3L` copies and `6L` support vertices per class, with vertex color
  load at most `D`.

The grouping theorem does not assert that the piece union already equals
all joining copies, construct cut parity, or supply native reserve alignment.
Those inputs must be established by the decomposition wrapper.

`Overfull.CircuitPatterns.exists_equiv_of_asymmetric_conflicts` proves
finite Hall choice for balanced sides of order `m`, with row conflict bound
`a`, column conflict bound `b`, and `a+b<=m`, including equality and empty
sides. Its star specialization still requires the exact actual finite-side
balance and both conflict bounds as inputs.

The earlier native reserve selection/completion, residual no-overfull safety,
retained robustness, residual joining decompositions, unweighted joining
palettes, exceptional-pair coloring, prescribed empty colors, and protected
reserve-boundary insertion are already proved. Preserve and reuse them.

## Next mathematical obligations

1. **Derive actual copy partitions and the combined incidence bound.** For
   an unpaired exception `z`, let `j_z` be its joining degree and `t` the
   number of mutual copies when the two exceptions have the same assigned
   core. Use the surviving reserved assigned-core incidences to prove
   `j_z+t<=h-r`. Two independent bounds by `D` do not replace this combined
   estimate. Keep every actual parallel copy distinct.
2. **Handle the shared internal exceptional bundle first.** If both
   exceptions have the same assigned core, color their mutual copies
   injectively outside the protected colors and both joining-used palettes.
   If they have different assigned cores, their mutual copies are already
   joining copies. Derive the required common-free-color count from the
   combined incidence estimate.
3. **Preserve reserve prescriptions and exclude all protected colors.**
   Insert the exact prescribed surviving boundaries, remove those selected
   star copies from the remaining pools, and forbid every protected label
   in the remaining star colorings. Maintain the original joining palette
   and added copies separately; an augmented reserve class family is not
   automatically a joining-only `JoiningPalette`.
4. **Prove exact remaining-star/free-palette balance.** Derive from
   regularity and disjoint copy/color accounting
   `|A_z|=|F_z|=h-s-j_z-t>=h-s-D`, where `s` is the number of protected
   colors. This equality is still unproved for the actual unpaired stars.
5. **Construct the stars sequentially using actual Hall relations.** The
   first star sees row obstruction at most `D` and column obstruction at
   most `h/8`. After inserting it, the second sees bounds `D+b` and
   `h/8+b`. Prove these on the actual current copies and colors, then apply
   the available asymmetric Hall theorem. Independently chosen star
   colorings do not establish their mutual endpoint compatibility.
6. **Supply native weighted wrappers and parity.** Instantiate the seed
   certificates from the odd/even joining decompositions and protected
   primary pieces. Retain exact joining coverage, cut parity, and original
   reserve alignment. Combine exceptional saturation with assigned-fiber
   parity to derive even uncovered order in each original core. Account
   for the additional at-most-two copies/four support vertices per color.
7. **Complete and reconstruct the factorization.** Establish every
   hypothesis of the existing robust core completion interfaces, construct
   the remaining perfect color classes, and restore the removed perfect
   matchings using disjoint palettes. A theorem assuming the missing
   residual coloring does not finish this construction.

**Coverage remains 47/69.** Full Corollary 4.6, the full five-exception
Corollary 4.5, remaining four-label circuit/terminal/Section 6 and structural
inputs, and the main theorem remain unproved. These supporting modules
complete no new numbered assertion. The 69 assertion records and their
statement hashes must remain unchanged.

## Verification and provenance

All five focused `lake build --wfail` target checks passed, with exact source
snapshots, genuine logs and unchanged recorded inputs. The complete frozen
verifier is the next gate at this documentation freeze. Its actual
`full-*/command.json`, `frozen-candidate-inputs.json`, output logs,
`verification/results.json`, complete declaration maps, and final
preservation report determine global status. Do not infer a new global
declaration total from the 41-public-proof source inventory or from a
focused target build.

Use Lean 4.24.0 and pinned mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; do not run `lake update`.
Current worktree:
`/workspace/scratch/0f64d20031b0/overfull-weighted-verified`.
The retained wrappers set the runtime path to
`/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin`.

```sh
python3 scripts/update_weighted_palette_manifest.py
python3 verification/runs/20261123T230808Z/run-verifier.py full-NN
python3 verification/runs/20261123T230808Z/record-final.py
```

Choose a fresh full-attempt name. Freeze source, configuration, manifests,
documentation and verifier inputs before the complete run, and do not edit
them during it. `Audit.lean` remains unchanged; permitted axioms remain
`propext`, `Classical.choice`, and `Quot.sound`. Preserve every prior
declaration name/module/axiom set, completed-result mapping, nonroot source,
and historical verification artifact. Append root imports after the full
old import prefix before the first non-import command.

The initial focused recorder looked for `lakefile.lean` and omitted the
repository's actual `lakefile.toml` from its input hashes. This provenance
limitation is recorded in `recorder-correction.json`. The recorder was
corrected to include `lakefile.toml` and its own source hash for future
attempts. **No prior genuine receipt was rewritten.** The complete frozen
runner includes `lakefile.toml`, the toolchain and package manifest, so the
full run covers the actual configuration. Preserve the original failed
`loads-001` attempt and every other genuine development record.

Any later publication must preserve the exact checked tree and complete
evidence, use expected-head branch updates, and read back both public heads
and the resulting tree. This handoff records successful baseline publication
and new local work; it does not predict a remote Actions result or a later
publication outcome.


## Isolated recovery of an unavailable verification execution

The first full attempt began at `2026-11-23T23:16:15.229419+00:00` in
`/workspace/scratch/0f64d20031b0/overfull-weighted-star`. Its execution session
became unavailable, while its original receipt still recorded `running`
and a null exit code. Its completion result and process state are unknown;
no termination, success, failure, or exit code is inferred.

The active continuation is now the separate worktree named above. It has
an independent project build cache and shares only the pinned dependency
packages. Every frozen Lean source, `Audit.lean`, and `scripts/verify.py`
was copied unchanged. The earlier checkout remains untouched so an
unobserved execution there cannot race with the new verification outputs.

Original attempt bytes, its own frozen inputs and snapshots, observed aliases,
and completed build/version/source stage logs are retained under
`verification/runs/20261123T230808Z/unrecovered-execution/full-01/`.
`recovery-observation.json` records the actual capture and unknown result.
The old axiom log is not claimed as a current completed audit. The next
active attempt is `full-02`; only a successful active attempt in this new
worktree with unchanged frozen inputs can satisfy final verification.
