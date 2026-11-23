# Unverified continuation attempt: four-label deletion witnesses (20261123T005647Z)

**Latest attempted branch:** `continuation-attempt/20261123T005647Z` based on `51c17b4936cf450fa86aa40e646328c8f01771f8`. The two verified branches must remain at their last checked checkpoint. A Lean 4.24.0 runtime and pinned mathlib checkout were not available in this execution container, and direct Git transport could not resolve github.com. The new source in `Overfull/CompatibleCircuits/FourVertexDeletion.lean` is **not Lean-checked**. A finite Python arithmetic test of 202 local tuples passed; this is not a kernel proof or a complete assertion. No changes to the 47/69 numbered inventory or source-statement hashes are claimed.

**Concrete next step:** recover this attempt branch in a Lean-capable environment, run `lake env lean Overfull/CompatibleCircuits/FourVertexDeletion.lean` and `python3 scripts/verify.py`, repair any elaboration errors, regenerate source/declaration maps and exact logs, then advance both verified branches only if all gates pass. Continue the original two-core 4.6 joining construction separately; the new lemmas supply a necessary and sufficient safe-deletion test but **do not** construct a selector. A new four-cycle crossing a tight cut four times can never be safe under compatibility; at slack two, a four-crossing circuit must meet that class. No manuscript excerpt from a private workspace is included.

---

# Continuation handoff: complete three-vertex compatible circuits

## Authoritative state

Resume from the newest remote `main` and
`verified-bipartite-continuation-2026-11-21` in `fly31415926/overfull-lean`.
Verified publications keep these branches at the same commit. This run's
base was `b5afb03a0f0613eedd0cb3310e06706942afe2e7`; its previously missing
three-label selector is now proved. This is not the original `cb05ef5` tree.

Run identifier: `20261122T235931Z` (UTC start). Read
`verification/results.json` and `verification/runs/20261122T235931Z/`
for fresh verification and preservation evidence. The earlier
`verification/reconstruction-checkpoint.json` remains historical evidence
for the reconstructed base, not this continuation's run record.

## Completed proof and exact interfaces

The original even-degree and half-cut conditions suffice for an exact
compatible circuit partition on any finite vertex type of cardinality
at most three, with arbitrary edge-copy type `E` and class type `K`.

Main entry points in `Overfull/CompatibleCircuits/AtMostThree.lean`:

```lean
G.exists_safe_circuit_of_card_le_three
  hV classOf C hC hadmissible heven
G.exists_compatibleCircuitPartition_of_card_le_three
  hV classOf C hadmissible heven
G.compatibleCircuitPartition_iff_admissible_of_card_le_three
  hV classOf C heven
```

The selector returns `D ⊆ C`, an original-class compatible circuit,
admissibility of `C \ D`, and `D.card = 2 ∨ D.card = 3`. The partition
retains exactly the original copies, with pairwise disjoint parts and
exact union. No selector, partition, finite class type, or `Inhabited K`
assumption is supplied. Empty selected copy sets and isolated vertices
are included. See `docs/three-label-circuit-verification.md`, its semantic
review, and `docs/three-label-circuit-source.json` for the full proof map.

## Next concrete obligation

Continue the distinct **two-core branch of Corollary 4.6** from the
original statement and actual joining-copy construction. Inspect
`docs/few-exception-source.json`, `Overfull/FewExceptions/`,
`Overfull/CompatibleCircuits/Lifting.lean`, and the terminal/fixed-pattern
interfaces. Identify the exact quotient vertices, endpoint classes,
degree parity and every half-cut bound required by the new theorem.
Derive those hypotheses from the original host. Lift the circuit parts
back to compatible joining pieces and compose the proved core factorizations.

If an essential fourth quotient label remains, record the precise
obstruction and address the four-label selector or a valid source-level
alternative. `Deletion.lean` gives the four-label critical-cut correction:
both slack-zero and slack-two cuts matter. The new three-label proof
only treats circuits crossing any cut at most twice; do not assume that
bound on four labels.

Full fixed-pattern 4.4/4.5, remaining 4.16 parity branches, general
Section 6 setup/absorber, critical average-degree input and main theorem
also remain open. The numbered count remains **47/69**. No numbered
statement or statement hash was changed by the new supporting theorem.

## Preserve these proof details

- Compatibility alone does not make a circuit safely deletable.
- Local coarsening needs `identity_or_tight`, as well as refinement,
  half bounds and tight-class witnesses, for a bundle of exactly half
  the incident copies.
- Parallel copies remain separate elements of `E`; endpoint-pair images
  must not identify distinct parts or original copies.
- Injective padding uses `Option K` at isolated labels and assumes no
  default original class.
- `FourLabel.lean` already owns the generic `isCircuit_parallel_pair`.
  Reuse it; an initially duplicated specialized helper was removed.
- The earlier Python selector experiment remains separate evidence.

## Reproduction and publication

Use `leanprover/lean4:v4.24.0` and the committed dependency manifest,
including mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Do not use `lake update` to reproduce this checkpoint.

```sh
python3 scripts/setup_vizing.py
python3 scripts/verify.py
```

The verifier runs the strict build and unchanged full `Audit.lean`, checks
all mapped theorem names/modules, and records exact source/input hashes.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. If a
reviewed new source changes, regenerate its mapping with
`python3 scripts/update_three_label_manifest.py`, then verify again.
Refreshing a mapping is not proof verification.

The previous temporary checkout was
`/workspace/scratch/4ffd54dab476/overfull-lean-rebuild`, with pinned Lean
under `/workspace/scratch/4ffd54dab476/lean-runtime/lean-4.24.0-linux/bin`.
These are optional conveniences. Recover the complete project from
GitHub if the environment is replaced.

The user authorizes continued work and publication after every run.
Fetch current heads, preserve concurrent work, verify the exact candidate,
update both verified branches without destructive force pushes, and read
both heads back. Save unfinished attempts and genuine diagnostics on a
dated `continuation-attempt/` branch. Maintain timestamped run records and
this handoff, publishing a recovery checkpoint before context/runtime
limits. Use a supported fresh-chat operation when available; do not claim
to create a conversation when that control is absent. Resume from this
handoff without needing the previous chat.
