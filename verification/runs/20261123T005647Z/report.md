# Attempt report: 20261123T005647Z

Base: `51c17b4936cf450fa86aa40e646328c8f01771f8` (the newest synchronized heads fetched on this run). Working branch: `continuation-attempt/20261123T005647Z`.

## New formal source, not yet compiled

`Overfull/CompatibleCircuits/FourVertexDeletion.lean` defines three theorem attempts with original definitions and no new axioms/admissions:

1. `Overfull.Multigraph.IsCircuit.cutOn_card_zero_two_four_of_card_le_four`: any circuit on at most four labels crosses a cut in 0, 2 or 4 actual edge copies.
2. `Overfull.Multigraph.admissibleOn_sdiff_iff_critical_cuts_of_card_le_four`: the critical slack-0/slack-2 deletion inequalities are **equivalent** to preservation of admissibility (generalizes the previous sufficient-only Fin 4 interface).
3. `Overfull.Multigraph.admissibleOn_sdiff_iff_four_label_witnesses`: for a compatible circuit, an exact witness version forbids four crossings on a tight cut, requires a class witness for two crossings of a tight cut, and requires a class witness for four crossings at slack two.

These are attempts, not statements with audited proof terms. The original four-label selector, original-host two-core Corollary 4.6, and main theorem remain open. The numbered inventory remains 47/69 according to the last verified checkpoint, not this attempt.

## Actual checks and diagnostics

- Direct `git ls-remote https://github.com/fly31415926/overfull-lean.git`: **failed** with `Could not resolve host: github.com`.
- `command -v lean; command -v lake` and search for local Lean binaries: no binary found. The previous workspace checkout was not mounted. Therefore targeted Lean checking and `python3 scripts/verify.py` were **not executed**. No new verification/results.json was generated.
- `python3 four_cut_arithmetic.py`: **passed 202 admissible integer tuples**, checking exact local inequality versus the proposed witness conditions. This verifies only a finite numerical implication, not Lean parsing, proof checking, or existence of a selector.
- Static search of the proposed Lean file found no `sorry`, `admit`, or `axiom` declarations. This is not a semantic audit.

## Next obligations

Run pinned Lean 4.24.0 and mathlib f897ebcf72cd16f89ab4577d0c826cd14afaafc7 with this attempt; fix any compiler errors, regenerate complete source and declaration maps, perform the unchanged strict build and stock axiom audit, then update verified heads only after all passed logs have been produced for the exact tree. Extend the safe-selector proof to four labels or show how original two-core joining avoids the fourth label. Do not count the generic four-label witness theorem as full Corollary 4.6.
