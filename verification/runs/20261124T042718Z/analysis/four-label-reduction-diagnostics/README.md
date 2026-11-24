# Exploratory four-label reduction diagnostics

These files preserve five finite obstruction checks from the read-only mathematical assessment. They are **Python diagnostics, not Lean proofs, kernel certificates, or numbered-assertion closures**. No Lean build is run by the script. They do not establish the proposed degree-two suppression or bounded-layer extraction theorems.

`diagnostics.py` uses only the Python standard library. It models distinct actual edge copies and the exact cardinality predicates `degreeOn`, `cutOn`, `classCutOn`, `AdmissibleOn`, `Compatible`, and `IsCircuit` from `Overfull/CompatibleCircuits/Basic.lean`. It explicitly checks all 16 shores. For a given vertex, classes with no incidence there have class-cut size zero and need no separate enumeration. Circuit connectivity is checked using the nonempty proper support-cut condition itself.

## Expected outcomes enforced by the script

| Example | Diagnostic |
| --- | --- |
| A | Original degrees `(8,4,4,8)` are admissible. Splitting one `01` and one `02` copy at vertex `0` gives degrees `(6,4,4,8)` and preserves every local half-degree bound, but the cut `{0,3}` changes from total/class counts `8/4` to `6/4` and fails admissibility. |
| B | Original and split graphs are admissible. A displayed compatible partition of the split graph has a part whose expansion is not a circuit and has no compatible circuit partition of its own. All 15 set partitions of that four-copy expansion are enumerated; its unique circuit partition consists of two incompatible parallel pairs. A separate compatible partition of the original graph demonstrates that only partwise lifting is refuted. |
| C | The admissible degree sequence `(6,4,4,4)` has no spanning four-regular actual-copy subgraph. All 512 actual-copy subsets are checked. A purported such layer would leave residual degrees `(2,0,0,0)`, impossible for a loopless graph. |
| D | The specified admissible four-regular graph has 10 spanning two-factors and 0 compatible spanning two-factors. All 256 actual-copy subsets are checked. Its partition into two triangles and a parallel pair is compatible. |
| E | An admissible graph with no tight nontrivial class-cut inequality loses admissibility after deletion of a compatible four-cycle. On `{0,2}`, original total/class counts are `6/2` (slack two), deleted counts are `4/0`, and residual counts are `2/2`. |

The JSON preserves every input copy and incidence class, all failed inequalities, the designated cut calculations, the relevant partitions and factor enumeration, and the expected-outcome checks.

## Retained execution

The script was run once for this evidence bundle. `stdout.json` is its exact captured standard output, and `stderr.txt` is its exact captured standard error. `run.json` records the actual command, times, exit code, interpreter, file sizes, hashes, and hashes of the referenced Lean source files. `SHA256SUMS` records the hashes of the script, this note, and the retained execution files.

To reproduce the diagnostic without overwriting the retained evidence, run from the repository root:

```sh
python -I verification/runs/20261124T042718Z/analysis/four-label-reduction-diagnostics/diagnostics.py
```

The script prints JSON to standard output and writes no files. Its assertions use an explicit checked function and remain active even if Python optimization is enabled. Review the retained exit status before treating the expected outcomes as observed.
