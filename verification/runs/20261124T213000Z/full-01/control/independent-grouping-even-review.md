# Independent review: four-piece grouping and four even cores

Reviewer: `/root/rebuild_two_odd`, independently of the author of these eight modules.

## Conclusion and scope

**No mathematical or statement-scope gap was identified in the eight reviewed modules.** The generic grouping proof supplies the advertised conflict and size bounds from actual edge-copy incidence. The all-even terminal construction removes every joining copy, constructs colorings of the closed residual robust cores, and restores a one-factorization on the original edge-copy type. Its positive tolerance and order threshold are selected before the host graph and core data.

This was a read-only semantic review of the eight source files below and the relevant existing completion, closed-core, and reassembly interfaces. No Lean sources were edited and no additional tests or compiler commands were run for this review. The compiler evidence cited below is the genuine existing development receipt, rather than a claim about a new full-project audit or publication.

## Generic grouping and exact joining copies

In `Overfull/ResidualPalette/FourPaletteGrouping.lean`, `pieceConflict_card_le_of_size` bounds the conflict degree by `2*s*D`. A piece of at most `s` copies has support of size at most `2*s`. Pairwise copy-disjointness and containment in the actual incidence-bounded set `S` bound the number of pieces using each support vertex by `D`. The support-overlap count therefore bounds the actual conflict relation. This argument does not replace edge copies with an unproved quotient or assume that disjoint edge sets have disjoint supports.

`exists_bounded_matching_grouping_of_size` applies the existing bounded palette extension to that conflict relation. Prescribed primary colors remain fixed, and their injectivity gives initial load at most one. Properness prevents support overlap within a grouped class. The result explicitly includes matching classes, pairwise copy-disjointness, and equality of the complete grouped union with the original piece union. The cardinality and support estimates are `s*L` and `2*s*L`; at `s = 4` these become `4*L` and `8*L`, with conflict allowance `8*D`. The conversion from the incidence budget to the number of indices uses nonempty pieces and the established inequality `2*#pieces ≤ #vertices*D`.

In `Overfull/ResidualPalette/FourJoiningGrouping.lean`, the indices are the actual members of `FourJoiningDecomposition.parts`. Its matching, nonempty, size, disjointness, and exact-cover fields discharge the generic hypotheses. Thus the resulting grouped union equals the entire original `joiningCopies` set. The even fiber-cut property is summed over disjoint actual pieces. The result uses the existing `JoiningPalette` interface at capacity `2*L`: the stronger new bounds `4*L` copies and `8*L` support imply that interface's `6*L` and `12*L` bounds. This relaxation loses numerical sharpness, but no copies or required property.

In `Overfull/Terminal/FourPalette.lean`, `exists_four_even_prefix_palette` sets `remaining := ∅`, with boundary classes covering all joining copies. The same file's two-odd constructor selects exactly `r` primary pieces and groups them together with all surplus pieces. Its primary seed extension gives exactly one selected primary in each boundary class; surplus pieces contribute even cuts. The remaining family is exactly the unselected primary pieces, has cardinality `h-r`, and is copy-disjoint from every boundary class. The union statement still accounts for every original joining copy. No residual coloring is an input to either constructor.

## Numerical room and completed prefix

`Overfull/TerminalFourEven/Parameters.lean` applies the existing three-copy parameter lemma with error argument `2*a` and packing tolerance `εp/2`, then returns half its input tolerance. The floor inequality `2*⌊a⌋₊ ≤ ⌊2*a⌋₊` makes the old conflict margin `6*⌊2*a⌋₊` dominate `8*⌊a⌋₊`. The old incidence budget consequently implies the required budget with denominator margin `r-8*⌊a⌋₊`. With `L = prefixCapacity α (εp/2) n`, the old footprint `6*L ≤ (εp/2)*m` implies the actual completion footprint `6*(2*L) ≤ εp*m`. The use of capacity `2*L` is therefore fully funded. Order, horizon, density, and final-error bounds remain available, and the numerical quantifiers put the chosen constants before `n`, `m`, `h`, and `a`.

`Overfull/TerminalFourEven/Prefix.lean` first selects the epoch parameters and output robustness. Only afterward does it accept the requested final error and minimum core order, choose the input tolerance/order threshold, and accept the host. The joining degree bound is derived from the original host's regular degree minus the embedded core degree and rounded down to `⌊a⌋₊`. The all-even joining decomposition is constructed from the original regular, no-overfull host and its even fibers. It is not supplied as an additional hypothesis.

The prefix completion receives the actual grouped boundary matchings and all required footprint, parity, horizon, density, and robustness bounds. Existing `completed_joining_copies` proves that completion adds only internal core edges and removes precisely the prescribed joining copies. `remaining_joining_copies`, together with the empty remaining family, proves the exact `joining_removed` field in `FourEvenPrefix`. The final core-size error bound uses `h-r ≤ h ≤ n` for the simple regular host and `α*n ≤ |U_i|`; the residual-density and minimum-core-order conclusions match the completion interface.

## Closed residual cores, restoration, and endpoint

`Overfull/TerminalFourEven/Completed.lean` transports the exact original-copy removal statement to the actual simple residual. It derives empty residual joining copies and hence an empty cut for each labeled core. The existing `completionCore`, `completionCore_robust`, `completionCore_degree`, and `completionResidual_regular` interfaces supply embedded robust cores and regular residual degree `h-rounds`; `rounds ≤ h` justifies the natural-number subtraction in the degree bound.

`exists_uniform_closed_core_factorization` is then applied to these closed, disjoint, covering, even cores. It constructs their component colorings from the robust-core hypotheses and glues them on the actual residual edge type. No component coloring, residual coloring, or final factorization is assumed. `completion_restores_coloring` transports through the existing residual-edge equivalence and restores the deleted matching prefix on `G.edgeSet`.

The public theorem `Overfull.four_even_terminal_one_factorization` in `Overfull/TerminalFourEven/Theorem.lean` normalizes the density parameter to `β = min α 1` and composes the uniform prefix and residual theorems in the required order. The hypothesis `τ ≤ min α 1 / 64` provides both the prefix and residual parameter ranges. The positive `ε` and positive `n₀` precede the host type, graph, four core sets, core graphs, labels, regular degree, and error. Host assumptions are the intended four even covering robust cores in a dense regular simple graph with no overfull set and small core degree error. The conclusion is an actual family `Fin h → Finset G.edgeSet` of pairwise disjoint perfect matchings with union `univ`. The local `DecidableEq` transport is an equality of instances, not a mathematical assumption or weakening.

## Existing compiler evidence

The genuine attempt [four-even-full-04/command.json](development/four-even-full-04/command.json), duplicated by its [terminal receipt](development/four-even-full-04/terminal.json), records:

- Command: `lake build --wfail Overfull.TerminalFourEven.Theorem`.
- Working directory: `/workspace/scratch/05b9e46fe96b/overfull-lean`.
- Start: `2026-11-24T21:45:55.939949+00:00`; finish: `2026-11-24T21:46:03.343251+00:00`.
- Command exit code `0`, wrapper exit code `0`, status `passed`, and `inputs_changed_during_command: []`.
- The [unaltered output log](development/four-even-full-04/output.log) ends with `Build completed successfully (3530 jobs).` This is an incremental target build; the job total is not a count of freshly compiled modules in that attempt.
- Receipt SHA256, for both `command.json` and `terminal.json`: `20491d03121b198d94e104a76e9de09338e22724b35ce055eb82390a101ccb1e`.
- Output log SHA256: `30b14c9613b86e1160f377860803e349e61ec0bb0fc073cdd90b6b9e69f87975`.

## Exact reviewed source hashes

For every row, the current source SHA256 equals both the corresponding `source_sha256` entry in that receipt and the SHA256 of its captured `source/` snapshot. All eight equalities were checked during this review.

| Source file | SHA256 |
| --- | --- |
| `Overfull/ResidualPalette/FourPaletteGrouping.lean` | `8a410245769c8fea660bf87e1210bfd114878dfd85adeae0e58e3d12e1da929e` |
| `Overfull/ResidualPalette/FourJoiningGrouping.lean` | `4e6be75d810b4617a3691c8fa85de6ac2a4316534639a79745961d9b7dd52639` |
| `Overfull/Terminal/FourPalette.lean` | `61805afa55070ce8c2643c61a7fee6244a348e75947c43d82180998bd8c95c34` |
| `Overfull/TerminalFourEven/Parameters.lean` | `76437a79287169f035e3278e193fa6e7ad04bd3091af5be387d43f509ff9566f` |
| `Overfull/TerminalFourEven/PrefixResult.lean` | `7a133d7a4799edfc4a378b3c63a546f30c38c9fcfb5ac987dad50cf359ed0e5b` |
| `Overfull/TerminalFourEven/Prefix.lean` | `cf69618156521d9358b4aa26035e76b9ccc5b5808be4f546b25fe6ea176bf88b` |
| `Overfull/TerminalFourEven/Completed.lean` | `921ef9fa3a1ad745ed1eb4ae914cbef233f03aea3ffa09c8cd47b577369c8ebb` |
| `Overfull/TerminalFourEven/Theorem.lean` | `e86c981eb3708917c011c71aa5ccbf4bafba24267f3fd3b8be8dd4d86bb31254` |
