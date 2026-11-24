# Exceptional palette constructions: proof map

The exact source manifest is `exceptional-palette-source.json`. It lists
every new module, its SHA256, and its explicit public theorem proofs.
The complete audit additionally enumerates private and generated Lean
proof declarations in `verification/exceptional-palette-declarations.json`.
The latest complete verification and preservation report is under
`verification/runs/20261123T221916Z/`.

This stage proves supporting constructions for the two-core branch of
Corollary 4.6. **Coverage remains 47/69, with 22 incomplete assertions.**
The main theorem is not verified.

## Prescribed empty colors

`EvenJoiningDecomposition.exists_palette_avoiding_colors` constructs a
complete all-even joining palette that leaves a prescribed finite set of
labels empty. It uses the complement palette and derives matching,
disjointness, exact edge-copy coverage, parity, class size and vertex load.

`AssignedParts.exists_assigned_even_joiningPalette_avoiding_colors_in_host`
applies this construction to the actual assignment of an original
representative in a possibly different residual host. Its even uncovered
orders refer to assigned fibers.

The two `exists_small_...avoiding_colors...` wrappers choose the natural
capacity explicitly and give the requested whole-class support bound
`εn` under the protected palette budget. The same construction applies to
any prescribed set of labels, so reserve labels can be chosen first.

## Exceptional-pair free palettes and actual coloring

`JoiningPalette.pair_freeColors_eq` derives equality of the two free
palettes from whole-class parity of the actual two-vertex fiber.
`JoiningPalette.pair_freeColors_card` derives equality between the number
of free colors and the number of actual parallel copies from degree `h`
and exact joining coverage. Neither identity is an assumed input.

The pair-coloring and extension modules extend an injective prescription
on selected actual pair copies to all remaining pair copies. They retain
the prescribed copy identities and colors and prove matching,
pairwise disjointness, exact union, full coverage of both exceptional
vertices, unchanged assigned cuts, and the one-edge/two-vertex increment
for each palette class. The original-assignment interface identifies the
pair fiber before applying this construction.

## Protected full boundaries

The reserve-copy transport proves that the selected original boundaries
survive in the actual residual edge type with their original support and
matching properties. The insertion theorem replaces protected joining
classes by these full boundaries when their joining portions agree.

The principal exact identities are `reserveClasses_joining`,
`reserveClasses_cut_eq`, `reserveClasses_cover`, and
`reserveClasses_added_copies`. They ensure that insertion neither loses a
joining copy nor silently adds an unrelated copy. Matching and
disjointness are proved separately, as are whole-class size bounds.
Native wrappers establish the boundary indices, survival and joining
portions from the actual reserve.

## Limits of the conclusion

The semantic review in `exceptional-palette-semantic-review.md` distinguishes
the completed pair and protected-color constructions from the remaining
exceptional-to-core coloring. Final robust completions, factorization,
and reconstruction are still required. The original 69 assertion records
and their statement hashes remain unchanged; only the top-level coverage
summary is updated to describe the current supporting stage accurately.

## Reproduction

Use the pinned Lean 4.24.0 and the recorded mathlib commit. Do not run
`lake update`. After preparing the pinned Vizing source:

```sh
python3 scripts/update_exceptional_palette_manifest.py
python3 verification/runs/20261123T221916Z/run-verifier.py full-NN
python3 verification/runs/20261123T221916Z/record-final.py
```

Choose a fresh `full-NN` attempt directory. The supplementary checker
does not replace the full build or axiom audit. The actual current pass
status, counts, hashes, preserved inputs and failed diagnostics are
reported in the run directory, rather than predeclared here.
