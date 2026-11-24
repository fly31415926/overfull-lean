# Native prefix and core bounds semantic review

Recorded: 2026-11-24T01:16:31.853091+00:00  
Reviewer task: `inspect_next_target`

## Conclusion and scope

No semantic defect was identified in the reviewed `exists_uniform_native_unprotected_prefix` and `exists_native_palette_from_core_bounds` statements or their parameter composition. The result constructs the full external palette and completes all nonprotected colors into an actual perfect-matching prefix. It establishes an exact protected external remainder and robust retained cores; terminal factorization is still a separate task.

This is an independent review of the modules authored by the root agent. `PrefixSelection.lean` was authored by this reviewer and is listed for source traceability, without claiming independent review of that source. The review is distinct from compiler verification and the final frozen full audit.

## Uniform parameters and integer rounding

The constants `δ`, `θ`, and `n₀` are quantified before all host types, graphs, residual deletion families, reserve packings, and embedded cores. The packing constants depend on `α/30`, `α/120`, `ν`, `τ`, and `σ`; the additional scaling uses only `β`. There is no host-dependent choice hidden in the uniform constants.

Writing `n = |V|`, the construction chooses `η = εβ`. Each shore satisfies `|Uᵢ| ≥ βn`, so both the whole-class support bound `ηn` and error bound `a ≤ ηn` fit the required local budget `ε|Uᵢ|`. The positive choice `δ = min η (min (α/3840) (ηα/720))` simultaneously supplies the weighted density, weighted support, and core-error conditions.

The order threshold dominates `1`, `⌈20/η⌉`, `⌈120/α⌉`, and `⌈m₀/β⌉`. These provide positive host order, the palette support budget, the half-reserve rounding margin, and sufficient order in both cores. From `αn/30 ≤ r` and `n ≥ 120/α`, the selection lemma proves `(α/120)|Uᵢ| ≤ ⌊r/2⌋`, and consequently the exact prefix length `h-r/2` fits both packing floors. Finally `r ≤ h` justifies `h-(h-r/2)=r/2` with natural-number subtraction.

The core packing density is `α/30`: `|Uᵢ| ≤ n` and `αn/30 ≤ r ≤ h` give the required degree lower bound. The explicit assumption `τ ≤ α/240` is exactly `τ ≤ (α/30)/8`.

## Native class hypotheses are derived

`CoreBounds.lean` defines `D = ⌊max a (h-r)⌋₊` from the actual residual core data. The nonnegative residual reserve deficit and the core-complement estimates derive the integer joining-degree and exceptional parallel-copy bounds. These estimates are not additional unproved class assumptions.

The weighted resources are the actual exceptional vertices `Z`, whose cardinality is at most two. Using `U₀ ∪ U₁` as each resource shore controls either assigned old core by monotonicity. The original palette remains `Fin h`; the proof does not reduce the weighted threshold to a smaller nonprotected palette. Positivity of `L` and `|Z| ≤ 2` justify `max (3L) (|Z|+1) = 3L`, giving the support bounds used by the completed external family.

## Exact copies, protected selection, and completion

The protected map `f : Fin(r/2) → Fin h` is injective. Its complement has exactly `h-r/2` colors; `unprotectedColor` enumerates that complement injectively and exhaustively. Reindexing retains actual matching classes and their copy disjointness. Exact protected prescriptions and the palette union identity separate all external copies into selected classes and the original protected reserve union.

The completion theorem supplies actual perfect matchings extending each selected class. Every added copy lies internally in `U₀` or `U₁`. Each original shore has a constant frozen assigned label and avoids `Z`, so those internal pools are disjoint from both joining and exceptional copies. Consequently removing the completed prefix deletes exactly the selected external classes, and the surviving exterior is exactly the protected reserve union.

The conclusion retains copy identities at both residual levels: it proves a set difference in the first residual edge type, equality of `survivingCopies` in the second residual edge subtype, and the exact image under `Subtype.val`. No endpoint-pair identification discards parallel copies. The prefix contains exactly `h-r/2` pairwise disjoint perfect matchings, avoids all protected reserve copies, and leaves an `r/2`-regular graph with constructed robust old-shore cores and unchanged additive error `a`.

## Final elaboration edits reviewed

The final changes from the initial source snapshot add theorem-local `maxHeartbeats 1200000`, unfold the local abbreviation `A` for protected-union membership, use a private `degree_fintype_independent` lemma proved with `Subsingleton.elim`, and transport the surviving-copy equality by finite-set extensionality. The helper equates two finite-enumeration structures on the same edge type; it changes neither the graph nor its incidence relation. The extensionality proof retains every actual protected copy. These are elaboration transports only: the public theorem statement, quantified assumptions, and mathematical construction are unchanged.

## Semantic caveats for the next step

- The theorem constructs a partial factorization. It makes no claim that the final `r/2`-regular graph is colorable or fully factorized.
- The input no-overfull condition is not asserted for the final residual after deleting the constructed prefix.
- The exterior is defined using the frozen original assignment `assignedLabel G M U₀ U₁ Z`. A later factorization must preserve that label or prove an explicit equivalence before replacing it. Recomputing an assignment from the prefix or final residual is not justified by this theorem alone.

## Observed focused verification

The recorded `nativeprefix-004` command passed with exit `0`, all **3374 jobs** successful, and no input changes during the command. The recorder reports elapsed time `7.854` seconds and completion at `2026-11-24T01:16:05.424714+00:00`.

Command: `lake build --wfail Overfull.NativeCore.NativePrefix`  
Receipt: `verification/runs/20261124T010000Z/development/nativeprefix-004/command.json`

The genuine failed development attempts `nativeprefix-001`, `nativeprefix-002`, and `nativeprefix-003` remain recorded separately. This review does not rewrite their results or claim that they passed.

All six reviewed source hashes below match the successful `nativeprefix-004` input snapshot. Root reported the Lean sources frozen after that success. This focused verification and semantic review remain distinct from the final frozen full audit; no full-audit outcome is asserted here.

## Exact reviewed source hashes

| Reviewed source | SHA-256 |
|---|---|
| `Overfull/NativeCore/NativePrefix.lean` | `43e1cff9640b75c859d435c2505b50f3f89694db200f4ddd274bbc4379469c05` |
| `Overfull/NativeWeighted/CoreBounds.lean` | `b3b17421a6ee396e72bd98830da3e5a096d04a77e429c03047a5eea58f3936bf` |
| `Overfull/NativeCore/ExternalPalette.lean` | `498761dfa9b88b05707f2d7b9a22babb7649cb778bb8ce173aa28ec9faecae33` |
| `Overfull/NativeCore/Completion.lean` | `0628b91bb2241b3b86393bb60e70f996689584bb6576b53d3df23fcc6c9a3b69` |
| `Overfull/NativeCore/Incidence.lean` | `e53cc10c86a37a8266d48f4229f30442e898ec293288696bba59d0e20bd397e2` |
| `Overfull/NativeCore/PrefixSelection.lean` | `82477088824bc26d4475a29339e7b0e9bdfc5df4541d9b89a9c177954affb41d` |
