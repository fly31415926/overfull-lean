# Independent review of the three-core public composition

Reviewer: `terminal_route`. Review completed 2026-11-24 UTC against the frozen
snapshot recorded by `development/three-core-005/command.json`.

## Scope and conclusion

I reviewed `Overfull/Terminal/ThreeCore.lean`,
`Overfull/Terminal/CompletedFactorization.lean`, their core/copy transport and
restoration interfaces, and `docs/three-core-terminal-semantic-review.md`.
I found no mathematical gap, circular conclusion hypothesis, or quantifier-order
defect in this public composition. The final public statements quantify the
positive tolerance and positive order threshold before all graph-specific data.

This is an independent review of the public integration authored by the root
agent and the relevant interfaces authored by other agents. I authored
`Palette.lean`, `Parameters.lean`, `PrefixCompletion.lean`, `PrefixResult.lean`,
and `Prefix.lean`; this report is therefore **not** an independent review of my
own complete prefix development. I inspected those interfaces for the present
composition and have identified their hashes below. No Lean source, documentation,
manifest, verifier, or control file was changed for this review. No new build was
run.

## Public hypotheses and uniformity

The declarations reviewed are
`Overfull.three_core_terminal_factorization` and
`Overfull.three_core_terminal_one_factorization`.
They assume an even-order regular simple host, a positive linear degree bound,
no overfull vertex set in that original host, and three disjoint covering parts
with positive linear order bounds. Each supplied simple core embeds in its
induced part, is robust with the fixed parameters, and has minimum degree at
least `h - a`, where `0 ≤ a` and `a + 1 ≤ ε * n`.

No joining decomposition, completed prefix, residual coloring, leaf coloring,
or contracted-host no-overfull certificate is among these public hypotheses.
The theorem does not assume that its target graph already has a factorization.
The auxiliary `exists_uniform_completed_prefix_factorization` does accept a
`ThreeCorePrefix` transcript; the public theorem constructs this transcript
from the original hypotheses via `exists_uniform_three_core_prefix`.

The density normalization `β = min α 1` is valid: its positivity follows from
`α > 0`, and lowering the density preserves both original degree and part-order
bounds. The parameter dependency is:

1. Fix `α, ν, τ` and their stated inequalities.
2. Obtain `θ > 0`, `θ ≤ τ/2` from the uniform prefix theorem, before requesting
   any final error tolerance or final part-order threshold.
3. Obtain a common residual tolerance `η > 0` and threshold `m₀` at density
   `β/2` and robust parameters `(θ, τ/2)`.
4. Request those particular `η, m₀` from the prefix theorem to obtain
   `ε > 0, n₀ > 0`, still before the vertex type, host, degree, parts, or error.

The required residual range inequality is exactly
`τ/2 ≤ (β/2)/64`, which follows from the public bound `τ ≤ β/64`.
The even branch's weaker range condition is satisfied by the same constants.
Taking the minimum of the two residual tolerances and maximum of the two
thresholds is in the correct direction. The core error passed to each branch
is measured against that part's actual cardinality.

## Residual geometry, case coverage, and degree arithmetic

`CompletedFactorization.lean` defines the actual simple residual as
`afterDeletions G P.completion.full P.rounds`. `completionCore` embeds the
actual remaining simple core into the edge-copy multigraph of this residual.
`completionCore_robust`, `completionCore_degree`, and
`completionResidual_regular` supply the robust expansion, degree error, and
regularity used by the terminal theorems. The inequality `P.rounds ≤ h` is
explicitly used both in `Nat.cast_sub` and in final palette arithmetic; no
truncated natural subtraction is silently replaced by real subtraction.

Even total order and a disjoint covering three-part partition leave all-even
or exactly-two-odd part orders. The constructed prefix records these exhaustive
alternatives. In the even case, `P.remaining = ∅` and the exact joining identity
give empty residual cuts for every part. The theorem
`exists_uniform_closed_core_factorization` constructs the component colorings
from the robust cores; the local colorings are conclusions of that theorem.

In the two-odd case, `exists_third_core_index` supplies the actual even part,
and `reordered_three_core_cover` proves that the reordered three parts still
cover the host. `ThreeCorePrefix.exists_residual_primary_family` reindexes the
retained finite family by `Fin (h - P.rounds)` using its proved exact cardinality.
The family is transported through `residualPool`, whose edge embedding retains
the original endpoints. Its matching and pairwise-disjoint properties survive,
its union is exactly the union of the two odd cuts, and its crossing cardinality
at each odd part is exactly one. Survival is derived from `P.remaining_eq`;
it is not assumed as a replacement for the required copy identity.

These are precisely the combinatorial inputs to
`exists_uniform_two_odd_coloring`. Inspection of that theorem and
`exists_uniform_central_coloring` confirms that the central and leaf colorings
are constructed. The central no-overfull condition is obtained from
`robust_two_exterior_no_overfull` and the actual exterior matching cover before
calling `bounded_input_factorization`; it is not a supplied certificate for
the contracted target. The central/leaf gluing dependency includes original
copies between the odd parts.

The public order threshold is positive. Together with the positive density
and part-size bounds this excludes empty-host, zero-degree, and empty-core
accidents in the public theorem. Parity is imposed on vertex order, not on `h`.
No unmentioned assumption that `h` is even appears in the composition.

## Restoration and exact factorization

`completion_restores_coloring` uses `restoredColoring`, which first transports
the residual coloring through the explicit `residualEdgeEquiv` to the surviving
original-copy subtype. Prefix matching colors and residual colors occupy
disjoint parts of a palette of size `P.rounds + (h - P.rounds)`. The proved
round bound identifies this with `h`.

The public one-factorization theorem applies
`BoundedExterior.exists_oneFactorization_of_coloring` using the original
host's `h`-regularity. Its conclusion contains exactly `h` actual original-edge
copy classes, each a perfect matching, with pairwise disjointness and union
equal to all original copies. The final `Subsingleton.elim` substitutions only
identify `DecidableEq` instances; they do not weaken mathematical properties.

## Source scope, coverage, and validation status

The semantic review document accurately describes this explicit three-core
terminal-host theorem and its construction. Full Proposition 4.16 also includes
four-core cases and is not proved here. A direct formal application to the
`FrequentPatternResult` interface of Lemma 4.13 is a useful next wrapper; the
current public theorem is the terminal-host result that wrapper would invoke.
No full numbered assertion is promoted by this round.

I compared all 69 current numbered assertion records with the published
baseline and found them identical. The current count remains 48/69 and the
`three:prop:terminal` record remains unverified with pinned statement hash
`1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c`.
The baseline commit is `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`; a read-only
Git query confirmed its tree is `5d031253d02d0d0878422f8fbc367f04b812450c`.

The final focused receipt records
`lake build --wfail Overfull.Terminal.ThreeCore`, exit 0, 3,545 jobs,
2026-11-24 03:38:13.815265 to 03:38:18.886151 UTC, with
`inputs_changed_during_command = []`. I independently compared the receipt's
21 terminal source hashes with the files reviewed; every hash matched.
The receipt SHA-256 is
`445e8dfefade452a43f69df2d69f4fc4bf3f8df0d604695e166076560b8de1b6`.

The full project audit and preservation checks are pending at this report's
completion. This report does not assert that the full audit has passed, that
all generated declaration mappings have been validated, or that all prior
axiom sets and source files have been independently re-audited. Those are the
separate obligations described in the semantic review document.

## Reviewed snapshot SHA-256

```text
0b3088e0a199d67f58d580a8cce48777cfd81625ee9a3249d05c62fe3aa092b1  Overfull/Terminal/ThreeCore.lean
f73eb10d44c333f03f6a103eaa621955c50ae6337bb90c49f52bb9f886a24435  Overfull/Terminal/CompletedFactorization.lean
a2defcea9dad137a8ad224368b4b4567f623126559387bfbcfc3becd97b0763e  Overfull/Terminal/CoreBridge.lean
f59ce3a3da2fcfc33331a32eaa2110e87165c9cfb6f0386e13e9e3bc7ef2bccb  Overfull/Terminal/RemainingProfile.lean
27a7377ae0469e7048563214f7c3598445e3d95ca964ecc460ce4c81fb0d704e  Overfull/Terminal/ClosedCores.lean
e1957ec7fe99d68ac4cc9a728a8a8d02d012eedfa39d8485a19a4c3d54e5bf3d  Overfull/Terminal/OddFactorization.lean
cb29f0cc83e5b69fd3f92d13b02bca75c93a83992f3c422a3f661627548a7823  Overfull/Terminal/CentralFactorization.lean
4a038b5861a83b7c374f1af02b7fb5a3a2a45c7b2cd23cc8b638a230b06879df  Overfull/Terminal/Reassembly.lean
d4ab3bb6eaf6c6540a071c93928fa1e9ea299d8f365da383dd06752edfba4977  Overfull/Terminal/Prefix.lean
d57bc73b64e75780308a292f2c18cc534792fd6dbc89e8e1d8381db9dc055040  Overfull/Terminal/Parameters.lean
5851a4b1256d92642a65712a485b31ec9966a8128da623a8a37d7860cf770afa  Overfull/Terminal/PrefixCompletion.lean
8ba5b690dde71440ccff6af41817eed7ca2dd4f0b5a6897ada0915aefd4e1159  Overfull/Terminal/PrefixResult.lean
6035ed6e9a0828b5425902dead42f11906c9402a84fad9da8d62881a6816b33d  Overfull/Terminal/Palette.lean
ea6cd1b3bc1cf02576492c40e8efc5910de8650476edcd70ce60f4f411209ad4  docs/three-core-terminal-semantic-review.md
```
