# Actual assigned parts, exact matching cuts, and joining transport

## Mathematical result

Fix a finite loopless multigraph `G : Multigraph V E`, a specified actual
perfect matching `M`, and a disjoint vertex partition into two core sets
`U₀`, `U₁` and an exceptional set `Z`. The construction retains this exact
matching representative; it does not select an unrelated matching.

`AssignedParts.assignedExceptions G M Z U` consists of the exceptional
vertices whose selected matching copy goes to `U`. The corresponding
`corePart` is the union of the original core and these vertices.
`pairPart G M Z` is the support of the actual selected copies internal
to `Z`. Matching uniqueness makes these three parts disjoint and
perfect-matching coverage makes their union the original vertex type.

The explicit map `assignedLabel : V → Fin 3` has precisely those three
fibers. Every unpaired exception has an actual selected copy to its
assigned original core. Parallel copies remain distinct elements of `E`.
The matching-support identity proves

`(pairPart G M Z).card = 2 * (G.internalOn M Z).card`.

When `Z.card ≤ 2`, there is at most one selected internal copy and the
third fiber has cardinality zero or two. No exceptional singleton is
left as an admissibility-obstructing quotient part.

## Exact cuts and parity

Let `T = G.cutOn M U₀ ∩ G.cutOn M U₁`, the actual selected copies
between the two original cores. The proof establishes:

- `G.cutOn M (corePart G M Z U₀) = T`;
- `G.cutOn M (corePart G M Z U₁) = T`;
- `G.cutOn M (pairPart G M Z) = ∅`.

The perfect-matching handshake gives both core-fiber cardinalities
congruent to `T.card` modulo two, and the pair fiber is even. Thus the
constructed fibers are all even, or exactly labels zero and one are odd.
The desired parity profile is derived, not assumed.

The cut identities are statements on original selected copies, not only
on a quotient. Any identification with a separately defined manuscript
boundary-pattern statistic still requires its own checked bridge.

## Composition with the joining theorem

`assignedLabel_joining_decomposition` combines the constructed label
and proved parity with the recovered original-host joining theorem.
For regular degree `h` and no `h`-overfull vertex set, it constructs:

- In the even case, an exact partition of every joining copy into
  disjoint nonempty host matchings of size at most three.
- In the two-odd case, exactly `h` primary matchings of size at most two,
  plus surplus matchings of size at most three, with exact disjoint
  coverage and the previously checked fiber-cut footprints.

The new `assignedLabel_joining_decomposition_in_host` transports the
same assignment to another multigraph `H : Multigraph V F` on the same
vertices. The representative belongs to `G`; it need not remain a
perfect matching after reserves are removed from `H`. The output retains
actual `F` copies. Regularity and absence of overfull sets for `H` are
explicit stage inputs. This theorem does not prove that deleting a
chosen reserve preserves those properties.

The generic label and composition results can aggregate several internal
exceptional pairs into one even fiber. The source-specific interpretation
as one optional pair uses the explicit `Z.card ≤ 2` theorem. Aggregating
many pairs does not supply the separate pair footprints needed for the
broader source branches.

## Source and declaration map

| Module | Role |
| --- | --- |
| `Overfull.AssignedParts.PairFiberParity` | Exact three-fiber cardinal sum and exhaustive parity alternatives. |
| `Overfull.AssignedParts.ThreePartLabels` | Explicit labels with exact fibers for disjoint covering parts. |
| `Overfull.AssignedParts.Basic` | Original-copy assignment, matching support count, exact part partition, pair size and derived parity. |
| `Overfull.AssignedParts.MatchedCuts` | Exact original selected cuts and crossing-count parity. |
| `Overfull.AssignedParts.JoiningConstruction` | Same-host and separate-host joining compositions. |

The [source manifest](assigned-part-source.json) maps the actual final
module hashes and all public theorem names. The complete verifier checks
those names and modules against its fresh stock axiom audit and generates
`verification/assigned-part-declarations.json`, including private and
generated proofs. Manifest generation alone does not verify a proof.

## Recovery provenance and evidence

The five joining modules were recovered byte-for-byte from
`28edc7b555d459b93a00d15258ca374abf5f0bb0`. The earlier final publication
was interrupted after an observed full check but before the verified
branches moved. Its final raw outputs were not retained in that referenced
commit. The five assigned-part drafts were also lost with the workspace.
This run recreates them, adds the separate-host refinement, and performs
new checks. It does not claim to reproduce the lost drafts' exact bytes
or fabricate their old diagnostic logs.

The actual recovery record, fresh command logs and run report are under
`verification/runs/20261123T042619Z/`. The independent
[semantic review](assigned-part-semantic-review.md) records its authorship
boundaries and observed checks. Full verification uses:

```sh
python3 scripts/update_assigned_manifest.py
python3 scripts/verify.py
```

Lean remains 4.24.0; mathlib remains the committed
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The stock audit is unchanged;
only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

## Remaining original manuscript obligations

This is a supporting construction, not full Corollary 4.6. The numbered
count remains **47/69**, and the main theorem is unproved. One must still
construct the native multigraph heavy-pattern/reserve step, its degree
bounds and residual safety, prove alignment with source pattern statistics,
choose palettes, obtain robust perfect-matching completions, construct
regular auxiliary graphs, and reconstruct the final factorization.

Existing `Patterns` and `CircuitPatterns` distribution/reserve wrappers
use `SimpleGraph`. Their bound that a fixed exceptional internal pair has
weight at most one relies on simplicity. It cannot be transferred to a
multigraph with many distinct copies of that pair. The next proof must
retain those copies and any internal pair required by the source pattern.
Full 4.4/4.5, remaining 4.16 parity branches, general Section 6, structural
inputs and the main theorem also remain unfinished. All 69 original
statement hashes and all 47 completed assertion records are preserved.
