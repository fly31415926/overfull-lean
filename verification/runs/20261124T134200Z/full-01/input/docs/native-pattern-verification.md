# Native multigraph assignment patterns and boundary compression

## Scope

This continuation starts from `ec258578dfa68d0ac50cd9ff9e70b8dcbc2232b6`.
It supplies the finite native multigraph bridge identified in the previous
handoff: actual-copy distribution capacities, at most five assignment
signatures, a heavy actual matching representative, and compression of its
boundary with the exact core parities preserved.

The numbered inventory remains **47 of 69**. This stage does not complete
Corollary 4.6, the general fixed-pattern Lemma 4.4, or the main theorem.
The original 69 assertion statements and all previous completed proofs are
preserved. Fresh compiler and audit evidence is in the current run directory,
`verification/runs/20261123T113235Z/`, and `verification/results.json`.

## Original hypotheses and copies

Let `G : Multigraph V E` be a finite loopless multigraph, with original
edge-copy type `E`. For the heavy matching construction, `G` has positive
regular degree `k` and no `k`-overfull vertex set. The vertex sets
`U₀`, `U₁`, and `Z` are disjoint and cover the original vertices, with
`Z.card ≤ 2`. No simplicity condition is imposed on the ambient host.

These finite statements do not need robust expansion. They can therefore
be applied to the original robust-core hypotheses of the two-core branch
without changing their parameter order. They make no claim about the
robustness, regularity or absence of overfull sets in a subsequently
constructed residual graph.

## Native scaled weights

`NativeWeights.scaledWeight` scales the already proved native perfect-matching
distribution by `k`. The resulting weights are nonnegative and sum to `k`.
Each individual original edge copy has marginal exactly one. Double counting
therefore gives, for every actual-copy pool `A`,

```text
sum_s w(s) * card(M(s) intersect A) = card A.
```

If `F(s)` is a selected submatching of `M(s)`, the equality becomes an
upper bound by `card A`. Finite aggregation by any code preserves all
weighted statistics. A fixed code has weight at most `card A` whenever
every sample with that code uses a copy from `A`.

This is the correct multigraph statement. A fixed exceptional endpoint
pair may have many parallel copies. Its pattern weight is not universally
bounded by one.

## At most five assignment signatures

`AssignmentSignature Z` is `Option (↥Z → Fin 2)`. The code `none` means
that the matching contains an internal exceptional copy. With at most two
exceptions, this copy uses all of `Z`; both old core parts remain unchanged.
The code `some σ` records the old core to which each exceptional vertex is
matched. It retains the actual matching's assignment.

The signature type has `2 ^ Z.card + 1 ≤ 5` elements. Grouping the scaled
distribution gives a signature of weight at least `k/5` and a positive-weight
sample with exactly that signature. There is no replacement of this sample
by an unrelated perfect matching.

Equal signatures determine the same actual enlarged core parts, optional
pair part, and `Fin 3` vertex-label map. They also determine the parity of
the old-core crossing count, by the previously checked exact matching-cut
identity. Their uncompressed crossing counts and individual copies need
not be equal.

## Forced pools in the original host

Every sample of the heavy signature uses the relevant original-copy pools:

| Signature requirement | Actual-copy pool | Proved conclusion |
| --- | --- | --- |
| Internal exceptional pair | `G.internalOn univ Z` | At least `k/5` copies when the heavy code is `none`. |
| Unpaired exception `z` assigned to core `Uᵢ` | `exceptionCorePool G z Uᵢ` | At least `k/5` copies for every such exception. |
| Odd old-core crossing parity | `coreCrossingPool G U₀ U₁` | At least `k/5` copies. |

The paired case has an exact identity: its signature weight equals the
cardinality of the whole exceptional internal-copy pool. Each sample uses
zero or one copy from that pool, so the native marginal identity counts
its full parallel multiplicity.

There is also an exact marginal identity for each exceptional vertex and
either original core. The sum of the weights of all signatures assigning
that vertex to the specified core equals the number of actual copies in
its pool to that core. This derives a degree-accounting identity directly
from the native distribution and retains every parallel copy.

`exists_assignment_matching_with_linear_pools` constructs the distribution
and actual matching from the original regularity and no-overfull hypotheses.
The supplies are conclusions, not assumed inputs. Copy counts do not
imply the same number of distinct neighbors or a simultaneous disjoint
reserve selection.

## Compression of the same actual matching

For a specified perfect matching `M`, let `T` be its selected original
copies between the two old cores. `compressedBoundary` retains every
copy of `M` touching `Z`, together with no member of `T` when `T.card`
is even or one actual member of `T` when it is odd.

The proofs establish all of the following:

- The compression is a subset of `M`, hence a matching on original copies.
- Every exceptional vertex remains covered with selected degree exactly one.
- At most `Z.card + 1` copies, and at most `2 * (Z.card + 1)` vertices,
  are retained. In the target branch these are at most three copies and
  six vertices.
- Every selected internal exceptional copy is retained exactly, including
  its identity within a parallel bundle.
- The exceptional assignments, both enlarged core parts, optional pair
  part, assigned label map, and coarse signature are unchanged.
- No selected copy is internal to an old core; the statement for the
  second core follows by the proved symmetry.
- The compressed old-core crossing count is exactly `T.card % 2`.
- Both original cores have even uncovered order.

The last conclusion comes from actual matching incidence counting. In
any matching, the covered vertices of a shore equal twice its internal
selected edges plus its selected cut size. Replacing `T` by a subset of
the same parity preserves the old-core cut parity, so the uncovered
vertex count in each core is even.

The compression itself works for an arbitrary finite exceptional set;
the bound of two is needed for the five-signature classification and its
pool conclusions.

## Composition and source-statistic alignment

`exists_compressed_assignment_with_linear_pools` constructs the original
perfect matching and its compression together from the original finite
host hypotheses. The same representative controls its assignment,
original pool bounds, selected internal exceptional copies and both core
parities. The final crossing supply is stated using the actual retained
crossing count, and is proved by its exact equality with the original
crossing parity.

`compressedBoundary_crossing_card_eq_of_signature_eq` separately proves
that matchings of the same signature have the same retained crossing
statistic. This is a checked alignment for this native compression. It
does not assert identity with the pre-existing simple-host `Encodes`
relation or transfer its internal-pair deletion lemmas.

## Proof modules and verification

| Module | Role |
| --- | --- |
| `AssignedParts.NativeWeights` | Exact native marginals, pool capacities and finite weighted pigeonhole. |
| `AssignedParts.Signatures` | Actual signatures, constant assigned parts and crossing parity, cardinal bound. |
| `AssignedParts.SignaturePools` | Actual-copy pool usage for every forced signature requirement. |
| `AssignedParts.HeavySignature` | Heavy representative, linear supplies and exact internal-pair weight. |
| `AssignedParts.ExactPoolWeights` | Exact signature-weight sums for each exceptional-to-core copy pool. |
| `AssignedParts.BoundaryCompression` | Original-copy compression, size, exceptional coverage and assignment retention. |
| `AssignedParts.CompressionCuts` | Exact cut partitions, crossing identity and even uncovered order. |
| `AssignedParts.NativePatternConstruction` | Same-representative composition and retained-statistic alignment. |

`scripts/update_native_pattern_manifest.py` produces the source hashes and
public declaration map. The full verifier checks those names against the
fresh stock audit, including their actual modules, and generates
`verification/native-pattern-declarations.json` with private and generated
proof declarations as well. The new verifier checks are additive; the
stock audit and every previous verification gate are preserved.

## Next obligations

The next construction must turn these fractional capacities into actual
simultaneously disjoint selected matching boundaries and a retained
reserve. It must preserve the exceptional pair and prove the required
residual-degree and reserve-incidence bounds. No-overfull safety needs
its own actual-cut argument; deletion of a perfect matching preserves
regularity but is not automatically safe for odd cuts.

The existing assigned-part and joining theorems can then be applied to
that verified residual. Palette grouping, robust core completion,
regular auxiliary graph construction, reconstruction of the whole
factorization, and the original uniform parameter choices remain to be
completed for full Corollary 4.6.
