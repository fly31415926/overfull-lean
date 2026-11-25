# Root semantic review

## Independent review of reserved four-label primaries

Reviewer: `/root`. Primary author: `/root/proof_target_review`.

Source: `Overfull/ResidualPalette/FourReservedPrimary.lean`.
SHA-256: `8edf10f3c4f1ac849d36d32a1f2fedd07d75683e64db3b25d8d7564ab6c4f35e`.
Actual strict receipt: `focused/four-reserved-primary-01/command.json`.

I read the complete source and checked the induction against its stated
quantifiers and the existing four-label circuit interface. Each selected
original crossing is paired with a distinct virtual crossing. The resulting
two-circuit respects the original incidence-class compatibility requirement.
Removing it preserves even degrees. Closed-cut inequalities remain unchanged;
separating-cut and virtual-copy budgets decrease together. The residual class
bound is preserved after the selected-set size decreases. Reassembly keeps
the original copies and produces singleton primary pieces with distinct
indices. The induction base uses the already proved unrestricted compatible
circuit theorem, not an assumed selector or new existence axiom.

The host-level application derives the circuit cut conditions from actual
regularity, no overfull vertex set, joining-degree control and
`D ≤ h - |A|`. It does not replace selected copies with endpoint pairs.
No semantic issue was found. This independent review is complemented by
`pair-star-independent-review.json` at the same source hash.

## Integration review and scope

I also reviewed the final composition interfaces against their intended
native construction. This is integration review, not independent review of
the four modules I authored (`FourProtectedPalette`, `TwoPairOneStar`,
`TwoPairParity`, and `TwoPairExternal`). Other agents provide independent
reviews of those files and their successful strict source snapshots.

The final theorem builds the palette, protected traces, actual one-star
geometry, and exceptional extension; it assumes the safe regular residual
and retained-core/numerical budgets. Its exact union is joining copies plus
exceptional copies, with no claim to cover all internal unused core copies.
Its per-vertex whole-family load follows from actual core degree deficits.
The two-pair hypothesis is explicit; the reserve-selection theorem itself
also permits zero-pair and one-pair representatives. No numbered assertion is
promoted, and the safe residual, multi-star branches and later full native
factorization remain open.

All failed elaboration attempts are retained. The final repairs to the
external composition normalize finite-set membership across classical
equality instances on residual-copy subtypes; they do not weaken a premise
or conclusion. The final strict source hash is
`e39608d92ccb73cc0f144866fa74eb1ae7f1355bc68b2272d3ea5e5aa2b954d5`.
