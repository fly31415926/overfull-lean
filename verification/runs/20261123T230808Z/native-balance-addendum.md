# Additional existing interface for exact prescribed-star counts

This is a planning note, not a new Lean proof or completed assertion.

After lifting the reserve witness into the residual assigned-star pool,
apply `AssignedParts.exceptionCorePool_matching_card_le_one` to
`BoundaryPacking.residualBoundary_matching`. The witnessed intersection
is nonempty and has cardinality at most one, hence exactly one. Combine
this with `BoundaryPacking.residualBoundary_disjoint` to show that a
selected set of `s` reserve boundaries supplies exactly `s` distinct
prescribed copies in that star pool.

The relevant sources are `Overfull/AssignedParts/ExactPoolWeights.lean` and
`Overfull/ExceptionalPalette/ReserveCopies.lean`. This gives a direct route
to the prescribed-copy subtraction in the prospective remaining-star
balance proof; that native composition has not yet been formalized.
