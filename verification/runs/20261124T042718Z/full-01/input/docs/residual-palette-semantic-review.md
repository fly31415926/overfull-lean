# Semantic review: actual residual joining palettes

This source-level review supplements strict compilation and the unchanged
transitive axiom audit. The exact checked source hashes and declarations
are recorded by the manifest and the current run's final verification
report. No numbered manuscript assertion is promoted in this continuation.

## Reviewed mathematical interfaces

1. **Parameter order.** The retained robustness is fixed before the later
   error. Taking its minimum with the prescribed range uses the existing
   robust-expansion monotonicity. It preserves every original-host
   construction conclusion and does not change the old theorem.
2. **Actual incidences.** Old-core copies are monochromatic for the original
   assignment. At an exception, the reserved incidence injection uses
   distinct original copies that genuinely survive deletion. The joining
   bound is an actual degree bound, including parallel multiplicity.
3. **Greedy capacity.** The total-size hypothesis is non-strict; an actual
   insertion has a strict predecessor bound. Primary colors remain fixed.
   The whole-class load bound is proved independently of the size-three
   bound for one piece.
4. **Parity.** The all-even construction retains every circuit's parity.
   The two-odd construction has exactly one primary per palette class.
   Disjoint cut cardinalities add, so surplus pieces contribute even parity.
   Every map and union preserves actual edge-copy identity.
5. **Assigned versus old cores.** The uncovered-even result is for the
   assigned fibers, including the possible two-vertex exceptional fiber.
   It requires subsequent internal coverage of assigned exceptions before
   it can give the needed old-core parity for robust completion.
6. **Prescribed primary crossings.** The circuit-side construction deletes
   explicitly chosen original/virtual pairs and proves the residual cut
   inequalities. It does not infer safety from regularity alone or assume
   a safe deletion selector. Selected actual crossings may share endpoints;
   they occupy different primary colors.
7. **Protected palettes.** All surplus pieces conflict with protected
   primaries, so those primary pieces remain whole singleton classes. The
   additional protected-color budget is stated and proved separately.
8. **Uniform footprint choice.** The common capacity is chosen from `nD`,
   not from an unrelated smaller piece count. This supplies the exact
   common budget required by the even and two-odd wrappers.

## Issues identified and resolved during development

- The old completion theorem did not expose robustness before the later
  error, although its proof supported that order. A new stronger theorem
  provides it; the old proof is retained unchanged.
- A capacity based only on the actual number of pieces did not immediately
  imply the stronger `nD` budget accepted by the common joining wrapper.
  The uniform natural choice `L=(nD/2)/gap+1` proves that budget directly.
- `6D<h` alone does not imply `6D+s<h` for a linear protected reserve.
  The protected budget uses `δ≤α/720` and `s≤h/2` to prove a positive
  margin of at least `αn/120`. The unprotected constant is not reused.
- The previous all-even wrapper forgot per-piece parity. A new structure
  retains the certificates from the actual compatible circuits.

Independent reviews of the incidence, grouping, parity, parameter and
actual-copy transport interfaces found no missing hypothesis in their
stated conclusions. Actual compiler diagnostics are retained, including
the early unsupported direct-Lean `--wfail` invocations. The final direct
checks use `-DwarningAsError=true`; the full project uses `lake build --wfail`.

## Remaining boundary

The native protected palette constructs singleton **joining** classes for
selected surviving reserve crossings. It does not yet insert all internal
exceptional copies of those reserve boundaries. Equal free palettes on an
exceptional pair, valid old-core footprints after exceptional coverage,
robust completion of the remaining color classes, and final reconstruction
are additional obligations. Full Corollary 4.6 and the main theorem remain
unproved; the original assertion inventory remains 47/69.
