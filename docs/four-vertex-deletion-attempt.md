# Four-label safe-deletion condition (attempt, **not Lean verified**)

The existing `Deletion.lean` proves the exact deletion correction for arbitrary finite selected edge copies and a sufficient critical-cut test on `Fin 4`. This source attempt proposes two upgrades: an iff criterion for any finite vertex type of size at most four, and an equivalent incidence-witness version for compatible circuits.

For a cut `X`, write `b = |cut_C(X)|`, `a = |classCut_C(v,k,X)|`, `d = |cut_D(X)|`, and `s = |classCut_D(v,k,X)|`. The exact correction is `2a+d ≤ b+2s`. Original admissibility gives even nonnegative slack `b-2a`; circuit parity and at most four labels give `d ∈ {0,2,4}`; compatibility gives `s≤1`. Therefore:

- On a tight cut (`b=2a`), `d=2` requires `s=1`, while `d=4` is impossible for a safe deletion.
- On a slack-two cut (`b=2a+2`), only `d=4` needs a witness `s=1`.
- Cuts with slack at least four require no further test because `d≤4`.

The equivalence is proved at the arithmetic level and tested on 202 bounded admissible tuples. **Neither Lean compilation nor an unbounded theorem has been verified in this environment.** In particular, these conditions do not produce a circuit satisfying them. The two-core joining problem still requires proving the actual quotient's parity and half-cut inequalities and lifting the selected copies without collapsing parallel edges.
