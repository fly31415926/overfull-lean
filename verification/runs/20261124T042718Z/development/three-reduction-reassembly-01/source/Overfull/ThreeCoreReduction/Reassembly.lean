import Overfull.Terminal.Reassembly
import Overfull.ForeignEdges.Incidence

/-! Restoration through a regular reduction with its actual matching prefix. -/

noncomputable section

namespace Overfull.ThreeCoreReduction

open Finset Classical SimpleGraph ForeignPhase ForeignIncidence Terminal

variable {V : Type*} [Fintype V]

/-- The original and actual residual regularities determine the total palette.
No supplied degree-loss identity or separate feasible-prefix hypothesis is
needed. -/
theorem regular_prefix_degree_identity (G R : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q k h : ℕ)
    (hn : 0 < Fintype.card V) (hgraph : R = afterDeletions G N q)
    (hregular : ∀ v, G.degree v = k) (hresidual : ∀ v, R.degree v = h)
    (hperfect : ∀ j < q, (N j).IsPerfectMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j) :
    q + h = k := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
  have hid := perfect_deletion_degree_identity G N q hperfect hpresent v
  change (afterDeletions G N q).degree v + q = G.degree v at hid
  rw [← hgraph, hresidual v, hregular v] at hid
  omega

/-- A coloring of the actual regular residual restores all original copies
with exactly the original degree palette. -/
theorem restore_regular_coloring (G R : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q k h : ℕ)
    (hn : 0 < Fintype.card V) (hgraph : R = afterDeletions G N q)
    (hregular : ∀ v, G.degree v = k) (hresidual : ∀ v, R.degree v = h)
    (hperfect : ∀ j < q, (N j).IsPerfectMatching)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (hc : Nonempty ((Multigraph.ofSimpleGraph R).EdgeColoring h)) :
    Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring k) := by
  obtain ⟨c⟩ := hc
  have c' : (Multigraph.ofSimpleGraph (afterDeletions G N q)).EdgeColoring h := by
    rw [← hgraph]
    exact c
  have hsum := regular_prefix_degree_identity G R N q k h hn hgraph
    hregular hresidual hperfect hpresent
  have hcolor : Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring (q + h)) :=
    ⟨restoredColoring G N q (fun j hj => (hperfect j hj).1) c'⟩
  simpa only [hsum] using hcolor

end Overfull.ThreeCoreReduction
