import Overfull.TerminalFourOdd.StarGeometry
import Overfull.TerminalFourOdd.Dominant

/-! Uniform factorization directly from actual common-center primary forests. -/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd SmallCuts Multi

theorem exists_uniform_common_center_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (label : V → Fin 4) (C : ∀ i, Core G (labelShore label {i})) (k : ℕ) (a : ℝ),
        (∀ i, m₀ ≤ (labelShore label {i}).card) →
        (∀ i, (labelShore label {i}).card % 2 = 1) →
        (∀ v, G.degree v = k) →
        (∀ i, α*(labelShore label {i}).card ≤ (k : ℝ)) →
        (∀ i, IsRobustExpander (C i).graph ν τ) →
        (∀ i, a ≤ ε*(labelShore label {i}).card) →
        (∀ i v, (k : ℝ)-a ≤ ((C i).graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → Pairwise (fun i j => Disjoint (M i) (M j)) →
        univ.biUnion M = joiningCopies G label →
        (∀ j, PrimaryProfile G label (M j)) → (∀ j, (M j).card ≤ 3) →
        (c : Fin 4) → (∀ j, (G.cutOn (M j) (labelShore label {c})).card = 3) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ := exists_uniform_dominant_coloring α ν τ 3 hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E _ _ G label C k a hm hodd hregular hk hrob ha hdegree
    M hdisj hcover hprofile hsize c hcenter
  let U := labelShore label {c}
  let X := fun i : LeafLabel c => labelShore label {i.val}
  have heven : Even (U.card+Fintype.card (LeafLabel c)) := by
    apply Nat.even_iff.mpr
    rw [leafLabel_card]
    have hc := hodd c
    dsimp [U]
    omega
  exact hfactor V E (LeafLabel c) G U X (leafLabel label c) (C c)
    (fun i => C i.val) k a
    (fun i => label_shores_disjoint label (Ne.symm i.property))
    (fun i j hij => label_shores_disjoint label (fun he => hij (Subtype.ext he)))
    (center_and_leaves_cover label c) (leaf_fiber label c) heven
    (by rw [leafLabel_card]) (fun i => Nat.odd_iff.mpr (hodd i.val))
    (hm c) (fun i => hm i.val) hregular
    (common_center_leaf_cutSize G label k M c hdisj hcover hprofile hcenter)
    (hk c) (fun i => hk i.val)
    (common_center_exterior_labels G label k M c hcover hsize hcenter)
    (hrob c) (fun i => hrob i.val) (ha c) (fun i => ha i.val)
    (hdegree c) (fun i => hdegree i.val)

end Overfull.TerminalFourOdd
