import Overfull.AuxiliarySimple.Graph
import Overfull.RobustRealization.Relabeling

/-! Exact core transport under an injective change of ambient vertex names. -/

noncomputable section

namespace Overfull.AuxiliarySimple

open Finset Classical SimpleGraph

/-- Robust expansion is independent of the selected decision procedures for
vertex equality and adjacency. This lets concrete sum types use their own
instances while retaining the identical graph and numerical parameters. -/
theorem robust_instance_transfer {X : Type*} [Fintype X] (G : SimpleGraph X)
    {d d' : DecidableEq X} {r r' : DecidableRel G.Adj} {ν τ : ℝ}
    (h : @IsRobustExpander X _ d G r ν τ) :
    @IsRobustExpander X _ d' G r' ν τ := by
  cases Subsingleton.elim d d'
  cases Subsingleton.elim r r'
  exact h

variable {V W : Type*} (f : V ↪ W) (U : Finset V)

/-- The vertices of a core correspond exactly to their mapped ambient names. -/
def partEquiv : U ≃ U.map f :=
  Equiv.ofBijective
    (fun v => ⟨f v.val, mem_map.mpr ⟨v.val, v.property, rfl⟩⟩)
    ⟨by
      intro v w h
      exact Subtype.ext (f.injective (congrArg Subtype.val h)), by
      intro w
      obtain ⟨v, hv, heq⟩ := mem_map.mp w.property
      exact ⟨⟨v, hv⟩, Subtype.ext heq⟩⟩

@[simp] theorem partEquiv_coe (v : U) : (partEquiv f U v).val = f v.val := rfl

@[simp] theorem partEquiv_symm_coe (w : U.map f) :
    f ((partEquiv f U).symm w).val = w.val := by
  rw [← partEquiv_coe, Equiv.apply_symm_apply]

/-- The transported core has exactly the original adjacencies. -/
def mappedCore (H : SimpleGraph U) : SimpleGraph (U.map f) :=
  H.comap (partEquiv f U).symm

theorem mappedCore_degree (H : SimpleGraph U) (w : U.map f) :
    (mappedCore f U H).degree w = H.degree ((partEquiv f U).symm w) :=
  RobustRealization.comap_equiv_degree H (partEquiv f U).symm w

theorem mappedCore_robust (H : SimpleGraph U) (ν τ : ℝ)
    (hrobust : IsRobustExpander H ν τ) :
    IsRobustExpander (mappedCore f U H) ν τ :=
  RobustRealization.robust_comap_equiv H (partEquiv f U).symm ν τ hrobust

theorem mappedCore_embed (G : SimpleGraph V) (R : SimpleGraph W) (H : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V))
    (hmap : ∀ v w, G.Adj v w → R.Adj (f v) (f w)) :
    mappedCore f U H ≤ R.induce ((U.map f : Finset W) : Set W) := by
  intro v w hvw
  change R.Adj v.val w.val
  rw [← partEquiv_symm_coe f U v, ← partEquiv_symm_coe f U w]
  exact hmap _ _ (hH hvw)

end Overfull.AuxiliarySimple
