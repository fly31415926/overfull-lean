import Overfull.RobustExpansion
import Mathlib.Logic.Equiv.Set

/-!
# Relabeling a robust degree realization

Robust expansion and actual vertex degrees are transported by a bijection.
Equal-sized prescribed vertex sets can be matched by a permutation.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem comap_neighbor_inter_card (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ≃ W) (v : V) (S : Finset V) :
    ((G.comap e).neighborFinset v ∩ S).card =
      (G.neighborFinset (e v) ∩ S.image e).card := by
  have himage : (((G.comap e).neighborFinset v ∩ S).image e) =
      G.neighborFinset (e v) ∩ S.image e := by
    ext w
    simp only [Finset.mem_image, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.comap_adj]
    constructor
    · rintro ⟨u, ⟨hu, huS⟩, rfl⟩
      exact ⟨hu, ⟨u, huS, rfl⟩⟩
    · rintro ⟨hu, ⟨u, huS, rfl⟩⟩
      exact ⟨u, ⟨hu, huS⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ e.injective]

theorem comap_equiv_degree (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ≃ W) (v : V) :
    (G.comap e).degree v = G.degree (e v) := by
  have h := comap_neighbor_inter_card G e v univ
  have he : (univ : Finset V).image e = univ := Finset.image_univ_of_surjective e.surjective
  simpa only [he, Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree] using h

theorem robust_comap_equiv (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ≃ W) (ν τ : ℝ) (hG : IsRobustExpander G ν τ) :
    IsRobustExpander (G.comap e) ν τ := by
  intro S hlow hupp
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have himage : (S.image e).card = S.card := Finset.card_image_of_injective _ e.injective
  have hl : τ * Fintype.card W ≤ ((S.image e).card : ℝ) := by
    simpa only [himage, hcard] using hlow
  have hu : ((S.image e).card : ℝ) ≤ (1-τ)*Fintype.card W := by
    simpa only [himage, hcard] using hupp
  have h := hG (S.image e) hl hu
  have hmap : ∀ w ∈ robustNeighbors G ν (S.image e),
      e.symm w ∈ robustNeighbors (G.comap e) ν S := by
    intro w hw
    rw [mem_robustNeighbors] at hw ⊢
    have hc := comap_neighbor_inter_card G e (e.symm w) S
    rw [e.apply_symm_apply] at hc
    simpa only [hc, hcard] using hw
  have hbound := Finset.card_le_card_of_injOn e.symm hmap
    (fun _ _ _ _ h => e.symm.injective h)
  have hboundR : ((robustNeighbors G ν (S.image e)).card : ℝ) ≤
      (robustNeighbors (G.comap e) ν S).card := by exact_mod_cast hbound
  simpa only [himage, hcard] using h.trans hboundR

omit [Fintype W] [DecidableEq W] in
theorem exists_perm_mem_iff (S T : Finset V) (hcard : S.card = T.card) :
    ∃ e : Equiv.Perm V, ∀ v, e v ∈ S ↔ v ∈ T := by
  have hinside : Fintype.card (T : Set V) = Fintype.card (S : Set V) := by
    simpa using hcard.symm
  have houtside : Fintype.card ((T : Set V)ᶜ : Set V) =
      Fintype.card ((S : Set V)ᶜ : Set V) := by
    change Fintype.card {v : V // v ∉ T} = Fintype.card {v : V // v ∉ S}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    exact congrArg (fun k => Fintype.card V-k) hinside
  let e₁ : (T : Set V) ≃ (S : Set V) := Fintype.equivOfCardEq hinside
  let e₂ : ((T : Set V)ᶜ : Set V) ≃ ((S : Set V)ᶜ : Set V) :=
    Fintype.equivOfCardEq houtside
  let e : Equiv.Perm V := (Equiv.Set.sumCompl (T : Set V)).symm.trans
    ((Equiv.sumCongr e₁ e₂).trans (Equiv.Set.sumCompl (S : Set V)))
  refine ⟨e, ?_⟩
  intro v
  by_cases hv : v ∈ T
  · have he : e v = (e₁ ⟨v, hv⟩).val := by
      have hs : (Equiv.Set.sumCompl (T : Set V)).symm v = Sum.inl ⟨v, hv⟩ :=
        (Equiv.Set.sumCompl (T : Set V)).symm_apply_apply (Sum.inl ⟨v, hv⟩)
      change (Equiv.Set.sumCompl (S : Set V))
        ((Equiv.sumCongr e₁ e₂) ((Equiv.Set.sumCompl (T : Set V)).symm v)) = _
      rw [hs]
      rfl
    rw [he]
    exact iff_of_true (e₁ ⟨v, hv⟩).property hv
  · have he : e v = (e₂ ⟨v, hv⟩).val := by
      have hs : (Equiv.Set.sumCompl (T : Set V)).symm v = Sum.inr ⟨v, hv⟩ :=
        (Equiv.Set.sumCompl (T : Set V)).symm_apply_apply (Sum.inr ⟨v, hv⟩)
      change (Equiv.Set.sumCompl (S : Set V))
        ((Equiv.sumCongr e₁ e₂) ((Equiv.Set.sumCompl (T : Set V)).symm v)) = _
      rw [hs]
      rfl
    rw [he]
    exact iff_of_false (e₂ ⟨v, hv⟩).property hv

end Overfull.RobustRealization
