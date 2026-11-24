import Overfull.OrdinaryRobustStability

/-!
# Robust expansion after adding a small set of vertices

This is an addition theorem, independent of any deletion stability result.
The old vertices are embedded in the enlarged graph, and their actual
neighbor counts give robust expansion in the enlarged normalization.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]

/-- Restrict a tested set to the embedded old vertex set. -/
noncomputable def oldPart (e : V ↪ W) (S : Finset W) : Finset V :=
  univ.filter (fun v => e v ∈ S)

omit [Fintype W] [DecidableEq V] in
@[simp] theorem mem_oldPart (e : V ↪ W) (S : Finset W) (v : V) :
    v ∈ oldPart e S ↔ e v ∈ S := by
  simp [oldPart]

omit [Fintype W] [DecidableEq V] in
theorem image_oldPart (e : V ↪ W) (S : Finset W) :
    (oldPart e S).image e = (univ.image e) ∩ S := by
  ext w
  simp only [mem_image, mem_inter, mem_univ, true_and]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨⟨v,rfl⟩,(mem_oldPart e S v).mp hv⟩
  · rintro ⟨⟨v,rfl⟩,hv⟩
    exact ⟨v,(mem_oldPart e S v).mpr hv,rfl⟩

omit [DecidableEq V] in
/-- At most the newly added vertices are lost when restricting a set. -/
theorem oldPart_card_bounds (e : V ↪ W) (S : Finset W) :
    (oldPart e S).card ≤ S.card ∧
      S.card + Fintype.card V ≤ (oldPart e S).card + Fintype.card W := by
  have hc : (univ.image e).card = Fintype.card V := by
    rw [card_image_of_injective _ e.injective, card_univ]
  have hT : (oldPart e S).card = ((univ.image e) ∩ S).card := by
    rw [← image_oldPart, card_image_of_injective _ e.injective]
  have hupper := card_le_card (inter_subset_right : (univ.image e) ∩ S ⊆ S)
  have heq := card_union_add_card_inter (univ.image e) S
  have hunion := card_le_univ ((univ.image e) ∪ S)
  rw [hc, ← hT] at heq
  exact ⟨by simpa only [hT] using hupper,by omega⟩

/-- Embedded old neighbors remain actual neighbors in the enlarged graph. -/
theorem old_neighbors_le (H : SimpleGraph V) (K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel K.Adj] (e : V ↪ W)
    (hembed : ∀ {u v}, H.Adj u v → K.Adj (e u) (e v))
    (S : Finset W) (v : V) :
    (H.neighborFinset v ∩ oldPart e S).card ≤
      (K.neighborFinset (e v) ∩ S).card := by
  have hs : (H.neighborFinset v ∩ oldPart e S).image e ⊆
      K.neighborFinset (e v) ∩ S := by
    rintro w hw
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hw
    rcases mem_inter.mp hu with ⟨huH,huS⟩
    exact mem_inter.mpr ⟨(K.mem_neighborFinset (e v) (e u)).mpr
      (hembed ((H.mem_neighborFinset v u).mp huH)),
      (mem_oldPart e S u).mp huS⟩
  have hc := card_le_card hs
  rwa [card_image_of_injective _ e.injective] at hc

/-- Adding at most `ν|V|/4` vertices preserves fixed robust parameters.
No condition on the newly added edges is needed for the enlarged tested
range. A later minimum-degree hypothesis restores a smaller range. -/
theorem robust_after_addition (H : SimpleGraph V) (K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel K.Adj] (e : V ↪ W)
    (hembed : ∀ {u v}, H.Adj u v → K.Adj (e u) (e v))
    (ν τ : ℝ) (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hsmall : (Fintype.card W : ℝ)-Fintype.card V ≤ ν*Fintype.card V/4)
    (hrobust : IsRobustExpander H ν τ) :
    IsRobustExpander K (ν/4) (2*τ) := by
  let n : ℝ := Fintype.card V
  let N : ℝ := Fintype.card W
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hnN : n ≤ N := by
    dsimp [n,N]
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  have hτ0 : 0 ≤ τ := hν.trans hντ
  have hν1 : ν ≤ 1 := by linarith
  change N-n ≤ ν*n/4 at hsmall
  have hνn : ν*n ≤ n := by nlinarith [mul_le_mul_of_nonneg_right hν1 hn]
  have hNtwo : N ≤ 2*n := by linarith
  have hdiff : N-n ≤ τ*n := by
    have hmul := mul_le_mul_of_nonneg_right hντ hn
    nlinarith
  have hνN : ν*N ≤ 2*(ν*n) := by
    nlinarith [mul_le_mul_of_nonneg_left hNtwo hν]
  intro S hlow hupp
  change 2*τ*N ≤ (S.card : ℝ) at hlow
  change (S.card : ℝ) ≤ (1-2*τ)*N at hupp
  let T := oldPart e S
  have hbounds := oldPart_card_bounds e S
  have hupper : (T.card : ℝ) ≤ S.card := by exact_mod_cast hbounds.1
  have hlower : (S.card : ℝ)+n ≤ T.card+N := by
    dsimp [n,N,T]
    exact_mod_cast hbounds.2
  have hTlow : τ*n ≤ (T.card : ℝ) := by
    have hm := mul_nonneg hτ0 (sub_nonneg.mpr hnN)
    nlinarith
  have hTupp : (T.card : ℝ) ≤ (1-τ)*n := by
    have hm := mul_nonneg hτ0 (sub_nonneg.mpr hnN)
    nlinarith
  have hex := hrobust T hTlow hTupp
  have hmap : ∀ v ∈ robustNeighbors H ν T, e v ∈ robustNeighbors K (ν/4) S := by
    intro v hv
    rw [mem_robustNeighbors] at hv ⊢
    have hc : ((H.neighborFinset v ∩ T).card : ℝ) ≤
        (K.neighborFinset (e v) ∩ S).card := by
      exact_mod_cast old_neighbors_le H K e hembed S v
    change ν*n ≤ _ at hv
    change ν/4*N ≤ _
    nlinarith
  have hcard := card_le_card_of_injOn e hmap
    (fun _ _ _ _ h => e.injective h)
  have hcardR : ((robustNeighbors H ν T).card : ℝ) ≤
      (robustNeighbors K (ν/4) S).card := by exact_mod_cast hcard
  change (T.card : ℝ)+ν*n ≤ _ at hex
  change (S.card : ℝ)+ν/4*N ≤ _
  nlinarith

/-- A linear minimum degree restores any prescribed smaller tested range
after the enlargement. All output parameters are explicit and fixed. -/
theorem robust_after_addition_smaller_range (H : SimpleGraph V) (K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel K.Adj] (e : V ↪ W)
    (hembed : ∀ {u v}, H.Adj u v → K.Adj (e u) (e v))
    (η ν τ σ : ℝ) (hη : 0 < η) (hηone : η ≤ 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : 2*τ ≤ η/4)
    (hσ : 0 < σ) (hστ : σ ≤ 2*τ)
    (hsmall : (Fintype.card W : ℝ)-Fintype.card V ≤ ν*Fintype.card V/4)
    (hdegree : ∀ v, η*Fintype.card W ≤ (K.degree v : ℝ))
    (hrobust : IsRobustExpander H ν τ) :
    IsRobustExpander K (min (ν/4) (η*σ/2)) σ := by
  have hlarge := robust_after_addition H K e hembed ν τ hν.le hντ
    (by linarith) hsmall hrobust
  exact robust_range_reduction K η (ν/4) (2*τ) σ hη hηone
    (by positivity) hτ hσ hστ hdegree hlarge

end Overfull.Absorption
