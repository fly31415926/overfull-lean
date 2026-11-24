import Overfull.Dense.LinkFlows
import Overfull.Dense.GeometricCorrection

/-!
# Fractional triangle decompositions of dense locally balanced graphs

This file proves the actual graph correction and applies geometric summation.
-/

namespace Overfull
namespace TripartiteGraph

open Finset Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- Intersecting with a set removes at most the vertices outside that set. -/
theorem card_le_inter_add_missing {V : Type*} [Fintype V] (S T : Finset V) :
    (S.card : ℝ) ≤ (S ∩ T).card + ((Fintype.card V : ℝ) - T.card) := by
  have hpart := Finset.card_inter_add_card_sdiff S T
  have hsub : S \ T ⊆ Tᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  have hbound := Finset.card_le_card hsub
  have hcomp := Finset.card_compl_add_card T
  have h : S.card + T.card ≤ (S ∩ T).card + Fintype.card V := by omega
  have hr : (S.card : ℝ) + T.card ≤ (S ∩ T).card + Fintype.card V := by exact_mod_cast h
  linarith

/-- A uniform coordinate bound controls a sum over any finite set. -/
theorem abs_sum_le_card_mul {V : Type*} (S : Finset V) (f : V → ℝ) (d : ℝ)
    (hf : ∀ v ∈ S, |f v| ≤ d) : |∑ v ∈ S, f v| ≤ S.card * d := by
  calc
    _ ≤ ∑ v ∈ S, |f v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, d := Finset.sum_le_sum hf
    _ = _ := by simp

theorem third_part_bounds (η ε : ℝ) (hη : 0 < η) (hε : ε ≤ 1)
    (hG : G.DensityConditions η ε) (hm : 0 < Fintype.card A) :
    (0 : ℝ) < Fintype.card W ∧
    (Fintype.card A : ℝ) / 2 ≤ Fintype.card W ∧
    (Fintype.card W : ℝ) ≤ 2 * Fintype.card A := by
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hm
  have hdeg := hG.degreeA a
  have hbal := hG.localBalance.1 a
  have hneighW : ((G.neighborsWA a).card : ℝ) ≤ Fintype.card W := by
    exact_mod_cast Finset.card_le_univ (G.neighborsWA a)
  have hneighB : ((G.neighborsB a).card : ℝ) ≤ Fintype.card A := by
    rw [hG.partSizes]
    exact_mod_cast Finset.card_le_univ (G.neighborsB a)
  have hbalReal : ((G.neighborsB a).card : ℝ) = (G.neighborsWA a).card := by exact_mod_cast hbal
  have hmiss := hG.missingA a
  have hmReal : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm
  have hprod := mul_nonneg hη.le hmReal.le
  have hεprod := mul_le_mul_of_nonneg_right hε hmReal.le
  constructor
  · nlinarith only [hdeg,hbalReal,hneighW,hmReal,hprod]
  constructor
  · nlinarith only [hdeg,hbalReal,hneighW,hprod]
  · nlinarith only [hmiss,hbalReal,hneighB,hεprod]

theorem common_colors_bounds (η ε : ℝ) (hG : G.DensityConditions η ε)
    (a : A) (b : B) :
    (Fintype.card W : ℝ) - 2 * ε * Fintype.card A ≤
      ((G.neighborsWA a ∩ G.neighborsWB b).card : ℝ) ∧
    ((G.neighborsWA a ∩ G.neighborsWB b).card : ℝ) ≤ Fintype.card W := by
  have h := card_le_inter_add_missing (G.neighborsWA a) (G.neighborsWB b)
  refine ⟨by linarith [hG.missingA a,hG.missingB b],?_⟩
  exact_mod_cast Finset.card_le_univ (G.neighborsWA a ∩ G.neighborsWB b)

theorem incident_triangles_A_bounds (η ε : ℝ) (hG : G.DensityConditions η ε)
    (a : A) (w : W) :
    (Fintype.card W : ℝ) - 2 * ε * Fintype.card A ≤
      ((G.neighborsB a ∩ G.linkB w).card : ℝ) ∧
    ((G.neighborsB a ∩ G.linkB w).card : ℝ) ≤ Fintype.card W := by
  have h := card_le_inter_add_missing (G.neighborsB a) (G.linkB w)
  rw [← hG.partSizes] at h
  have hbal : ((G.neighborsB a).card : ℝ) = (G.neighborsWA a).card := by
    exact_mod_cast hG.localBalance.1 a
  refine ⟨by linarith [hG.missingA a,hG.missingWB w],?_⟩
  have hsub := Finset.card_le_card
    (Finset.inter_subset_left : G.neighborsB a ∩ G.linkB w ⊆ G.neighborsB a)
  have hbound := Finset.card_le_univ (G.neighborsWA a)
  rw [hG.localBalance.1 a] at hsub
  exact_mod_cast hsub.trans hbound

theorem incident_triangles_B_bounds (η ε : ℝ) (hG : G.DensityConditions η ε)
    (b : B) (w : W) :
    (Fintype.card W : ℝ) - 2 * ε * Fintype.card A ≤
      ((G.neighborsA b ∩ G.linkA w).card : ℝ) ∧
    ((G.neighborsA b ∩ G.linkA w).card : ℝ) ≤ Fintype.card W := by
  have h := card_le_inter_add_missing (G.neighborsA b) (G.linkA w)
  have hbal : ((G.neighborsA b).card : ℝ) = (G.neighborsWB b).card := by
    exact_mod_cast hG.localBalance.2.1 b
  refine ⟨by linarith [hG.missingB b,hG.missingWA w],?_⟩
  have hsub := Finset.card_le_card
    (Finset.inter_subset_left : G.neighborsA b ∩ G.linkA w ⊆ G.neighborsA b)
  have hbound := Finset.card_le_univ (G.neighborsWB b)
  rw [hG.localBalance.2.1 b] at hsub
  exact_mod_cast hsub.trans hbound

/-- The incidence of a uniform triangle weight is its actual triangle count
multiplied by that weight. -/
theorem uniform_incidence_ab (c : ℝ) (a : A) (b : B) (hab : G.ab a b) :
    G.incidence (fun _ => c) (abPos a b) =
      ((G.neighborsWA a ∩ G.neighborsWB b).card : ℝ) * c := by
  simp only [incidence,abPos,extendTriangle,IsTriangle,hab,true_and]
  simp only [dite_eq_ite]
  rw [← Finset.sum_filter]
  have heq : univ.filter (fun w => G.aw a w ∧ G.bw b w) =
      G.neighborsWA a ∩ G.neighborsWB b := by ext w; simp [neighborsWA,neighborsWB]
  rw [heq]
  simp

theorem uniform_incidence_aw (c : ℝ) (a : A) (w : W) (haw : G.aw a w) :
    G.incidence (fun _ => c) (awPos a w) =
      ((G.neighborsB a ∩ G.linkB w).card : ℝ) * c := by
  simp only [incidence,awPos,extendTriangle,IsTriangle,haw,true_and]
  simp only [dite_eq_ite]
  rw [← Finset.sum_filter]
  have heq : univ.filter (fun b => G.ab a b ∧ G.bw b w) =
      G.neighborsB a ∩ G.linkB w := by ext b; simp [neighborsB,linkB]
  rw [heq]
  simp

theorem uniform_incidence_bw (c : ℝ) (b : B) (w : W) (hbw : G.bw b w) :
    G.incidence (fun _ => c) (bwPos b w) =
      ((G.neighborsA b ∩ G.linkA w).card : ℝ) * c := by
  simp only [incidence,bwPos,extendTriangle,IsTriangle,hbw,and_true]
  simp only [dite_eq_ite]
  rw [← Finset.sum_filter]
  have heq : univ.filter (fun a => G.ab a b ∧ G.aw a w) =
      G.neighborsA b ∩ G.linkA w := by ext a; simp [neighborsA,linkA]
  rw [heq]
  simp

/-- Spread an edge weighting on the first two parts uniformly over its triangles. -/
noncomputable def spread (r : EdgePosition (A := A) (B := B) (W := W) → ℝ) (k : ℝ) :
    G.Triangle → ℝ := fun t => r (abPos t.val.1 t.val.2.1) / k

theorem spread_incidence_ab (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (k : ℝ) (a : A) (b : B) (hab : G.ab a b) :
    G.incidence (G.spread r k) (abPos a b) =
      ((G.neighborsWA a ∩ G.neighborsWB b).card : ℝ) * (r (abPos a b) / k) := by
  simp only [incidence,abPos,extendTriangle,spread,IsTriangle,hab,true_and,dite_eq_ite]
  rw [← Finset.sum_filter]
  have heq : univ.filter (fun w => G.aw a w ∧ G.bw b w) =
      G.neighborsWA a ∩ G.neighborsWB b := by ext w; simp [neighborsWA,neighborsWB]
  rw [heq]
  simp

theorem spread_incidence_aw (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : ∀ a b, ¬ G.ab a b → r (abPos a b) = 0)
    (k : ℝ) (a : A) (w : W) (haw : G.aw a w) :
    G.incidence (G.spread r k) (awPos a w) =
      (∑ b ∈ G.linkB w, r (abPos a b)) / k := by
  rw [Finset.sum_div]
  simp only [incidence,awPos,extendTriangle,spread,linkB,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  have hz : ¬ G.ab a b → r (Sum.inl (a,b)) = 0 := hr a b
  by_cases hab : G.ab a b <;> by_cases hbw : G.bw b w <;>
    simp [IsTriangle,hab,haw,hbw,hz,abPos]

theorem spread_incidence_bw (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : ∀ a b, ¬ G.ab a b → r (abPos a b) = 0)
    (k : ℝ) (b : B) (w : W) (hbw : G.bw b w) :
    G.incidence (G.spread r k) (bwPos b w) =
      (∑ a ∈ G.linkA w, r (abPos a b)) / k := by
  rw [Finset.sum_div]
  simp only [incidence,bwPos,extendTriangle,spread,linkA,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have hz : ¬ G.ab a b → r (Sum.inl (a,b)) = 0 := hr a b
  by_cases hab : G.ab a b <;> by_cases haw : G.aw a w <;>
    simp [IsTriangle,hab,haw,hbw,hz,abPos]

private theorem scaled_missing_bound (m k ε d s : ℝ)
    (hk : 0 < k) (hε : 0 ≤ ε) (hd : 0 ≤ d) (hmk : m ≤ 2*k)
    (hs : s ≤ 2*ε*m) : s*d/k ≤ 4*ε*d := by
  apply (div_le_iff₀ hk).mpr
  have h₁ := mul_le_mul_of_nonneg_right hs hd
  have h₂ := mul_le_mul_of_nonneg_left hmk
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε) hd)
  nlinarith only [h₁,h₂]

/-- The second correction contracts an edge weighting supported on the first
bipartite pair and having zero row and column sums. -/
theorem spread_residual_bound (η ε : ℝ) (hε : 0 ≤ ε)
    (hG : G.DensityConditions η ε)
    (hk : (0 : ℝ) < Fintype.card W)
    (hmk : (Fintype.card A : ℝ) ≤ 2 * Fintype.card W)
    (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : G.BalancedWeight r)
    (hza : ∀ a w, r (awPos a w) = 0) (hzb : ∀ b w, r (bwPos b w) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hbound : ∀ e, |r e| ≤ d) :
    ∀ e, |r e - G.incidence (G.spread r (Fintype.card W)) e| ≤ 4 * ε * d := by
  have hnonneg : 0 ≤ 4*ε*d := by positivity
  have hrow (a : A) : ∑ b, r (abPos a b) = 0 := by
    rw [hr.2.2.2.1 a]
    simp [hza]
  have hcol (b : B) : ∑ a, r (abPos a b) = 0 := by
    rw [hr.2.2.2.2.1 b]
    simp [hzb]
  have hmissB (w : W) : ((G.linkB w)ᶜ.card : ℝ) ≤ ε * Fintype.card A := by
    have hcomp : ((G.linkB w)ᶜ.card : ℝ) + (G.linkB w).card = Fintype.card A := by
      rw [hG.partSizes]
      exact_mod_cast Finset.card_compl_add_card (G.linkB w)
    linarith [hG.missingWB w]
  have hmissA (w : W) : ((G.linkA w)ᶜ.card : ℝ) ≤ ε * Fintype.card A := by
    have hcomp : ((G.linkA w)ᶜ.card : ℝ) + (G.linkA w).card = Fintype.card A := by
      exact_mod_cast Finset.card_compl_add_card (G.linkA w)
    linarith [hG.missingWA w]
  intro e
  rcases e with ab | aw | bw
  · rcases ab with ⟨a,b⟩
    change |r (abPos a b) - G.incidence (G.spread r (Fintype.card W)) (abPos a b)| ≤ _
    by_cases hab : G.ab a b
    · rw [G.spread_incidence_ab r (Fintype.card W) a b hab]
      let t : ℝ := (G.neighborsWA a ∩ G.neighborsWB b).card
      have ht := G.common_colors_bounds η ε hG a b
      have ht0 : 0 ≤ (Fintype.card W : ℝ) - t := sub_nonneg.mpr ht.2
      have heq : r (abPos a b) - t * (r (abPos a b) / Fintype.card W) =
          ((Fintype.card W : ℝ)-t) * r (abPos a b) / Fintype.card W := by
        field_simp
      change |r (abPos a b) - t * (r (abPos a b) / Fintype.card W)| ≤ _
      rw [heq,abs_div,abs_mul,abs_of_nonneg ht0,abs_of_pos hk]
      calc
        _ ≤ (((Fintype.card W : ℝ)-t) * d) / Fintype.card W :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound _) ht0) hk.le
        _ ≤ 4*ε*d := scaled_missing_bound _ _ _ _ _ hk hε hd hmk (by linarith [ht.1])
    · have hz := (G.incidence_balanced (G.spread r (Fintype.card W))).1 a b hab
      rw [hr.1 a b hab,hz,sub_self,abs_zero]
      exact hnonneg
  · rcases aw with ⟨a,w⟩
    change |r (awPos a w) - G.incidence (G.spread r (Fintype.card W)) (awPos a w)| ≤ _
    rw [hza]
    by_cases haw : G.aw a w
    · rw [G.spread_incidence_aw r hr.1 (Fintype.card W) a w haw]
      have hsplit := Finset.sum_add_sum_compl (G.linkB w) (fun b => r (abPos a b))
      rw [hrow] at hsplit
      have heq : -(∑ b ∈ G.linkB w, r (abPos a b)) =
          ∑ b ∈ (G.linkB w)ᶜ, r (abPos a b) := by linarith
      rw [zero_sub,← neg_div,heq,abs_div,abs_of_pos hk]
      calc
        _ ≤ (((G.linkB w)ᶜ.card : ℝ)*d) / Fintype.card W :=
          div_le_div_of_nonneg_right
            (abs_sum_le_card_mul _ _ d (fun b _ => hbound (abPos a b))) hk.le
        _ ≤ 4*ε*d := scaled_missing_bound _ _ _ _ _ hk hε hd hmk
          (by nlinarith [hmissB w, mul_nonneg hε (Nat.cast_nonneg (Fintype.card A))])
    · have hz := (G.incidence_balanced (G.spread r (Fintype.card W))).2.1 a w haw
      rw [hz,sub_self,abs_zero]
      exact hnonneg
  · rcases bw with ⟨b,w⟩
    change |r (bwPos b w) - G.incidence (G.spread r (Fintype.card W)) (bwPos b w)| ≤ _
    rw [hzb]
    by_cases hbw : G.bw b w
    · rw [G.spread_incidence_bw r hr.1 (Fintype.card W) b w hbw]
      have hsplit := Finset.sum_add_sum_compl (G.linkA w) (fun a => r (abPos a b))
      rw [hcol] at hsplit
      have heq : -(∑ a ∈ G.linkA w, r (abPos a b)) =
          ∑ a ∈ (G.linkA w)ᶜ, r (abPos a b) := by linarith
      rw [zero_sub,← neg_div,heq,abs_div,abs_of_pos hk]
      calc
        _ ≤ (((G.linkA w)ᶜ.card : ℝ)*d) / Fintype.card W :=
          div_le_div_of_nonneg_right
            (abs_sum_le_card_mul _ _ d (fun a _ => hbound (abPos a b))) hk.le
        _ ≤ 4*ε*d := scaled_missing_bound _ _ _ _ _ hk hε hd hmk
          (by nlinarith [hmissA w, mul_nonneg hε (Nat.cast_nonneg (Fintype.card A))])
    · have hz := (G.incidence_balanced (G.spread r (Fintype.card W))).2.2.1 b w hbw
      rw [hz,sub_self,abs_zero]
      exact hnonneg

private theorem uniform_deficit_bound (m k ε t : ℝ)
    (hk : 0 < k) (hε : 0 ≤ ε) (hmk : m ≤ 2*k)
    (htlo : k-2*ε*m ≤ t) (hthi : t ≤ k) : |1-t/k| ≤ 4*ε := by
  have hhi : t/k ≤ 1 := (div_le_iff₀ hk).mpr (by simpa using hthi)
  have hlo : 1-4*ε ≤ t/k := by
    apply (le_div_iff₀ hk).mpr
    have hm := mul_le_mul_of_nonneg_left hmk hε
    nlinarith only [htlo,hm]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The uniform weighting has small deficit on every actual edge. -/
theorem uniform_residual_bound (η ε : ℝ) (hε : 0 ≤ ε)
    (hG : G.DensityConditions η ε)
    (hk : (0 : ℝ) < Fintype.card W)
    (hmk : (Fintype.card A : ℝ) ≤ 2 * Fintype.card W) :
    ∀ e, |G.edgeOne e - G.incidence (fun _ => 1/(Fintype.card W : ℝ)) e| ≤ 4*ε := by
  have hnonneg : 0 ≤ 4*ε := by positivity
  intro e
  rcases e with ab | aw | bw
  · rcases ab with ⟨a,b⟩
    change |G.edgeOne (abPos a b) - G.incidence _ (abPos a b)| ≤ _
    by_cases hab : G.ab a b
    · rw [G.uniform_incidence_ab _ a b hab]
      simp only [edgeOne,abPos,hab,if_true,mul_one_div]
      exact uniform_deficit_bound _ _ _ _ hk hε hmk
        (G.common_colors_bounds η ε hG a b).1 (G.common_colors_bounds η ε hG a b).2
    · have hz := (G.incidence_balanced (fun _ => 1/(Fintype.card W : ℝ))).1 a b hab
      rw [hz]
      simpa [edgeOne,abPos,hab] using hnonneg
  · rcases aw with ⟨a,w⟩
    change |G.edgeOne (awPos a w) - G.incidence _ (awPos a w)| ≤ _
    by_cases haw : G.aw a w
    · rw [G.uniform_incidence_aw _ a w haw]
      simp only [edgeOne,awPos,haw,if_true,mul_one_div]
      exact uniform_deficit_bound _ _ _ _ hk hε hmk
        (G.incident_triangles_A_bounds η ε hG a w).1
        (G.incident_triangles_A_bounds η ε hG a w).2
    · have hz := (G.incidence_balanced (fun _ => 1/(Fintype.card W : ℝ))).2.1 a w haw
      rw [hz]
      simpa [edgeOne,awPos,haw] using hnonneg
  · rcases bw with ⟨b,w⟩
    change |G.edgeOne (bwPos b w) - G.incidence _ (bwPos b w)| ≤ _
    by_cases hbw : G.bw b w
    · rw [G.uniform_incidence_bw _ b w hbw]
      simp only [edgeOne,bwPos,hbw,if_true,mul_one_div]
      exact uniform_deficit_bound _ _ _ _ hk hε hmk
        (G.incident_triangles_B_bounds η ε hG b w).1
        (G.incident_triangles_B_bounds η ε hG b w).2
    · have hz := (G.incidence_balanced (fun _ => 1/(Fintype.card W : ℝ))).2.2.1 b w hbw
      rw [hz]
      simpa [edgeOne,bwPos,hbw] using hnonneg

/-- Every triangle correction preserves weighted local balance. -/
theorem balanced_sub_incidence (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : G.BalancedWeight r) (p : G.Triangle → ℝ) :
    G.BalancedWeight (r - G.incidence p) :=
  (G.balancedSpace).sub_mem hr (G.incidence_balanced p)

/-- A bound on individual triangle weights bounds their incidence at an AB edge. -/
theorem incidence_ab_abs_le (p : G.Triangle → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hp : ∀ t, |p t| ≤ d) (a : A) (b : B) :
    |G.incidence p (abPos a b)| ≤ (Fintype.card W : ℝ) * d := by
  simpa [incidence,abPos] using abs_sum_le_card_mul (univ : Finset W)
    (fun w => G.extendTriangle p a b w) d
    (fun w _ => G.extendTriangle_abs_le p d hd hp a b w)

/-- After the link flows, the residual is supported on AB and remains bounded. -/
theorem first_residual_bound (η d : ℝ) (hη : 0 < η) (hd : 0 ≤ d)
    (hm : (0 : ℝ) < Fintype.card A)
    (hkm : (Fintype.card W : ℝ) ≤ 2 * Fintype.card A)
    (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : ∀ e, |r e| ≤ d) (p : G.Triangle → ℝ)
    (hpA : ∀ a w, G.incidence p (awPos a w) = r (awPos a w))
    (hpB : ∀ b w, G.incidence p (bwPos b w) = r (bwPos b w))
    (hp : ∀ t, |p t| ≤ 2*d/(η*(Fintype.card A : ℝ))) :
    ∀ e, |(r - G.incidence p) e| ≤ (1+4/η)*d := by
  have hP : 0 ≤ 2*d/(η*(Fintype.card A : ℝ)) := by positivity
  have hmult : (Fintype.card W : ℝ) * (2*d/(η*(Fintype.card A : ℝ))) ≤ 4/η*d := by
    calc
      _ ≤ (2*(Fintype.card A : ℝ)) * (2*d/(η*(Fintype.card A : ℝ))) :=
        mul_le_mul_of_nonneg_right hkm hP
      _ = _ := by field_simp; ring
  have hM : 0 ≤ (1+4/η)*d := by positivity
  intro e
  rcases e with ab | aw | bw
  · rcases ab with ⟨a,b⟩
    change |r (abPos a b) - G.incidence p (abPos a b)| ≤ _
    have h := abs_sub (r (abPos a b)) (G.incidence p (abPos a b))
    have hinc := G.incidence_ab_abs_le p _ hP hp a b
    nlinarith only [h,hr (abPos a b),hinc,hmult]
  · rcases aw with ⟨a,w⟩
    change |r (awPos a w) - G.incidence p (awPos a w)| ≤ _
    rw [hpA,sub_self,abs_zero]
    exact hM
  · rcases bw with ⟨b,w⟩
    change |r (bwPos b w) - G.incidence p (bwPos b w)| ≤ _
    rw [hpB,sub_self,abs_zero]
    exact hM

/-- The graph correction from Lemma 5.7. Both its incidence equations and
its contraction estimate are obtained from the actual graph hypotheses. -/
theorem exists_triangle_correction (η ε : ℝ)
    (hη : 0 < η) (hε : 0 ≤ ε) (hεη : ε ≤ η) (hε1 : ε ≤ 1)
    (hmNat : 0 < Fintype.card A) (hG : G.DensityConditions η ε)
    (r : EdgePosition (A := A) (B := B) (W := W) → ℝ) (hr : G.BalancedWeight r)
    (d : ℝ) (hd : 0 ≤ d) (hbound : ∀ e, |r e| ≤ d) :
    ∃ p : G.Triangle → ℝ,
      (∀ t, |p t| ≤ ((2+10/η)/(Fintype.card A : ℝ))*d) ∧
      ∀ e, |r e - G.incidence p e| ≤ 4*ε*(1+4/η)*d := by
  have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast hmNat
  obtain ⟨hk,hmhalf,hkm⟩ := G.third_part_bounds η ε hη hε1 hG hmNat
  have hmk : (Fintype.card A : ℝ) ≤ 2 * Fintype.card W := by linarith
  obtain ⟨p,hpA,hpB,hp⟩ := G.exists_link_correction η ε hη hεη hmNat hG r hr d hd hbound
  let r₀ := r - G.incidence p
  let δ : ℝ := (1+4/η)*d
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hr₀ : G.BalancedWeight r₀ := G.balanced_sub_incidence r hr p
  have hr₀A (a : A) (w : W) : r₀ (awPos a w) = 0 := by simp [r₀,hpA]
  have hr₀B (b : B) (w : W) : r₀ (bwPos b w) = 0 := by simp [r₀,hpB]
  have hr₀bound : ∀ e, |r₀ e| ≤ δ :=
    G.first_residual_bound η d hη hd hm hkm r hbound p hpA hpB hp
  let q := G.spread r₀ (Fintype.card W)
  have hq (t : G.Triangle) : |q t| ≤ δ/(Fintype.card W : ℝ) := by
    dsimp [q,spread]
    rw [abs_div,abs_of_pos hk]
    exact div_le_div_of_nonneg_right (hr₀bound _) hk.le
  have hquot : δ/(Fintype.card W : ℝ) ≤ 2*δ/(Fintype.card A : ℝ) := by
    apply (div_le_div_iff₀ hk hm).mpr
    have h := mul_le_mul_of_nonneg_left hmk hδ
    nlinarith only [h]
  have hconstant : 2*d/(η*(Fintype.card A : ℝ)) + 2*δ/(Fintype.card A : ℝ) =
      ((2+10/η)/(Fintype.card A : ℝ))*d := by
    dsimp [δ]
    field_simp
    ring
  refine ⟨p+q,?_,?_⟩
  · intro t
    have h := abs_add_le (p t) (q t)
    change |p t+q t| ≤ _
    linarith [hp t,hq t]
  · intro e
    have hspread := G.spread_residual_bound η ε hε hG hk hmk r₀ hr₀ hr₀A hr₀B δ hδ hr₀bound e
    have hmap : G.incidence (p+q) = G.incidence p + G.incidence q :=
      G.incidenceLinear.map_add p q
    rw [hmap]
    have heq : r e - (G.incidence p + G.incidence q) e = r₀ e - G.incidence q e := by
      dsimp [r₀]
      ring
    rw [heq]
    simpa only [q,δ,mul_assoc] using hspread

/-- Lemma 5.7 with its sufficient numerical error bound made explicit. -/
theorem fractional_triangles_of_small_error (η ε : ℝ)
    (hη : 0 < η) (hε : 0 ≤ ε) (hεη : ε ≤ η) (hε1 : ε ≤ 1)
    (hεcap : ε ≤ 1/(32*(2+10/η))) (hG : G.DensityConditions η ε) :
    ∃ ω : G.Triangle → ℝ,
      G.incidence ω = G.edgeOne ∧
      ∀ t, 1/(2*(Fintype.card W : ℝ)) ≤ ω t ∧ ω t ≤ 3/(2*(Fintype.card W : ℝ)) := by
  by_cases hmNat : 0 < Fintype.card A
  · have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast hmNat
    obtain ⟨hk,hmhalf,hkm⟩ := G.third_part_bounds η ε hη hε1 hG hmNat
    have hmk : (Fintype.card A : ℝ) ≤ 2 * Fintype.card W := by linarith
    let κ : ℝ := 2+10/η
    have hκ : 0 < κ := by dsimp [κ]; positivity
    have hcap : 32*κ*ε ≤ 1 := by
      have h := (le_div_iff₀ (by positivity : (0:ℝ) < 32*κ)).mp hεcap
      nlinarith only [h]
    have hfactor : 1+4/η ≤ κ := by
      have hinv : (0:ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη.le
      dsimp [κ]
      simp only [div_eq_mul_inv]
      linarith only [hinv]
    have hcontract : 4*ε*(1+4/η) ≤ (1:ℝ)/2 := by
      have h := mul_le_mul_of_nonneg_left hfactor (by positivity : (0:ℝ) ≤ 4*ε)
      nlinarith only [h,hcap]
    let C : ℝ := κ/(Fintype.card A : ℝ)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hLS : LinearMap.range G.incidenceLinear ≤ G.balancedSpace := by
      rintro r ⟨p,rfl⟩
      exact G.incidence_balanced p
    have hstep : ∀ r, r ∈ G.balancedSpace → ∀ d : ℝ, 0 ≤ d →
        (∀ e, |r e| ≤ d) → ∃ p : G.Triangle → ℝ,
          (∀ t, |p t| ≤ C*d) ∧
          ∀ e, |r e - G.incidenceLinear p e| ≤ d/2 := by
      intro r hr d hd hbound
      obtain ⟨p,hp,hres⟩ := G.exists_triangle_correction η ε hη hε hεη hε1 hmNat hG r hr d hd hbound
      refine ⟨p,hp,?_⟩
      intro e
      have hc := mul_le_mul_of_nonneg_right hcontract hd
      exact (hres e).trans (by nlinarith only [hc])
    let u : G.Triangle → ℝ := fun _ => 1/(Fintype.card W : ℝ)
    let r := G.edgeOne - G.incidence u
    have hr : r ∈ G.balancedSpace :=
      G.balanced_sub_incidence G.edgeOne (G.edgeOne_balanced hG.localBalance) u
    have hrbound : ∀ e, |r e| ≤ 4*ε := G.uniform_residual_bound η ε hε hG hk hmk
    obtain ⟨p,hpexact,hpbound⟩ := GeometricCorrection.exists_exact_correction
      G.incidenceLinear G.balancedSpace hLS C hC hstep r hr (4*ε) (by positivity) hrbound
    have hsmall : 2*C*(4*ε) ≤ 1/(2*(Fintype.card W : ℝ)) := by
      calc
        _ = (8*κ*ε)/(Fintype.card A : ℝ) := by dsimp [C]; ring
        _ ≤ (1/4)/(Fintype.card A : ℝ) :=
          div_le_div_of_nonneg_right (by linarith only [hcap]) hm.le
        _ = 1/(4*(Fintype.card A : ℝ)) := by ring
        _ ≤ 1/(2*(Fintype.card W : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith only [hkm])
    refine ⟨u+p,?_,?_⟩
    · have hadd : G.incidence (u+p) = G.incidence u + G.incidence p :=
        G.incidenceLinear.map_add u p
      rw [hadd]
      change G.incidence u + G.incidenceLinear p = G.edgeOne
      rw [hpexact]
      dsimp [r]
      abel
    · intro t
      have hb := abs_le.mp ((hpbound t).trans hsmall)
      change 1/(2*(Fintype.card W : ℝ)) ≤ 1/(Fintype.card W : ℝ)+p t ∧
        1/(Fintype.card W : ℝ)+p t ≤ 3/(2*(Fintype.card W : ℝ))
      have hone : 1/(Fintype.card W : ℝ) = 2*(1/(2*(Fintype.card W : ℝ))) := by
        field_simp
      have hthree : 3/(2*(Fintype.card W : ℝ)) = 3*(1/(2*(Fintype.card W : ℝ))) := by ring
      constructor <;> linarith only [hb.1,hb.2,hone,hthree]
  · have hzA : Fintype.card A = 0 := by omega
    have hzB : Fintype.card B = 0 := hG.partSizes.symm.trans hzA
    haveI : IsEmpty A := Fintype.card_eq_zero_iff.mp hzA
    haveI : IsEmpty B := Fintype.card_eq_zero_iff.mp hzB
    refine ⟨fun _ => 0,?_,?_⟩
    · funext e
      rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩
      · exact isEmptyElim a
      · exact isEmptyElim a
      · exact isEmptyElim b
    · intro t
      exact isEmptyElim t.val.1

end TripartiteGraph

/-- Lemma `dense:fractional`: a locally balanced simple tripartite graph
satisfying the actual density and missing-neighbor conditions has a fractional
triangle decomposition with weights between `1/(2k)` and `3/(2k)`.
The positive error threshold is chosen before the graph and all vertex types. -/
theorem dense_fractional_triangles (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
        (G : TripartiteGraph A B W) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ → G.DensityConditions η ε →
        ∃ ω : G.Triangle → ℝ,
          G.incidence ω = G.edgeOne ∧
          ∀ t, 1/(2*(Fintype.card W : ℝ)) ≤ ω t ∧
            ω t ≤ 3/(2*(Fintype.card W : ℝ)) := by
  let ε₀ : ℝ := min η (1/(32*(2+10/η)))
  have hpos : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨ε₀,hpos,?_⟩
  intro A B W _ _ _ G ε hε hsmall hG
  have hεη : ε ≤ η := hsmall.trans (min_le_left _ _)
  have hεcap : ε ≤ 1/(32*(2+10/η)) := hsmall.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith
  exact G.fractional_triangles_of_small_error η ε hη hε hεη hε1 hεcap hG

end Overfull
