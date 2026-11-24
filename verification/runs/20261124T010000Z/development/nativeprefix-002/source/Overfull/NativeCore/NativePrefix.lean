import Overfull.NativeCore.ExternalPalette
import Overfull.NativeCore.Completion
import Overfull.NativeCore.PrefixSelection

/-!
# Uniform native completion of all nonprotected colors

The constants are fixed before the host. Actual residual core data first
produce the whole external palette; all colors outside the protected half
reserve are then completed inside the two old cores. The remaining graph
is exactly `r/2`-regular and retains robust embedded cores. Its external
copies are precisely the selected original reserve copies. This is a
constructed partial factorization, not a factorization of the final reserve.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical NativeReserve AssignedParts FourOdd SmallCuts

set_option maxHeartbeats 1200000 in
/-- Complete every nonprotected color in the actual native residual, with
uniform parameters and exact residual external-copy identity. The final
protected regular graph is constructed but is not assumed colorable. -/
theorem exists_uniform_native_unprotected_prefix (α β ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/240)
    (hσ : 0 < σ) (hσhalf : σ < 1/2) :
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E J : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U₀ U₁ Z : Finset V) (M : Finset E)
        (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
        (N : J → Finset E) (T : Finset J) (h : ℕ) (a : ℝ)
        (C₀ : Core (residualGraph G N T) U₀)
        (C₁ : Core (residualGraph G N T) U₁),
        n₀ ≤ Fintype.card V → G.IsPerfectMatching M →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        β * Fintype.card V ≤ U₀.card → β * Fintype.card V ≤ U₁.card →
        α * Fintype.card V / 30 ≤ r → r ≤ h →
        (∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) →
        (∀ v, (residualGraph G N T).degree v = h) →
        (∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        (∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        max a ((h : ℝ)-r) ≤ δ * Fintype.card V →
        let H := residualGraph G N T
        let X := joiningCopies H (assignedLabel G M U₀ U₁ Z) ∪
          exceptionalCopies H univ Z
        ∃ (q : Fin (r/2) → Fin r)
          (W : Fin (h-r/2) → Finset {e : E // e ∉ removedCopies N T})
          (C₀' : Core (residualGraph H W univ) U₀)
          (C₁' : Core (residualGraph H W univ) U₁),
          Function.Injective q ∧
          (∀ j, H.IsPerfectMatching (W j)) ∧
          Pairwise (fun i j => Disjoint (W i) (W j)) ∧
          (∀ j, Disjoint (W j) (univ.biUnion (fun i => Q.residualBoundary N T (q i)))) ∧
          (∀ v, (residualGraph H W univ).degree v = r/2) ∧
          IsRobustExpander C₀'.graph θ σ ∧ IsRobustExpander C₁'.graph θ σ ∧
          (∀ v, ((r/2 : ℕ) : ℝ)-a ≤ (C₀'.graph.degree v : ℝ)) ∧
          (∀ v, ((r/2 : ℕ) : ℝ)-a ≤ (C₁'.graph.degree v : ℝ)) ∧
          X \ removedCopies W univ = univ.biUnion (fun i => Q.residualBoundary N T (q i)) ∧
          survivingCopies (removedCopies W univ) X =
            survivingCopies (removedCopies W univ)
              (univ.biUnion (fun i => Q.residualBoundary N T (q i))) ∧
          (survivingCopies (removedCopies W univ) X).image Subtype.val =
            univ.biUnion (fun i => Q.residualBoundary N T (q i)) := by
  have hα' : 0 < α/30 := div_pos hα (by norm_num)
  have hα1' : α/30 ≤ 1 := by linarith only [hα1]
  have hγ : 0 < α/120 := div_pos hα (by norm_num)
  have hτ' : τ ≤ (α/30)/8 := by linarith only [hτ]
  obtain ⟨ε,θ,hε,hθ,m₀,hprefix⟩ := exists_two_core_boundary_prefix
    (α/30) (α/120) ν τ σ hα' hα1' hγ hν hντ hτ' hσ hσhalf
  let η := ε*β
  have hη : 0 < η := mul_pos hε hβ
  let δ := min η (min (α/3840) (η*α/720))
  have hδ : 0 < δ := lt_min hη
    (lt_min (div_pos hα (by norm_num)) (div_pos (mul_pos hη hα) (by norm_num)))
  have hδη : δ ≤ η := min_le_left _ _
  have hδdensity : δ ≤ α/3840 := (min_le_right _ _).trans (min_le_left _ _)
  have hδsupport : δ ≤ η*α/720 := (min_le_right _ _).trans (min_le_right _ _)
  let n₀ := max 1 (max (Nat.ceil (20/η))
    (max (Nat.ceil (120/α)) (Nat.ceil ((m₀ : ℝ)/β))))
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  refine ⟨δ,θ,hδ,hθ,n₀,hn₀,?_⟩
  intro V E J _ _ G U₀ U₁ Z M r Q N T h a C₀ C₁ hn hM h01 h0Z h1Z
    hcover hZ hU₀ hU₁ hr hrh havoid hregular hno hrob₀ hrob₁ hcore₀ hcore₁ herror
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let n := Fintype.card V
  have hnpos : 0 < n := lt_of_lt_of_le hn₀ hn
  have hn20 : Nat.ceil (20/η) ≤ n := by dsimp only [n₀] at hn; omega
  have hn120 : Nat.ceil (120/α) ≤ n := by dsimp only [n₀] at hn; omega
  have hnm : Nat.ceil ((m₀ : ℝ)/β) ≤ n := by dsimp only [n₀] at hn; omega
  have hlarge : 20/η ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn20)
  have hlarge' : 120/α ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn120)
  have hmβ : (m₀ : ℝ) ≤ β*n := by
    have hh := (div_le_iff₀ hβ).mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr hnm))
    nlinarith only [hh]
  have hm₀ : m₀ ≤ U₀.card := by exact_mod_cast hmβ.trans hU₀
  have hm₁ : m₀ ≤ U₁.card := by exact_mod_cast hmβ.trans hU₁
  have hε₀ : η*n ≤ ε*U₀.card := by
    have hh := mul_le_mul_of_nonneg_left hU₀ hε.le
    dsimp only [η]
    nlinarith only [hh]
  have hε₁ : η*n ≤ ε*U₁.card := by
    have hh := mul_le_mul_of_nonneg_left hU₁ hε.le
    dsimp only [η]
    nlinarith only [hh]
  have haη : a ≤ η*n := ((le_max_left _ _).trans herror).trans
    (mul_le_mul_of_nonneg_right hδη (Nat.cast_nonneg n))
  have hdensity : α*n/30 ≤ (h : ℝ) := hr.trans (Nat.cast_le.mpr hrh)
  have hdense₀ : (α/30)*U₀.card ≤ (h : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_univ U₀)) hα'.le
    nlinarith only [hh,hdensity]
  have hdense₁ : (α/30)*U₁.card ≤ (h : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_univ U₁)) hα'.le
    nlinarith only [hh,hdensity]
  obtain ⟨q,f,F,hq,hf,hFm,hFd,hpres,hFZ,hFparity,hFcover,hout₀,hout₁,hsize,_hload₀,_hload₁⟩ :=
    exists_native_external_palette_from_core_bounds G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
      r Q N T havoid h a α δ η hrh hregular hno C₀ C₁ hcore₀ hcore₁
      hα hη hnpos hdensity herror hδdensity hδsupport hlarge
  let R := fun i => Q.residualBoundary N T (q i)
  let A := univ.biUnion R
  let B := unprotectedClasses F f hf
  let X := joiningCopies H label ∪ exceptionalCopies H univ Z
  let K := H.internalOn univ U₀ ∪ H.internalOn univ U₁
  have hA₀ : Disjoint A (OneCore.coreEdges C₀) := by
    apply disjoint_left.mpr
    intro e he hc
    obtain ⟨i,_,hei⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hout₀ (f i)) ((hpres i).symm ▸ hei) hc
  have hA₁ : Disjoint A (OneCore.coreEdges C₁) := by
    apply disjoint_left.mpr
    intro e he hc
    obtain ⟨i,_,hei⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hout₁ (f i)) ((hpres i).symm ▸ hei) hc
  have hBavoid (j : Fin (h-r/2)) : Disjoint (B j) A := by
    have hh := unprotectedClasses_disjoint_reserve F f hf R hFd hpres j
    apply disjoint_left.mpr
    intro e heB heA
    exact disjoint_left.mp hh heB (by simpa only [A,mem_biUnion] using heA)
  have hroom₀ := (half_reserve_prefix_room α n r h U₀.card hα hr hrh
    (card_le_univ U₀) hlarge').2
  have hroom₁ := (half_reserve_prefix_room α n r h U₁.card hα hr hrh
    (card_le_univ U₁) hlarge').2
  obtain ⟨W,C₀',C₁',hWm,hWd,hcontains,hWA,hadded,hWreg,hrob₀',hrob₁',hdeg₀',hdeg₁'⟩ :=
    hprefix V {e : E // e ∉ removedCopies N T} H h U₀ U₁ Z C₀ C₁ a
      h01 hcover hm₀ hm₁ hrob₀ hrob₁ hdense₀ hdense₁ hregular hcore₀ hcore₁
      (haη.trans hε₀) (haη.trans hε₁) (h-r/2) B A
      (Nat.sub_le _ _) hroom₀ hroom₁
      (unprotectedClasses_matching H F f hf hFm)
      (unprotectedClasses_disjoint F f hf hFd)
      (fun j => hFZ (unprotectedColor f hf j))
      (fun j => hout₀ (unprotectedColor f hf j))
      (fun j => hout₁ (unprotectedColor f hf j))
      (fun j => (hsize (unprotectedColor f hf j)).trans hε₀)
      (fun j => (hsize (unprotectedColor f hf j)).trans hε₁)
      (fun j => (hFparity (unprotectedColor f hf j)).1)
      (fun j => (hFparity (unprotectedColor f hf j)).2)
      hBavoid hA₀ hA₁
  have hX : X = univ.biUnion F := by
    ext e
    simpa only [X,mem_biUnion,mem_union] using (Finset.ext_iff.mp hFcover e).symm
  have hKX : Disjoint K X := by
    have hh := two_internalOn_disjoint_joining_exceptional H label U₀ U₁ Z h0Z h1Z 0 1
      (fun _ hv => assignedLabel_on_core₀ G M U₀ U₁ Z hv)
      (fun _ hv => assignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hv)
    apply disjoint_left.mpr
    intro e heK heX
    exact disjoint_left.mp hh
      (by simpa only [K,mem_union] using heK) (by simpa only [X,mem_union] using heX)
  have hadded' (j : Fin (h-r/2)) : W j ⊆ B j ∪ K := by
    intro e he
    rcases hadded j e he with heB | he₀ | he₁
    · exact mem_union_left _ heB
    · exact mem_union_right _ (mem_union_left _ he₀)
    · exact mem_union_right _ (mem_union_right _ he₁)
  have hrem := completed_prefix_external_remainder F f hf R hFd hpres
    X K (by ext e; simpa only [mem_biUnion] using Finset.ext_iff.mp hX e) hKX W
    hcontains (by intro j e he; simpa only [mem_union] using hadded' j he)
  have hsurvive := completed_prefix_surviving_external F f hf R hFd hpres
    X K (by ext e; simpa only [mem_biUnion] using Finset.ext_iff.mp hX e) hKX W
    hcontains (by intro j e he; simpa only [mem_union] using hadded' j he)
  have hremain : h-(h-r/2) = r/2 :=
    Nat.sub_sub_self ((Nat.div_le_self r 2).trans hrh)
  refine ⟨q,W,C₀',C₁',hq,hWm,hWd,hWA,?_,hrob₀',hrob₁',?_,?_,?_,?_,?_⟩
  · simpa only [hremain] using hWreg
  · simpa only [hremain] using hdeg₀'
  · simpa only [hremain] using hdeg₁'
  · ext e
    simpa only [mem_sdiff,mem_biUnion] using Finset.ext_iff.mp hrem e
  · exact hsurvive.1
  · ext e
    simpa only [mem_image,mem_biUnion] using Finset.ext_iff.mp hsurvive.2 e

end Overfull.NativeCore
