import Overfull.NativeReserve.CompletionConstruction

/-!
# Reserve completion with robustness fixed before the requested error

The surviving robustness parameter is chosen before the surplus tolerance.
This permits the tolerance to depend on that robustness parameter in later
palette grouping and core completion. Every host, reserve and edge copy
is still constructed from the original hypotheses.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts CircuitPatterns ForceMatching SmallCuts
open scoped BigOperators

/-- Choose a positive surviving expansion parameter at most the prescribed
range before every requested surplus tolerance, then choose the original
error and order thresholds and construct the actual reserve completion. -/
theorem exists_uniform_native_reserve_completion_parameters (α c ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8)
    (hσ : 0 < σ) (hσhalf : σ < 1/2) (hσsmall : σ ≤ α/300) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ σ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ)
        (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁) (a : ℝ),
        n₀ ≤ Fintype.card V → α*Fintype.card V ≤ k →
        c*Fintype.card V ≤ U₀.card → c*Fintype.card V ≤ U₁.card →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        (∀ v, G.degree v = k) → (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        0 < a → a ≤ ξ*Fintype.card V →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        ∃ (r h q : ℕ) (M : Finset E) (Q : BoundaryPacking G U₀ U₁ Z M r)
          (N : Fin q → Finset E)
          (C₀' : Core (residualGraph G N univ) U₀)
          (C₁' : Core (residualGraph G N univ) U₁),
          G.IsPerfectMatching M ∧ (k : ℝ)/30 ≤ r ∧ h+q=k ∧ r≤h ∧
          (h : ℝ)-r ≤ δ*Fintype.card V ∧
          (∀ j, G.IsPerfectMatching (N j)) ∧
          Pairwise (fun i j => Disjoint (N i) (N j)) ∧
          (∀ j, Disjoint (N j) (removedCopies Q.boundary univ)) ∧
          (∀ v, (residualGraph G N univ).degree v = h) ∧
          (∀ X : Finset V, ¬ (residualGraph G N univ).IsOverfull h X) ∧
          IsRobustExpander C₀'.graph θ σ ∧ IsRobustExpander C₁'.graph θ σ ∧
          (∀ v, (h : ℝ)-a ≤ (C₀'.graph.degree v : ℝ)) ∧
          (∀ v, (h : ℝ)-a ≤ (C₁'.graph.degree v : ℝ)) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := pack_original_core α (α/30) ν τ σ
    hα hα1 (by positivity) hν hντ hτ hσ hσhalf
  refine ⟨min θ σ, lt_min hθ hσ, min_le_right _ _, ?_⟩
  intro δ hδ
  obtain ⟨η, ξ, hη, hη1, hξ, _hξ1, nSetup, hnSetup, hparams⟩ :=
    exists_completion_setup_parameters α c ε (δ/2) hα hc hε (by positivity) m₀
  obtain ⟨nLarge, hnLarge⟩ := exists_nat_gt (3/(θ^2*c^2))
  refine ⟨min ξ (α/300), lt_min hξ (by positivity),
    max nSetup nLarge, hnSetup.trans (le_max_left _ _), ?_⟩
  intro V E _ _ G k U₀ U₁ Z C₀ C₁ a hn hdensity hsize₀ hsize₁
    h01 h0Z h1Z hcover hZ hregular hno hrobust₀ hrobust₁ ha haSmall hdegree₀ hdegree₁
  have hnSetup' : nSetup ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnLarge' : nLarge ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V from (by omega))
  have hu₀ : U₀.card ≤ Fintype.card V := card_le_univ _
  have hu₁ : U₁.card ≤ Fintype.card V := card_le_univ _
  have haξ : a ≤ ξ*Fintype.card V := haSmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  obtain ⟨hk30, hm₀, hfoot₀, haCore₀, haOrder, hdensity₀, _haDegree, hlater₀⟩ :=
    hparams (Fintype.card V) U₀.card k a hnSetup' hsize₀ hu₀ hdensity ha.le haξ
  obtain ⟨_hk30', hm₁, hfoot₁, haCore₁, _haOrder', hdensity₁, _haDegree', hlater₁⟩ :=
    hparams (Fintype.card V) U₁.card k a hnSetup' hsize₁ hu₁ hdensity ha.le haξ
  obtain ⟨r, h, M, Q, m, B, hM, hr, hcount, hrh, hupper,
    hBmatching, hBdisj, hBavoid, hBcover, hBpool, hBsize, hBprops, hBodd, hBeven⟩ :=
    native_boundary_reserve_selection G k hk30 hregular hno U₀ U₁ Z C₀ C₁
      h01 h0Z h1Z hcover hZ a η ha hη hη1 hdegree₀ hdegree₁
  let q := ∑ p, m p
  let F (j : Fin q) := B (copyEnumeration m j)
  have hqk : q ≤ k := by dsimp [q]; omega
  have hkh : k-q=h := by dsimp [q]; omega
  obtain ⟨_hretained₀, hhorizon₀, hmargin₀, _hretainedCore₀⟩ :=
    hlater₀ r h q hr hrh hcount hupper
  obtain ⟨_hretained₁, hhorizon₁, _hmargin₁, _hretainedCore₁⟩ :=
    hlater₁ r h q hr hrh hcount hupper
  have hFmatching (j : Fin q) : G.IsMatching (F j) := hBmatching _
  have hFdisj : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    exact hBdisj _ _ (fun he => hij ((copyEnumeration m).injective he))
  have hFpool (j : Fin q) : ∀ e ∈ F j, ∃ p, e ∈ poolCopies G U₀ U₁ Z p := hBpool _
  have hFsize (j : Fin q) : (F j).card ≤ 3 := hBsize _
  have hout₀ (j : Fin q) : Disjoint (F j) (OneCore.coreEdges C₀) :=
    boundary_disjoint_core G (F j) U₀ U₁ Z U₀ h01 h0Z h1Z (Or.inl rfl) C₀ (hFpool j)
  have hout₁ (j : Fin q) : Disjoint (F j) (OneCore.coreEdges C₁) :=
    boundary_disjoint_core G (F j) U₀ U₁ Z U₁ h01 h0Z h1Z (Or.inr rfl) C₁ (hFpool j)
  obtain ⟨P₀⟩ := hpack V E G U₀ C₀ k a hm₀ hrobust₀ hdensity₀ hregular hdegree₀
    haCore₀ hfoot₀ q F hhorizon₀ hFdisj hout₀ hFsize (fun j => (hBprops _).2.1)
  obtain ⟨P₁⟩ := hpack V E G U₁ C₁ k a hm₁ hrobust₁ hdensity₁ hregular hdegree₁
    haCore₁ hfoot₁ q F hhorizon₁ hFdisj hout₁ hFsize (fun j => (hBprops _).2.2)
  have hApool : ∀ e ∈ removedCopies Q.boundary univ,
      ∃ p, e ∈ poolCopies G U₀ U₁ Z p := by
    intro e he
    obtain ⟨j, _hj, he⟩ := (mem_removedCopies Q.boundary univ e).mp he
    exact compressedBoundary_exists_pool G (Q.parent j) U₀ U₁ Z hcover he
  let N (j : Fin q) := completedBoundary C₀ C₁ (F j) (P₀.matching j) (P₁.matching j)
  obtain ⟨hNperfect, hNdisj, hNavoid, hFN, hadded, _hpoolExact⟩ :=
    glue_two_core_packings C₀ C₁ Z h01 h0Z h1Z hcover F hFmatching hFdisj
      (fun j => hBcover _) hFpool (removedCopies Q.boundary univ)
      (fun j => hBavoid _) hApool P₀ P₁
  have hremoved₀ (e : C₀.graph.edgeSet) : C₀.edgeMap e ∈ removedCopies N univ ↔
      ∃ j : Fin q, e.val ∈ (P₀.matching j).edgeSet := by
    simp only [mem_removedCopies, mem_univ, true_and]
    exact exists_congr (fun j => completedBoundary_core₀_copy_iff C₀ C₁ h01
      (F j) (hout₀ j) (P₀.matching j) (P₁.matching j) e)
  have hremoved₁ (e : C₁.graph.edgeSet) : C₁.edgeMap e ∈ removedCopies N univ ↔
      ∃ j : Fin q, e.val ∈ (P₁.matching j).edgeSet := by
    simp only [mem_removedCopies, mem_univ, true_and]
    exact exists_congr (fun j => completedBoundary_core₁_copy_iff C₀ C₁ h01
      (F j) (hout₁ j) (P₀.matching j) (P₁.matching j) e)
  let C₀' : Core (residualGraph G N univ) U₀ :=
    packingRemainderCore C₀ P₀ (removedCopies N univ) hremoved₀
  let C₁' : Core (residualGraph G N univ) U₁ :=
    packingRemainderCore C₁ P₁ (removedCopies N univ) hremoved₁
  have hRrobust₀ : IsRobustExpander C₀'.graph θ σ :=
    packingRemainderCore_robust C₀ P₀ (removedCopies N univ) hremoved₀
  have hRrobust₁ : IsRobustExpander C₁'.graph θ σ :=
    packingRemainderCore_robust C₁ P₁ (removedCopies N univ) hremoved₁
  have hRdegree₀ (v : U₀) : (h : ℝ)-a ≤ (C₀'.graph.degree v : ℝ) := by
    have hd := packingRemainderCore_degree_lower C₀ P₀ (removedCopies N univ)
      hremoved₀ k a hqk hdegree₀ v
    simpa only [hkh] using hd
  have hRdegree₁ (v : U₁) : (h : ℝ)-a ≤ (C₁'.graph.degree v : ℝ) := by
    have hd := packingRemainderCore_degree_lower C₁ P₁ (removedCopies N univ)
      hremoved₁ k a hqk hdegree₁ v
    simpa only [hkh] using hd
  have hRregular (v : V) : (residualGraph G N univ).degree v = h := by
    have hd := residual_regular G hregular N univ
      (fun _ _ _ _ hij => hNdisj hij) (fun j _ => hNperfect j) v
    simpa only [card_univ, Fintype.card_fin, hkh] using hd
  have hreindex : removedCopies F univ = removedCopies B univ := by
    ext e
    simp only [mem_removedCopies, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨copyEnumeration m j, hj⟩
    · rintro ⟨b, hb⟩
      obtain ⟨j, rfl⟩ := (copyEnumeration m).surjective b
      exact ⟨j, hb⟩
  have hFodd : ∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=1 →
      h ≤ (residualGraph G F univ).cutSize X := by
    intro X hX hp
    rw [residual_cutSize, hreindex, ← residual_cutSize G B univ X]
    exact hBodd X hX hp
  have hFeven : ∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=0 →
      2*a ≤ ((residualGraph G F univ).cutSize X : ℝ) ∨
        G.cutEdges X \ removedCopies F univ = G.cutEdges X := by
    intro X hX hp
    rw [residual_cutSize, hreindex, ← residual_cutSize G B univ X]
    exact hBeven X hX hp
  obtain ⟨hwhole, hcases⟩ := completed_whole_cut_certificates G U₀ U₁ Z
    h01 h0Z h1Z F N univ (fun j _ => hFN j) (fun j _ => hadded j) h a hFodd hFeven
  have hU₀pos : 0 < U₀.card := by exact_mod_cast (mul_pos hc hnpos).trans_le hsize₀
  obtain ⟨v, hv⟩ := card_pos.mp hU₀pos
  have hcoreUpper : (C₀.graph.degree ⟨v, hv⟩ : ℝ) ≤ U₀.card := by
    exact_mod_cast (show C₀.graph.degree ⟨v, hv⟩ ≤ U₀.card from
      by simpa only [Fintype.card_coe] using (C₀.graph.degree_lt_card_verts ⟨v, hv⟩).le)
  have hkUpper : (k : ℝ) ≤ 2*Fintype.card V :=
    degree_le_twice_order (Fintype.card V) U₀.card k a
      (C₀.graph.degree ⟨v, hv⟩) hu₀ haOrder hcoreUpper (hdegree₀ ⟨v, hv⟩)
  have hmargin : (h : ℝ)-r ≤ δ*Fintype.card V :=
    margin_of_degree_upper δ 2 hδ.le (by norm_num) (Fintype.card V) k h r hkUpper hmargin₀
  have hhDensity : (α/30)*Fintype.card V ≤ (h : ℝ) := by
    have hrhR : (r : ℝ) ≤ h := by exact_mod_cast hrh
    nlinarith only [hdensity, hr, hrhR]
  have hhUpper : (h : ℝ) ≤ 2*Fintype.card V := by
    have hhk : (h : ℝ) ≤ k := by exact_mod_cast (show h≤k from by omega)
    exact hhk.trans hkUpper
  have haError : a ≤ (α/30)*Fintype.card V/10 := by
    have hsmall := haSmall.trans
      (mul_le_mul_of_nonneg_right (min_le_right ξ (α/300)) (Nat.cast_nonneg _))
    linarith only [hsmall]
  have hlarge : 3 < θ^2*c^2*(Fintype.card V : ℝ) := by
    have hnR : (nLarge : ℝ) ≤ Fintype.card V := by exact_mod_cast hnLarge'
    have hg := (div_lt_iff₀ (show 0 < θ^2*c^2 by positivity)).mp (hnLarge.trans_le hnR)
    nlinarith only [hg]
  let C' := pairedEmbeddedCores (residualGraph G N univ) U₀ U₁ C₀' C₁'
  have hCrobust : ∀ i, IsRobustExpander (C' i).graph θ σ := by
    intro i
    fin_cases i
    · exact hRrobust₀
    · exact hRrobust₁
  have hCdegree : ∀ i v, (h : ℝ)-a ≤ ((C' i).graph.degree v : ℝ) := by
    intro i
    fin_cases i
    · exact hRdegree₀
    · exact hRdegree₁
  have hCsize : ∀ i, c*Fintype.card V ≤ ((originalCores U₀ U₁ i).card : ℝ) := by
    intro i
    fin_cases i
    · exact hsize₀
    · exact hsize₁
  have hCcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ originalCores U₀ U₁ i := by
    intro v
    rcases hcover v with hv₀ | hv₁ | hvZ
    · exact Or.inr ⟨0, hv₀⟩
    · exact Or.inr ⟨1, hv₁⟩
    · exact Or.inl hvZ
  have hCdisj := originalCores_disjoint U₀ U₁ h01
  have hCZ := originalCores_disjoint_exceptions U₀ U₁ Z h0Z h1Z
  have hRno : ∀ X : Finset V, ¬ (residualGraph G N univ).IsOverfull h X := by
    apply no_overfull_of_whole_cut_bounds (residualGraph G N univ)
      (originalCores U₀ U₁) Z hCdisj hCZ hCcover h hRregular C'
      (α/30) c θ σ a (by positivity) hc hθ hσ.le (by linarith only [hσsmall])
      hhDensity hhUpper haError hlarge hCsize hCrobust hCdegree hwhole
    exact residual_whole_toggles_safe G N univ (originalCores U₀ U₁) Z
      hCdisj hCZ hCcover k h hregular hRregular hno C' a hCdegree hwhole hcases
  exact ⟨r, h, q, M, Q, N, C₀', C₁', hM, hr, hcount, hrh, hmargin,
    hNperfect, hNdisj, hNavoid, hRregular, hRno,
    IsRobustExpander.mono_parameter _ hRrobust₀ (min_le_left _ _),
    IsRobustExpander.mono_parameter _ hRrobust₁ (min_le_left _ _),
    hRdegree₀, hRdegree₁⟩

end Overfull.NativeReserve
