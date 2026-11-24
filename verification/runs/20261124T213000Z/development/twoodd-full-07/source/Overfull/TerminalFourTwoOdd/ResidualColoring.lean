import Overfull.TerminalFourTwoOdd.CentralFactorization
import Overfull.TerminalFourTwoOdd.CentralMatchings
import Overfull.Terminal.OddGluing
import Overfull.NativeTerminal.ShoreFactorization

/-! Factor the two retained even cores and align both odd leaves on original copies. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical Multigraph SmallCuts Terminal BoundaryExtension NativeTerminal

private theorem robust_instances_transport {W : Type*} [Fintype W]
    (H : SimpleGraph W) (d₀ d₁ : DecidableEq W) (r₀ r₁ : DecidableRel H.Adj)
    (ν τ : ℝ) (h : @IsRobustExpander W _ d₀ H r₀ ν τ) :
    @IsRobustExpander W _ d₁ H r₁ ν τ := by
  cases Subsingleton.elim d₀ d₁
  cases Subsingleton.elim r₀ r₁
  exact h

private theorem cut_not_internal_of_whole {V E : Type*} [Fintype E]
    (G : Multigraph V E) (X T : Finset V) (hwhole : T ⊆ X ∨ Disjoint T X)
    {e : E} (he : e ∈ G.cutEdges X) : e ∉ G.internalEdges T := by
  intro hi
  have hends := (G.mem_internalEdges T e).mp hi
  exact (G.mem_cutEdges X e).mp he (propext
    (NativeReserve.whole_core_membership_iff T X hwhole hends.1 hends.2))

set_option maxHeartbeats 1600000 in
theorem exists_uniform_four_two_odd_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (U W A B : Finset V) (C₀ : Core G U) (C₁ : Core G W)
        (C₂ : Core G A) (C₃ : Core G B) (k : ℕ) (a : ℝ),
        Disjoint U W → Disjoint U A → Disjoint U B →
        Disjoint W A → Disjoint W B → Disjoint A B →
        (∀ v, v ∈ U ∨ v ∈ W ∨ v ∈ A ∨ v ∈ B) →
        Even U.card → Even W.card → Odd A.card → Odd B.card →
        m₀ ≤ U.card → m₀ ≤ W.card → m₀ ≤ A.card → m₀ ≤ B.card →
        (∀ v, G.degree v = k) → α*Fintype.card V ≤ (k : ℝ) →
        α*Fintype.card V ≤ (U.card : ℝ) → α*Fintype.card V ≤ (W.card : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        IsRobustExpander C₂.graph ν τ → IsRobustExpander C₃.graph ν τ →
        a ≤ ε*U.card → a ≤ ε*W.card → a ≤ ε*A.card → a ≤ ε*B.card →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₂.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₃.graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → (∀ j, G.IsMatching (M j)) →
        Pairwise (fun i j => Disjoint (M i) (M j)) →
        (∀ e, e ∉ G.internalEdges U → e ∉ G.internalEdges W →
          e ∉ G.internalEdges A → e ∉ G.internalEdges B → ∃ j, e ∈ M j) →
        (∀ j, (M j ∩ G.cutEdges A).card = 1) →
        (∀ j, (M j ∩ G.cutEdges B).card = 1) →
        (∀ j, Even (U \ G.edgeSupport (M j)).card) →
        (∀ j, Even (W \ G.edgeSupport (M j)).card) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨εC,hεC,mC,hcentral⟩ := exists_uniform_two_core_central_coloring α ν τ
    hα hα1 hν hντ hτ
  have hτleaf : τ ≤ min α 1/16 := by rw [min_eq_left hα1]; linarith
  obtain ⟨εL,hεL,mL,hleaf⟩ := exists_uniform_shore_coloring α ν τ 0 hα hν hντ hτleaf
  refine ⟨min εC εL,lt_min hεC hεL,max mC mL,?_⟩
  intro V E _ _ G U W A B C₀ C₁ C₂ C₃ k a hUW hUA hUB hWA hWB hAB
    hcover hU hW hA hB hmU hmW hmA hmB hregular hk hsizeU hsizeW
    hrobU hrobW hrobA hrobB haU _haW haA haB hdegU hdegW hdegA hdegB
    M hM hdM hcoverM hcrossA hcrossB hparU hparW
  let S := U ∪ W
  have hSA : Disjoint S A := disjoint_union_left.mpr ⟨hUA,hWA⟩
  have hSB : Disjoint S B := disjoint_union_left.mpr ⟨hUB,hWB⟩
  have hcoverS : ∀ v, v ∈ S ∨ v ∈ A ∨ v ∈ B := by
    intro v
    rcases hcover v with hv | hv | hv | hv
    · exact Or.inl (mem_union_left _ hv)
    · exact Or.inl (mem_union_right _ hv)
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  have hcutA : G.cutSize A = k := cutSize_of_matching_partition G A k M hdM
    (fun e he => hcoverM e
      (cut_not_internal_of_whole G A U (Or.inr hUA) he)
      (cut_not_internal_of_whole G A W (Or.inr hWA) he)
      (cut_not_internal_of_whole G A A (Or.inl subset_rfl) he)
      (cut_not_internal_of_whole G A B (Or.inr hAB.symm) he)) hcrossA
  have hcutB : G.cutSize B = k := cutSize_of_matching_partition G B k M hdM
    (fun e he => hcoverM e
      (cut_not_internal_of_whole G B U (Or.inr hUB) he)
      (cut_not_internal_of_whole G B W (Or.inr hWB) he)
      (cut_not_internal_of_whole G B A (Or.inr hAB) he)
      (cut_not_internal_of_whole G B B (Or.inl subset_rfl) he)) hcrossB
  have hS_even : Even S.card := by
    rw [show S.card = U.card+W.card from card_union_of_disjoint hUW]
    exact hU.add hW
  have hpartition : (S ∪ A) ∪ B = univ := by
    ext v
    simp only [mem_union,mem_univ,iff_true]
    rcases hcoverS v with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hcard : S.card+A.card+B.card = Fintype.card V := by
    rw [← card_union_of_disjoint hSA,
      ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hSB,hAB⟩),hpartition,card_univ]
  have hAn := Nat.odd_iff.mp hA
  have hBn := Nat.odd_iff.mp hB
  have hcentral_le : Fintype.card (CentralVertex S) ≤ Fintype.card V := by
    rw [centralVertex_card]
    omega
  have hcentral_leR : (Fintype.card (CentralVertex S) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hcentral_le
  have hUcentral : U.card ≤ Fintype.card (CentralVertex S) := by
    rw [centralVertex_card]
    exact (card_le_card (subset_union_left : U ⊆ S)).trans (Nat.le_add_right _ _)
  have haUC : a ≤ εC*U.card := haU.trans
    (mul_le_mul_of_nonneg_right (min_le_left εC εL) (Nat.cast_nonneg U.card))
  let MC := fun j => centralMatching G S A (M j)
  have hcentralInst : (fun v w : CentralVertex S => propDecidable (v=w)) =
      (inferInstance : DecidableEq (CentralVertex S)) := Subsingleton.elim _ _
  obtain ⟨c⟩ := hcentral (CentralVertex S) (CentralEdge G S A) (centralGraph G S A)
    (keptSet (subset_union_left : U ⊆ S)) (keptSet (subset_union_right : W ⊆ S))
    (centralApices S) (keptCore subset_union_left C₀ A) (keptCore subset_union_right C₁ A)
    k a (((le_max_left mC mL).trans hmU).trans hUcentral)
    (central_even_order S hS_even)
    (keptSet_disjoint subset_union_left subset_union_right hUW)
    (keptSet_disjoint_apices subset_union_left) (keptSet_disjoint_apices subset_union_right)
    (central_two_core_cover U W) (by simp)
    (central_regular G S A B k hSA hSB hAB hcoverS (fun v _ => hregular v) hcutA hcutB)
    ((mul_le_mul_of_nonneg_left hcentral_leR hα.le).trans hk)
    (by simpa only [keptSet_card] using (mul_le_mul_of_nonneg_left hcentral_leR hα.le).trans hsizeU)
    (by simpa only [keptSet_card] using (mul_le_mul_of_nonneg_left hcentral_leR hα.le).trans hsizeW)
    (by apply robust_instances_transport _ _ _ _ _ ν τ
        exact keptCore_robust subset_union_left C₀ A ν τ hrobU)
    (by apply robust_instances_transport _ _ _ _ _ ν τ
        exact keptCore_robust subset_union_right C₁ A ν τ hrobW)
    (haUC.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hUcentral) hεC.le))
    (by intro v; rw [keptCore_degree]; exact hdegU _)
    (by intro v; rw [keptCore_degree]; exact hdegW _)
    MC (fun j => centralMatching_isMatching G S A B hSA hSB hAB hcoverS
      (M j) (hM j) (hcrossA j).le (hcrossB j).le)
    (fun i j hij => centralMatching_disjoint G S A (M i) (M j) (hdM hij))
    (centralMatching_two_core_cover G U W A B hSA hSB hAB hcoverS k M hcoverM)
    (by
      intro j v hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      fin_cases i
      · exact centralMatching_covers_apex G S A A (Sum.inr 0)
          (centralMap_eq_first_apex_iff S A hSA) (M j) (hcrossA j)
      · exact centralMatching_covers_apex G S A B (Sum.inr 1)
          (centralMap_eq_second_apex_iff S A B hSB hAB hcoverS) (M j) (hcrossB j))
    (by intro j
        have hp := hparU j
        rw [← centralMatching_uncovered_card G S U A subset_union_left (M j)] at hp
        simpa only [MC,hcentralInst] using hp)
    (by intro j
        have hp := hparW j
        rw [← centralMatching_uncovered_card G S W A subset_union_right (M j)] at hp
        simpa only [MC,hcentralInst] using hp)
  have haAL : a ≤ εL*A.card := haA.trans
    (mul_le_mul_of_nonneg_right (min_le_right εC εL) (Nat.cast_nonneg A.card))
  have haBL : a ≤ εL*B.card := haB.trans
    (mul_le_mul_of_nonneg_right (min_le_right εC εL) (Nat.cast_nonneg B.card))
  have hkA : α*A.card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ A) hα.le).trans hk
  have hkB : α*B.card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ B) hα.le).trans hk
  obtain ⟨_,hfactorA⟩ := hleaf V E G A A C₂ k a subset_rfl
    ((le_max_right mC mL).trans hmA) (by simp) (fun v _ => hregular v) hkA hrobA haAL hdegA
    (by ext e; simp)
  obtain ⟨_,hfactorB⟩ := hleaf V E G B B C₃ k a subset_rfl
    ((le_max_right mC mL).trans hmB) (by simp) (fun v _ => hregular v) hkB hrobB haBL hdegB
    (by ext e; simp)
  obtain ⟨cA⟩ := hfactorA hcutA hA (by intro e he v hv hvA; exact hvA)
  obtain ⟨cB⟩ := hfactorB hcutB hB (by intro e he v hv hvB; exact hvB)
  exact glue_central_and_odd_leaves G S A B k hSA hSB hAB hcoverS hcutA hcutB c cA cB

end Overfull.TerminalFourTwoOdd
