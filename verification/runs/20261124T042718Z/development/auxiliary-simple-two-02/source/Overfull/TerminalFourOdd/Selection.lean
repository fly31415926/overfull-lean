import Overfull.TerminalFourOdd.ProfileCounts

/-!
# Choosing the prefix before completing it

Disjoint center classes permit one selection of prescribed size such that the
remaining primary forests either all have one center, or every part has a
positive singleton reserve.  The selection is made from the actual primary
family before the robust matching completion is applied.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd

variable {A I : Type*}

theorem complement_reserve_after_removal (R S C : Finset A) (r : ℕ)
    (h : C.card + S.card + r ≤ R.card) : r ≤ ((R \ S) \ C).card := by
  have h₁ := card_le_card_sdiff_add_card (s := R) (t := S)
  have h₂ := card_le_card_sdiff_add_card (s := R \ S) (t := C)
  omega

/-- A family of disjoint center classes admits a prescribed-size selection
leaving either one common center or at least `r` noncenter pieces for each
index. No cardinality assumption on the index type is required. -/
theorem exists_center_or_reserve_selection (R : Finset A) (C : I → Finset A)
    (hsub : ∀ i, C i ⊆ R) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (r : ℕ) (hr : 4 * r ≤ R.card) :
    ∃ S ⊆ R, S.card = r ∧
      ((∃ i, R \ S ⊆ C i) ∨ ∀ i, r ≤ ((R \ S) \ C i).card) := by
  have hrR : r ≤ R.card := by omega
  by_cases hdom : ∃ i, R.card ≤ (C i).card + r
  · obtain ⟨i, hi⟩ := hdom
    have hsmall : (R \ C i).card ≤ r := by
      rw [card_sdiff_of_subset (hsub i)]
      omega
    obtain ⟨S, hlow, hSR, hS⟩ := exists_subsuperset_card_eq
      (sdiff_subset : R \ C i ⊆ R) hsmall hrR
    refine ⟨S, hSR, hS, Or.inl ⟨i, ?_⟩⟩
    intro x hx
    by_contra hc
    exact (mem_sdiff.mp hx).2 (hlow (mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, hc⟩))
  · have hnotdom (i : I) : (C i).card + r < R.card := by
      by_contra h
      exact hdom ⟨i, Nat.le_of_not_gt h⟩
    by_cases hnear : ∃ i, R.card < (C i).card + 2 * r
    · obtain ⟨i, hi⟩ := hnear
      have hri : r ≤ (C i).card := by omega
      obtain ⟨S, hSC, hS⟩ := exists_subset_card_eq hri
      have hSR : S ⊆ R := hSC.trans (hsub i)
      refine ⟨S, hSR, hS, Or.inr ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        have heq : (R \ S) \ C i = R \ C i := by
          ext x
          simp only [mem_sdiff]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · exact fun h => ⟨⟨h.1, fun hs => h.2 (hSC hs)⟩, h.2⟩
        rw [heq, card_sdiff_of_subset (hsub i)]
        have hni := hnotdom i
        omega
      · have hpair : (C i).card + (C j).card ≤ R.card := by
          rw [← card_union_of_disjoint (hdisj (Ne.symm hji))]
          exact card_le_card (union_subset (hsub i) (hsub j))
        apply complement_reserve_after_removal
        omega
    · obtain ⟨S, hSR, hS⟩ := exists_subset_card_eq hrR
      refine ⟨S, hSR, hS, Or.inr ?_⟩
      intro i
      have hi : (C i).card + 2 * r ≤ R.card := by
        by_contra h
        exact hnear ⟨i, Nat.lt_of_not_ge h⟩
      apply complement_reserve_after_removal
      omega

variable {V E : Type*} [Fintype V]

/-- The actual primary matching family has a selection giving the precise
common-center or singleton-reserve alternatives used in terminal coloring. -/
theorem exists_primary_center_or_singleton_selection (G : Multigraph V E)
    (label : V → Fin 4) (R : Finset (Finset E))
    (hR : ∀ M ∈ R, PrimaryProfile G label M) (r : ℕ) (hr : 4 * r ≤ R.card) :
    ∃ S ⊆ R, S.card = r ∧
      ((∃ i, ∀ M ∈ R \ S, (G.cutOn M (labelShore label {i})).card = 3) ∨
        ∀ i, r ≤ (singletonParts G label (R \ S) i).card) := by
  obtain ⟨S, hSR, hS, hresult⟩ := exists_center_or_reserve_selection R
    (tripleParts G label R) (fun _ => filter_subset _ _)
    (tripleParts_pairwise_disjoint G label R hR) r hr
  refine ⟨S, hSR, hS, ?_⟩
  rcases hresult with ⟨i, hi⟩ | hall
  · exact Or.inl ⟨i, fun M hM => (mem_filter.mp (hi hM)).2⟩
  · right
    intro i
    have heq : (R \ S) \ tripleParts G label R i = singletonParts G label (R \ S) i := by
      ext M
      simp only [mem_sdiff, tripleParts, singletonParts, mem_filter]
      constructor
      · rintro ⟨⟨hM, hMS⟩, hnot⟩
        refine ⟨⟨hM, hMS⟩, ?_⟩
        have hp := (hR M hM).cut_one_or_three i
        have hn : ¬ (G.cutOn M (labelShore label {i})).card = 3 := fun h => hnot ⟨hM, h⟩
        omega
      · rintro ⟨⟨hM, hMS⟩, hone⟩
        exact ⟨⟨hM, hMS⟩, fun h => by omega⟩
    simpa only [heq] using hall i

end Overfull.TerminalFourOdd
