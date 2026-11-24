import Overfull.TerminalFourOdd.Palette

/-!
# Center counts and surviving singleton reserves

A primary forest has at most one triple-cut part. The actual surviving
families retain singleton colors unless almost all primary forests have
one common center. In that latter case the completed prefix can be chosen
to contain every forest with a different center.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd Compression CircuitPatterns Terminal

variable {V E : Type*} [Fintype V]

theorem PrimaryProfile.triple_unique {G : Multigraph V E}
    {label : V → Fin 4} {M : Finset E} (hp : PrimaryProfile G label M)
    {i j : Fin 4} (hi : (G.cutOn M (labelShore label {i})).card = 3)
    (hj : (G.cutOn M (labelShore label {j})).card = 3) : i = j := by
  obtain ⟨F, hF, hcuts⟩ := hp
  rw [hcuts] at hi hj
  rcases hF with hm | ⟨c, rfl⟩
  · have hc := (labelPerfectMatching_spec F hm).2.1 i
    omega
  · rw [(labelStar_spec c).2.1 i] at hi
    rw [(labelStar_spec c).2.1 j] at hj
    split_ifs at hi hj <;> simp_all

def singletonParts (G : Multigraph V E) (label : V → Fin 4)
    (R : Finset (Finset E)) (i : Fin 4) : Finset (Finset E) :=
  R.filter (fun M => (G.cutOn M (labelShore label {i})).card = 1)

def tripleParts (G : Multigraph V E) (label : V → Fin 4)
    (R : Finset (Finset E)) (i : Fin 4) : Finset (Finset E) :=
  R.filter (fun M => (G.cutOn M (labelShore label {i})).card = 3)

theorem singleton_add_triple (G : Multigraph V E) (label : V → Fin 4)
    (R : Finset (Finset E)) (hR : ∀ M ∈ R, PrimaryProfile G label M) (i : Fin 4) :
    (singletonParts G label R i).card + (tripleParts G label R i).card = R.card := by
  have heq : R.filter (fun M => ¬ (G.cutOn M (labelShore label {i})).card = 1) =
      tripleParts G label R i := by
    ext M
    simp only [tripleParts, mem_filter]
    apply and_congr_right
    intro hM
    have hp := (hR M hM).cut_one_or_three i
    omega
  have h := filter_card_add_filter_neg_card_eq_card
    (s := R) (fun M => (G.cutOn M (labelShore label {i})).card = 1)
  simpa only [heq, singletonParts] using h

theorem tripleParts_pairwise_disjoint (G : Multigraph V E) (label : V → Fin 4)
    (R : Finset (Finset E)) (hR : ∀ M ∈ R, PrimaryProfile G label M) :
    Pairwise (fun i j => Disjoint (tripleParts G label R i) (tripleParts G label R j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro M hi hj
  have hmi := mem_filter.mp hi
  have hmj := mem_filter.mp hj
  exact hij ((hR M hmi.1).triple_unique hmi.2 hmj.2)

theorem singleton_reserve_after_removal (G : Multigraph V E) (label : V → Fin 4)
    (R S : Finset (Finset E)) (i : Fin 4) (t : ℕ)
    (hreserve : S.card+t ≤ (singletonParts G label R i).card) :
    t ≤ (singletonParts G label (R \ S) i).card := by
  have heq : singletonParts G label R i \ S = singletonParts G label (R \ S) i := by
    ext M
    simp only [singletonParts, mem_filter, mem_sdiff]
    tauto
  have hc := card_le_card_sdiff_add_card (s := singletonParts G label R i) (t := S)
  rw [heq] at hc
  omega

/-- A bound on center frequency gives the exact singleton reserve needed
after deleting an arbitrary selected prefix. -/
theorem singleton_reserve_of_center_bound (G : Multigraph V E) (label : V → Fin 4)
    (R S : Finset (Finset E)) (hR : ∀ M ∈ R, PrimaryProfile G label M)
    (i : Fin 4) (t : ℕ)
    (hcenter : (tripleParts G label R i).card + S.card+t ≤ R.card) :
    t ≤ (singletonParts G label (R \ S) i).card := by
  apply singleton_reserve_after_removal G label R S i t
  have hc := singleton_add_triple G label R hR i
  omega

/-- If all but at most `r` primary pieces have one center, choose exactly
`r` pieces to complete so that every remaining primary has that center. -/
theorem exists_selection_retaining_common_center (G : Multigraph V E)
    (label : V → Fin 4) (R : Finset (Finset E)) (r : ℕ) (i : Fin 4)
    (hr : r ≤ R.card) (hcenter : R.card ≤ (tripleParts G label R i).card+r) :
    ∃ S ⊆ R, S.card = r ∧ R \ S ⊆ tripleParts G label R i := by
  have hsub : tripleParts G label R i ⊆ R := filter_subset _ _
  have hcount : (R \ tripleParts G label R i).card ≤ r := by
    rw [card_sdiff_of_subset hsub]
    omega
  obtain ⟨S, hlow, hSR, hS⟩ := exists_subsuperset_card_eq
    (sdiff_subset : R \ tripleParts G label R i ⊆ R) hcount hr
  refine ⟨S, hSR, hS, ?_⟩
  intro M hM
  by_contra hm
  exact (mem_sdiff.mp hM).2 (hlow (mem_sdiff.mpr ⟨(mem_sdiff.mp hM).1, hm⟩))

variable [Fintype E]

/-- In the dominant-center case the palette construction removes every
other primary and leaves only the actual common-center star matchings. -/
theorem exists_common_center_prefix_palette (G : Multigraph V E) (label : V → Fin 4)
    {h r D L : ℕ} (P : JoiningDecomposition G label h) (i : Fin 4)
    (hrh : r ≤ h) (hcenter : h ≤ (tripleParts G label P.primary i).card+r)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDr : 6*D < r)
    (hbudget : Fintype.card V*D ≤ 2*L*(r-6*D)) :
    ∃ B : PrefixPalette G label r L (fun _ => 1),
      B.remaining.card = h-r ∧ B.remaining ⊆ P.primary ∧
      (∀ M ∈ B.remaining, (G.cutOn M (labelShore label {i})).card = 3) ∧
      (∀ M ∈ B.remaining, ∀ j, j ≠ i → (G.cutOn M (labelShore label {j})).card = 1) := by
  obtain ⟨S, hSP, hS, hleft⟩ := exists_selection_retaining_common_center G label
    P.primary r i (by simpa only [P.primary_card] using hrh)
      (by simpa only [P.primary_card] using hcenter)
  obtain ⟨B, hB, hc⟩ := exists_prefix_palette_of_selected G label P S hSP hS
    hdegree hL hDr hbudget
  have hBP : B.remaining ⊆ P.primary := by rw [hB]; exact sdiff_subset
  have htriple : ∀ M ∈ B.remaining, (G.cutOn M (labelShore label {i})).card = 3 := by
    intro M hM
    rw [hB] at hM
    exact (mem_filter.mp (hleft hM)).2
  refine ⟨B, hc, hBP, htriple, ?_⟩
  intro M hM j hji
  rcases (P.primary_profile M (hBP hM)).cut_one_or_three j with hs | ht
  · exact hs
  · exact (hji ((P.primary_profile M (hBP hM)).triple_unique ht (htriple M hM))).elim

end Overfull.TerminalFourOdd
