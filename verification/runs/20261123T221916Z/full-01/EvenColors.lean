import Overfull.ResidualPalette.JoiningGrouping

/-!
# Empty reserved colors in an all-even joining palette

The joining pieces are colored using the complement of a prescribed set
of palette labels. Transport back to the original labels preserves actual
edge copies, matching and cut-parity certificates, and class size and load
bounds. Every prescribed color is left empty for its later reserve boundary.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

/-- An all-even joining decomposition can avoid any prescribed palette
labels, paying exactly their number in the palette margin. -/
theorem EvenJoiningDecomposition.exists_palette_avoiding_colors
    (P : EvenJoiningDecomposition G label) {h D L : ℕ}
    (Q : Finset (Fin h))
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 6*D+Q.card < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-Q.card)) :
    ∃ C : JoiningPalette G label h D L (fun _ => 0),
      ∀ j ∈ Q, C.classes j = ∅ := by
  have hmargin : 6*D < h-Q.card := by omega
  have hgap : h-Q.card-6*D = h-6*D-Q.card := by omega
  obtain ⟨B⟩ := P.exists_palette G label hdegree hL hmargin
    (by simpa only [hgap] using hbudget)
  let A : Finset (Fin h) := univ \ Q
  have hA : A.card = h-Q.card := by
    simp [A, card_sdiff_of_subset (subset_univ Q)]
  let e : A ≃ Fin (h-Q.card) := A.equivFinOfCardEq hA
  let F : Fin h → Finset E :=
    fun j => if hj : j ∈ A then B.classes (e ⟨j,hj⟩) else ∅
  have hF (j : A) : F j.val = B.classes (e j) := by
    simp only [F, dif_pos j.property]
  have hFempty (j : Fin h) (hj : j ∉ A) : F j = ∅ := by
    simp only [F, dif_neg hj]
  have hmatching : ∀ j, G.IsMatching (F j) := by
    intro j
    by_cases hj : j ∈ A
    · rw [hF ⟨j,hj⟩]
      exact B.matching _
    · rw [hFempty j hj]
      simp [Multigraph.IsMatching]
  have hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · rw [hF ⟨i,hi⟩, hF ⟨j,hj⟩]
        apply B.disjoint
        intro heq
        exact hij (congrArg Subtype.val (e.injective heq))
      · rw [hFempty j hj]
        exact disjoint_empty_right _
    · rw [hFempty i hi]
      exact disjoint_empty_left _
  have hcover : univ.biUnion F = joiningCopies G label := by
    rw [← B.cover]
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨j,hj⟩
      by_cases hjA : j ∈ A
      · rw [hF ⟨j,hjA⟩] at hj
        exact ⟨e ⟨j,hjA⟩,hj⟩
      · rw [hFempty j hjA] at hj
        exact (notMem_empty x hj).elim
    · rintro ⟨k,hk⟩
      obtain ⟨j,rfl⟩ := e.surjective k
      exact ⟨j.val,by simpa only [hF j] using hk⟩
  have hsubset : ∀ j, F j ⊆ joiningCopies G label := by
    intro j x hx
    rw [← hcover]
    exact mem_biUnion.mpr ⟨j,mem_univ _,hx⟩
  let C : JoiningPalette G label h D L (fun _ => 0) := {
    classes := F
    matching := hmatching
    disjoint := hdisjoint
    cover := hcover
    cut_parity := by
      intro j i
      by_cases hj : j ∈ A
      · rw [hF ⟨j,hj⟩]
        exact B.cut_parity _ i
      · rw [hFempty j hj]
        simp [Multigraph.cutOn]
    card_le := by
      intro j
      by_cases hj : j ∈ A
      · rw [hF ⟨j,hj⟩]
        exact B.card_le _
      · rw [hFempty j hj]
        simp
    support_card_le := by
      intro j
      by_cases hj : j ∈ A
      · rw [hF ⟨j,hj⟩]
        exact B.support_card_le _
      · rw [hFempty j hj]
        simp [Multigraph.edgeSupport]
    vertex_load_le := fun v =>
      (G.family_support_load_le_degreeOn F (joiningCopies G label)
        hdisjoint hsubset v).trans (hdegree v)
  }
  refine ⟨C,?_⟩
  intro j hj
  exact hFempty j (by simpa only [A,mem_sdiff,mem_univ,true_and,not_not] using hj)

end Overfull.FourOdd

namespace Overfull.AssignedParts

open Finset Classical NativeReserve FourOdd

variable {V E F : Type*} [Fintype V] [Fintype F]
    (G : Multigraph V E) (H : Multigraph V F)

/-- For the original representative assignment, all-even assigned fibers
give an actual residual joining palette with the chosen colors empty.
The representative is not required to survive as a residual matching. -/
theorem exists_assigned_even_joiningPalette_avoiding_colors_in_host
    (M : Finset E) (U₀ U₁ Z : Finset V) {h D L : ℕ}
    (Q : Finset (Fin h))
    (hregular : ∀ v, H.degree v = h)
    (hno : ∀ X : Finset V, ¬ H.IsOverfull h X)
    (heven : ∀ i, (univ.filter
      (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 = 0)
    (hdegree : ∀ v,
      H.degreeOn (joiningCopies H (assignedLabel G M U₀ U₁ Z)) v ≤ D)
    (hL : 0 < L) (hDh : 6*D+Q.card < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-Q.card)) :
    ∃ C : JoiningPalette H (assignedLabel G M U₀ U₁ Z) h D L
      (fun i => (univ.filter
        (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2),
      (∀ j ∈ Q, C.classes j = ∅) ∧
      ∀ j i, Even ((univ.filter
        (fun v => assignedLabel G M U₀ U₁ Z v = i)) \
        H.edgeSupport (C.classes j)).card := by
  obtain ⟨P⟩ := exists_evenJoining_decomposition H
    (assignedLabel G M U₀ U₁ Z) (by decide) hregular hno heven
  obtain ⟨B,hB⟩ := P.exists_palette_avoiding_colors H
    (assignedLabel G M U₀ U₁ Z) Q hdegree hL hDh hbudget
  let C := B.congr_parity (fun i => (heven i).symm)
  exact ⟨C,hB,fun j i => assigned_joiningPalette_uncovered_even G H U₀ U₁ Z C j i⟩

end Overfull.AssignedParts
