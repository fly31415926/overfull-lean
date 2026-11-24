import Overfull.Sharpness.WholeCliques
import Overfull.SharpnessArithmetic

/-!
Every vertex set of the graph in Proposition 7.1 satisfies the maximum-degree
edge bound. A set meeting a clique partially is handled by its actual crossing
edges. Otherwise, the whole-clique counting identity reduces the assertion to
the checked weighted Petersen odd-cut certificate.
-/

namespace Overfull.Sharpness.OddSets

open Family WholeCliques

def clique {Δ : ℕ} (i : Fin 4) : Finset (Vertex Δ) :=
  Finset.univ.image (fun a : Fin Δ => Sum.inl (i, a))

@[simp] theorem mem_clique {Δ : ℕ} (i j : Fin 4) (a : Fin Δ) :
    Sum.inl (j, a) ∈ clique i ↔ i = j := by
  simp [clique]

@[simp] theorem inr_not_mem_clique {Δ : ℕ} (i : Fin 4) (w : Fin 5) :
    Sum.inr w ∉ clique (Δ := Δ) i := by
  simp [clique]

theorem clique_card {Δ : ℕ} (i : Fin 4) : (clique (Δ := Δ) i).card = Δ := by
  have hi : Function.Injective (fun a : Fin Δ => (Sum.inl (i, a) : Vertex Δ)) := by
    intro a b h
    simpa using h
  simp [clique, Finset.card_image_of_injective _ hi]

theorem clique_complete {Δ : ℕ} (i : Fin 4) :
    ∀ x ∈ clique (Δ := Δ) i, ∀ y ∈ clique i, x ≠ y → (graph Δ).Adj x y := by
  intro x hx y hy hxy
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  exact Or.inl ⟨rfl, by intro hab; apply hxy; simp [hab]⟩

theorem partial_clique_not_overfull {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (X : Finset (Vertex Δ)) (i : Fin 4)
    (hpos : 0 < (X ∩ clique i).card) (hlt : (X ∩ clique i).card < Δ) :
    ¬ IsOverfull (graph Δ) Δ X := by
  by_cases hodd : X.card % 2 = 1
  · have hcut := clique_cut_bound (graph Δ) X (clique i) Δ (degree_bound hΔ)
      (clique_card i) (clique_complete i)
    have hclique := SharpnessArithmetic.clique_cut_lower_bound Δ (X ∩ clique i).card
      (by omega) hlt
    have hc : X.card = 2 * (X.card / 2) + 1 := by omega
    have hΔ1 : Δ - 1 + 1 = Δ := by omega
    rw [hc] at hcut
    unfold IsOverfull
    nlinarith
  · exact not_overfull_of_even_card (graph Δ) X Δ (degree_bound hΔ) (by omega)

theorem whole_of_no_partial_clique {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ))
    (hpartial : ¬ ∃ i : Fin 4, 0 < (X ∩ clique i).card ∧ (X ∩ clique i).card < Δ) :
    ∀ (i : Fin 4) (a : Fin Δ), Sum.inl (i, a) ∈ X ↔ Sum.inl (i, u hΔ) ∈ X := by
  intro i a
  have hle : (X ∩ clique i).card ≤ Δ := by
    simpa only [clique_card] using
      Finset.card_le_card (Finset.inter_subset_right (s₁ := X) (s₂ := clique i))
  have hcases : (X ∩ clique i).card = 0 ∨ (X ∩ clique i).card = Δ := by
    by_cases hz : (X ∩ clique i).card = 0
    · exact Or.inl hz
    · right
      have hnlt : ¬ (X ∩ clique i).card < Δ := by
        intro hlt
        exact hpartial ⟨i, by omega, hlt⟩
      omega
  rcases hcases with hz | hfull
  · have hnot (b : Fin Δ) : Sum.inl (i, b) ∉ X := by
      intro hb
      have hmem : Sum.inl (i, b) ∈ X ∩ clique i := Finset.mem_inter.mpr ⟨hb, by simp⟩
      have hp := Finset.card_pos.mpr ⟨Sum.inl (i, b), hmem⟩
      omega
    simp [hnot a, hnot (u hΔ)]
  · have heq : X ∩ clique i = clique i := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      rw [clique_card, hfull]
    have hsub : clique i ⊆ X := by
      rw [← heq]
      exact Finset.inter_subset_left
    exact iff_of_true (hsub (by simp)) (hsub (by simp))

end Overfull.Sharpness.OddSets

namespace Overfull.Sharpness.Family

/-- No vertex set of the actual sharpness graph is overfull with respect to
its maximum degree. The statement includes all subsets, of either parity. -/
theorem no_overfull {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (X : Finset (Vertex Δ)) : ¬ IsOverfull (graph Δ) Δ X := by
  by_cases hpartial : ∃ i : Fin 4,
      0 < (X ∩ OddSets.clique i).card ∧ (X ∩ OddSets.clique i).card < Δ
  · obtain ⟨i, hpos, hlt⟩ := hpartial
    exact OddSets.partial_clique_not_overfull hΔ X i hpos hlt
  · exact WholeCliques.whole_cliques_not_overfull hΔ hodd X
      (OddSets.whole_of_no_partial_clique hΔ X hpartial)

end Overfull.Sharpness.Family
