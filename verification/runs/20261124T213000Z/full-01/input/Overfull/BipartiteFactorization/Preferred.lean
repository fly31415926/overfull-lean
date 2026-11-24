import Overfull.BipartiteFactorization.Moves

/-!
# Preferred sides and actual representative copies

The preferred side contains at least half the actual incidences to the
core. Under the ordinary-vertex alternatives, it also contains a positive
fraction of distinct neighbors. One original edge copy is then selected
for each such neighbor; no representative set is supplied as an input.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype E]
variable (G : Multigraph V E)

theorem edgesTo_union (x : V) (A B : Finset V) :
    G.edgesTo x (A ∪ B) = G.edgesTo x A ∪ G.edgesTo x B := by
  ext e
  simp only [Multigraph.mem_edgesTo, Finset.mem_union]
  tauto

theorem edgesTo_disjoint (x : V) {A B : Finset V} (hAB : Disjoint A B) :
    Disjoint (G.edgesTo x A) (G.edgesTo x B) := by
  apply Finset.disjoint_left.mpr
  intro e heA heB
  exact Finset.disjoint_left.mp hAB
    ((G.mem_edgesTo x A e).mp heA).2 ((G.mem_edgesTo x B e).mp heB).2

theorem edgesTo_union_card (x : V) {A B : Finset V} (hAB : Disjoint A B) :
    (G.edgesTo x (A ∪ B)).card = (G.edgesTo x A).card + (G.edgesTo x B).card := by
  rw [edgesTo_union, Finset.card_union_of_disjoint (edgesTo_disjoint G x hAB)]

theorem edgesTo_card_le_degree (x : V) (X : Finset V) :
    (G.edgesTo x X).card ≤ G.degree x := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Choose a side with the larger actual incidence count, resolving ties
in favor of the first side. -/
def preferredSide (x : V) (A B : Finset V) : Finset V :=
  if (G.edgesTo x B).card ≤ (G.edgesTo x A).card then A else B

theorem preferredSide_eq_left_or_right (x : V) (A B : Finset V) :
    preferredSide G x A B = A ∨ preferredSide G x A B = B := by
  unfold preferredSide
  split_ifs <;> simp

theorem preferredSide_subset (x : V) (A B : Finset V) :
    preferredSide G x A B ⊆ A ∪ B := by
  rcases preferredSide_eq_left_or_right G x A B with h | h
  · rw [h]
    exact Finset.subset_union_left
  · rw [h]
    exact Finset.subset_union_right

/-- The chosen side receives at least half of the actual core incidences. -/
theorem preferredSide_incidence_lower (x : V) (A B : Finset V)
    (hAB : Disjoint A B) :
    ((G.edgesTo x (A ∪ B)).card : ℝ) / 2 ≤
      (G.edgesTo x (preferredSide G x A B)).card := by
  have hsum : ((G.edgesTo x (A ∪ B)).card : ℝ) =
      (G.edgesTo x A).card + (G.edgesTo x B).card := by
    exact_mod_cast edgesTo_union_card G x hAB
  unfold preferredSide
  split_ifs with h
  · have hh : ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x A).card := by
      exact_mod_cast h
    linarith
  · have hh : ((G.edgesTo x A).card : ℝ) ≤ (G.edgesTo x B).card := by
      exact_mod_cast (le_of_not_ge h)
    linarith

/-- Select one actual edge copy for each distinct neighbor in the target
set. The image is exactly the neighbor set and the other ends are distinct. -/
theorem exists_representative_edges (x : V) (X : Finset V) :
    ∃ F : Finset E, F ⊆ G.edgesTo x X ∧ Set.InjOn (G.otherEnd x) F ∧
      F.image (G.otherEnd x) = neighborsIn G x X ∧
      F.card = (neighborsIn G x X).card := by
  have hsurj : Set.SurjOn (G.otherEnd x) (G.edgesTo x X) (neighborsIn G x X) := by
    intro y hy
    obtain ⟨e, he, hey⟩ := Finset.mem_image.mp hy
    exact ⟨e, he, hey⟩
  obtain ⟨F, hF, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      (↑(G.edgesTo x X) : Set E) (neighborsIn G x X) hsurj
  refine ⟨F, hF, hinj, himage, ?_⟩
  rw [← himage, Finset.card_image_of_injOn hinj]

/-- Either ordinary-vertex alternative gives many distinct neighbors on
the same side selected by the actual incidence counts. -/
theorem preferredSide_neighbors_lower (x : V) (A B : Finset V)
    (k : ℕ) (a β : ℝ) (hAB : Disjoint A B)
    (hβ₀ : 0 ≤ β) (hβ : β ≤ 1) (hdegree : G.degree x ≤ k)
    (ha : a ≤ ((G.edgesTo x (A ∪ B)).card : ℝ) / 10)
    (halt : ((G.edgesTo x (A ∪ B)).card : ℝ) ≤
        (neighborsIn G x (A ∪ B)).card + a ∨
      (β * k ≤ (neighborsIn G x A).card ∧
        β * k ≤ (neighborsIn G x B).card)) :
    β * (G.edgesTo x (A ∪ B)).card / 4 ≤
      (neighborsIn G x (preferredSide G x A B)).card := by
  have hc₀ : (0 : ℝ) ≤ (G.edgesTo x (A ∪ B)).card := Nat.cast_nonneg _
  have hc : ((G.edgesTo x (A ∪ B)).card : ℝ) ≤ k := by
    exact_mod_cast (edgesTo_card_le_degree G x (A ∪ B)).trans hdegree
  rcases halt with hrep | hboth
  · have hp := preferredSide_incidence_lower G x A B hAB
    have hm := repeated_incidence_real_mono G x (preferredSide_subset G x A B)
    have hβc := mul_le_mul_of_nonneg_right hβ hc₀
    nlinarith
  · have hβc := mul_le_mul_of_nonneg_left hc hβ₀
    have hβc₀ : 0 ≤ β * ((G.edgesTo x (A ∪ B)).card : ℝ) := mul_nonneg hβ₀ hc₀
    rcases preferredSide_eq_left_or_right G x A B with h | h
    · rw [h]
      nlinarith [hboth.1]
    · rw [h]
      nlinarith [hboth.2]

/-- Construct the preferred side and all its actual representative edge
copies, with both the incidence and the distinct-neighbor lower bounds. -/
theorem exists_preferred_representatives (x : V) (A B : Finset V)
    (k : ℕ) (a β : ℝ) (hAB : Disjoint A B)
    (hβ₀ : 0 ≤ β) (hβ : β ≤ 1) (hdegree : G.degree x ≤ k)
    (ha : a ≤ ((G.edgesTo x (A ∪ B)).card : ℝ) / 10)
    (halt : ((G.edgesTo x (A ∪ B)).card : ℝ) ≤
        (neighborsIn G x (A ∪ B)).card + a ∨
      (β * k ≤ (neighborsIn G x A).card ∧
        β * k ≤ (neighborsIn G x B).card)) :
    ∃ F : Finset E,
      (preferredSide G x A B = A ∨ preferredSide G x A B = B) ∧
      ((G.edgesTo x (A ∪ B)).card : ℝ) / 2 ≤
        (G.edgesTo x (preferredSide G x A B)).card ∧
      F ⊆ G.edgesTo x (preferredSide G x A B) ∧
      Set.InjOn (G.otherEnd x) F ∧
      F.image (G.otherEnd x) = neighborsIn G x (preferredSide G x A B) ∧
      F.card = (neighborsIn G x (preferredSide G x A B)).card ∧
      β * (G.edgesTo x (A ∪ B)).card / 4 ≤ F.card := by
  obtain ⟨F, hF, hinj, himage, hcard⟩ :=
    exists_representative_edges G x (preferredSide G x A B)
  refine ⟨F, preferredSide_eq_left_or_right G x A B,
    preferredSide_incidence_lower G x A B hAB, hF, hinj, himage, hcard, ?_⟩
  rw [hcard]
  exact preferredSide_neighbors_lower G x A B k a β hAB hβ₀ hβ hdegree ha halt

/-- The ordinary-vertex hypotheses and one finite error budget supply all
preferred-side representative sets for the actual multigraph. -/
theorem ordinary_preferred_representatives (A B Z₀ : Finset V)
    (k : ℕ) (a β : ℝ) (hAB : Disjoint A B)
    (hβ₀ : 0 ≤ β) (hβ : β ≤ 1) (hdegree : ∀ v, G.degree v ≤ k)
    (hsmall : 10 * a ≤ β * k)
    (hports : OrdinaryPorts (G := G) A B Z₀ k a β) :
    ∀ x, x ∉ A ∪ B → x ∉ Z₀ →
      ∃ F : Finset E,
        (preferredSide G x A B = A ∨ preferredSide G x A B = B) ∧
        ((G.edgesTo x (A ∪ B)).card : ℝ) / 2 ≤
          (G.edgesTo x (preferredSide G x A B)).card ∧
        F ⊆ G.edgesTo x (preferredSide G x A B) ∧
        Set.InjOn (G.otherEnd x) F ∧
        F.image (G.otherEnd x) = neighborsIn G x (preferredSide G x A B) ∧
        F.card = (neighborsIn G x (preferredSide G x A B)).card ∧
        β * (G.edgesTo x (A ∪ B)).card / 4 ≤ F.card := by
  intro x hx hxZ₀
  obtain ⟨hc, halt⟩ := hports x hx hxZ₀
  exact exists_preferred_representatives G x A B k a β hAB hβ₀ hβ (hdegree x)
    (by linarith) halt

end Overfull.BipartiteFactorization
