import Overfull.BipartiteMatching

/-!
# Robust expansion after deleting edges and vertices

All neighborhoods in this file are taken in the stated finite simple graphs.
The estimates use the degree actually lost at each vertex.
-/

namespace Overfull

open Finset

private theorem intersection_card_bound {V : Type*} [DecidableEq V]
    (S T X : Finset V) (hTS : T ⊆ S) :
    (S ∩ X).card + T.card ≤ (T ∩ X).card + S.card := by
  have hsub : S ∩ X ⊆ (T ∩ X) ∪ (S \ T) := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvX⟩
    by_cases hvT : v ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvT, hvX⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvS, hvT⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have htotal := Finset.card_sdiff_add_card_eq_card hTS
  omega

section Ordinary

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

theorem robustNeighbors_mono_graph (hGH : G ≤ H) (ν : ℝ) (S : Finset V) :
    robustNeighbors G ν S ⊆ robustNeighbors H ν S := by
  intro v hv
  rw [mem_robustNeighbors] at hv ⊢
  apply hv.trans
  have hsub : G.neighborFinset v ∩ S ⊆ H.neighborFinset v ∩ S := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwG, hwS⟩
    exact Finset.mem_inter.mpr ⟨by simpa using hGH (by simpa using hwG), hwS⟩
  exact_mod_cast Finset.card_le_card hsub

theorem IsRobustExpander.mono_graph {ν τ : ℝ}
    (hexpand : IsRobustExpander G ν τ) (hGH : G ≤ H) :
    IsRobustExpander H ν τ := by
  intro S hS hS'
  exact (hexpand S hS hS').trans (by
    exact_mod_cast (Finset.card_le_card (robustNeighbors_mono_graph G H hGH ν S)))

theorem robustNeighbors_after_edge_deletion (hHG : H ≤ G) (ν μ : ℝ)
    (hloss : ∀ v, (G.degree v : ℝ) ≤ H.degree v + μ * Fintype.card V)
    (S : Finset V) :
    robustNeighbors G ν S ⊆ robustNeighbors H (ν - μ) S := by
  intro v hv
  rw [mem_robustNeighbors] at hv ⊢
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    simpa using hHG (by simpa using hw)
  have hcount := intersection_card_bound (G.neighborFinset v) (H.neighborFinset v) S hsub
  have hreal : ((G.neighborFinset v ∩ S).card : ℝ) + H.degree v ≤
      (H.neighborFinset v ∩ S).card + G.degree v := by
    exact_mod_cast hcount
  have hdegree := hloss v
  nlinarith

/-- A spanning edge deletion losing at most `μ` times the order at any vertex
preserves robust expansion with neighborhood parameter `ν - μ`. -/
theorem IsRobustExpander.after_edge_deletion {ν τ μ : ℝ}
    (hexpand : IsRobustExpander G ν τ) (hHG : H ≤ G) (hμ : 0 ≤ μ)
    (hloss : ∀ v, (G.degree v : ℝ) ≤ H.degree v + μ * Fintype.card V) :
    IsRobustExpander H (ν - μ) τ := by
  intro S hS hS'
  have h := hexpand S hS hS'
  have hcard : ((robustNeighbors G ν S).card : ℝ) ≤
      (robustNeighbors H (ν - μ) S).card := by
    exact_mod_cast Finset.card_le_card
      (robustNeighbors_after_edge_deletion G H hHG ν μ hloss S)
  have hnonneg : 0 ≤ μ * (Fintype.card V : ℝ) := mul_nonneg hμ (Nat.cast_nonneg _)
  nlinarith

end Ordinary

section Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G H : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem leftNeighbors_mono_graph (hHG : H ≤ G) (b : B) :
    leftNeighbors H b ⊆ leftNeighbors G b := by
  intro a ha
  simp only [leftNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact hHG ha

omit [DecidableEq B] in
theorem bipartiteRobustNeighbors_mono_graph (hGH : G ≤ H) (ν : ℝ) (S : Finset A) :
    bipartiteRobustNeighbors G ν S ⊆ bipartiteRobustNeighbors H ν S := by
  intro b hb
  simp only [bipartiteRobustNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  apply hb.trans
  have hsub : S ∩ leftNeighbors G b ⊆ S ∩ leftNeighbors H b := by
    intro a ha
    rcases Finset.mem_inter.mp ha with ⟨haS, haG⟩
    exact Finset.mem_inter.mpr ⟨haS, leftNeighbors_mono_graph H G hGH b haG⟩
  exact_mod_cast Finset.card_le_card hsub

omit [DecidableEq B] in
theorem IsBipartiteRobustExpander.mono_graph {ν τ : ℝ}
    (hexpand : IsBipartiteRobustExpander G ν τ) (hGH : G ≤ H) :
    IsBipartiteRobustExpander H ν τ := by
  intro S hS hS'
  exact (hexpand S hS hS').trans (by
    exact_mod_cast (Finset.card_le_card (bipartiteRobustNeighbors_mono_graph G H hGH ν S)))

omit [DecidableEq B] in
theorem bipartiteRobustNeighbors_after_edge_deletion (hHG : H ≤ G) (ν μ : ℝ)
    (hloss : ∀ b, ((leftNeighbors G b).card : ℝ) ≤
      (leftNeighbors H b).card + μ * Fintype.card A) (S : Finset A) :
    bipartiteRobustNeighbors G ν S ⊆ bipartiteRobustNeighbors H (ν - μ) S := by
  intro b hb
  simp only [bipartiteRobustNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  have hcount := intersection_card_bound (leftNeighbors G b) (leftNeighbors H b) S
    (leftNeighbors_mono_graph G H hHG b)
  have hreal : ((S ∩ leftNeighbors G b).card : ℝ) + (leftNeighbors H b).card ≤
      (S ∩ leftNeighbors H b).card + (leftNeighbors G b).card := by
    simpa only [Finset.inter_comm] using (show
      ((leftNeighbors G b ∩ S).card : ℝ) + (leftNeighbors H b).card ≤
        (leftNeighbors H b ∩ S).card + (leftNeighbors G b).card by exact_mod_cast hcount)
  have hdegree := hloss b
  nlinarith

omit [DecidableEq B] in
theorem IsBipartiteRobustExpander.after_edge_deletion {ν τ μ : ℝ}
    (hexpand : IsBipartiteRobustExpander G ν τ) (hHG : H ≤ G) (hμ : 0 ≤ μ)
    (hloss : ∀ b, ((leftNeighbors G b).card : ℝ) ≤
      (leftNeighbors H b).card + μ * Fintype.card A) :
    IsBipartiteRobustExpander H (ν - μ) τ := by
  intro S hS hS'
  have h := hexpand S hS hS'
  have hcard : ((bipartiteRobustNeighbors G ν S).card : ℝ) ≤
      (bipartiteRobustNeighbors H (ν - μ) S).card := by
    exact_mod_cast Finset.card_le_card
      (bipartiteRobustNeighbors_after_edge_deletion G H hHG ν μ hloss S)
  have hnonneg : 0 ≤ μ * (Fintype.card A : ℝ) := mul_nonneg hμ (Nat.cast_nonneg _)
  nlinarith

private theorem leftNeighbors_card_eq_degree
    (hbip : ∀ b b' : B, ¬ G.Adj (.inr b) (.inr b')) (b : B) :
    (leftNeighbors G b).card = G.degree (.inr b) := by
  have himage : (leftNeighbors G b).image Sum.inl = G.neighborFinset (.inr b) := by
    ext v
    cases v with
    | inl a => simp [leftNeighbors, G.adj_comm]
    | inr b' => simp [leftNeighbors, hbip b b']
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
    Finset.card_image_of_injective _ Sum.inl_injective]

/-- The degree-loss formulation of part (1) of Lemma `bip:bip:stable`.
The side `B` has no internal edges, so its total degrees are its crossing degrees. -/
theorem IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound {ν τ μ : ℝ}
    (hexpand : IsBipartiteRobustExpander G ν τ) (hHG : H ≤ G) (hμ : 0 ≤ μ)
    (hbip : ∀ b b' : B, ¬ G.Adj (.inr b) (.inr b'))
    (hloss : ∀ b : B, (G.degree (.inr b) : ℝ) - H.degree (.inr b) ≤
      μ * Fintype.card A) :
    IsBipartiteRobustExpander H (ν - μ) τ := by
  apply IsBipartiteRobustExpander.after_edge_deletion G H hexpand hHG hμ
  intro b
  have hbipH : ∀ b b' : B, ¬ H.Adj (.inr b) (.inr b') := by
    intro b b' hb
    exact hbip b b' (hHG hb)
  rw [leftNeighbors_card_eq_degree G hbip, leftNeighbors_card_eq_degree H hbipH]
  linarith [hloss b]

end Bipartite

section BipartiteVertices

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- The graph induced on the specified subsets of the two sides. -/
def bipartiteInduce (A' : Finset A) (B' : Finset B) : SimpleGraph (A' ⊕ B') :=
  G.comap (Sum.map Subtype.val Subtype.val)

instance (A' : Finset A) (B' : Finset B) : DecidableRel (bipartiteInduce G A' B').Adj :=
  inferInstanceAs (DecidableRel (G.comap (Sum.map Subtype.val Subtype.val)).Adj)

omit [Fintype B] [DecidableEq B] in
private theorem bipartiteInduce_neighbors_card (A' : Finset A) (B' : Finset B)
    (S : Finset A') (b : B') :
    (S ∩ leftNeighbors (bipartiteInduce G A' B') b).card =
      (S.image Subtype.val ∩ leftNeighbors G b.val).card := by
  have heq : (S ∩ leftNeighbors (bipartiteInduce G A' B') b).image Subtype.val =
      S.image Subtype.val ∩ leftNeighbors G b.val := by
    ext a
    simp only [Finset.mem_image, Finset.mem_inter, leftNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and, bipartiteInduce,
      SimpleGraph.comap_adj, Sum.map_inl, Sum.map_inr]
    constructor
    · rintro ⟨x, ⟨hxS, hxG⟩, rfl⟩
      exact ⟨⟨x, hxS, rfl⟩, hxG⟩
    · rintro ⟨⟨x, hxS, rfl⟩, hxG⟩
      exact ⟨x, ⟨hxS, hxG⟩, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

/-- Deleting equally many vertices from the two sides, at most `ν m / 2`,
preserves bipartite robust expansion after changing the parameters to
`(ν/2, 2τ)`. This is part (2) of Lemma `bip:bip:stable`. -/
theorem IsBipartiteRobustExpander.after_vertex_deletion {ν τ : ℝ}
    (hexpand : IsBipartiteRobustExpander G ν τ)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ < 1 / 4)
    (hbalance : Fintype.card A = Fintype.card B)
    (A' : Finset A) (B' : Finset B) (hbalance' : A'.card = B'.card)
    (hdelete : (Fintype.card A : ℝ) - A'.card ≤ ν * Fintype.card A / 2) :
    IsBipartiteRobustExpander (bipartiteInduce G A' B') (ν / 2) (2 * τ) := by
  classical
  let m : ℝ := Fintype.card A
  let m' : ℝ := A'.card
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hm' : 0 ≤ m' := Nat.cast_nonneg _
  have hle : m' ≤ m := by
    dsimp [m, m']
    exact_mod_cast Finset.card_le_univ A'
  have hhalf : m / 2 ≤ m' := by
    have hmul := mul_le_mul_of_nonneg_right hν1 hm
    change m - m' ≤ ν * m / 2 at hdelete
    linarith
  intro S hSlow hShigh
  have hScard : (S.image Subtype.val).card = S.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hdom : Fintype.card A' = A'.card := Fintype.card_coe _
  rw [hdom] at hSlow hShigh ⊢
  change 2 * τ * m' ≤ (S.card : ℝ) at hSlow
  change (S.card : ℝ) ≤ (1 - 2 * τ) * m' at hShigh
  have hSlow' : τ * m ≤ ((S.image Subtype.val).card : ℝ) := by
    rw [hScard]
    have hmul := mul_le_mul_of_nonneg_left hhalf hτ
    linarith
  have hShigh' : ((S.image Subtype.val).card : ℝ) ≤ (1 - τ) * m := by
    rw [hScard]
    have h1 := mul_le_mul_of_nonneg_left hle (show 0 ≤ 1 - 2 * τ by linarith)
    have h2 := mul_nonneg hτ hm
    nlinarith
  have hex := hexpand (S.image Subtype.val) hSlow' hShigh'
  rw [hScard] at hex
  let R := bipartiteRobustNeighbors G ν (S.image Subtype.val)
  let R' := bipartiteRobustNeighbors (bipartiteInduce G A' B') (ν / 2) S
  have hsubset : R ∩ B' ⊆ R'.image Subtype.val := by
    intro b hb
    rcases Finset.mem_inter.mp hb with ⟨hbR, hbB⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨b, hbB⟩, ?_, rfl⟩
    simp only [R', bipartiteRobustNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hdom, bipartiteInduce_neighbors_card]
    have hbcount : ν * m ≤ ((S.image Subtype.val ∩ leftNeighbors G b).card : ℝ) := by
      simpa only [R, bipartiteRobustNeighbors, Finset.mem_filter,
        Finset.mem_univ, true_and] using hbR
    have hmul := mul_le_mul_of_nonneg_left hle hν
    have hnonneg := mul_nonneg hν hm'
    change ν / 2 * m' ≤ _
    nlinarith
  have hcard : (R ∩ B').card ≤ R'.card := by
    have h := Finset.card_le_card hsubset
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h
  have hunion : (R ∪ B').card ≤ Fintype.card B := Finset.card_le_univ _
  have hsum := Finset.card_union_add_card_inter R B'
  have hcount : R.card + B'.card ≤ R'.card + Fintype.card B := by omega
  rw [← hbalance, ← hbalance'] at hcount
  have hreal : (R.card : ℝ) + m' ≤ R'.card + m := by
    dsimp [m, m']
    exact_mod_cast hcount
  change (S.card : ℝ) + ν * m ≤ R.card at hex
  change (S.card : ℝ) + ν / 2 * m' ≤ R'.card
  have hmul := mul_le_mul_of_nonneg_left hle hν
  change m - m' ≤ ν * m / 2 at hdelete
  nlinarith

end BipartiteVertices

end Overfull
