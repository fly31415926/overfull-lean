import Overfull.Dense.SignedFlow

/-!
# Signed flows with unequal bipartite vertex classes

A weighted cut estimate gives the stronger edge bound
`2 * θ / (2 * c - 1)`. Lemma 5.9 of the manuscript follows with its stated
bound `3 * θ / (2 * c - 1)`. Empty vertex classes are included.
-/

namespace Overfull

open Finset

private theorem weighted_product_le {m n p q : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsize : n * p + m * q ≤ m * n) :
    4 * p * q ≤ n * p + m * q := by
  have ht : 0 ≤ n * p + m * q := add_nonneg (mul_nonneg hn.le hp) (mul_nonneg hm.le hq)
  have hsquare := sq_nonneg (n * p - m * q)
  have hproduct := mul_le_mul_of_nonneg_left hsize ht
  have hscaled : (m * n) * (4 * p * q) ≤ (m * n) * (n * p + m * q) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (mul_pos hm hn)).mp hscaled

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- A cut containing at most half of the weighted vertex order has the
required number of actual crossing edges. -/
theorem unequal_bipartite_cut_lower (c : ℝ)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hleft : ∀ a, c * Fintype.card B ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, c * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (X : Finset A) (Y : Finset B)
    (hsize : (Fintype.card B : ℝ) * X.card + (Fintype.card A : ℝ) * Y.card ≤
      (Fintype.card A : ℝ) * Fintype.card B) :
    (c - 1 / 2) * ((Fintype.card B : ℝ) * X.card +
      (Fintype.card A : ℝ) * Y.card) ≤ bipartiteCutSize G X Y := by
  have hx : c * Fintype.card B * X.card ≤
      ∑ a ∈ X, ((rightNeighbors G a).card : ℝ) := by
    calc
      _ = ∑ _a ∈ X, c * Fintype.card B := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun a _ => hleft a
  have hy : c * Fintype.card A * Y.card ≤
      ∑ b ∈ Y, ((leftNeighbors G b).card : ℝ) := by
    calc
      _ = ∑ _b ∈ Y, c * Fintype.card A := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun b _ => hright b
  have hdegree := bipartite_cut_degree_identity G X Y
  have hinside := bipartite_edge_count_le G X Y
  have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hn : (0 : ℝ) < Fintype.card B := by exact_mod_cast hB
  have hproduct := weighted_product_le hm hn
    (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card) hsize
  nlinarith

/-- The unequal-side signed-flow theorem with a stronger constant than
the manuscript requires. No nonemptiness or nonnegativity assumption on
`θ` is added to the statement. -/
theorem dense_unequal_flow_strong (c θ : ℝ) (hc : 1 / 2 < c)
    (hleft : ∀ a, c * Fintype.card B ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, c * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, |r a| ≤ θ * Fintype.card B)
    (hs : ∀ b, |s b| ≤ θ * Fintype.card A)
    (htotal : ∑ a, r a = ∑ b, s b) :
    ∃ z : A → B → ℝ,
      (∀ a b, ¬ G.Adj (.inl a) (.inr b) → z a b = 0) ∧
      (∀ a, ∑ b, z a b = r a) ∧
      (∀ b, ∑ a, z a b = s b) ∧
      ∀ a b, |z a b| ≤ 2 * θ / (2 * c - 1) := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · letI := hA
    have hs0 (b : B) : s b = 0 := abs_nonpos_iff.mp (by simpa using hs b)
    exact ⟨fun _ _ => 0, by simp [hs0]⟩
  · rcases isEmpty_or_nonempty B with hB | hB
    · letI := hB
      have hr0 (a : A) : r a = 0 := abs_nonpos_iff.mp (by simpa using hr a)
      exact ⟨fun _ _ => 0, by simp [hr0]⟩
    · have hm : 0 < Fintype.card A := Fintype.card_pos_iff.mpr hA
      have hn : 0 < Fintype.card B := Fintype.card_pos_iff.mpr hB
      have hnR : (0 : ℝ) < Fintype.card B := by exact_mod_cast hn
      obtain ⟨a⟩ := hA
      have hθ : 0 ≤ θ := by
        by_contra h
        have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge h) hnR
        have hh := hr a
        linarith [abs_nonneg (r a)]
      have hden : 0 < 2 * c - 1 := by linarith
      have hM : 0 ≤ 2 * θ / (2 * c - 1) := by positivity
      apply bipartite_signed_flow_of_cut G (2 * θ / (2 * c - 1)) hM r s htotal
      intro X Y
      have hsmall (U : Finset A) (W : Finset B)
          (hsize : (Fintype.card B : ℝ) * U.card + (Fintype.card A : ℝ) * W.card ≤
            (Fintype.card A : ℝ) * Fintype.card B) :
          |(∑ a ∈ U, r a) - ∑ b ∈ W, s b| ≤
            (2 * θ / (2 * c - 1)) * bipartiteCutSize G U W := by
        have hcut := unequal_bipartite_cut_lower G c hm hn hleft hright U W hsize
        have hh := mul_le_mul_of_nonneg_left hcut hM
        have hcancel : (2 * θ / (2 * c - 1)) *
            ((c - 1 / 2) * ((Fintype.card B : ℝ) * U.card +
              (Fintype.card A : ℝ) * W.card)) =
            θ * ((Fintype.card B : ℝ) * U.card +
              (Fintype.card A : ℝ) * W.card) := by
          field_simp
        calc
          _ ≤ (θ * Fintype.card B) * U.card + (θ * Fintype.card A) * W.card :=
            bipartite_demand_abs_le r s _ _ hr hs U W
          _ = θ * ((Fintype.card B : ℝ) * U.card +
              (Fintype.card A : ℝ) * W.card) := by ring
          _ ≤ _ := by rwa [hcancel] at hh
      apply (le_abs_self _).trans
      by_cases hsize : (Fintype.card B : ℝ) * X.card +
          (Fintype.card A : ℝ) * Y.card ≤ (Fintype.card A : ℝ) * Fintype.card B
      · exact hsmall X Y hsize
      · have hx : (Xᶜ.card : ℝ) + X.card = Fintype.card A := by
          exact_mod_cast Finset.card_compl_add_card X
        have hy : (Yᶜ.card : ℝ) + Y.card = Fintype.card B := by
          exact_mod_cast Finset.card_compl_add_card Y
        have hcomp : (Fintype.card B : ℝ) * Xᶜ.card +
            (Fintype.card A : ℝ) * Yᶜ.card ≤ (Fintype.card A : ℝ) * Fintype.card B := by
          nlinarith
        have hh := hsmall Xᶜ Yᶜ hcomp
        rw [bipartite_demand_compl r s htotal, abs_neg, bipartite_cut_compl] at hh
        exact hh

/-- Lemma 5.9 of the manuscript, with exactly its bound on every real edge
weight. The upper bound `c ≤ 1` is unnecessary for the implication. -/
theorem dense_unequal_flow (c θ : ℝ) (hc : 1 / 2 < c)
    (hleft : ∀ a, c * Fintype.card B ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, c * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, |r a| ≤ θ * Fintype.card B)
    (hs : ∀ b, |s b| ≤ θ * Fintype.card A)
    (htotal : ∑ a, r a = ∑ b, s b) :
    ∃ z : A → B → ℝ,
      (∀ a b, ¬ G.Adj (.inl a) (.inr b) → z a b = 0) ∧
      (∀ a, ∑ b, z a b = r a) ∧
      (∀ b, ∑ a, z a b = s b) ∧
      ∀ a b, |z a b| ≤ 3 * θ / (2 * c - 1) := by
  obtain ⟨z, hzG, hzr, hzs, hz⟩ :=
    dense_unequal_flow_strong G c θ hc hleft hright r s hr hs htotal
  refine ⟨z, hzG, hzr, hzs, ?_⟩
  intro a b
  have hn : (0 : ℝ) < Fintype.card B := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨b⟩
  have hθ : 0 ≤ θ := by
    by_contra h
    have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge h) hn
    have hh := hr a
    linarith [abs_nonneg (r a)]
  have hden : 0 < 2 * c - 1 := by linarith
  exact (hz a b).trans (div_le_div_of_nonneg_right (by linarith) hden.le)

end Overfull

