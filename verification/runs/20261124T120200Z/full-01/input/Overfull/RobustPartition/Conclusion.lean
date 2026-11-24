import Overfull.RobustPartition.Pieces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The quantitative conclusion of a robust partition

Terminal pieces give actual induced robust expanders and actual ordered
almost bipartite shores.  The ambient degree lower bound upgrades their
coarse size bounds, giving the sharp weighted component count.  Small
boundaries also give the required internal-degree conclusion outside an
explicit exceptional set in each whole part.
-/

namespace Overfull.RobustPartition

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def ordinaryCount : List (Piece V) → ℕ
  | [] => 0
  | .ordinary _ :: L => 1 + ordinaryCount L
  | .bipartite _ _ :: L => ordinaryCount L

def bipartiteCount : List (Piece V) → ℕ
  | [] => 0
  | .ordinary _ :: L => bipartiteCount L
  | .bipartite _ _ :: L => 1 + bipartiteCount L

/-- An ordinary component counts once and a bipartite component counts twice. -/
theorem rank_eq_weighted_count (L : List (Piece V)) :
    rank L = ordinaryCount L + 2 * bipartiteCount L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
      cases p with
      | ordinary U =>
          rw [rank_ordinary_cons, ih]
          simp only [ordinaryCount, bipartiteCount]
          omega
      | bipartite A B =>
          rw [rank_bipartite_cons, ih]
          simp only [ordinaryCount, bipartiteCount]
          omega

variable [Fintype V]

/-- The full graph-theoretic output, on an actual list of vertex-set pieces.
`IsPartition` asserts that all ordinary sets and all ordered bipartite shores
are pairwise disjoint and cover the ambient vertex set. -/
structure PartitionConclusion (G : SimpleGraph V) (d ρ ν τ : ℝ)
    (L : List (Piece V)) : Prop where
  partition : IsPartition L
  ordinary : ∀ U : Finset V, Piece.ordinary U ∈ L →
    IsRobustExpander (G.induce (U : Set V)) ν τ ∧
      Real.sqrt ρ * Fintype.card V ≤ (U.card : ℝ)
  bipartite : ∀ A B : Finset V, Piece.bipartite A B ∈ L →
    Disjoint A B ∧
      Real.sqrt ρ * Fintype.card V ≤ (A.card : ℝ) ∧
      Real.sqrt ρ * Fintype.card V ≤ (B.card : ℝ) ∧
      |(A.card : ℝ) - B.card| ≤ ρ * Fintype.card V ∧
      ((internalEdges G A).card : ℝ) + (internalEdges G B).card + cut G (A ∪ B) ≤
        ρ * (Fintype.card V : ℝ)^2
  internal_degree : ∀ p ∈ L, ∃ Z : Finset V, Z ⊆ p.vertices ∧
    (Z.card : ℝ) ≤ ρ * Fintype.card V ∧
      ∀ v ∈ p.vertices, v ∉ Z →
        d - ρ * Fintype.card V ≤ ((G.neighborFinset v ∩ p.vertices).card : ℝ)
  weighted_count : ordinaryCount L + 2 * bipartiteCount L ≤
    ⌊(1 + ρ ^ (1 / (3 : ℝ))) * Fintype.card V / d⌋₊

/-- The ordinary size argument and its two-shore counterpart apply to every
member of the actual shore partition. -/
theorem valid_shore_degree_lower (G : SimpleGraph V) (d a ε : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (ha : 0 < a) (hε : 0 ≤ ε)
    (hn : 0 < (Fintype.card V : ℝ)) (L : List (Piece V))
    (hvalid : ∀ p ∈ L, p.Valid G a ε) :
    ∀ U ∈ shoreList L, d - (2 * ε / a) * Fintype.card V ≤ (U.card : ℝ) := by
  intro U hU
  obtain ⟨p, hp, hUp⟩ := List.mem_flatMap.mp hU
  have hv := hvalid p hp
  cases p with
  | ordinary X =>
      have hUX : U = X := by simpa [Piece.shoreList] using hUp
      subst U
      exact block_size_lower G d a ε hdegree ha hε hn X hv.1 hv.2
  | bipartite A B =>
      have hUAB : U = A ∨ U = B := by simpa [Piece.shoreList] using hUp
      have hsizes := bipartite_sizes_lower G d a ε hdegree ha hε hn A B
        hv.2.1 hv.2.2.1 hv.2.2.2.1
      rcases hUAB with rfl | rfl
      · exact hsizes.1
      · exact hsizes.2

theorem valid_piece_cut_le (G : SimpleGraph V) (a ε : ℝ)
    (p : Piece V) (hp : p.Valid G a ε) :
    cut G p.vertices ≤ ε * (Fintype.card V : ℝ)^2 := by
  cases p with
  | ordinary U => exact hp.2
  | bipartite A B => exact (cut_union_le_bad G A B).trans hp.2.2.2.1

/-- Convert a terminal partition with a quadratic incidence budget into all
the quantitative conclusions of the robust-partition theorem. -/
theorem partition_conclusion_of_terminal (G : SimpleGraph V) (d a ρ ν τ : ℝ)
    (ha : 0 < a) (hn : 0 < (Fintype.card V : ℝ)) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ a^2 / 4) (hρone : ρ ≤ 1)
    (had : a * Fintype.card V ≤ d)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (L : List (Piece V))
    (hpart : IsPartition L)
    (hvalid : ∀ p ∈ L, p.Valid G a (ρ^2))
    (hterminal : ∀ p ∈ L, p.Terminal G ν τ) :
    PartitionConclusion G d ρ ν τ L := by
  have hsqrt : Real.sqrt ρ ≤ a / 2 := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ a / 2)).mpr
    nlinarith
  have hsqrtmul : Real.sqrt ρ * Fintype.card V ≤ a * Fintype.card V / 2 := by
    have h := mul_le_mul_of_nonneg_right hsqrt hn.le
    nlinarith
  have hρsq : ρ^2 ≤ ρ := by nlinarith
  have herr1 := mul_le_mul_of_nonneg_right hρsq hn.le
  have herr2 := mul_le_mul_of_nonneg_right hρsq (sq_nonneg (Fintype.card V : ℝ))
  have hd : 0 < d := (mul_pos ha hn).trans_le had
  refine ⟨hpart, ?_, ?_, ?_, ?_⟩
  · intro U hU
    exact ⟨hterminal (.ordinary U) hU, hsqrtmul.trans (hvalid (.ordinary U) hU).1⟩
  · intro A B hAB
    have hv := hvalid (.bipartite A B) hAB
    exact ⟨hv.1, hsqrtmul.trans hv.2.1, hsqrtmul.trans hv.2.2.1,
      hv.2.2.2.2.trans herr1,
      (internal_edges_add_cut_le_bad G A B hv.1).trans (hv.2.2.2.1.trans herr2)⟩
  · intro p hp
    refine ⟨internalBad G d ρ p.vertices, Finset.filter_subset _ _, ?_, ?_⟩
    · exact bad_internal_degree_count G d ρ hdegree hρ hn p.vertices
        (valid_piece_cut_le G a (ρ^2) p (hvalid p hp))
    · intro v hv hgood
      exact internal_good_of_not_bad G d ρ p.vertices v hv hgood
  · have hcoarse := valid_rank_bound G a (ρ^2) hn L hpart hvalid
    have hmass := lower_mul_length_le_union_card (shoreList L) hpart.1
      (d - (2 * ρ^2 / a) * Fintype.card V)
      (valid_shore_degree_lower G d a (ρ^2) hdegree ha (sq_nonneg ρ) hn L hvalid)
    rw [hpart.2, Finset.card_univ] at hmass
    have hsharp := sharp_count_estimate (rank L) (Fintype.card V) d a ρ
      (Nat.cast_nonneg _) hn.le ha hρ.le hρsmall hcoarse hmass
    have hroot : ρ ≤ ρ ^ (1 / (3 : ℝ)) :=
      Real.self_le_rpow_of_le_one hρ.le hρone (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hroot hn.le
    have hcount : (rank L : ℝ) ≤
        (1 + ρ ^ (1 / (3 : ℝ))) * Fintype.card V / d := by
      apply (le_div_iff₀ hd).mpr
      nlinarith
    rw [← rank_eq_weighted_count]
    exact Nat.le_floor hcount

end Overfull.RobustPartition
