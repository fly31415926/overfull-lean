import Overfull.RobustPartition.Pieces
import Overfull.RobustPartition.Scales
import Overfull.RobustPartition.FiniteRefinement
import Overfull.RobustPartition.Split

/-!
# Terminating robust partition refinement

Starting with the whole graph, a failed induced expansion test replaces one
ordinary block by two ordinary blocks or by one block with two ordered shores.
Every replacement preserves the actual partition and increases its shore rank
by one.  A density bound limits that rank, so the fixed finite scale ladder
contains a stage at which every ordinary block is a robust expander.
-/

namespace Overfull.RobustPartition

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Realize a split inside the current list, retaining every untouched piece
at the new error scale and increasing the number of shores by exactly one. -/
private theorem replace_ordinary_of_split (G : SimpleGraph V) (a ε μ : ℝ)
    (hεμ : ε ≤ μ) (L : List (Piece V)) (U : Finset V)
    (hU : Piece.ordinary U ∈ L) (hpart : IsPartition L)
    (hvalid : ∀ p ∈ L, p.Valid G a ε) (hsplit : SplitOutcome G a μ U) :
    ∃ L' : List (Piece V), IsPartition L' ∧
      (∀ p ∈ L', p.Valid G a μ) ∧ rank L < rank L' := by
  obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp hU
  obtain ⟨P, Q, hPQ, hunion, hPsize, hQsize, houtcome⟩ := hsplit
  have hnew := partition_replace_ordinary left right U P Q hpart hPQ hunion
  have hleft (p : Piece V) (hp : p ∈ left) : p.Valid G a μ := by
    apply Piece.valid_mono G a ε μ hεμ p
    exact hvalid p (List.mem_append_left _ hp)
  have hright (p : Piece V) (hp : p ∈ right) : p.Valid G a μ := by
    apply Piece.valid_mono G a ε μ hεμ p
    exact hvalid p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  rcases houtcome with hcuts | hbip
  · refine ⟨left ++ .ordinary P :: .ordinary Q :: right, hnew.1, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | rfl | hp
      · exact hleft p hp
      · exact ⟨hPsize, hcuts.1⟩
      · exact ⟨hQsize, hcuts.2⟩
      · exact hright p hp
    · simp only [rank_append, rank_ordinary_cons]
      omega
  · refine ⟨left ++ .bipartite P Q :: right, hnew.2, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact hleft p hp
      · exact ⟨hPQ, hPsize, hQsize, hbip.1, hbip.2⟩
      · exact hright p hp
    · simp only [rank_append, rank_ordinary_cons, rank_bipartite_cons]
      omega

/-- A uniform finite scale ladder produces an actual terminal partition.
The stage and partition may depend on the graph; every scale was fixed before
the graph and every ordinary terminal piece satisfies actual induced robust
expansion at that stage's common parameter. -/
theorem exists_terminal_partition (G : SimpleGraph V)
    (a τ : ℝ) (f : ℝ → ℝ) (K : ℕ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hK : (2 / a : ℝ) ≤ K) (ladder : ScaleLadder a τ f K)
    (d : ℝ) (hn : 0 < (Fintype.card V : ℝ))
    (had : a * (Fintype.card V : ℝ) ≤ d)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hdegree' : ∀ v, (G.degree v : ℝ) ≤ d + ladder.gamma * (Fintype.card V : ℝ)) :
    ∃ i < K, ∃ L : List (Piece V), IsPartition L ∧
      (∀ p ∈ L, p.Valid G a ((ladder.rho i)^2)) ∧
      (∀ p ∈ L, p.Terminal G (ladder.nu i) τ) := by
  let valid (i : ℕ) (L : List (Piece V)) : Prop :=
    IsPartition L ∧ ∀ p ∈ L, p.Valid G a ((ladder.rho i)^2)
  let terminal (i : ℕ) (L : List (Piece V)) : Prop :=
    ∀ p ∈ L, p.Terminal G (ladder.nu i) τ
  have hstart : ∃ L, valid 0 L ∧ 0 < rank L := by
    refine ⟨[.ordinary (Finset.univ : Finset V)],
      valid_initial G a ((ladder.rho 0)^2) ha1 (sq_nonneg _), ?_⟩
    simp [rank, shoreList, Piece.shoreList]
  have hbound : ∀ i ≤ K, ∀ L, valid i L → rank L ≤ K := by
    intro i _hi L hL
    have hcoarse := valid_rank_bound G a ((ladder.rho i)^2) hn L hL.1 hL.2
    have hrank : (rank L : ℝ) ≤ 2 / a := (le_div_iff₀ ha).mpr hcoarse
    exact_mod_cast hrank.trans hK
  have hstep : ∀ i < K, ∀ L, valid i L → ¬ terminal i L →
      ∃ L', valid (i + 1) L' ∧ rank L < rank L' := by
    intro i hi L hL hnot
    have hfailure : ¬ ∀ p ∈ L, p.Terminal G (ladder.nu i) τ := hnot
    push_neg at hfailure
    obtain ⟨p, hp, hpnot⟩ := hfailure
    cases p with
    | bipartite A B => exact False.elim (hpnot trivial)
    | ordinary U =>
        have hUvalid := hL.2 (.ordinary U) hp
        have hnext : i + 1 ≤ K := Nat.succ_le_of_lt hi
        have hsplit : SplitOutcome G a ((ladder.rho (i + 1))^2) U :=
          nonexpanding_block_split G a τ d ladder.gamma ((ladder.rho i)^2)
            (ladder.nu i) ((ladder.rho (i + 1))^2) ha ha1 hτ hτ1 hn
            ladder.gamma_pos.le (sq_nonneg _) (ladder.nu_pos i hi.le)
            (sq_pos_of_pos (ladder.rho_pos (i + 1) hnext))
            (ladder.split_range i hi) (ladder.split_expansion i hi)
            (ladder.error_le_nu i hi.le) (ladder.gamma_le_nu i hi.le)
            had hdegree hdegree' U hUvalid.1 hUvalid.2 hpnot
        obtain ⟨L', hpart', hvalid', hrank'⟩ := replace_ordinary_of_split G a
          ((ladder.rho i)^2) ((ladder.rho (i + 1))^2) (ladder.error_mono i hi)
          L U hp hL.1 hL.2 hsplit
        exact ⟨L', ⟨hpart', hvalid'⟩, hrank'⟩
  obtain ⟨i, hi, L, hL, hterminal⟩ :=
    exists_terminal_of_bounded_rank K valid terminal rank hstart hbound hstep
  exact ⟨i, hi, L, hL.1, hL.2, hterminal⟩

end Overfull.RobustPartition
