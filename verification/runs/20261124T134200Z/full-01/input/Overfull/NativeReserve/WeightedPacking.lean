import Overfull.AssignedParts.NativeWeights
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Disjoint selected boundaries from native matching weights

Only the selected original copies must be disjoint. Their parent perfect
matchings may overlap, and empty selected boundaries are allowed.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S P : Type*} [Fintype S] [Fintype P]
  {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

/-- A code heavier than a forbidden set has an actual selected boundary
avoiding that set, even if its parent perfect matching uses the set. -/
theorem exists_sample_avoiding (hk : 0 < k) (code : S → P)
    (F : S → Finset E) (hF : ∀ s, F s ⊆ D.matching s)
    (p : P) (A : Finset E)
    (hweight : (A.card : ℝ) < aggregateWeight (scaledWeight D) code p) :
    ∃ s, code s = p ∧ Disjoint (F s) A := by
  by_contra hn
  push_neg at hn
  have hstat : ∀ s, (if code s = p then 1 else 0) ≤ (F s ∩ A).card := by
    intro s
    split_ifs with hs
    · exact (not_disjoint_iff_nonempty_inter.mp (hn s hs)).card_pos
    · exact Nat.zero_le _
  have hcap := aggregate_capacity D hk code F hF A
    (fun q => if q = p then 1 else 0) hstat
  have hle : aggregateWeight (scaledWeight D) code p ≤ A.card := by
    simpa using hcap
  linarith

/-- A weight of at least `n*B` supplies `n` pairwise disjoint selected
boundaries of the same code when each boundary has at most `B` copies. -/
theorem exists_disjoint_selected_family (hk : 0 < k) (code : S → P)
    (F : S → Finset E) (hF : ∀ s, F s ⊆ D.matching s)
    (p : P) (B : ℕ) (hB : 0 < B) (hsize : ∀ s, (F s).card ≤ B)
    (n : ℕ) (hweight : (n : ℝ)*B ≤ aggregateWeight (scaledWeight D) code p) :
    ∃ f : Fin n → S, (∀ i, code (f i) = p) ∧
      Pairwise (fun i j => Disjoint (F (f i)) (F (f j))) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
    have hprev : (n : ℝ)*B ≤ aggregateWeight (scaledWeight D) code p := by
      push_cast at hweight
      nlinarith
    obtain ⟨f, hf, hdisj⟩ := ih hprev
    let A := univ.biUnion (fun i => F (f i))
    have hcard : A.card ≤ n*B := by
      calc
        _ ≤ ∑ i : Fin n, (F (f i)).card := card_biUnion_le
        _ ≤ ∑ _i : Fin n, B := sum_le_sum (fun i _ => hsize (f i))
        _ = n*B := by simp
    have hlt : (A.card : ℝ) < aggregateWeight (scaledWeight D) code p := by
      have hc : (A.card : ℝ) ≤ (n : ℝ)*B := by exact_mod_cast hcard
      push_cast at hweight
      nlinarith
    obtain ⟨s, hs, havoid⟩ := exists_sample_avoiding D hk code F hF p A hlt
    have havoid' (i : Fin n) : Disjoint (F s) (F (f i)) := by
      apply havoid.mono_right
      exact subset_biUnion_of_mem (fun i => F (f i)) (mem_univ i)
    refine ⟨Fin.snoc f s, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hs
      · simpa using hf j
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · intro _
          simpa using havoid' j
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _
          simpa using (havoid' i).symm
        · intro hij
          simpa using hdisj (show i ≠ j from fun he => hij (congrArg Fin.castSucc he))

end Overfull.NativeReserve
