import Overfull.PairedCut.Matching
import Overfull.OrdinaryMatchingCompletion
import Overfull.OrdinaryRobustStability

/-!
# Perfect matchings after a small core vertex deletion

The core's robust expansion and minimum degree give an actual perfect
matching on every sufficiently large even remaining vertex set. The cut
is constructed using the proved paired-cut theorem, and Hall's theorem
supplies the matching.
-/

namespace Overfull.ForceMatching

open Finset Classical SimpleGraph
open OrdinaryPackingWorking

/-- A uniform perfect-matching consequence of the paired-cut theorem. -/
theorem exists_ordinary_perfect_matching_threshold (δ ν τ : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ 1/8) (hτδ : 6*τ ≤ δ) :
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → Even (Fintype.card V) →
      (∀ v, δ*Fintype.card V ≤ (G.degree v : ℝ)) →
      IsRobustExpander G ν τ → ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨ξ,hξ,n₀,hcut⟩ := PairedCut.exists_matching_cut δ ν τ hδ hν hντ hτ
  refine ⟨n₀,?_⟩
  intro V _ _ G _ hn heven hdegree hrobust
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    exact False.elim hv
  obtain ⟨A,B,e,Q,hbalance,_hl,_hr,hQG,hleft,hright,hQ⟩ :=
    hcut V G G ⊥ hbot heven hn hdegree hrobust
  have hscale : 4*τ ≤ 2*δ/3 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hscale
    (Nat.cast_nonneg (Fintype.card A) (α := ℝ))
  obtain ⟨M,hM⟩ := bipartite_robust_perfect_matching Q ξ (4*τ) hξ hbalance
    (fun a => hscaled.trans (hleft a)) (fun b => hscaled.trans (hright b)) hQ
  let f : Q →g G := ⟨e,fun h => hQG h⟩
  refine ⟨M.map f,⟨hM.1.map f e.injective,?_⟩⟩
  intro v
  exact ⟨e.symm v,hM.2 (e.symm v),e.apply_symm_apply v⟩

set_option maxHeartbeats 800000 in
/-- The tolerance and order threshold precede the core and the deleted
set. The threshold also makes deletion of one matching edge at each
vertex smaller than half of the original robust parameter. -/
theorem exists_core_completion_parameters (δ ν τ : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ 1/16) (hτδ : 24*τ ≤ δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      (∀ m : ℕ, n₀ ≤ m → 2 ≤ ν*m) ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
        n₀ ≤ Fintype.card V → (S.card : ℝ) ≤ η*Fintype.card V →
        Even (Fintype.card V-S.card) →
        (∀ v, δ*Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = (S : Set V)ᶜ := by
  have hτpos : 0 < τ := hν.trans_le hντ
  obtain ⟨nCut,hcut⟩ := exists_ordinary_perfect_matching_threshold
    (δ/2) (ν/2) (2*τ) (by positivity) (by positivity)
    (by linarith) (by linarith) (by linarith)
  let η := min (δ/4) (min (ν/4) (1/4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η ≤ δ/4 := min_le_left _ _
  have hην : η ≤ ν/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηone : η ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨q,hq⟩ := exists_nat_gt (2/ν)
  let n₀ := max (2*nCut) q
  have hlarge (m : ℕ) (hm : n₀ ≤ m) : 2 ≤ ν*m := by
    have hqm : (q : ℝ) ≤ m := by exact_mod_cast (le_max_right (2*nCut) q).trans hm
    have hh := (div_lt_iff₀ hν).mp (hq.trans_le hqm)
    linarith
  refine ⟨η,hη,n₀,hlarge,?_⟩
  intro V _ _ G _ S hn hS heven hdegree hrobust
  have hSδ : (S.card : ℝ) ≤ (δ/4)*Fintype.card V :=
    hS.trans (mul_le_mul_of_nonneg_right hηδ (Nat.cast_nonneg _))
  have hSν : (S.card : ℝ) ≤ (ν/4)*Fintype.card V :=
    hS.trans (mul_le_mul_of_nonneg_right hην (Nat.cast_nonneg _))
  have hSone : (S.card : ℝ) ≤ (1/4 : ℝ)*Fintype.card V :=
    hS.trans (mul_le_mul_of_nonneg_right hηone (Nat.cast_nonneg _))
  have hScard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hSfour : 4*S.card ≤ Fintype.card V := by
    have hh : (4 : ℝ)*S.card ≤ Fintype.card V := by linarith only [hSone]
    exact_mod_cast hh
  have hremainingOrder : Fintype.card (Remaining S) = Fintype.card V-S.card := by
    have hh := remaining_order S
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hremaining : nCut ≤ Fintype.card (Remaining S) := by
    rw [hremainingOrder]
    have hh : 2*nCut ≤ Fintype.card V := (le_max_left _ _).trans hn
    omega
  have heven' : Even (Fintype.card (Remaining S)) := by
    rwa [hremainingOrder]
  have hremainrobust : IsRobustExpander (G.induce (S : Set V)ᶜ) (ν/2) (2*τ) := by
    have hh := IsRobustExpander.after_vertex_deletion G hrobust hν.le
      (by linarith) hτpos.le (by linarith) Sᶜ
      (by rw [Finset.card_compl]; push_cast [hScard]; nlinarith only [hSν])
    let eW : Remaining S ≃ ↥((Sᶜ : Finset V) : Set V) :=
      { toFun v := ⟨v.val, Finset.mem_compl.mpr v.property⟩
        invFun v := ⟨v.val, Finset.mem_compl.mp v.property⟩
        left_inv v := by rfl
        right_inv v := by rfl }
    convert RobustRealization.robust_comap_equiv
      (G.induce ((Sᶜ : Finset V) : Set V)) eW (ν/2) (2*τ) hh using 1
  have hremaindegree (v : Remaining S) :
      (δ/2)*Fintype.card (Remaining S) ≤
        ((G.induce (S : Set V)ᶜ).degree v : ℝ) := by
    have hdel := (BipartitePackingAccounting.induced_compl_degree_bounds G S v).2
    have hdelR : (G.degree v.val : ℝ) ≤ (G.induce (S : Set V)ᶜ).degree v + S.card := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] at hdel ⊢
      exact_mod_cast hdel
    have hrem : (Fintype.card (Remaining S) : ℝ) ≤ Fintype.card V := by
      rw [hremainingOrder]
      exact_mod_cast Nat.sub_le (Fintype.card V) S.card
    have hscale := mul_le_mul_of_nonneg_left hrem (show 0 ≤ δ/2 by positivity)
    have hd := hdegree v.val
    nlinarith only [hSδ,hdelR,hscale,hd]
  obtain ⟨M,hM⟩ := hcut (Remaining S) (G.induce (S : Set V)ᶜ)
    hremaining heven' hremaindegree hremainrobust
  refine ⟨liftMatching G S M,liftMatching_isMatching G S M hM.1,?_⟩
  rw [liftMatching_verts,hM.2.verts_eq_univ]
  exact Subtype.coe_image_univ _

end Overfull.ForceMatching
