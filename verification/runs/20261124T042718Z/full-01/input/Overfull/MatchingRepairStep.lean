import Overfull.OrdinaryMatchingCompletion
import Overfull.OrdinaryRobustStability
import Overfull.OrdinaryPackingWorking
import Overfull.PairedCut.Matching

/-!
# Completing one matching in an unused ordinary reserve

The paired cut is constructed from the actual surviving reserve. Vertices
already covered by the matching can be protected from any reserve use.
-/

namespace Overfull.MatchingRepairStep

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting OrdinaryPackingWorking

set_option maxHeartbeats 1200000 in
theorem exists_protected_completion (ζ ν τ : ℝ)
    (hζ : 0 < ζ) (hν : 0 < ν) (hντ : ν ≤ 4 * τ)
    (hτ : τ ≤ 1 / 16) (hτζ : 16 * τ ≤ ζ / 3) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G R P : SimpleGraph V) (_hRG : R ≤ G) (_hPR : P ≤ R)
        (M : G.Subgraph), M.IsMatching → Disjoint M.spanningCoe R →
        ∀ X Z : Finset V, M.verts ⊆ (X : Set V)ᶜ →
        (∀ v ∈ Z, v ∈ M.verts) →
        ∀ (m ℓ : ℕ) (μ δ : ℝ), n₀ ≤ m → 0 < m → Fintype.card V = m →
        Even (m - X.card) → 0 ≤ μ → 0 ≤ δ → μ ≤ ν / 2 → μ + δ ≤ ζ / 2 →
        δ ≤ ν / 2 → δ ≤ 1 / 2 →
        (∀ v, ζ * m ≤ (R.degree v : ℝ)) → IsRobustExpander R ν τ →
        (∀ v, (R.degree v : ℝ) ≤ P.degree v + μ * m) →
        (X.card : ℝ) ≤ δ * m → Nat.ceil (2 / ξ) + 2 ≤ ℓ →
        16 ≤ min ξ (ζ / 3) * m →
        (2 : ℝ) * Z.card + ℓ * (uncoveredOutside G M X).card ≤
          min ξ (ζ / 3) * m / 16 →
        ∃ N : G.Subgraph,
          N.IsMatching ∧ N.verts = (X : Set V)ᶜ ∧
          N.spanningCoe ≤ M.spanningCoe ⊔ P ∧
          (∀ v ∈ X ∪ Z, (N.spanningCoe ⊓ R).degree v = 0) ∧
          (∀ v, (N.spanningCoe ⊓ R).degree v ≤ 1) ∧
          (∑ v, (N.spanningCoe ⊓ R).degree v) ≤ ℓ * (uncoveredOutside G M X).card := by
  classical
  have hτpos : 0 < τ := by linarith
  have hν1 : ν ≤ 1 := by linarith
  obtain ⟨ξ, hξ, nCut, hcut⟩ := PairedCut.exists_matching_cut (ζ / 2) (ν / 2) (2 * τ)
    (by positivity) (by positivity) (by linarith) (by linarith)
  refine ⟨ξ, hξ, 2 * nCut, ?_⟩
  intro V _ _ G R P hRG hPR M hM hMR X Z hMX hZ m ℓ μ δ hn hm hV
    hparity hμ _hδ hμν hμδζ hδν hδhalf hRmin hRexpand hloss hX hℓ hslack hbudget
  let Q₀ := P.induce (X : Set V)ᶜ
  have hremain : Fintype.card (Remaining X) = m - X.card := by
    have hh := remaining_order X
    rw [hV] at hh
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hXhalf : (X.card : ℝ) ≤ (m : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hδhalf (Nat.cast_nonneg m (α := ℝ))
    linarith only [hh, hX]
  have hremainLarge : m ≤ 2 * Fintype.card (Remaining X) := by
    have hx : 2 * X.card ≤ m := by
      exact_mod_cast (show 2 * (X.card : ℝ) ≤ m by linarith only [hXhalf])
    rw [hremain]
    omega
  have hCutOrder : nCut ≤ Fintype.card (Remaining X) := by omega
  have hQrobust : IsRobustExpander Q₀ (ν / 2) (2 * τ) := by
    have hdelete : (Fintype.card V : ℝ) - Xᶜ.card ≤ ν * Fintype.card V / 2 := by
      have hc : (X.card : ℝ) + Xᶜ.card = Fintype.card V := by
        exact_mod_cast Finset.card_add_card_compl X
      have he := mul_le_mul_of_nonneg_right hδν (Nat.cast_nonneg m (α := ℝ))
      rw [hV] at hc ⊢
      linarith only [hc, he, hX]
    have hh := IsRobustExpander.after_edge_and_vertex_deletion R P hRexpand hPR
      hν.le hν1 hτpos.le (by linarith) hμν
      (by simpa only [hV] using hloss) Xᶜ hdelete
    let eW : Remaining X ≃ ↥((Xᶜ : Finset V) : Set V) :=
      { toFun v := ⟨v.val, Finset.mem_compl.mpr v.property⟩
        invFun v := ⟨v.val, Finset.mem_compl.mp v.property⟩
        left_inv v := by rfl
        right_inv v := by rfl }
    convert RobustRealization.robust_comap_equiv
      (P.induce ((Xᶜ : Finset V) : Set V)) eW (ν / 2) (2 * τ) hh using 1
  have hQmin (v : Remaining X) :
      (ζ / 2) * Fintype.card (Remaining X) ≤ (Q₀.degree v : ℝ) := by
    have hp : (ζ - μ) * m ≤ (P.degree v.val : ℝ) := by
      have hh := hloss v.val
      have hd := hRmin v.val
      nlinarith only [hh, hd]
    have hdel := (induced_compl_degree_bounds P X v).2
    have hdelR : (P.degree v.val : ℝ) ≤ Q₀.degree v + X.card := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdel ⊢
      exact_mod_cast hdel
    have horder : (Fintype.card (Remaining X) : ℝ) ≤ m := by
      rw [hremain]
      exact_mod_cast Nat.sub_le m X.card
    have hζorder := mul_le_mul_of_nonneg_left horder (show 0 ≤ ζ / 2 by positivity)
    have hζsmall := mul_le_mul_of_nonneg_right hμδζ (Nat.cast_nonneg m (α := ℝ))
    nlinarith only [hp, hdelR, hX, hζorder, hζsmall]
  let K := OrdinaryMatchingCompletion.restrictMatching G M X
  have hK : K.IsMatching := OrdinaryMatchingCompletion.restrictMatching_isMatching G M hM X hMX
  have heven : Even (Fintype.card (Remaining X)) := by rw [hremain]; exact hparity
  obtain ⟨A, B, e, Q, hbalance, hleftM, hrightM, hQP, hleft, hright, hQexpand⟩ :=
    hcut (Remaining X) (G.induce (X : Set V)ᶜ) Q₀ K hK heven hCutOrder hQmin hQrobust
  have hδeq : 2 * (ζ / 2) / 3 = ζ / 3 := by ring
  have hleft' : ∀ a, (ζ / 3) * Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ) := by
    simpa only [hδeq] using hleft
  have hright' : ∀ b, (ζ / 3) * Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ) := by
    simpa only [hδeq] using hright
  have hside : m ≤ 4 * Fintype.card A := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_sum, ← hbalance] at hc
    omega
  have hsideR : (m : ℝ) ≤ 4 * Fintype.card A := by exact_mod_cast hside
  have hη : 0 < min ξ (ζ / 3) := lt_min hξ (by positivity)
  have hsidebound := mul_le_mul_of_nonneg_left hsideR hη.le
  have hcompletion : (2 : ℝ) * Z.card + ℓ * (uncoveredOutside G M X).card ≤
      min ξ (ζ / 3) * Fintype.card A / 2 - 1 := by
    nlinarith only [hbudget, hslack, hsidebound]
  exact OrdinaryMatchingCompletion.exists_completion_outside_set G R P hPR
    (hPR.trans hRG) M hM X hMX hMR e hbalance hleftM hrightM
    Q hQP Z hZ ξ (8 * τ) (ζ / 3) hξ (by positivity) (by linarith)
    hleft' hright' (by simpa only [show 4 * (2 * τ) = 8 * τ by ring] using hQexpand)
    ℓ hℓ hcompletion

end Overfull.MatchingRepairStep
