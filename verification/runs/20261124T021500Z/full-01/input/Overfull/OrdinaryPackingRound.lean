import Overfull.OrdinaryMatchingCompletion
import Overfull.OrdinaryPackingWorking
import Overfull.OrdinaryPackingBounds
import Overfull.OrdinaryRobustStability
import Overfull.BipartitePackingRound
import Overfull.PairedCut.Matching

/-!
# One round of adaptive ordinary matching packing

The preliminary matching is constructed in the actual working graph.
The unused reserve on the remaining vertices gives an actual paired cut,
through which the matching is completed while protecting every saturated
vertex. All reserve counts refer to the resulting actual enlarged union.
-/

namespace Overfull.OrdinaryPackingRound

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting OrdinaryPackingWorking

set_option maxHeartbeats 1200000 in
/-- Uniform paired-cut constants give one complete ordinary packing
round. Every graph and matching in the conclusion is constructed from the
given reserve, history, and current forbidden set. -/
theorem exists_round (lam θ σ : ℝ)
    (hlam : 0 < lam) (hθ : 0 < θ) (hθσ : θ ≤ 4*σ)
    (hσ : σ ≤ 1/16) (hσlam : 16*σ ≤ lam/3) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [DecidableEq V]
        (G R : SimpleGraph V) (_hRG : R ≤ G) (M : I → G.Subgraph) (T : Finset I)
        (S : Finset V) (m ℓ : ℕ) (Δ p ε γ c₀ μ : ℝ),
        n₀ ≤ m → 0 < m → Fintype.card V = m →
        (∀ i ∈ T, (M i).IsMatching) →
        (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (M i).spanningCoe (M j).spanningCoe) →
        0 ≤ ε → 0 < γ → 0 ≤ c₀ → 0 < μ →
        μ ≤ θ/2 → μ+ε ≤ lam/2 → ε ≤ θ/2 → ε ≤ 1/2 → ε ≤ γ/40 →
        1 ≤ ε*m → 2 ≤ μ*m → 16 ≤ min ξ (lam/3)*m →
        4*c₀*ε/μ < γ/8 →
        (4*c₀/μ + 30*ℓ*(1+c₀)/γ)*ε ≤ min ξ (lam/3)/16 →
        Nat.ceil (2/ξ)+2 ≤ ℓ → Even (m-S.card) →
        (∀ v, Δ-ε*m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ+ε*m) →
        (∀ v, |(R.degree v : ℝ)-p*Δ| ≤ 2*ε*m) →
        (∀ v, lam*m ≤ (R.degree v : ℝ)) → IsRobustExpander R θ σ →
        (∀ v, (missingCount G M T v : ℝ) ≤ ε*m) →
        (S.card : ℝ) ≤ ε*m → γ*m/2 ≤ (1-p)*Δ-T.card →
        (∀ v, reserveLoad G R M T v ≤ Nat.floor (μ*m)) →
        (∑ v, (reserveLoad G R M T v : ℝ)) ≤ c₀*ε*(m : ℝ)^2 →
        ∃ (N : G.Subgraph) (h : ℕ),
          N.IsMatching ∧ N.verts = (↑S : Set V)ᶜ ∧
          Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) T) ∧
          (∀ v, (R ⊓ (edgeUnion (fun i => (M i).spanningCoe) T ⊔ N.spanningCoe)).degree v ≤
            Nat.floor (μ*m)) ∧
          (h : ℝ) ≤ (30/γ)*(ε*m + (∑ v, (reserveLoad G R M T v : ℝ))/m) ∧
          (h : ℝ) ≤ 30*(1+c₀)*ε*m/γ ∧
          (∑ v, (N.spanningCoe ⊓ R).degree v) ≤ ℓ*h ∧
          (∑ v, ((R ⊓ (edgeUnion (fun i => (M i).spanningCoe) T ⊔ N.spanningCoe)).degree v : ℝ)) ≤
            (1+60*ℓ/(γ*m))*(∑ v, (reserveLoad G R M T v : ℝ)) + 60*ℓ*ε*m/γ := by
  classical
  have hσpos : 0 < σ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨ξ, hξ, nCut, hcut⟩ := PairedCut.exists_matching_cut (lam/2) (θ/2) (2*σ)
    (by positivity) (by positivity) (by linarith) (by linarith)
  refine ⟨ξ, hξ, 2*nCut, ?_⟩
  intro V I _ _ G R hRG M T S m ℓ Δ p ε γ c₀ μ hn hm hV hM hdisj
    hε hγ hc₀ hμ hμθ hμεlam hεθ hεhalf hεγ hεm hμm hηm hcε hsmall hℓ
    hparity hG hR hRmin hRexpand hmissing hS hd hcapacity hload
  let U := edgeUnion (fun i => (M i).spanningCoe) T
  let P := R \ U
  let H := P.induce (↑S : Set V)ᶜ
  let u := reserveLoad G R M T
  let r := Nat.floor (μ*m)
  let t : ℝ := ∑ v, (u v : ℝ)
  let d : ℝ := (1-p)*Δ-T.card
  have hεγ' : ε < γ/16 := by linarith only [hεγ, hγ]
  obtain ⟨hr, hbudget₀⟩ := BipartitePackingParameters.capacity_budget
    m μ γ ε c₀ d hm hμ hγ hμm hεγ' hcε hd
  have hbudget : 2*t < (r : ℝ)*(d-4*ε*m) := by
    have hh := mul_le_mul_of_nonneg_left hload (by norm_num : (0 : ℝ) ≤ 2)
    exact hh.trans_lt hbudget₀
  obtain ⟨L, hL, hLS, hLR, hLU, hLcover, _hLeven, _hLdef, hLcoarse⟩ :=
    exists_large_matching_outside_reserve G R hRG M T hM hdisj S m r Δ p ε γ
      hm hr hε hγ hεγ hεm hV.le (by simpa only [hV] using hparity)
      hG hR hmissing hS hd hbudget
  let h := (uncoveredOutside G L S).card
  have hhcoarse : (h : ℝ) ≤ 30*(1+c₀)*ε*m/γ :=
    OrdinaryPackingBounds.deficiency_with_total_bound m h γ ε c₀ t hm hγ hLcoarse hload
  let Z := univ.filter (fun v => v ∉ S ∧ u v = r)
  have hZ (v : V) (hv : v ∈ Z) : v ∈ L.verts := by
    obtain ⟨_, hvS, hvr⟩ := Finset.mem_filter.mp hv
    exact hLcover v hvS (show r ≤ u v from hvr.symm.le)
  have hZcard : (Z.card : ℝ) ≤ 2*c₀*ε*m/μ :=
    BipartitePackingBounds.saturated_vertices_bound u Z m μ c₀ ε hm hμ hμm
      (fun v hv => (Finset.mem_filter.mp hv).2.2) hload
  have hureal (v : V) : (u v : ℝ) ≤ μ*m := by
    have hh : (u v : ℝ) ≤ r := by exact_mod_cast hcapacity v
    exact hh.trans (Nat.floor_le (by positivity))
  have hremain : Fintype.card (Remaining S) = m-S.card := by
    have hh := remaining_order S
    rw [hV] at hh
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hSbound : (S.card : ℝ) ≤ (m : ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hεhalf (Nat.cast_nonneg m (α := ℝ))
    linarith only [hh, hS]
  have hremainLarge : m ≤ 2*Fintype.card (Remaining S) := by
    have hs : 2*S.card ≤ m := by exact_mod_cast (show 2*(S.card : ℝ) ≤ m by linarith)
    rw [hremain]
    omega
  have hCutOrder : nCut ≤ Fintype.card (Remaining S) := by omega
  have hHrobust : IsRobustExpander H (θ/2) (2*σ) := by
    have hdelete : (Fintype.card V : ℝ)-Sᶜ.card ≤ θ*Fintype.card V/2 := by
      have hc : (S.card : ℝ) + Sᶜ.card = Fintype.card V := by
        exact_mod_cast Finset.card_add_card_compl S
      have he := mul_le_mul_of_nonneg_right hεθ (Nat.cast_nonneg m (α := ℝ))
      rw [hV] at hc ⊢
      linarith only [hc, he, hS]
    have hh := OrdinaryPackingReserve.unused_reserve_after_vertex_deletion
      G R M T θ σ μ hRexpand hθ.le hθ1 hσpos.le (by linarith) hμθ
      (by simpa only [hV] using hureal) Sᶜ hdelete
    let eW : Remaining S ≃ ↥((Sᶜ : Finset V) : Set V) :=
      { toFun v := ⟨v.val, Finset.mem_compl.mpr v.property⟩
        invFun v := ⟨v.val, Finset.mem_compl.mp v.property⟩
        left_inv v := by rfl
        right_inv v := by rfl }
    convert RobustRealization.robust_comap_equiv
      (P.induce ((Sᶜ : Finset V) : Set V)) eW (θ/2) (2*σ) hh using 1
  have hHmin (v : Remaining S) :
      (lam/2)*Fintype.card (Remaining S) ≤ (H.degree v : ℝ) := by
    have hp : (lam-μ)*m ≤ (P.degree v.val : ℝ) := by
      have hh := unused_reserve_degree_lower G R M T lam μ m hRmin hureal v.val
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hh
    have hdel := (induced_compl_degree_bounds P S v).2
    have hdelR : (P.degree v.val : ℝ) ≤ H.degree v + S.card := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdel ⊢
      exact_mod_cast hdel
    have horder : (Fintype.card (Remaining S) : ℝ) ≤ m := by
      rw [hremain]
      exact_mod_cast Nat.sub_le m S.card
    have hlamorder := mul_le_mul_of_nonneg_left horder (show 0 ≤ lam/2 by positivity)
    have hlamsmall := mul_le_mul_of_nonneg_right hμεlam (Nat.cast_nonneg m (α := ℝ))
    nlinarith only [hp, hdelR, hS, hlamorder, hlamsmall]
  let K := OrdinaryMatchingCompletion.restrictMatching G L S
  have hK : K.IsMatching := OrdinaryMatchingCompletion.restrictMatching_isMatching G L hL S hLS
  have hWeven : Even (Fintype.card (Remaining S)) := by rw [hremain]; exact hparity
  obtain ⟨A, B, e, Q, hbalance, hleftM, hrightM, hQH, hleft, hright, hQexpand⟩ :=
    hcut (Remaining S) (G.induce (↑S : Set V)ᶜ) H K hK hWeven hCutOrder hHmin hHrobust
  have hδeq : 2*(lam/2)/3 = lam/3 := by ring
  have hleft' : ∀ a, (lam/3)*Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ) := by
    simpa only [hδeq] using hleft
  have hright' : ∀ b, (lam/3)*Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ) := by
    simpa only [hδeq] using hright
  have hside : m ≤ 4*Fintype.card A := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_sum, ← hbalance] at hc
    omega
  have hcompletionBudget : (2 : ℝ)*Z.card + ℓ*h ≤
      min ξ (lam/3)*Fintype.card A/2-1 :=
    OrdinaryPackingBounds.completion_budget m (Fintype.card A) Z.card h ℓ γ ε c₀ μ
      (min ξ (lam/3)) (Nat.cast_nonneg ℓ) (by positivity) hside hηm hZcard hhcoarse hsmall
  obtain ⟨N, hN, hNverts, hNedges, hNzero, hNone, hNtotal⟩ :=
    OrdinaryMatchingCompletion.exists_completion_outside_set G R P sdiff_le
      (sdiff_le.trans hRG) L hL S hLS hLR e hbalance hleftM hrightM
      Q hQH Z hZ ξ (8*σ) (lam/3) hξ (by positivity) (by linarith)
      hleft' hright' (by simpa only [show 4*(2*σ)=8*σ by ring] using hQexpand)
      ℓ hℓ hcompletionBudget
  have hNU : Disjoint N.spanningCoe U := by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    rcases hNedges v w hvw.1 with hLvw | hPvw
    · exact hLU.le_bot ⟨hLvw, hvw.2⟩
    · exact hPvw.2 hvw.2
  have hafter (v : V) : (R ⊓ (U ⊔ N.spanningCoe)).degree v =
      u v + (N.spanningCoe ⊓ R).degree v :=
    BipartitePackingRound.extended_reserve_degree R U N.spanningCoe hNU.symm v
  have hcap (v : V) : (R ⊓ (U ⊔ N.spanningCoe)).degree v ≤ r := by
    rw [hafter]
    by_cases hv : u v = r
    · have hz : (N.spanningCoe ⊓ R).degree v = 0 := by
        by_cases hvS : v ∈ S
        · exact hNzero v (Finset.mem_union_left _ hvS)
        · exact hNzero v (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, hv⟩))
      rw [hz, Nat.add_zero, hv]
    · have hc : u v ≤ r := hcapacity v
      have hn := hNone v
      omega
  have hafterTotal : (∑ v, ((R ⊓ (U ⊔ N.spanningCoe)).degree v : ℝ)) =
      t + ∑ v, ((N.spanningCoe ⊓ R).degree v : ℝ) := by
    calc
      _ = ∑ v, ((u v : ℝ) + (N.spanningCoe ⊓ R).degree v) := by
        apply Finset.sum_congr rfl
        intro v _
        exact_mod_cast hafter v
      _ = _ := Finset.sum_add_distrib
  have hNtotalR : (∑ v, ((N.spanningCoe ⊓ R).degree v : ℝ)) ≤ (ℓ : ℝ)*h := by
    exact_mod_cast hNtotal
  have huse : (∑ v, ((R ⊓ (U ⊔ N.spanningCoe)).degree v : ℝ)) ≤ t + 2*ℓ*h := by
    rw [hafterTotal]
    have hh : (0 : ℝ) ≤ (ℓ : ℝ)*h := by positivity
    nlinarith only [hNtotalR, hh]
  refine ⟨N, h, hN, hNverts, hNU, hcap, hLcoarse, hhcoarse, hNtotal, ?_⟩
  exact OrdinaryPackingBounds.reserve_step_bound m h ℓ γ ε t _
    hm (Nat.cast_nonneg ℓ) hγ hLcoarse huse

end Overfull.OrdinaryPackingRound
