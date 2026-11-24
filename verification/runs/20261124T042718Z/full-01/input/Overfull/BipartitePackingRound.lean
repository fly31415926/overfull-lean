import Overfull.BipartiteMatchingCompletion
import Overfull.BipartitePackingWorking
import Overfull.BipartitePackingReserve
import Overfull.BipartitePackingParameters

/-!
# One round of adaptive bipartite packing

A large matching is chosen in the actual graph obtained by removing the
reserve, the previously used edges, and the current forbidden vertices.
It is completed through the unused reserve. The resulting graph degree
bounds and the total load recurrence concern the actual enlarged edge union.
-/

namespace Overfull.BipartitePackingRound

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting

variable {V : Type*} [Fintype V]

/-- Appending an edge-disjoint graph adds its actual reserve degree. -/
theorem extended_reserve_degree (R U N : SimpleGraph V) (hUN : Disjoint U N) (v : V) :
    (R ⊓ (U ⊔ N)).degree v = (R ⊓ U).degree v + (N ⊓ R).degree v := by
  have hn : (R ⊓ (U ⊔ N)).neighborFinset v =
      (R ⊓ U).neighborFinset v ∪ (N ⊓ R).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union,
      SimpleGraph.inf_adj, SimpleGraph.sup_adj]
    tauto
  have hd : Disjoint ((R ⊓ U).neighborFinset v) ((N ⊓ R).neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hwU hwN
    have hU : U.Adj v w := ((R ⊓ U).mem_neighborFinset v w |>.mp hwU).2
    have hN : N.Adj v w := ((N ⊓ R).mem_neighborFinset v w |>.mp hwN).1
    exact hUN.le_bot ⟨hU, hN⟩
  change ((R ⊓ (U ⊔ N)).neighborFinset v).card = _
  rw [hn, Finset.card_union_of_disjoint hd]
  rfl

variable {A B I : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- One complete packing round, including the choice of the preliminary
matching and every augmenting path. All hypotheses concern the existing
history, the given graphs, and the current forbidden set.

The output includes the actual enlarged-union capacity and the affine
recurrence for its total reserve degree. The natural number `h` is the
number of unmatched pairs in the constructed preliminary matching.
-/
theorem exists_round
    (G R : SimpleGraph (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hRG : R ≤ G) (M : I → G.Subgraph) (T : Finset I)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe)
    (S : Finset (A ⊕ B)) (m ℓ : ℕ) (Δ p ε γ c₀ θ τ δ₀ μ : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ) (hc₀ : 0 ≤ c₀)
    (hθ : 0 < θ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hμθ : μ ≤ θ / 2) (hμδ : μ ≤ δ₀ / 2) (hδτ : 2 * τ ≤ δ₀ - μ)
    (hlarge : 2 ≤ μ * m) (hslack : 1 ≤ min θ δ₀ * m / 8)
    (hεγ : ε < γ / 16) (hcε : 4 * c₀ * ε / μ < γ / 8)
    (hsmall : (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
      min θ δ₀ / 8)
    (hℓ : Nat.ceil (2 / (θ / 2)) + 2 ≤ ℓ)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (hbalanced : (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ S)).card =
      (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ S)).card)
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hRmin : ∀ v, δ₀ * m ≤ (R.degree v : ℝ))
    (hRexpand : IsBipartiteRobustExpander R θ τ)
    (hmissing : ∀ v, (missingCount G M T v : ℝ) ≤ ε * m)
    (hS : (S.card : ℝ) ≤ ε * m)
    (hd : γ * m / 2 ≤ (1 - p) * Δ - T.card)
    (hcapacity : ∀ v, reserveLoad G R M T v ≤ Nat.floor (μ * m))
    (hload : (∑ v, (reserveLoad G R M T v : ℝ)) ≤ c₀ * ε * (m : ℝ) ^ 2) :
    ∃ (N : G.Subgraph) (h : ℕ),
      N.IsMatching ∧ N.verts = (S : Set (A ⊕ B))ᶜ ∧
      Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) T) ∧
      (∀ v, (R ⊓ (edgeUnion (fun i => (M i).spanningCoe) T ⊔ N.spanningCoe)).degree v ≤
        Nat.floor (μ * m)) ∧
      ((h : ℝ) ≤ (8 * ε * (m : ℝ) ^ 2 + ∑ v, (reserveLoad G R M T v : ℝ)) /
        ((1 - p) * Δ - T.card)) ∧
      ((h : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ) ∧
      (∑ v, (N.spanningCoe ⊓ R).degree v ≤ 2 * ℓ * h) ∧
      (∑ v, ((R ⊓ (edgeUnion (fun i => (M i).spanningCoe) T ⊔ N.spanningCoe)).degree v : ℝ)) ≤
        (1 + 4 * ℓ / (γ * m)) * (∑ v, (reserveLoad G R M T v : ℝ)) +
          32 * ℓ * ε * m / γ := by
  classical
  let U := edgeUnion (fun i => (M i).spanningCoe) T
  let Q := R \ U
  let u := reserveLoad G R M T
  let r := Nat.floor (μ * m)
  let d : ℝ := (1 - p) * Δ - T.card
  let t : ℝ := ∑ v, (u v : ℝ)
  obtain ⟨hr, hworkingBudget⟩ := BipartitePackingParameters.capacity_budget
    m μ γ ε c₀ d hm hμ hγ hlarge hεγ hcε hd
  obtain ⟨L, hL, hLS, hLR, hLU, hLcover, hLbalance, hLdef, hLcoarse⟩ :=
    BipartitePackingWorking.exists_large_matching_outside_reserve G R hbip hRG M T
      hM hdisj S m r Δ p ε γ c₀ hm hr hε hγ hA hB (by
        convert hbalanced using 1 <;> congr 1 <;> ext v <;> simp) hG hR hmissing hS
      hd hload hworkingBudget
  let K : (⊤ : SimpleGraph (A ⊕ B)).Subgraph := {
    verts := L.verts
    Adj := L.Adj
    adj_sub := fun h => (show G ≤ ⊤ from le_top) (L.adj_sub h)
    edge_vert := L.edge_vert
    symm := L.symm
  }
  have hK : IsCrossingMatching K := by
    refine ⟨hL, ?_, ?_⟩
    · intro a a' h
      simpa using hbip.mem_of_adj (L.adj_sub h)
    · intro b b' h
      simpa using hbip.mem_of_adj (L.adj_sub h)
  have hKR : ∀ v w, K.Adj v w → ¬R.Adj v w := by
    intro v w hvw hRvw
    exact hLR.le_bot ⟨hvw, hRvw⟩
  have hKS : ∀ v ∈ S, v ∉ K.verts := by
    intro v hvS hvL
    exact hLS hvL hvS
  let Z : Finset (A ⊕ B) := univ.filter (fun v => v ∉ S ∧ u v = r)
  have hZ : ∀ v ∈ Z, v ∈ K.verts := by
    intro v hv
    obtain ⟨_, hvS, hvr⟩ := Finset.mem_filter.mp hv
    exact hLcover v hvS (show r ≤ u v from hvr.symm.le)
  have hZcard : (Z.card : ℝ) ≤ 2 * c₀ * ε * m / μ :=
    BipartitePackingBounds.saturated_vertices_bound u Z m μ c₀ ε hm hμ hlarge
      (fun v hv => (Finset.mem_filter.mp hv).2.2) hload
  have hleftCount : BipartiteMatchingCompletion.uncoveredLeftOutside K S =
      BipartitePackingWorking.uncoveredLeftOutside G L S := by
    ext a
    simp [BipartiteMatchingCompletion.uncoveredLeftOutside,
      BipartitePackingWorking.uncoveredLeftOutside, K]
  have hrightCount : BipartiteMatchingCompletion.uncoveredRightOutside K S =
      BipartitePackingWorking.uncoveredRightOutside G L S := by
    ext b
    simp [BipartiteMatchingCompletion.uncoveredRightOutside,
      BipartitePackingWorking.uncoveredRightOutside, K]
  have hbalance : (BipartiteMatchingCompletion.uncoveredLeftOutside K S).card =
      (BipartiteMatchingCompletion.uncoveredRightOutside K S).card := by
    rw [hleftCount, hrightCount]
    exact hLbalance
  let h := (BipartiteMatchingCompletion.uncoveredLeftOutside K S).card
  have hhdef : (h : ℝ) ≤ (8 * ε * (m : ℝ) ^ 2 + t) / d := by
    dsimp only [h]
    rw [hleftCount]
    exact hLdef
  have hhcoarse : (h : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ := by
    dsimp only [h]
    rw [hleftCount]
    exact hLcoarse
  have hRbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
    exact ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj (hRG h)⟩
  have hQbip : Q.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
    exact ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj (hRG h.1)⟩
  have hureal (v : A ⊕ B) : (u v : ℝ) ≤ μ * m := by
    have hu : (u v : ℝ) ≤ r := by exact_mod_cast hcapacity v
    exact hu.trans (Nat.floor_le (by positivity))
  have hQexpand : IsBipartiteRobustExpander Q (θ / 2) τ := by
    apply BipartitePackingReserve.unused_reserve_robust_half G R M T θ τ μ
      hRexpand hRbip hμ.le hμθ
    simpa only [hA] using hureal
  have hQmin (v : A ⊕ B) : (δ₀ - μ) * Fintype.card A ≤ (Q.degree v : ℝ) := by
    rw [hA]
    exact unused_reserve_degree_lower G R M T δ₀ μ m hRmin hureal v
  have hQleft (a : A) : (δ₀ - μ) * Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ) := by
    have heq := RandomReserve.crossingDegree_eq_degree Q hQbip (.inl a)
    have hdeg : (rightNeighbors Q a).card = Q.degree (.inl a) := heq
    simpa only [hdeg] using hQmin (.inl a)
  have hQright (b : B) : (δ₀ - μ) * Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ) := by
    have heq := RandomReserve.crossingDegree_eq_degree Q hQbip (.inr b)
    have hdeg : (leftNeighbors Q b).card = Q.degree (.inr b) := heq
    simpa only [hdeg] using hQmin (.inr b)
  have hcompletionBudget : (S.card : ℝ) + 2 * Z.card + 2 * ℓ * h ≤
      min (θ / 2) (δ₀ - μ) * Fintype.card A / 2 - 1 := by
    rw [hA]
    exact BipartitePackingParameters.completion_budget m h Z.card S.card ℓ θ δ₀ μ γ ε c₀
      hγ hε hc₀ hμδ hslack hS hZcard hhcoarse hsmall
  obtain ⟨N, hN, hNverts, _, hNedges, hNzero, hNone, hNtotal⟩ :=
    BipartiteMatchingCompletion.exists_completion_in_graph Q R G sdiff_le
      (sdiff_le.trans hRG) K hK (fun _ _ he => L.adj_sub he) hKR
      S Z hKS hZ hbalance (θ / 2) τ (δ₀ - μ) (by positivity) hτ hδτ
      hQleft hQright hQexpand ℓ hℓ hcompletionBudget
  have hNU : Disjoint N.spanningCoe U := by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    rcases hNedges v w hvw.1 with hk | hq
    · exact hLU.le_bot ⟨hk, hvw.2⟩
    · exact hq.2 hvw.2
  have hafter (v : A ⊕ B) : (R ⊓ (U ⊔ N.spanningCoe)).degree v =
      u v + (N.spanningCoe ⊓ R).degree v :=
    extended_reserve_degree R U N.spanningCoe hNU.symm v
  have hcap (v : A ⊕ B) : (R ⊓ (U ⊔ N.spanningCoe)).degree v ≤ r := by
    rw [hafter]
    by_cases hv : u v = r
    · have hnzero : (N.spanningCoe ⊓ R).degree v = 0 := by
        by_cases hvS : v ∈ S
        · exact hNzero v (Finset.mem_union_left _ hvS)
        · exact hNzero v (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, hv⟩))
      rw [hnzero, Nat.add_zero, hv]
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
  have hNtotalR : (∑ v, ((N.spanningCoe ⊓ R).degree v : ℝ)) ≤ 2 * (ℓ : ℝ) * h := by
    exact_mod_cast hNtotal
  have huse : (∑ v, ((R ⊓ (U ⊔ N.spanningCoe)).degree v : ℝ)) ≤ t + 2 * ℓ * h := by
    rw [hafterTotal]
    linarith
  refine ⟨N, h, hN, hNverts, hNU, hcap, hhdef, hhcoarse, hNtotal, ?_⟩
  exact BipartitePackingBounds.reserve_step_bound m h ℓ γ ε d t _
    hm (by positivity) hγ hd hhdef huse

end Overfull.BipartitePackingRound
