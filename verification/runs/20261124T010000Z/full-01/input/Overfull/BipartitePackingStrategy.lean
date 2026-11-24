import Overfull.BipartitePackingRound
import Overfull.BipartitePackingHistory
import Overfull.BipartitePackingOnline

/-!
# A fixed strategy for adaptive bipartite packing

The invariant is stated using the actual matching history and actual used
reserve edges. The one-round construction supplies every local choice.
The resulting fixed rule works for arbitrary adaptive forbidden sets that
satisfy the current size, balance, and past incidence conditions.
-/

namespace Overfull.BipartitePackingStrategy

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting BipartitePackingOnline

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The matching and load properties maintained after each completed round. -/
structure Invariant (G R : SimpleGraph (A ⊕ B)) (m ℓ : ℕ) (ε γ μ : ℝ)
    (s : ℕ) (H : Fin s → Finset (A ⊕ B) × G.Subgraph) : Prop where
  matching : ∀ i, (H i).2.IsMatching
  verts : ∀ i, (H i).2.verts = ((H i).1 : Set (A ⊕ B))ᶜ
  disjoint : Pairwise (fun i j => Disjoint (H i).2.spanningCoe (H j).2.spanningCoe)
  capacity : ∀ v, reserveLoad G R (fun i => (H i).2) univ v ≤ Nat.floor (μ * m)
  total : (∑ v, (reserveLoad G R (fun i => (H i).2) univ v : ℝ)) ≤
    8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ s - 1)

/-- The current forbidden set and the incidences of previous forbidden sets
are the only conditions on the input to the next round. -/
structure Allowed (G : SimpleGraph (A ⊕ B)) (m : ℕ) (ε : ℝ)
    (s : ℕ) (H : Fin s → Finset (A ⊕ B) × G.Subgraph) (S : Finset (A ⊕ B)) : Prop where
  balanced : (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ S)).card =
    (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ S)).card
  size : (S.card : ℝ) ≤ ε * m
  incidences : ∀ v, ((univ.filter (fun i : Fin s => v ∈ (H i).1)).card : ℝ) ≤ ε * m

omit [DecidableEq A] [DecidableEq B] in
theorem invariant_zero (G R : SimpleGraph (A ⊕ B)) (m ℓ : ℕ) (ε γ μ : ℝ) :
    Invariant G R m ℓ ε γ μ 0 Fin.elim0 := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro v
    simp
  · simp

omit [DecidableEq A] [DecidableEq B] in
/-- The geometric part of the invariant supplies the fixed total-load budget. -/
theorem Invariant.total_le {G R : SimpleGraph (A ⊕ B)} {m ℓ s : ℕ} {ε γ μ : ℝ}
    {H : Fin s → Finset (A ⊕ B) × G.Subgraph}
    (hH : Invariant G R m ℓ ε γ μ s H)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ) (hs : s ≤ 2 * m) :
    (∑ v, (reserveLoad G R (fun i => (H i).2) univ v : ℝ)) ≤
      8 * (Real.exp (8 * ℓ / γ) - 1) * ε * (m : ℝ) ^ 2 := by
  calc
    _ ≤ 8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ s - 1) := hH.total
    _ ≤ 8 * ε * (m : ℝ) ^ 2 * (Real.exp (8 * ℓ / γ) - 1) := by
      apply mul_le_mul_of_nonneg_left
      · exact sub_le_sub_right
          (BipartitePackingBounds.geometric_factor_bound m s ℓ γ hm
            (Nat.cast_nonneg ℓ) hγ hs) 1
      · positivity
    _ = _ := by ring

/-- Exact covered-vertex sets identify the actual missing count with the
input incidence count used by the admissibility condition. -/
theorem Invariant.missing_le {G R : SimpleGraph (A ⊕ B)} {m ℓ s : ℕ} {ε γ μ : ℝ}
    {H : Fin s → Finset (A ⊕ B) × G.Subgraph} {S : Finset (A ⊕ B)}
    (hH : Invariant G R m ℓ ε γ μ s H) (hS : Allowed G m ε s H S) (v : A ⊕ B) :
    (missingCount G (fun i => (H i).2) univ v : ℝ) ≤ ε * m := by
  rw [missingCount_eq_forbidden G (fun i => (H i).2) univ
    (fun i => (H i).1) (fun i _ => hH.verts i)]
  convert hS.incidences v using 1
  congr 2
  ext i
  simp

private theorem geometric_step (m ℓ s : ℕ) (ε γ t t' : ℝ)
    (hm : 0 < m) (hγ : 0 < γ)
    (ht : t ≤ 8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ s - 1))
    (hstep : t' ≤ (1 + 4 * ℓ / (γ * m)) * t + 32 * ℓ * ε * m / γ) :
    t' ≤ 8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ (s + 1) - 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hconstant : (4 * (ℓ : ℝ) / (γ * m)) * (8 * ε * (m : ℝ) ^ 2) =
      32 * ℓ * ε * m / γ := by field_simp; ring
  calc
    _ ≤ (1 + 4 * ℓ / (γ * m)) * t + 32 * ℓ * ε * m / γ := hstep
    _ ≤ (1 + 4 * ℓ / (γ * m)) *
        (8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ s - 1)) +
          32 * ℓ * ε * m / γ :=
      add_le_add_right (mul_le_mul_of_nonneg_left ht (by positivity)) _
    _ = _ := by rw [pow_succ, ← hconstant]; ring

/-- The graph-theoretic round theorem extends every valid admissible history.
No future input or assumed matching completion enters this conclusion. -/
theorem exists_extension
    (G R : SimpleGraph (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) (hRG : R ≤ G)
    (m ℓ : ℕ) (Δ p ε γ c₀ θ τ δ₀ μ : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hc₀ : c₀ = 8 * (Real.exp (8 * ℓ / γ) - 1))
    (hθ : 0 < θ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hμθ : μ ≤ θ / 2) (hμδ : μ ≤ δ₀ / 2) (hδτ : 2 * τ ≤ δ₀ - μ)
    (hlarge : 2 ≤ μ * m) (hslack : 1 ≤ min θ δ₀ * m / 8)
    (hεγ : ε < γ / 16) (hcε : 4 * c₀ * ε / μ < γ / 8)
    (hsmall : (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
      min θ δ₀ / 8)
    (hℓ : Nat.ceil (2 / (θ / 2)) + 2 ≤ ℓ)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hRmin : ∀ v, δ₀ * m ≤ (R.degree v : ℝ))
    (hRexpand : IsBipartiteRobustExpander R θ τ)
    (s : ℕ) (hs : s ≤ 2 * m)
    (hd : γ * m / 2 ≤ (1 - p) * Δ - s)
    (H : Fin s → Finset (A ⊕ B) × G.Subgraph) (S : Finset (A ⊕ B))
    (hH : Invariant G R m ℓ ε γ μ s H) (hS : Allowed G m ε s H S) :
    ∃ N : G.Subgraph,
      Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N)) := by
  classical
  let M : Fin s → G.Subgraph := fun i => (H i).2
  have hc₀nonneg : 0 ≤ c₀ := by
    rw [hc₀]
    exact BipartitePackingParameters.total_load_coefficient_nonneg ℓ γ hγ
  have hload : (∑ v, (reserveLoad G R M univ v : ℝ)) ≤ c₀ * ε * (m : ℝ) ^ 2 := by
    rw [hc₀]
    exact hH.total_le hm hε hγ hs
  have hd' : γ * m / 2 ≤ (1 - p) * Δ - (univ : Finset (Fin s)).card := by
    simpa using hd
  obtain ⟨N, _, hN, hNverts, hNdisj, hNcapacity, _, _, _, hNtotal⟩ :=
    BipartitePackingRound.exists_round G R hbip hRG M univ
      (fun i _ => hH.matching i) (fun i _ j _ hij => hH.disjoint hij)
      S m ℓ Δ p ε γ c₀ θ τ δ₀ μ hm hε hγ hc₀nonneg hθ hτ hμ hμθ hμδ hδτ
      hlarge hslack hεγ hcε hsmall hℓ hA hB hS.balanced hG hR hRmin hRexpand
      (fun v => hH.missing_le hS v) hS.size hd' hH.capacity hload
  have hproj : (fun i : Fin (s + 1) =>
      ((Fin.snoc H (S, N) : Fin (s + 1) → Finset (A ⊕ B) × G.Subgraph) i).2) =
        Fin.snoc M N := snoc_outputs H S N
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hproj] using BipartitePackingHistory.matching_snoc G M N hH.matching hN
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using hNverts
    | cast i => simpa using hH.verts i
  · simpa only [← hproj] using
      BipartitePackingHistory.pairwise_disjoint_snoc G M N hH.disjoint hNdisj
  · intro v
    have hcap : reserveLoad G R (Fin.snoc M N) univ v ≤ Nat.floor (μ * m) := by
      rw [BipartitePackingHistory.reserveLoad_snoc_graph G R M N v]
      exact hNcapacity v
    simpa only [← hproj] using hcap
  · have hrec : (∑ v, (reserveLoad G R (Fin.snoc M N) univ v : ℝ)) ≤
        (1 + 4 * ℓ / (γ * m)) * (∑ v, (reserveLoad G R M univ v : ℝ)) +
          32 * ℓ * ε * m / γ := by
      calc
        _ = ∑ v, ((R ⊓ (edgeUnion (fun i => (M i).spanningCoe) univ ⊔
            N.spanningCoe)).degree v : ℝ) := by
          apply Finset.sum_congr rfl
          intro v _
          exact_mod_cast BipartitePackingHistory.reserveLoad_snoc_graph G R M N v
        _ ≤ _ := hNtotal
    have htotal := geometric_step m ℓ s ε γ _ _ hm hγ hH.total hrec
    simpa only [← hproj] using htotal

/-- One fixed rule works against every adaptive choice of admissible
forbidden sets. Its construction depends only on the initial graphs and
fixed parameters, before the adversary is specified. -/
theorem exists_strategy
    (G R : SimpleGraph (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) (hRG : R ≤ G)
    (m ℓ : ℕ) (Δ p ε γ c₀ θ τ δ₀ μ : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hc₀ : c₀ = 8 * (Real.exp (8 * ℓ / γ) - 1))
    (hθ : 0 < θ) (hτ : 0 < τ) (hμ : 0 < μ)
    (hμθ : μ ≤ θ / 2) (hμδ : μ ≤ δ₀ / 2) (hδτ : 2 * τ ≤ δ₀ - μ)
    (hlarge : 2 ≤ μ * m) (hslack : 1 ≤ min θ δ₀ * m / 8)
    (hεγ : ε < γ / 16) (hcε : 4 * c₀ * ε / μ < γ / 8)
    (hsmall : (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
      min θ δ₀ / 8)
    (hℓ : Nat.ceil (2 / (θ / 2)) + 2 ≤ ℓ)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hRmin : ∀ v, δ₀ * m ≤ (R.degree v : ℝ))
    (hRexpand : IsBipartiteRobustExpander R θ τ)
    (q : ℕ) (hq : q ≤ 2 * m)
    (hd : ∀ s < q, γ * m / 2 ≤ (1 - p) * Δ - s) :
    ∃ rule : (s : ℕ) → (Fin s → Finset (A ⊕ B) × G.Subgraph) →
        Finset (A ⊕ B) → G.Subgraph,
      ∀ adversary : (s : ℕ) → (Fin s → Finset (A ⊕ B) × G.Subgraph) → Finset (A ⊕ B),
        (∀ s < q, Allowed G m ε s (history rule adversary s)
          (adversary s (history rule adversary s))) →
        ∀ s ≤ q,
          Invariant G R m ℓ ε γ μ s (history rule adversary s) ∧
          IsBipartiteRobustExpander
            (G \ edgeUnion (fun i => (history rule adversary s i).2.spanningCoe) univ)
            (θ / 2) τ := by
  classical
  let good := fun (s : ℕ) (H : Fin s → Finset (A ⊕ B) × G.Subgraph)
    (S : Finset (A ⊕ B)) (N : G.Subgraph) =>
      Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N))
  let rule := choose (⊥ : G.Subgraph) good
  refine ⟨rule, ?_⟩
  intro adversary halong s hs
  have hstep : ∀ j < q, ∀ (H : Fin j → Finset (A ⊕ B) × G.Subgraph) S,
      Invariant G R m ℓ ε γ μ j H → Allowed G m ε j H S →
      Invariant G R m ℓ ε γ μ (j + 1) (Fin.snoc H (S, rule j H S)) := by
    intro j hj H S hH hS
    have hjm : j ≤ 2 * m := (Nat.le_of_lt hj).trans hq
    have hfeasible := exists_extension G R hbip hRG m ℓ Δ p ε γ c₀ θ τ δ₀ μ
      hm hε hγ hc₀ hθ hτ hμ hμθ hμδ hδτ hlarge hslack hεγ hcε hsmall hℓ
      hA hB hG hR hRmin hRexpand j hjm (hd j hj) H S hH hS
    exact choose_spec (⊥ : G.Subgraph) good j H S hfeasible
  have hH : Invariant G R m ℓ ε γ μ s (history rule adversary s) :=
    history_invariant_along rule adversary (Invariant G R m ℓ ε γ μ)
      (Allowed G m ε) q (invariant_zero G R m ℓ ε γ μ) halong hstep s hs
  refine ⟨hH, ?_⟩
  have hRbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) :=
    ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj (hRG h)⟩
  apply BipartitePackingReserve.residual_graph_robust_of_capacity G R
    (fun i => (history rule adversary s i).2) univ θ τ μ hRG hRexpand hRbip hμ.le hμθ
  intro v
  simpa only [hA] using hH.capacity v

end Overfull.BipartitePackingStrategy
