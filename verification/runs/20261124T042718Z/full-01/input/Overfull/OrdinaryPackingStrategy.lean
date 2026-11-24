import Overfull.OrdinaryPackingBounds
import Overfull.OrdinaryRobustStability
import Overfull.BipartitePackingHistory
import Overfull.BipartitePackingOnline

/-!
# Histories and choices for ordinary adaptive packing

The invariant counts actual used reserve edges. The final choice theorem
is a finite-recursion step: its local feasibility input is supplied by
the graph-theoretic ordinary round theorem in the full packing proof.
-/

namespace Overfull.OrdinaryPackingStrategy

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting BipartitePackingOnline

variable {V : Type*} [Fintype V]

structure Invariant (G R : SimpleGraph V) (m ℓ : ℕ) (ε γ μ : ℝ)
    (s : ℕ) (H : Fin s → Finset V × G.Subgraph) : Prop where
  matching : ∀ i, (H i).2.IsMatching
  verts : ∀ i, (H i).2.verts = ((H i).1 : Set V)ᶜ
  disjoint : Pairwise (fun i j => Disjoint (H i).2.spanningCoe (H j).2.spanningCoe)
  capacity : ∀ v, reserveLoad G R (fun i => (H i).2) univ v ≤ Nat.floor (μ * m)
  total : (∑ v, (reserveLoad G R (fun i => (H i).2) univ v : ℝ)) ≤
    ε * (m : ℝ)^2 * ((1 + 60 * ℓ / (γ * m)) ^ s - 1)

structure Allowed (G : SimpleGraph V) (m : ℕ) (ε : ℝ)
    (s : ℕ) (H : Fin s → Finset V × G.Subgraph) (S : Finset V) : Prop where
  parity : S.card % 2 = m % 2
  size : (S.card : ℝ) ≤ ε * m
  incidences : ∀ v, ((univ.filter (fun i : Fin s => v ∈ (H i).1)).card : ℝ) ≤ ε * m

theorem invariant_zero (G R : SimpleGraph V) (m ℓ : ℕ) (ε γ μ : ℝ) :
    Invariant G R m ℓ ε γ μ 0 Fin.elim0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro v; simp
  · simp

theorem Invariant.total_le {G R : SimpleGraph V} {m ℓ s : ℕ} {ε γ μ : ℝ}
    {H : Fin s → Finset V × G.Subgraph} (hH : Invariant G R m ℓ ε γ μ s H)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ) (hs : s ≤ 2 * m) :
    (∑ v, (reserveLoad G R (fun i => (H i).2) univ v : ℝ)) ≤
      (Real.exp (120 * ℓ / γ) - 1) * ε * (m : ℝ)^2 := by
  calc
    _ ≤ ε * (m : ℝ)^2 * ((1 + 60 * ℓ / (γ * m)) ^ s - 1) := hH.total
    _ ≤ ε * (m : ℝ)^2 * (Real.exp (120 * ℓ / γ) - 1) := by
      apply mul_le_mul_of_nonneg_left
      · exact sub_le_sub_right (OrdinaryPackingBounds.geometric_factor_bound m s ℓ γ
          hm (Nat.cast_nonneg ℓ) hγ hs) 1
      · positivity
    _ = _ := by ring

theorem Invariant.missing_le {G R : SimpleGraph V} {m ℓ s : ℕ} {ε γ μ : ℝ}
    {H : Fin s → Finset V × G.Subgraph} {S : Finset V}
    (hH : Invariant G R m ℓ ε γ μ s H) (hS : Allowed G m ε s H S) (v : V) :
    (missingCount G (fun i => (H i).2) univ v : ℝ) ≤ ε * m := by
  rw [missingCount_eq_forbidden G (fun i => (H i).2) univ
    (fun i => (H i).1) (fun i _ => hH.verts i)]
  convert hS.incidences v using 1

theorem geometric_step (m ℓ s : ℕ) (ε γ t t' : ℝ)
    (hm : 0 < m) (hγ : 0 < γ)
    (ht : t ≤ ε * (m : ℝ)^2 * ((1 + 60 * ℓ / (γ * m)) ^ s - 1))
    (hstep : t' ≤ (1 + 60 * ℓ / (γ * m)) * t + 60 * ℓ * ε * m / γ) :
    t' ≤ ε * (m : ℝ)^2 * ((1 + 60 * ℓ / (γ * m)) ^ (s + 1) - 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hconstant : (60 * (ℓ : ℝ) / (γ * m)) * (ε * (m : ℝ)^2) =
      60 * ℓ * ε * m / γ := by field_simp
  calc
    _ ≤ (1 + 60 * ℓ / (γ * m)) * t + 60 * ℓ * ε * m / γ := hstep
    _ ≤ (1 + 60 * ℓ / (γ * m)) *
        (ε * (m : ℝ)^2 * ((1 + 60 * ℓ / (γ * m)) ^ s - 1)) +
          60 * ℓ * ε * m / γ :=
      add_le_add_right (mul_le_mul_of_nonneg_left ht (by positivity)) _
    _ = _ := by rw [pow_succ, ← hconstant]; ring

theorem append_invariant (G R : SimpleGraph V) (m ℓ s : ℕ) (ε γ μ : ℝ)
    (hm : 0 < m) (hγ : 0 < γ) (H : Fin s → Finset V × G.Subgraph)
    (hH : Invariant G R m ℓ ε γ μ s H) (S : Finset V) (N : G.Subgraph)
    (hN : N.IsMatching) (hNverts : N.verts = (S : Set V)ᶜ)
    (hNdisj : Disjoint N.spanningCoe (edgeUnion (fun i => (H i).2.spanningCoe) univ))
    (hNcapacity : ∀ v,
      (R ⊓ (edgeUnion (fun i => (H i).2.spanningCoe) univ ⊔ N.spanningCoe)).degree v ≤
        Nat.floor (μ * m))
    (hNtotal : (∑ v, ((R ⊓ (edgeUnion (fun i => (H i).2.spanningCoe) univ ⊔
      N.spanningCoe)).degree v : ℝ)) ≤
        (1 + 60 * ℓ / (γ * m)) * (∑ v, (reserveLoad G R (fun i => (H i).2) univ v : ℝ)) +
          60 * ℓ * ε * m / γ) :
    Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N)) := by
  let M : Fin s → G.Subgraph := fun i => (H i).2
  have hproj : (fun i : Fin (s + 1) =>
      ((Fin.snoc H (S, N) : Fin (s + 1) → Finset V × G.Subgraph) i).2) =
        Fin.snoc M N := snoc_outputs H S N
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
        (1 + 60 * ℓ / (γ * m)) * (∑ v, (reserveLoad G R M univ v : ℝ)) +
          60 * ℓ * ε * m / γ := by
      calc
        _ = ∑ v, ((R ⊓ (edgeUnion (fun i => (M i).spanningCoe) univ ⊔
            N.spanningCoe)).degree v : ℝ) := by
          apply Finset.sum_congr rfl
          intro v _
          exact_mod_cast BipartitePackingHistory.reserveLoad_snoc_graph G R M N v
        _ ≤ _ := hNtotal
    have htotal := geometric_step m ℓ s ε γ _ _ hm hγ hH.total hrec
    simpa only [← hproj] using htotal

theorem Invariant.remaining_robust {G R : SimpleGraph V} {m ℓ s : ℕ} {ε γ μ : ℝ}
    {H : Fin s → Finset V × G.Subgraph}
    (hH : Invariant G R m ℓ ε γ μ s H) (hRG : R ≤ G)
    (θ σ σ₀ : ℝ) (hR : IsRobustExpander R θ σ) (hμ : 0 ≤ μ)
    (horder : Fintype.card V = m) (hrange : σ ≤ σ₀) :
    IsRobustExpander
      (G \ edgeUnion (fun i => (H i).2.spanningCoe) univ) (θ - μ) σ₀ := by
  apply IsRobustExpander.mono_range _ (hτσ := hrange)
  apply OrdinaryPackingReserve.residual_graph_robust G R (fun i => (H i).2) univ
    θ σ μ hRG hR hμ
  intro v
  rw [horder]
  have hc : (reserveLoad G R (fun i => (H i).2) univ v : ℝ) ≤ Nat.floor (μ * m) := by
    exact_mod_cast hH.capacity v
  exact hc.trans (Nat.floor_le (by positivity))

/-- Once every allowed round has a graph-theoretic extension, one fixed
choice rule handles every adaptive input sequence. -/
theorem exists_rule (G R : SimpleGraph V) (m ℓ q : ℕ) (ε γ μ : ℝ)
    (hfeasible : ∀ s < q, ∀ (H : Fin s → Finset V × G.Subgraph) S,
      Invariant G R m ℓ ε γ μ s H → Allowed G m ε s H S →
      ∃ N : G.Subgraph, Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N))) :
    ∃ rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph,
      ∀ adversary : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V,
        (∀ s < q, Allowed G m ε s (history rule adversary s)
          (adversary s (history rule adversary s))) →
        ∀ s ≤ q, Invariant G R m ℓ ε γ μ s (history rule adversary s) := by
  let good := fun (s : ℕ) (H : Fin s → Finset V × G.Subgraph)
    (S : Finset V) (N : G.Subgraph) =>
      Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N))
  let rule := choose (⊥ : G.Subgraph) good
  refine ⟨rule, ?_⟩
  intro adversary halong s hs
  apply history_invariant_along rule adversary (Invariant G R m ℓ ε γ μ)
    (Allowed G m ε) q (invariant_zero G R m ℓ ε γ μ) halong _ s hs
  intro j hj H S hH hS
  exact choose_spec (⊥ : G.Subgraph) good j H S (hfeasible j hj H S hH hS)

end Overfull.OrdinaryPackingStrategy
