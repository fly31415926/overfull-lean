import Overfull.OrdinaryPackingParameters
import Overfull.OrdinaryPackingInitial
import Overfull.OrdinaryPackingRound
import Overfull.OrdinaryPackingStrategy
import Overfull.BipartitePacking

/-!
# Adaptive packing in an ordinary robust expander

Lemma 2.20: the error, retained expansion parameter, and order threshold
are chosen before the graph. One rule works for every adaptive sequence
of forbidden sets satisfying the parity, size, and incidence conditions.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

theorem adaptive_ordinary_packing (α γ ν τ σ₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1 / 2) :
    ∃ ε θ₀ : ℝ, 0 < ε ∧ 0 < θ₀ ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (Δ : ℝ),
        m₀ ≤ Fintype.card V → IsRobustExpander G ν τ → α * Fintype.card V ≤ Δ →
        (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card V) →
        ∃ rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph,
          ∀ adversary : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V,
            (∀ s < Nat.floor (Δ - γ * Fintype.card V),
              OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε s
                (BipartitePackingOnline.history rule adversary s)
                (adversary s (BipartitePackingOnline.history rule adversary s))) →
            ∀ s ≤ Nat.floor (Δ - γ * Fintype.card V),
              IsPackingHistory G s (BipartitePackingOnline.history rule adversary s) ∧
              IsRobustExpander
                (G \ BipartitePackingAccounting.edgeUnion
                  (fun i => (BipartitePackingOnline.history rule adversary s i).2.spanningCoe)
                  univ) θ₀ σ₀ := by
  let p := min γ 1 / 16
  let σ := min τ (min σ₀ (p * α / 1000)) / 2
  let δ₀ := p * α / 2
  let θ := p * min ν (α * σ / 4) / 4
  have hparams : 0 < p ∧ p ≤ 1 ∧ p ≤ γ / 8 ∧
      0 < σ ∧ σ ≤ τ ∧ σ ≤ σ₀ ∧ σ ≤ 1 / 16 ∧ 16 * σ ≤ δ₀ / 3 ∧
      0 < δ₀ ∧ 0 < θ ∧ θ ≤ 4 * σ ∧ θ ≤ 1 :=
    OrdinaryPackingParameters.reserve_parameters α γ ν τ σ₀
      hα hα1 hγ hν hντ hτ hσ₀ hσ₀1
  obtain ⟨hp, hp1, hpγ, hσ, hστ, hσσ₀, hσsmall, hσδ, hδ₀, hθ, hθσ, _hθ1⟩ := hparams
  obtain ⟨ξ, hξ, nRound, hround⟩ :=
    OrdinaryPackingRound.exists_round δ₀ θ σ hδ₀ hθ hθσ hσsmall hσδ
  let ℓ := Nat.ceil (2 / ξ) + 2
  let c₀ := Real.exp (120 * (ℓ : ℝ) / γ) - 1
  let μ := min θ δ₀ / 100
  have herrors : 2 ≤ ℓ ∧ 0 ≤ c₀ ∧ 0 < μ ∧ μ ≤ θ / 2 ∧
      ∃ ε : ℝ, 0 < ε ∧ μ + ε ≤ δ₀ / 2 ∧ ε ≤ θ / 2 ∧ ε ≤ 1 / 2 ∧
        ε ≤ γ / 40 ∧ ε ≤ p ∧ ε ≤ p * α / 8 ∧
        4 * c₀ * ε / μ < γ / 8 ∧
        (4 * c₀ / μ + 30 * (ℓ : ℝ) * (1 + c₀) / γ) * ε ≤ min ξ (δ₀ / 3) / 16 :=
    OrdinaryPackingParameters.exists_error_parameter α γ p θ δ₀ ξ hα hγ hp hθ hδ₀ hξ
  obtain ⟨_hℓtwo, hc₀, hμ, hμθ, ε, hε, hμεδ, hεθ, hεhalf, hεγ,
    hεp, hεα, hcε, hsmall⟩ := herrors
  obtain ⟨nReserve, hreserve⟩ := OrdinaryPackingInitial.exists_initial_reserve
    α ν τ p σ ε μ hα hα1 hν hτ hp hp1 hσ hστ hε hεp hεα hμ
  let η := min ξ (δ₀ / 3)
  have hη : 0 < η := lt_min hξ (by positivity)
  obtain ⟨nSlack, hnSlack⟩ := exists_nat_gt (16 / η)
  refine ⟨ε, θ - μ, hε, by linarith, max nReserve (max nRound nSlack), ?_⟩
  intro V _ G Δ hm hGrob hΔ hdegrees
  let m := Fintype.card V
  have hnReserve : nReserve ≤ m := (le_max_left _ _).trans hm
  have hnRest : max nRound nSlack ≤ m := (le_max_right _ _).trans hm
  have hnRound : nRound ≤ m := (le_max_left _ _).trans hnRest
  have hnSlack' : nSlack ≤ m := (le_max_right _ _).trans hnRest
  have hslack : 16 ≤ η * m := by
    have hh : (nSlack : ℝ) ≤ m := by exact_mod_cast hnSlack'
    have h := (div_lt_iff₀ hη).mp (hnSlack.trans_le hh)
    linarith
  obtain ⟨R, hRG, hRexpand, hR, hRmin, hΔupper, hmpos, hεm, hμm, _hinitSlack⟩ :=
    hreserve V G Δ hnReserve hGrob hΔ hdegrees
  have hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m := by
    intro v
    obtain ⟨hl, hu⟩ := abs_le.mp (hdegrees v)
    constructor <;> linarith
  obtain ⟨hq, hd⟩ := BipartitePackingParameters.round_count_bounds m Δ p γ
    hp.le hpγ hγ.le hΔupper
  have hfeasible : ∀ s < Nat.floor (Δ - γ * m),
      ∀ (H : Fin s → Finset V × G.Subgraph) S,
        OrdinaryPackingStrategy.Invariant G R m ℓ ε γ μ s H →
        OrdinaryPackingStrategy.Allowed G m ε s H S →
        ∃ N : G.Subgraph,
          OrdinaryPackingStrategy.Invariant G R m ℓ ε γ μ (s + 1) (Fin.snoc H (S, N)) := by
    intro s hs H S hH hS
    have hload : (∑ v, (BipartitePackingAccounting.reserveLoad G R
        (fun i => (H i).2) univ v : ℝ)) ≤ c₀ * ε * (m : ℝ)^2 :=
      hH.total_le hmpos hε.le hγ ((Nat.le_of_lt hs).trans hq)
    have hparity : Even (m - S.card) := by
      have hcard : S.card ≤ m := Finset.card_le_univ S
      have hpS := hS.parity
      refine ⟨(m - S.card) / 2, ?_⟩
      omega
    have hd' : γ * m / 2 ≤ (1 - p) * Δ - (univ : Finset (Fin s)).card := by
      simpa using hd s hs
    obtain ⟨N, _h, hN, hNverts, hNdisj, hNcapacity, _hdef, _hcoarse, _huse, hNtotal⟩ :=
      hround V (Fin s) G R hRG (fun i => (H i).2) univ S m ℓ Δ p ε γ c₀ μ
        hnRound hmpos rfl (fun i _ => hH.matching i)
        (fun i _ j _ hij => hH.disjoint hij) hε.le hγ hc₀ hμ hμθ hμεδ hεθ hεhalf hεγ
        hεm hμm hslack hcε hsmall le_rfl hparity hG hR hRmin hRexpand
        (fun v => hH.missing_le hS v) hS.size hd' hH.capacity hload
    exact ⟨N, OrdinaryPackingStrategy.append_invariant G R m ℓ s ε γ μ
      hmpos hγ H hH S N hN hNverts hNdisj hNcapacity hNtotal⟩
  obtain ⟨rule, hrule⟩ := OrdinaryPackingStrategy.exists_rule G R m ℓ
    (Nat.floor (Δ - γ * m)) ε γ μ hfeasible
  refine ⟨rule, ?_⟩
  intro adversary hallowed s hs
  have hInv := hrule adversary hallowed s hs
  refine ⟨⟨hInv.matching, hInv.verts, hInv.disjoint⟩, ?_⟩
  exact hInv.remaining_robust hRG θ σ σ₀ hRexpand hμ.le rfl hσσ₀

end Overfull
