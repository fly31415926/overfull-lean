import Overfull.BipartitePackingInitial
import Overfull.BipartitePackingStrategy

/-!
# Adaptive packing in a bipartite robust expander

This is Theorem 2.16 of the manuscript. The error and order threshold are
chosen before the graph. For each graph, one fixed rule receives only the
previous rounds and the current forbidden set. It works for every adaptive
input sequence satisfying the stated balance, size and incidence bounds.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

/-- A history consists of actual edge-disjoint matchings, each perfect
outside the forbidden set presented in its own round. -/
def IsPackingHistory {V : Type*} (G : SimpleGraph V) (s : ℕ)
    (H : Fin s → Finset V × G.Subgraph) : Prop :=
  (∀ i, (H i).2.IsMatching) ∧
  (∀ i, (H i).2.verts = ((H i).1 : Set V)ᶜ) ∧
  Pairwise (fun i j => Disjoint (H i).2.spanningCoe (H j).2.spanningCoe)

/-- An adaptive version of Theorem 2.16, with one fixed rule that works
against every admissible choice of the next forbidden set. `Allowed`
means precisely balance, the current size bound, and the bound on past
forbidden-set incidences at every vertex. -/
theorem adaptive_bipartite_packing (α γ p ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hp : 0 < p) (hpγ : p < γ / 8) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ < p * α / 100) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (A B : Type*) [Fintype A] [Fintype B]
        (G : SimpleGraph (A ⊕ B)) (Δ : ℝ),
        G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        IsBipartiteRobustExpander G ν τ → α * Fintype.card A ≤ Δ →
        (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) →
        ∃ rule : (s : ℕ) → (Fin s → Finset (A ⊕ B) × G.Subgraph) →
            Finset (A ⊕ B) → G.Subgraph,
          ∀ adversary : (s : ℕ) → (Fin s → Finset (A ⊕ B) × G.Subgraph) →
              Finset (A ⊕ B),
            (∀ s < Nat.floor (Δ - γ * Fintype.card A),
              BipartitePackingStrategy.Allowed G (Fintype.card A) ε s
                (BipartitePackingOnline.history rule adversary s)
                (adversary s (BipartitePackingOnline.history rule adversary s))) →
            ∀ s ≤ Nat.floor (Δ - γ * Fintype.card A),
              IsPackingHistory G s (BipartitePackingOnline.history rule adversary s) ∧
              IsBipartiteRobustExpander
                (G \ BipartitePackingAccounting.edgeUnion
                  (fun i => (BipartitePackingOnline.history rule adversary s i).2.spanningCoe)
                  univ) (p * ν / 4) τ := by
  have hp1 : p ≤ 1 := by linarith
  have hτpos : 0 < τ := hν.trans_le hντ
  let θ := p * ν / 2
  let δ₀ := p * α / 2
  let ℓ := Nat.ceil (8 / θ) + 4
  let c₀ := 8 * (Real.exp (8 * (ℓ : ℝ) / γ) - 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨μ, ε, hμ, _, hμθ, hμδ, hδτ, hε, hεp, hε1, hεα, hεγ, hcε, hsmall⟩ :=
    BipartitePackingParameters.exists_parameters α γ p ν τ hα hα1 hγ hγ1 hp hpγ hν hτ
  obtain ⟨m₀, hm₀⟩ := BipartitePackingInitial.exists_initial_reserve p ν α ε μ
    hp hp1 hν hα hε hεp hε1 hεα.le hμ
  refine ⟨ε, hε, m₀, ?_⟩
  intro A B _ _ G Δ hbip hbalance hm hrob hΔ hdegrees
  obtain ⟨R, hRG, _, hRexpand, hR, hRmin, hΔupper, hmpos, hlarge, hslack⟩ :=
    hm₀ A B G τ Δ hbip hbalance hm hrob hΔ hdegrees
  have hG : ∀ v, Δ - ε * Fintype.card A ≤ (G.degree v : ℝ) ∧
      (G.degree v : ℝ) ≤ Δ + ε * Fintype.card A := by
    intro v
    obtain ⟨hl, hu⟩ := abs_le.mp (hdegrees v)
    constructor <;> linarith
  obtain ⟨hq, hd⟩ := BipartitePackingParameters.round_count_bounds (Fintype.card A)
    Δ p γ hp.le hpγ.le hγ.le hΔupper
  obtain ⟨rule, hstrategy⟩ := BipartitePackingStrategy.exists_strategy G R hbip hRG
    (Fintype.card A) ℓ Δ p ε γ c₀ θ τ δ₀ μ hmpos hε.le hγ rfl
    hθ hτpos hμ hμθ hμδ hδτ hlarge hslack hεγ hcε hsmall
    (BipartitePackingParameters.path_length_bound θ hθ)
    rfl hbalance.symm hG hR hRmin hRexpand
    (Nat.floor (Δ - γ * Fintype.card A)) hq hd
  refine ⟨rule, ?_⟩
  intro adversary hallowed s hs
  obtain ⟨hInv, hremaining⟩ := hstrategy adversary hallowed s hs
  refine ⟨⟨hInv.matching, hInv.verts, hInv.disjoint⟩, ?_⟩
  have hparameter : θ / 2 = p * ν / 4 := by dsimp [θ]; ring
  simpa only [hparameter] using hremaining

end Overfull
