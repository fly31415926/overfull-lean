import Overfull.BipartiteFactorization.UniformSelection
import Overfull.BipartiteFactorization.FineCoarseBlocks

/-!
# Actual simultaneous fine blocks and their coarse unions

Divisibility and a lower bound on every nonempty original part construct
the positions. Uniform graph-derived probability budgets then choose the
actual vertex blocks. No supplied random positions, probability estimates,
or numerical success budgets remain in this interface.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.UniformSelection

open Finset Classical PartitionPermutation SimultaneousBlocks

universe u v w

/-- Uniform construction of the actual fine and coarse vertex blocks.
Taking `c = 7` gives the seven manuscript coarse blocks and `c*t` fine
blocks. The common order threshold precedes the graph and its partition.
The correction pool is required to be large, as in the score application. -/
theorem exists_uniform_fine_coarse_blocks
    (α θ β lammin : ℝ) (c t specialBound : ℕ)
    (hα : 0 < α) (hθ : 0 < θ) (hβ : 0 < β) (hlammin : 0 < lammin)
    (hc : 0 < c) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (ι : Type w) [Fintype ι] (G : Multigraph V E) (k : ℕ)
          (D : ι → Finset V) (B U Wo Ws Zcorr : Finset V)
          (F : V → Finset E) (lam : ((Fin c × Fin t) ⊕ Fin c) → ℝ),
          α * m ≤ (k : ℝ) → (Wo.card : ℝ) ≤ ε * m → Ws.card ≤ specialBound →
          (∀ i j, i ≠ j → Disjoint (D i) (D j)) → univ.biUnion D = B →
          Disjoint B Zcorr →
          (∀ i, c * t ∣ (D i).card) →
          (∀ i, (D i).Nonempty → 2 * (c * t) ≤ (D i).card) →
          (∀ j, lammin ≤ lam j) →
          (∀ v ∈ B, (G.degree v : ℝ) ≤ a) →
          (∀ x ∈ Wo, F x ⊆ G.edgesTo x B) →
          (∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x)) →
          (∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card) →
          (∀ x ∈ Wo, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card) →
          (∀ x ∈ Zcorr, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Zcorr, ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2) →
          θ * k / 65536 ≤ (correctionPool G B Zcorr).card →
          ∃ T : ((Fin c × Fin t) ⊕ Fin c) → Finset V,
            FineCoarseBlocks D B c t T ∧
            ∀ j, BlockSelectionBudget.GoodBlock G B U Wo Ws Zcorr F β
              (positionFraction c t j) (lam j)
              (fun x => (⌊(15 / 16 : ℝ) * lam j * (G.edgesTo x U).card⌋₊ : ℝ))
              (T j) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpmin : 0 < 1 / ((c : ℝ) * t) := by positivity
  obtain ⟨ε, hε, m₀, hm₀, hblocks⟩ := exists_uniform_blocks
    α θ β (1 / ((c : ℝ) * t)) lammin specialBound (c * t + c)
    hα hθ hβ hpmin hlammin
  refine ⟨ε, hε, m₀, hm₀, ?_⟩
  intro m hm a ha haε V E _ ι _ G k D B U Wo Ws Zcorr F lam
    hk hWo hWs hdisj hcover hBZ hdiv hsize hlam hdegree hF hinj hFsize
    hordinary hspecial hspecial_side hcorr hdc hlarge
  have hdiv' : ∀ i, c * t ∣ Fintype.card (D i) := by
    simpa only [Fintype.card_coe] using hdiv
  have hsize' : ∀ i, Nonempty (D i) → 2 * (c * t) ≤ Fintype.card (D i) := by
    intro i ⟨x⟩
    simpa only [Fintype.card_coe] using hsize i ⟨x.val, x.property⟩
  obtain ⟨S, hcard, hSdisj, hScover, hcoarse_card, _hcoarse_disj, _hcoarse_cover,
      hfraction_bounds, hfraction, htwo⟩ :=
    exists_uniform_fine_coarse_positions (E := fun i => D i) hc ht hdiv' hsize'
  have htwo' : ∀ j i, (D i).Nonempty → 2 ≤ (combinedPositions S j i).card := by
    intro j i ⟨x, hx⟩
    exact htwo j i ⟨⟨x, hx⟩⟩
  obtain ⟨T, hreal, hgood⟩ := hblocks m hm a ha haε V E ι
    ((Fin c × Fin t) ⊕ Fin c) G k D B U Wo Ws Zcorr (combinedPositions S) F
    (positionFraction c t) lam hk hWo hWs (by simp) hdisj hcover hBZ
    (positionFraction_lower hc ht) (fun j => (hfraction_bounds j).2) hlam
    (by simpa only [Fintype.card_coe] using hfraction) htwo' hdegree hF hinj hFsize
    hordinary hspecial hspecial_side hcorr hdc hlarge
  refine ⟨T, ?_, hgood⟩
  exact fineCoarseBlocks_of_realizes D B S T
    (by simpa only [Fintype.card_coe] using hcard) hSdisj
    (by intro i; simpa only [Finset.ext_iff, mem_biUnion, mem_univ] using hScover i)
    (by simpa only [Fintype.card_coe] using hcoarse_card) hreal

end Overfull.BipartiteFactorization.UniformSelection
