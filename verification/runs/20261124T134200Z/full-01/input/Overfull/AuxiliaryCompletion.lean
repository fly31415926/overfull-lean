import Overfull.AuxiliaryCompletion.Construction
import Overfull.AuxiliaryCompletion.CoreCuts
import Overfull.AuxiliaryCompletion.OddSets
import Overfull.AuxiliaryCompletion.Structure

/-!
# Robust auxiliary completion

Lemma 2.22 constructs an even-order regular completion of an almost
regular loopless multigraph. The original edge copies are retained,
all added edges have multiplicity one, and no overfull set is created.
The auxiliary vertices induce a simple robust expander.
-/

namespace Overfull

open Finset Classical AuxiliaryCompletion
open scoped BigOperators

/-- Full auxiliary completion, with the least permitted auxiliary order.
The sum vertex type keeps the original and auxiliary vertices distinct,
and the sum edge type retains all original parallel copies. -/
theorem robust_auxiliary_completion (α τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hτ : 0 < τ) (hτα : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ),
        n₀ ≤ Fintype.card V → (∀ v, G.degree v ≤ k) →
        α * Fintype.card V ≤ (k : ℝ) → k ≤ 2 * Fintype.card V →
        (∑ v, ((k - G.degree v : ℕ) : ℝ)) ≤ ε * (Fintype.card V : ℝ)^2 →
        (∀ S : Finset V, ¬ G.IsOverfull k S) →
        let m := auxiliaryOrder (Fintype.card V) k
        let b := Nat.ceil ((∑ v, ((k - G.degree v : ℕ) : ℝ)) / m)
        ∃ N : V → Finset (Fin m), ∃ H : SimpleGraph (Fin m),
          let Gplus := graph G N H
          (∀ v, Gplus.degree v = k) ∧
          Fintype.card (V ⊕ Fin m) % 2 = 0 ∧
          Gplus.internalEdges ((univ : Finset V).disjSum ∅) =
            (univ : Finset E).map Function.Embedding.inl ∧
          Gplus.internalEdges ((∅ : Finset V).disjSum (univ : Finset (Fin m))) =
            (univ : Finset H.edgeSet).map (auxiliaryEmbedding (E := E) N H) ∧
          (∀ e f : CompletionEdges (E := E) N H,
            (∀ a : E, e ≠ Sum.inl a) → Gplus.edge e = Gplus.edge f → e = f) ∧
          IsRobustExpander H ν τ ∧
          (∀ z, (k : ℝ) - b ≤ (H.degree z : ℝ)) ∧
          (∀ X : Finset (V ⊕ Fin m), ¬ Gplus.IsOverfull k X) := by
  classical
  obtain ⟨ν, ε, hν, hε, n₀, hcore⟩ := exists_auxiliary_core α τ hα hα1 hτ hτα
  refine ⟨ν, ε, hν, hε, n₀, ?_⟩
  intro V E _ _ G k hn hdegree hk hkupper hdef hno
  let n := Fintype.card V
  let m := auxiliaryOrder n k
  let b := Nat.ceil ((∑ v, ((k - G.degree v : ℕ) : ℝ)) / m)
  change ∃ N : V → Finset (Fin m), ∃ H : SimpleGraph (Fin m), _
  obtain ⟨N, H, hN, _hbalance, hload, hHdegree, hHrobust, hHmin, hb, hm, hlarge⟩ :=
    hcore V E G k hn hdegree hk hkupper hdef
  change 8 * b ≤ k at hb
  have hbk : b ≤ k := by omega
  have hregular : ∀ v, (graph G N H).degree v = k := by
    intro v
    rcases v with v | z
    · rw [left_degree, hN.1 v]
      exact Nat.add_sub_of_le (hdegree v)
    · rw [right_degree, hHdegree z]
      exact Nat.add_sub_of_le ((hload z).trans hbk)
  have hparity : (n + m) % 2 = 0 := by
    have hp := auxiliaryOrder_mod_two n k
    change m % 2 = n % 2 at hp
    omega
  have heven : Fintype.card (V ⊕ Fin m) % 2 = 0 := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hparity
  have hcuts (T : Finset (Fin m)) (hT : 2 ≤ T.card) (hTc : 2 ≤ Tᶜ.card) :
      k < (Multigraph.ofSimpleGraph H).cutSize T := by
    apply core_cut_gt H n k b α ν τ hτ.le hτα hν.le
    · simpa only [Fintype.card_fin] using
        (show (m : ℝ) ≤ 3 * n by exact_mod_cast hm)
    · exact hk
    · have hbR : (8 : ℝ) * b ≤ k := by exact_mod_cast hb
      linarith
    · simpa only [Fintype.card_fin] using hlarge
    · exact hHmin
    · exact hHrobust
    · exact hT
    · exact hTc
  refine ⟨N, H, hregular, heven, internal_original_edges G N H,
    internal_auxiliary_edges G N H, added_edge_simple G N H,
    hHrobust, hHmin, ?_⟩
  apply AuxiliaryCompletion.no_overfull G N H k hdegree hN hregular
  · simpa only [Fintype.card_fin] using hparity
  · exact hno
  · intro T hT hTc
    apply hcuts T hT
    simpa only [Finset.card_compl] using hTc

end Overfull
