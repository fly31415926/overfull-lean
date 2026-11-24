import Overfull.BipartiteFactorization.ReservedCore
import Overfull.BipartiteFactorization.UniformRemainder
import Overfull.BipartiteFactorization.Exterior

/-!
# The uniform packing stage on the original reserved graph

Starting with the original regular host and an explicit reserved set of its
edge copies, this theorem derives the actual surviving core, its robustness,
its degree error, and the exact nonregular ambient degrees. It then completes
all colors of the remaining exterior and constructs the regular oriented
remainder. The reserved set and the balanced remaining exterior coloring are
explicit inputs: their complete absorber construction is a separate task.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts SimpleGraph

/-- Uniform final packing from the original regular host, with all loss
and residual degree conditions derived from the actual reserved copies. -/
theorem exists_uniform_reserved_remainder (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 32) :
    ∃ ε θ σ : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < σ ∧ σ ≤ τ ∧ ∃ m₀ : ℕ,
      ∀ (V E A B : Type*) [Fintype V] [Fintype E] [Fintype A] [Fintype B]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (e : A ⊕ B ≃ U) (T : Finset E) (k s r : ℕ) (a : ℝ)
        (c : (exterior (ReservedCore.core C T)).EdgeColoring (k - 2 * s)),
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        IsBipartiteRobustExpander (C.graph.comap e) ν τ →
        α * Fintype.card A ≤ k → γ * Fintype.card A ≤ 2 * r →
        r ≤ s → 4 * s ≤ k →
        ((2 * (s - r) : ℕ) : ℝ) ≤ (ν / 2) * Fintype.card A →
        (∀ v, G.degree v = k) →
        (∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r)) →
        (∀ v, v ∉ U → (G.restrictEdges T).degree v = 2 * s) →
        0 ≤ a → a ≤ ε * Fintype.card A →
        (∀ v : U, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (∀ i, (univ.filter (fun x : A => c.Covers i (e (.inl x)).val)).card =
          (univ.filter (fun y : B => c.Covers i (e (.inr y)).val)).card) →
        (∀ i, ((c.exteriorFootprint U i).card : ℝ) ≤
          2 * Fintype.card A * a / (k - 2 * s : ℕ) + 4) →
        ∃ D : ComplementCompletion (ReservedCore.core C T) c,
          IsBipartiteRobustExpander (D.remainingGraph.comap e) θ σ ∧
          Nonempty (ResidualOrientation (D.remainingGraph.comap e) r) := by
  obtain ⟨ε, θ, σ, hε, hθ, hσ, hστ, m₀, hpack⟩ :=
    exists_uniform_oriented_remainder (α / 2) γ (ν / 2) τ
      (by positivity) (by linarith) hγ hγ1 (by positivity)
      (by linarith) (by linarith)
  refine ⟨ε, θ, σ, hε, hθ, hσ, hστ, m₀, ?_⟩
  intro V E A B _ _ _ _ G U C e T k s r a c hcard hm hbip hrob
    hk hr hrs hsk4 hsmall hregular hreserved houtside ha hae hcore hbalance hsize
  have hsk : 2 * s ≤ k := by omega
  have hq : (α / 2) * Fintype.card A ≤ (k - 2 * s : ℕ) := by
    have hnat : k ≤ 2 * (k - 2 * s) := by omega
    have hreal : (k : ℝ) ≤ 2 * (k - 2 * s : ℕ) := by exact_mod_cast hnat
    linarith
  have hbip' : ((ReservedCore.core C T).graph.comap e).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) :=
    ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj h.1⟩
  have hrob' : IsBipartiteRobustExpander
      ((ReservedCore.core C T).graph.comap e) (ν / 2) τ := by
    have h := ReservedCore.bipartite_robust_of_reserved_degrees
      C T e s r ν τ (ν / 2) hrob hbip (by positivity) hreserved hsmall
    convert h using 1
    ring
  have hdegrees (v : U) :
      (((k - 2 * s) + 2 * r : ℕ) : ℝ) - a ≤ (ReservedCore.core C T).graph.degree v := by
    have heq : k - 2 * (s - r) = (k - 2 * s) + 2 * r := by omega
    have h := (ReservedCore.core_degree_bounds C T k s r a hregular hreserved hcore v).1
    simpa only [heq, ReservedCore.core_graph] using h
  exact hpack V ↥(Tᶜ) A B (ReservedCore.remainingHost G T) U (ReservedCore.core C T)
    e (k - 2 * s) r a c hcard hm hbip' hrob' hq hr
    (fun v hv => ReservedCore.remainingHost_degree_outside T k s hregular houtside v hv)
    (ReservedCore.remainingHost_degree_core_eq_palette_add T k s r hrs hsk hregular hreserved)
    ha hae hdegrees hbalance hsize

end Overfull.BipartiteFactorization
