import Overfull.OrdinaryPackingPrefix

/-!
# Packing a fixed finite family of forbidden sets

This interface applies the adaptive theorem to the actual prescribed sets.
The output includes their internal completions and the robust graph left by
those precise edges. In particular, no residual graph is assumed as input.
-/

namespace Overfull.BoundaryExtension

open Finset Classical SimpleGraph
open BipartitePackingAccounting BipartitePackingOnline

variable {W : Type*} [Fintype W]

/-- A family of internal completions for the supplied forbidden vertices. -/
structure CorePacking (H : SimpleGraph W) (q : ℕ)
    (S : Fin q → Finset W) (θ σ : ℝ) where
  matching : Fin q → H.Subgraph
  isMatching : ∀ j, (matching j).IsMatching
  verts : ∀ j, (matching j).verts = (S j : Set W)ᶜ
  disjoint : Pairwise (fun i j => Disjoint (matching i).spanningCoe (matching j).spanningCoe)
  robust : IsRobustExpander
    (H \ edgeUnion (fun j => (matching j).spanningCoe) univ) θ σ

namespace CorePacking

variable {H : SimpleGraph W} {q : ℕ} {S : Fin q → Finset W} {θ σ : ℝ}

/-- The whole unused simple core, including all unused reserve edges. -/
def remaining (P : CorePacking H q S θ σ) : SimpleGraph W :=
  H \ edgeUnion (fun j => (P.matching j).spanningCoe) univ

/-- Weaken only the certified expansion parameter; every chosen edge and
the actual unused graph are unchanged. -/
def weakenParameter (P : CorePacking H q S θ σ) (θ' : ℝ) (hθ : θ' ≤ θ) :
    CorePacking H q S θ' σ where
  matching := P.matching
  isMatching := P.isMatching
  verts := P.verts
  disjoint := P.disjoint
  robust := IsRobustExpander.mono_parameter _ P.robust hθ

theorem degree_identity (P : CorePacking H q S θ σ) (v : W) :
    P.remaining.degree v + q =
      H.degree v + (univ.filter (fun j : Fin q => v ∈ S j)).card := by
  have huse := matchingUnion_degree_add_missing H P.matching univ
    (fun j _ => P.isMatching j) (fun i _ j _ hij => P.disjoint hij) v
  have hmiss := missingCount_eq_forbidden H P.matching univ S (fun j _ => P.verts j) v
  have hremain := degree_sdiff_add_of_le H
    (edgeUnion (fun j => (P.matching j).spanningCoe) univ)
    (edgeUnion_le (fun j => (P.matching j).spanningCoe) univ H
      (fun j _ => (P.matching j).spanningCoe_le)) v
  rw [hmiss] at huse
  simp only [Finset.card_univ, Fintype.card_fin] at huse
  have hremain' : P.remaining.degree v +
      (edgeUnion (fun j => (P.matching j).spanningCoe) univ).degree v = H.degree v := by
    simpa only [remaining, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hremain
  omega

theorem degree_lower (P : CorePacking H q S θ σ) (d a : ℝ)
    (hdegree : ∀ v, d - a ≤ H.degree v) (v : W) :
    d - q - a ≤ (P.remaining.degree v : ℝ) := by
  have h := P.degree_identity v
  have hreal : (P.remaining.degree v : ℝ) + q =
      H.degree v + (univ.filter (fun j : Fin q => v ∈ S j)).card := by exact_mod_cast h
  have hnonneg := Nat.cast_nonneg (α := ℝ) (univ.filter (fun j : Fin q => v ∈ S j)).card
  linarith [hdegree v]

end CorePacking

/-- Uniform constants precede the graph, the number of colors, and the
entire fixed forbidden-set family. -/
theorem pack_fixed_forbidden_sets (α γ ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ : 0 < σ) (hσhalf : σ < 1/2) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ ∃ m₀ : ℕ,
      ∀ (W : Type*) [Fintype W] (H : SimpleGraph W) (d : ℝ),
        m₀ ≤ Fintype.card W → IsRobustExpander H ν τ → α * Fintype.card W ≤ d →
        (∀ v, |(H.degree v : ℝ) - d| ≤ ε * Fintype.card W) →
        ∀ (q : ℕ) (S : Fin q → Finset W), q ≤ Nat.floor (d - γ * Fintype.card W) →
          (∀ j, (S j).card % 2 = Fintype.card W % 2) →
          (∀ j, ((S j).card : ℝ) ≤ ε * Fintype.card W) →
          (∀ v, ((univ.filter (fun j : Fin q => v ∈ S j)).card : ℝ) ≤ ε * Fintype.card W) →
          Nonempty (CorePacking H q S θ σ) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := adaptive_ordinary_packing_prefix
    α γ ν τ σ hα hα1 hγ hν hντ hτ hσ hσhalf
  refine ⟨ε, θ, hε, hθ, m₀, ?_⟩
  intro W _ H d hm hrob hd hdegree q S hq hparity hsize hload
  obtain ⟨rule, hrule⟩ := hpack W H d hm hrob hd hdegree
  let input : ℕ → Finset W := fun j => if h : j < q then S ⟨j, h⟩ else ∅
  have hinput (j : Fin q) : input j.val = S j := by simp only [input, dif_pos j.isLt]
  have hallowed : ∀ j < q,
      OrdinaryPackingStrategy.Allowed H (Fintype.card W) ε j
        (run rule input j) (input j) := by
    intro j hj
    have hx := hinput ⟨j, hj⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]; exact hparity ⟨j, hj⟩
    · rw [hx]; exact hsize ⟨j, hj⟩
    · intro v
      have hcount : (univ.filter (fun i : Fin j => v ∈ (run rule input j i).1)).card ≤
          (univ.filter (fun i : Fin q => v ∈ S i)).card := by
        apply Finset.card_le_card_of_injOn (Fin.castLE hj.le)
        · intro i hi
          have hi' : v ∈ input i.val := by
            have hi' := (Finset.mem_filter.mp hi).2
            rwa [run_input] at hi'
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [← hinput (Fin.castLE hj.le i)] using hi'
        · intro i _ l _ hil
          exact Fin.ext (congrArg (fun t : Fin q => t.val) hil)
      have hreal : ((univ.filter (fun i : Fin j => v ∈ (run rule input j i).1)).card : ℝ) ≤
          (univ.filter (fun i : Fin q => v ∈ S i)).card := by exact_mod_cast hcount
      exact hreal.trans (hload v)
  obtain ⟨hhistory, hremaining⟩ := hrule (fun j _ => input j) q hq hallowed
  let M : Fin q → H.Subgraph := fun j => (run rule input q j).2
  refine ⟨⟨M, hhistory.1, ?_, hhistory.2.2, hremaining⟩⟩
  intro j
  have h := hhistory.2.1 j
  change (run rule input q j).2.verts = ((run rule input q j).1 : Set W)ᶜ at h
  change (run rule input q j).2.verts = (S j : Set W)ᶜ
  rwa [run_input, hinput] at h

end Overfull.BoundaryExtension
