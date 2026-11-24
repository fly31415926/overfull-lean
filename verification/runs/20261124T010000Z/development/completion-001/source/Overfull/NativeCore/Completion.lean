import Overfull.NativeReserve.CompletionGlue
import Overfull.NativeReserve.RetainedCore
import Overfull.NativeCore.Parity

/-!
# Completing bounded native boundary classes inside both original cores

The boundary classes may contain many joining pieces. Their actual support
bound replaces the three-copy hypothesis of the reserve construction. The
load is derived from disjoint original copies and the core degree deficit.
The resulting perfect matchings and robust residual cores are constructed.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical NativeReserve SmallCuts BoundaryExtension

/-- The fixed-forbidden-set packing theorem applies to whole boundary
classes using their actual support size, without a constant copy bound. -/
theorem pack_bounded_boundaries_in_core (α γ ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ : 0 < σ) (hσhalf : σ < 1 / 2) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → IsRobustExpander C.graph ν τ → α * U.card ≤ k →
        (∀ v, G.degree v = k) →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        a ≤ ε * U.card →
        ∀ (q : ℕ) (B : Fin q → Finset E),
          q ≤ Nat.floor ((k : ℝ) - γ * U.card) →
          Pairwise (fun i j => Disjoint (B i) (B j)) →
          (∀ j, Disjoint (B j) (OneCore.coreEdges C)) →
          (∀ j, ((G.edgeSupport (B j)).card : ℝ) ≤ ε * U.card) →
          (∀ j, Even (U \ G.edgeSupport (B j)).card) →
          Nonempty (CorePacking C.graph q
            (fun j => coreFootprint G U (B j)) θ σ) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := pack_fixed_forbidden_sets
    α γ ν τ σ hα hα1 hγ hν hντ hτ hσ hσhalf
  refine ⟨ε, θ, hε, hθ, m₀, ?_⟩
  intro V E _ G U C k a hm hrob hdensity hregular hdegree herror
    q B hq hdisj hout hsize heven
  have hnear : ∀ v, |(C.graph.degree v : ℝ) - k| ≤ ε * U.card := by
    intro v
    have hupper : (C.graph.degree v : ℝ) ≤ k := by
      exact_mod_cast (OneCore.core_degree_le C v).trans_eq (hregular v.val)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hupper)]
    linarith only [hdegree v, herror]
  apply hpack U C.graph k
  · simpa only [Fintype.card_coe] using hm
  · convert hrob using 1
  · simpa only [Fintype.card_coe] using hdensity
  · simpa only [Fintype.card_coe] using hnear
  · simpa only [Fintype.card_coe] using hq
  · exact fun j => coreFootprint_parity G U (B j) (heven j)
  · intro j
    have hsub : (coreFootprint G U (B j)).card ≤ (G.edgeSupport (B j)).card := by
      rw [coreFootprint_card]
      exact card_le_card inter_subset_right
    simpa only [Fintype.card_coe] using (Nat.cast_le.mpr hsub).trans (hsize j)
  · intro v
    simpa only [Fintype.card_coe] using
      (coreFootprint_load_le_error G C B hdisj hout k a hregular hdegree v).trans herror

/-- Uniformly construct a prescribed prefix of disjoint perfect matchings
in the two-core host and embed the exact unused robust cores in the actual
remaining edge-copy type. The reserved boundary copies are kept untouched. -/
theorem exists_two_core_boundary_prefix (α γ ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ : 0 < σ) (hσhalf : σ < 1 / 2) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E) (k : ℕ)
        (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁) (a : ℝ),
        Disjoint U₀ U₁ → (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) →
        m₀ ≤ U₀.card → m₀ ≤ U₁.card →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        α * U₀.card ≤ k → α * U₁.card ≤ k →
        (∀ v, G.degree v = k) →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        a ≤ ε * U₀.card → a ≤ ε * U₁.card →
        ∀ (q : ℕ) (B : Fin q → Finset E) (A : Finset E),
          q ≤ k → q ≤ Nat.floor ((k : ℝ) - γ * U₀.card) →
          q ≤ Nat.floor ((k : ℝ) - γ * U₁.card) →
          (∀ j, G.IsMatching (B j)) →
          Pairwise (fun i j => Disjoint (B i) (B j)) →
          (∀ j, Z ⊆ G.edgeSupport (B j)) →
          (∀ j, Disjoint (B j) (OneCore.coreEdges C₀)) →
          (∀ j, Disjoint (B j) (OneCore.coreEdges C₁)) →
          (∀ j, ((G.edgeSupport (B j)).card : ℝ) ≤ ε * U₀.card) →
          (∀ j, ((G.edgeSupport (B j)).card : ℝ) ≤ ε * U₁.card) →
          (∀ j, Even (U₀ \ G.edgeSupport (B j)).card) →
          (∀ j, Even (U₁ \ G.edgeSupport (B j)).card) →
          (∀ j, Disjoint (B j) A) →
          Disjoint A (OneCore.coreEdges C₀) → Disjoint A (OneCore.coreEdges C₁) →
          ∃ (N : Fin q → Finset E)
            (C₀' : Core (residualGraph G N univ) U₀)
            (C₁' : Core (residualGraph G N univ) U₁),
            (∀ j, G.IsPerfectMatching (N j)) ∧
            Pairwise (fun i j => Disjoint (N i) (N j)) ∧
            (∀ j, B j ⊆ N j) ∧ (∀ j, Disjoint (N j) A) ∧
            (∀ j, ∀ e ∈ N j, e ∈ B j ∨ e ∈ G.internalOn univ U₀ ∨
              e ∈ G.internalOn univ U₁) ∧
            (∀ v, (residualGraph G N univ).degree v = k - q) ∧
            IsRobustExpander C₀'.graph θ σ ∧ IsRobustExpander C₁'.graph θ σ ∧
            (∀ v, ((k - q : ℕ) : ℝ) - a ≤ (C₀'.graph.degree v : ℝ)) ∧
            (∀ v, ((k - q : ℕ) : ℝ) - a ≤ (C₁'.graph.degree v : ℝ)) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := pack_bounded_boundaries_in_core
    α γ ν τ σ hα hα1 hγ hν hντ hτ hσ hσhalf
  refine ⟨ε, θ, hε, hθ, m₀, ?_⟩
  intro V E _ G k U₀ U₁ Z C₀ C₁ a h01 hcover hm₀ hm₁ hrob₀ hrob₁
    hdense₀ hdense₁ hregular hdegree₀ hdegree₁ ha₀ ha₁ q B A hqk hq₀ hq₁
    hB hdisj hZ hout₀ hout₁ hsize₀ hsize₁ heven₀ heven₁ havoid hA₀ hA₁
  obtain ⟨P₀⟩ := hpack V E G U₀ C₀ k a hm₀ hrob₀ hdense₀ hregular hdegree₀ ha₀
    q B hq₀ hdisj hout₀ hsize₀ heven₀
  obtain ⟨P₁⟩ := hpack V E G U₁ C₁ k a hm₁ hrob₁ hdense₁ hregular hdegree₁ ha₁
    q B hq₁ hdisj hout₁ hsize₁ heven₁
  let N (j : Fin q) := completedBoundary C₀ C₁ (B j) (P₀.matching j) (P₁.matching j)
  have hperfect (j : Fin q) : G.IsPerfectMatching (N j) :=
    completedBoundary_isPerfectMatching C₀ C₁ Z h01 hcover (B j) (hB j) (hZ j)
      (P₀.matching j) (P₁.matching j) (P₀.isMatching j) (P₁.isMatching j)
      (P₀.verts j) (P₁.verts j)
  have hNdisj : Pairwise (fun i j => Disjoint (N i) (N j)) :=
    completedBoundary_pairwiseDisjoint C₀ C₁ h01 B P₀.matching P₁.matching
      hdisj hout₀ hout₁ P₀.disjoint P₁.disjoint
  have hremoved₀ (e : C₀.graph.edgeSet) : C₀.edgeMap e ∈ removedCopies N univ ↔
      ∃ j : Fin q, e.val ∈ (P₀.matching j).edgeSet := by
    simp only [mem_removedCopies, mem_univ, true_and]
    exact exists_congr (fun j => completedBoundary_core₀_copy_iff C₀ C₁ h01
      (B j) (hout₀ j) (P₀.matching j) (P₁.matching j) e)
  have hremoved₁ (e : C₁.graph.edgeSet) : C₁.edgeMap e ∈ removedCopies N univ ↔
      ∃ j : Fin q, e.val ∈ (P₁.matching j).edgeSet := by
    simp only [mem_removedCopies, mem_univ, true_and]
    exact exists_congr (fun j => completedBoundary_core₁_copy_iff C₀ C₁ h01
      (B j) (hout₁ j) (P₀.matching j) (P₁.matching j) e)
  let C₀' : Core (residualGraph G N univ) U₀ :=
    packingRemainderCore C₀ P₀ (removedCopies N univ) hremoved₀
  let C₁' : Core (residualGraph G N univ) U₁ :=
    packingRemainderCore C₁ P₁ (removedCopies N univ) hremoved₁
  refine ⟨N, C₀', C₁', hperfect, hNdisj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => completedBoundary_contains C₀ C₁ (B j) (P₀.matching j) (P₁.matching j)
  · exact fun j => completedBoundary_avoids C₀ C₁ (B j) A (havoid j) hA₀ hA₁
      (P₀.matching j) (P₁.matching j)
  · exact fun j e he => completedBoundary_added_internal C₀ C₁ (B j)
      (P₀.matching j) (P₁.matching j) e he
  · intro v
    have hd := residual_regular G hregular N univ
      (fun _ _ _ _ hij => hNdisj hij) (fun j _ => hperfect j) v
    simpa only [card_univ, Fintype.card_fin] using hd
  · exact packingRemainderCore_robust C₀ P₀ (removedCopies N univ) hremoved₀
  · exact packingRemainderCore_robust C₁ P₁ (removedCopies N univ) hremoved₁
  · exact packingRemainderCore_degree_lower C₀ P₀ (removedCopies N univ)
      hremoved₀ k a hqk hdegree₀
  · exact packingRemainderCore_degree_lower C₁ P₁ (removedCopies N univ)
      hremoved₁ k a hqk hdegree₁

end Overfull.NativeCore
