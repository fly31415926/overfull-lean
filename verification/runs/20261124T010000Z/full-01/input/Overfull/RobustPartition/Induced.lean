import Overfull.RobustExpansion
import Overfull.OrdinaryRobustStability

/-!
# Robust expansion inside an ambient vertex set

The local robust neighborhood counts original graph neighbors, restricted to
the vertex set of the induced graph.  Its normalization is the order of that
induced graph.  The transport lemmas below identify this description exactly
with `IsRobustExpander`, including the cardinalities of the tested sets.
-/

namespace Overfull.RobustPartition

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The robust neighborhood within `U`, normalized by `U.card`. -/
noncomputable def localRN (U : Finset V) (ν : ℝ) (S : Finset V) : Finset V := by
  classical
  exact U.filter (fun v => ν * (U.card : ℝ) ≤
    ((G.neighborFinset v ∩ S).card : ℝ))

theorem mem_localRN (U : Finset V) (ν : ℝ) (S : Finset V) (v : V) :
    v ∈ localRN G U ν S ↔ v ∈ U ∧
      ν * (U.card : ℝ) ≤ ((G.neighborFinset v ∩ S).card : ℝ) := by
  classical
  simp [localRN]

theorem localRN_subset (U : Finset V) (ν : ℝ) (S : Finset V) :
    localRN G U ν S ⊆ U := by
  classical
  exact Finset.filter_subset _ _

omit [Fintype V] in
/-- Forgetting subtype membership preserves the size of every tested set. -/
theorem induced_set_card (U : Finset V) (S : Finset (U : Set V)) :
    (S.image Subtype.val).card = S.card := by
  classical
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- The degree in the actual induced graph is the original local count. -/
theorem induced_degree_eq_local_count (U : Finset V) (v : (U : Set V)) :
    (G.induce (U : Set V)).degree v = (G.neighborFinset v.val ∩ U).card :=
  OrdinaryRobustStability.induced_degree G U v

/-- The actual induced robust neighborhood, viewed as original vertices. -/
theorem induced_robustNeighbors_image (U : Finset V) (ν : ℝ)
    (S : Finset (U : Set V)) :
    (robustNeighbors (G.induce (U : Set V)) ν S).image Subtype.val =
      localRN G U ν (S.image Subtype.val) := by
  classical
  have hdom : Nat.card (U : Set V) = U.card := by
    simpa only [← Nat.card_eq_fintype_card] using Fintype.card_coe U
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    apply (mem_localRN G U ν (S.image Subtype.val) w.val).mpr
    refine ⟨w.property, ?_⟩
    have hcount := (mem_robustNeighbors (G.induce (U : Set V)) ν S w).mp hw
    rw [OrdinaryRobustStability.induced_neighbors_card] at hcount
    simpa only [← Nat.card_eq_fintype_card, hdom] using hcount
  · intro hv
    rcases (mem_localRN G U ν (S.image Subtype.val) v).mp hv with ⟨hvU, hvcount⟩
    refine Finset.mem_image.mpr ⟨⟨v, hvU⟩, ?_, rfl⟩
    rw [mem_robustNeighbors, OrdinaryRobustStability.induced_neighbors_card]
    simpa only [← Nat.card_eq_fintype_card, hdom] using hvcount

/-- The two robust-neighborhood descriptions have exactly the same size. -/
theorem induced_robustNeighbors_card (U : Finset V) (ν : ℝ)
    (S : Finset (U : Set V)) :
    (robustNeighbors (G.induce (U : Set V)) ν S).card =
      (localRN G U ν (S.image Subtype.val)).card := by
  classical
  calc
    _ = ((robustNeighbors (G.induce (U : Set V)) ν S).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = _ := congrArg Finset.card (induced_robustNeighbors_image G U ν S)

/-- Robust expansion of the induced graph can be tested on ambient subsets
of its vertex set, with no change to the normalization or inequalities. -/
theorem induced_robust_iff (U : Finset V) (ν τ : ℝ) :
    IsRobustExpander (G.induce (U : Set V)) ν τ ↔
      ∀ S : Finset V, S ⊆ U →
        τ * (U.card : ℝ) ≤ (S.card : ℝ) →
        (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ) →
        (S.card : ℝ) + ν * (U.card : ℝ) ≤ (localRN G U ν S).card := by
  classical
  have hdom : Nat.card (U : Set V) = U.card := by
    simpa only [← Nat.card_eq_fintype_card] using Fintype.card_coe U
  constructor
  · intro hG S hSU hSlow hShigh
    let T : Finset (U : Set V) := univ.filter (fun v => v.val ∈ S)
    have hTmem (v : (U : Set V)) : v ∈ T ↔ v.val ∈ S := by simp [T]
    have hTimage : T.image Subtype.val = S := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
        exact (hTmem w).mp hw
      · intro hv
        exact Finset.mem_image.mpr ⟨⟨v, hSU hv⟩, (hTmem _).mpr hv, rfl⟩
    have hTcard : T.card = S.card := by
      rw [← hTimage, Finset.card_image_of_injective _ Subtype.val_injective]
    have hlow : τ * Fintype.card (U : Set V) ≤ (T.card : ℝ) := by
      simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using hSlow
    have hhigh : (T.card : ℝ) ≤ (1 - τ) * Fintype.card (U : Set V) := by
      simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using hShigh
    have h := hG T hlow hhigh
    rw [induced_robustNeighbors_card, hTimage] at h
    simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using h
  · intro hG T hSlow hShigh
    have hTsubset : T.image Subtype.val ⊆ U := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, _, rfl⟩
      exact w.property
    have hTcard : (T.image Subtype.val).card = T.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hlow : τ * (U.card : ℝ) ≤ ((T.image Subtype.val).card : ℝ) := by
      simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using hSlow
    have hhigh : ((T.image Subtype.val).card : ℝ) ≤ (1 - τ) * (U.card : ℝ) := by
      simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using hShigh
    have h := hG (T.image Subtype.val) hTsubset hlow hhigh
    rw [← induced_robustNeighbors_card] at h
    simpa only [← Nat.card_eq_fintype_card, hdom, hTcard] using h

/-- Failure of induced robust expansion supplies an ambient tested set
whose local robust neighborhood is strictly too small. -/
theorem exists_bad_set_of_not_induced_robust (U : Finset V) (ν τ : ℝ)
    (hG : ¬ IsRobustExpander (G.induce (U : Set V)) ν τ) :
    ∃ S : Finset V, S ⊆ U ∧
      τ * (U.card : ℝ) ≤ (S.card : ℝ) ∧
      (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ) ∧
      ((localRN G U ν S).card : ℝ) < (S.card : ℝ) + ν * (U.card : ℝ) := by
  classical
  have h := mt (induced_robust_iff G U ν τ).mpr hG
  push_neg at h
  exact h

end Overfull.RobustPartition
