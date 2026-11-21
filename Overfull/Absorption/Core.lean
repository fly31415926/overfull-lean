import Overfull.Absorption.CoreRobust

/-!
# Actual enlarged core graphs

Absorption changes the distinguished core and its vertex set. It leaves
the ambient graph unchanged. The enlarged core keeps exactly the original
core edges between old vertices and all ambient edges incident to a newly
absorbed vertex.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Inclusion of the old labels into the enlarged core. -/
def oldInclusion (U A : Finset V) : U ↪ ↥(U ∪ A) where
  toFun v := ⟨v.val,mem_union_left A v.property⟩
  inj' := by
    intro v w h
    exact Subtype.ext (congrArg (fun x : ↥(U ∪ A) => x.val) h)

/-- Actual ambient edges incident to the absorbed set. -/
def incidentGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ A ∨ v ∈ A)
  symm := by rintro u v ⟨h,ha⟩; exact ⟨h.symm,ha.symm⟩
  loopless := by intro v h; exact G.loopless v h.1

noncomputable instance (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    DecidableRel (incidentGraph G A).Adj := by
  intro u v
  infer_instance

/-- The core after absorbing `A`, on its actual enlarged vertex set. -/
def enlargedCore (G : SimpleGraph V) (U A : Finset V) (H : SimpleGraph U) :
    SimpleGraph ↥(U ∪ A) :=
  H.map (oldInclusion U A) ⊔ (incidentGraph G A).induce ((U ∪ A : Finset V) : Set V)

noncomputable instance (G : SimpleGraph V) (U A : Finset V) (H : SimpleGraph U) :
    DecidableRel (enlargedCore G U A H).Adj := Classical.decRel _

/-- Every old edge is retained with its original endpoint labels. -/
theorem enlargedCore_old_edge (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) {u v : U} (huv : H.Adj u v) :
    (enlargedCore G U A H).Adj (oldInclusion U A u) (oldInclusion U A v) :=
  Or.inl (SimpleGraph.map_adj_apply.mpr huv)

/-- Every ambient edge incident to a newly absorbed vertex is retained. -/
theorem enlargedCore_new_edge (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) (u v : ↥(U ∪ A))
    (huv : G.Adj u.val v.val) (hA : u.val ∈ A ∨ v.val ∈ A) :
    (enlargedCore G U A H).Adj u v := Or.inr ⟨huv,hA⟩

/-- The restriction to the old vertices is exactly the supplied old core. -/
theorem enlargedCore_old_adj (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) (hUA : Disjoint U A) (u v : U) :
    (enlargedCore G U A H).Adj (oldInclusion U A u) (oldInclusion U A v) ↔
      H.Adj u v := by
  constructor
  · intro huv
    rcases huv with huv | huv
    · exact SimpleGraph.map_adj_apply.mp huv
    · rcases huv.2 with hu | hv
      · exact False.elim (Finset.disjoint_left.mp hUA u.property hu)
      · exact False.elim (Finset.disjoint_left.mp hUA v.property hv)
  · exact enlargedCore_old_edge G U A H

theorem enlargedCore_old_restriction (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) (hUA : Disjoint U A) :
    (enlargedCore G U A H).comap (oldInclusion U A) = H := by
  ext u v
  exact enlargedCore_old_adj G U A H hUA u v

/-- The enlarged graph uses only actual ambient edges. -/
theorem enlargedCore_le_ambient (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V)) :
    enlargedCore G U A H ≤ G.induce ((U ∪ A : Finset V) : Set V) := by
  intro u v huv
  rcases huv with huv | huv
  · obtain ⟨x,y,hxy,rfl,rfl⟩ := huv
    exact hH hxy
  · exact huv.1

/-- Old vertices lose no core neighbors. -/
theorem enlargedCore_old_degree (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) [DecidableRel H.Adj] (v : U) :
    H.degree v ≤ (enlargedCore G U A H).degree (oldInclusion U A v) := by
  have h := old_neighbors_le H (enlargedCore G U A H) (oldInclusion U A)
    (enlargedCore_old_edge G U A H) univ v
  simpa only [oldPart,mem_univ,filter_true,inter_univ,card_neighborFinset_eq_degree] using h

variable [Fintype V]

/-- Enlarging a distinguished core never creates an ambient edge. -/
theorem enlargedCore_degree_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A : Finset V) (H : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V)) (v : ↥(U ∪ A)) :
    (enlargedCore G U A H).degree v ≤ G.degree v.val := by
  have hsub := (enlargedCore G U A H).degree_le_of_le
    (enlargedCore_le_ambient G U A H hH) (v := v)
  exact hsub.trans (OrdinaryRobustStability.induced_degree_bounds G (U ∪ A) v).1

/-- Neighbors in the old core, expressed on the old core's own vertex type. -/
noncomputable def oldNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) : Finset U :=
  univ.filter (fun u => G.Adj v u.val)

theorem oldNeighbors_image (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) :
    (oldNeighbors G U v).image Subtype.val = G.neighborFinset v ∩ U := by
  ext w
  simp only [mem_image, oldNeighbors, mem_filter, mem_univ, true_and,
    mem_inter, mem_neighborFinset]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨hu,u.property⟩
  · rintro ⟨hw,hwU⟩
    exact ⟨⟨w,hwU⟩,hw,rfl⟩

theorem oldNeighbors_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) :
    (oldNeighbors G U v).card = (G.neighborFinset v ∩ U).card := by
  rw [← oldNeighbors_image,card_image_of_injective _ Subtype.val_injective]

/-- A new vertex retains every one of its actual neighbors in the old core. -/
theorem enlargedCore_new_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A : Finset V) (H : SimpleGraph U) (v : ↥(U ∪ A)) (hv : v.val ∈ A) :
    (G.neighborFinset v.val ∩ U).card ≤ (enlargedCore G U A H).degree v := by
  have hs : (oldNeighbors G U v.val).image (oldInclusion U A) ⊆
      (enlargedCore G U A H).neighborFinset v := by
    rintro w hw
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hw
    apply ((enlargedCore G U A H).mem_neighborFinset v _).mpr
    apply enlargedCore_new_edge G U A H
    · exact (mem_filter.mp hu).2
    · exact Or.inl hv
  have hc := card_le_card hs
  rwa [card_image_of_injective _ (oldInclusion U A).injective,
    oldNeighbors_card,card_neighborFinset_eq_degree] at hc

/-- A common degree lower bound for the old and newly absorbed vertices. -/
theorem enlargedCore_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A : Finset V) (H : SimpleGraph U) [DecidableRel H.Adj] (d : ℝ)
    (hold : ∀ v, d ≤ (H.degree v : ℝ))
    (hnew : ∀ v ∈ A, d ≤ ((G.neighborFinset v ∩ U).card : ℝ)) :
    ∀ v, d ≤ ((enlargedCore G U A H).degree v : ℝ) := by
  intro v
  rcases mem_union.mp v.property with hv | hv
  · have hb : (H.degree ⟨v.val,hv⟩ : ℝ) ≤
        (enlargedCore G U A H).degree (oldInclusion U A ⟨v.val,hv⟩) := by
      exact_mod_cast enlargedCore_old_degree G U A H ⟨v.val,hv⟩
    exact (hold ⟨v.val,hv⟩).trans hb
  · have hb : ((G.neighborFinset v.val ∩ U).card : ℝ) ≤
        (enlargedCore G U A H).degree v := by
      exact_mod_cast enlargedCore_new_degree G U A H v hv
    exact (hnew v.val hv).trans hb

/-- If each absorbed vertex has at most `b` neighbors outside the old core,
the new common error is at most `a+b`. -/
theorem enlargedCore_degree_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A : Finset V) (H : SimpleGraph U) [DecidableRel H.Adj]
    (h : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hold : ∀ v, (h : ℝ)-a ≤ (H.degree v : ℝ))
    (hnew : ∀ v ∈ A, (h : ℝ)-b ≤ ((G.neighborFinset v ∩ U).card : ℝ)) :
    ∀ v, (h : ℝ)-(a+b) ≤ ((enlargedCore G U A H).degree v : ℝ) := by
  apply enlargedCore_degree_lower G U A H
  · intro v
    linarith [hold v]
  · intro v hv
    linarith [hnew v hv]

omit [Fintype V] in
/-- The actual enlarged core has fixed robust parameters. -/
theorem enlargedCore_robust (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) [DecidableRel H.Adj] (ν τ : ℝ)
    (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hsmall : (A.card : ℝ) ≤ ν*U.card/4)
    (hrobust : IsRobustExpander H ν τ) :
    IsRobustExpander (enlargedCore G U A H) (ν/4) (2*τ) := by
  apply robust_after_addition H (enlargedCore G U A H) (oldInclusion U A)
    (enlargedCore_old_edge G U A H) ν τ hν hντ hτ
  · simp only [Fintype.card_coe]
    have hc : ((U ∪ A).card : ℝ) ≤ U.card + A.card := by
      exact_mod_cast card_union_le U A
    linarith
  · exact hrobust

omit [Fintype V] in
/-- The same absorption constructor restores a smaller range using the
actual enlarged minimum degree. It can be applied at both absorptions. -/
theorem enlargedCore_robust_smaller_range (G : SimpleGraph V) (U A : Finset V)
    (H : SimpleGraph U) [DecidableRel H.Adj] (η ν τ σ : ℝ)
    (hη : 0 < η) (hηone : η ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 2*τ ≤ η/4) (hσ : 0 < σ) (hστ : σ ≤ 2*τ)
    (hsmall : (A.card : ℝ) ≤ ν*U.card/4)
    (hdegree : ∀ v, η*(U ∪ A).card ≤ ((enlargedCore G U A H).degree v : ℝ))
    (hrobust : IsRobustExpander H ν τ) :
    IsRobustExpander (enlargedCore G U A H) (min (ν/4) (η*σ/2)) σ := by
  apply robust_after_addition_smaller_range H (enlargedCore G U A H)
    (oldInclusion U A) (enlargedCore_old_edge G U A H)
    η ν τ σ hη hηone hν hντ hτ hσ hστ
  · simp only [Fintype.card_coe]
    have hc : ((U ∪ A).card : ℝ) ≤ U.card + A.card := by
      exact_mod_cast card_union_le U A
    linarith
  · simpa only [Fintype.card_coe] using hdegree
  · exact hrobust

end Overfull.Absorption
