import Overfull.OrdinaryFactorization.ResidualInterface
import Overfull.TwoApexFactorization.Shores

/-!
# The residual core in the two-apex shore interface

The recorded paired-cut sides index the actual surviving crossing core.
Their images in the ambient vertex type are exactly the shores used by
two-apex completion, including all nested subtype identifications.
-/

noncomputable section

namespace Overfull.OneCore

open Finset Classical SmallCuts PairedCut OrdinaryFactorization

section CutEquivalence

variable {V : Type*} {U : Finset V}

/-- Pulling a graph that already crosses the cut back through its side
equivalence produces exactly the explicitly indexed cut-sides graph. -/
theorem comap_cutSidesEquiv_eq (H : SimpleGraph U) (A B : Finset U)
    (hd : Disjoint A B) (hu : A ∪ B = univ)
    (hcross : crossingGraph H A = H) :
    H.comap (cutSidesEquiv A B hd hu) = cutSidesGraph H A B := by
  unfold cutSidesGraph
  rw [hcross]
  rfl

/-- The left side of the sum equivalence is the original left set mapped
into the ambient vertex type. -/
theorem cutSidesEquiv_leftShore (A B : Finset U)
    (hd : Disjoint A B) (hu : A ∪ B = univ) :
    TwoApexFactorization.leftShore (cutSidesEquiv A B hd hu) =
      A.map (Function.Embedding.subtype (fun v => v ∈ U)) := by
  ext v
  rw [TwoApexFactorization.mem_leftShore, Finset.mem_map]
  simp only [cutSidesEquiv_inl, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, ha⟩
  · rintro ⟨a, ha, hav⟩
    exact ⟨⟨a, ha⟩, hav⟩

/-- The right side of the sum equivalence is the original right set mapped
into the ambient vertex type. -/
theorem cutSidesEquiv_rightShore (A B : Finset U)
    (hd : Disjoint A B) (hu : A ∪ B = univ) :
    TwoApexFactorization.rightShore (cutSidesEquiv A B hd hu) =
      B.map (Function.Embedding.subtype (fun v => v ∈ U)) := by
  ext v
  rw [TwoApexFactorization.mem_rightShore, Finset.mem_map]
  simp only [cutSidesEquiv_inr, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, b.property, hb⟩
  · rintro ⟨b, hb, hbv⟩
    exact ⟨⟨b, hb⟩, hbv⟩

end CutEquivalence

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (C : Core G U) (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- Index the recorded surviving core by its two actual paired-cut sides. -/
def residualShoreEquiv : D.geometry.left ⊕ D.geometry.right ≃ U :=
  cutSidesEquiv D.geometry.left D.geometry.right D.geometry.disjoint D.geometry.cover

/-- The indexed residual core is exactly the graph to which the recorded
robust-expansion estimates apply. -/
theorem residualShore_comap :
    (residualCrossingCore C D).graph.comap (residualShoreEquiv C D) =
      cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right :=
  comap_cutSidesEquiv_eq _ _ _ D.geometry.disjoint D.geometry.cover
    (residualCrossing_crossing C D)

/-- The two-apex left shore consists of the same original ambient vertices
as the recorded left side. -/
theorem residualShore_left :
    TwoApexFactorization.leftShore (residualShoreEquiv C D) =
      D.geometry.left.map (Function.Embedding.subtype (fun v => v ∈ U)) :=
  cutSidesEquiv_leftShore _ _ D.geometry.disjoint D.geometry.cover

/-- The two-apex right shore consists of the same original ambient vertices
as the recorded right side. -/
theorem residualShore_right :
    TwoApexFactorization.rightShore (residualShoreEquiv C D) =
      D.geometry.right.map (Function.Embedding.subtype (fun v => v ∈ U)) :=
  cutSidesEquiv_rightShore _ _ D.geometry.disjoint D.geometry.cover

/-- The indexed sides have the same finite order. -/
theorem residualShore_balance :
    Fintype.card D.geometry.left = Fintype.card D.geometry.right :=
  residualCutSides_balance C D

/-- The exact graph passed to two-apex completion has its required sum
bipartition. -/
theorem residualShore_bipartite :
    ((residualCrossingCore C D).graph.comap (residualShoreEquiv C D)).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  rw [residualShore_comap]
  exact residualCutSides_bipartite C D

/-- Transport any recorded robust parameters through the exact graph
identity. In particular this applies directly to `BipartiteResidualData.robust`. -/
theorem residualShore_robust {ν' τ' : ℝ}
    (hrob : IsBipartiteRobustExpander
      (cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right)
      ν' τ') :
    IsBipartiteRobustExpander
      ((residualCrossingCore C D).graph.comap (residualShoreEquiv C D)) ν' τ' := by
  simpa only [residualShore_comap C D] using hrob

/-- The reserve-use bound itself supplies the expected residual parameters. -/
theorem residualShore_robust_of_reserve (hμ : 0 ≤ μ) (hμξ : 4 * μ ≤ ξ) :
    IsBipartiteRobustExpander
      ((residualCrossingCore C D).graph.comap (residualShoreEquiv C D)) (ξ / 2) (4 * τ) :=
  residualShore_robust C D (residualCrossing_robust C D hμ hμξ)

end Overfull.OneCore
