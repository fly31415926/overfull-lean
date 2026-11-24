import Overfull.CompatibleCircuits.ThreeLabel
import Overfull.CompatibleCircuits.VertexEmbedding

/-!
# Compatible circuit partitions on at most three vertices

The complete three-label theorem extends to any finite vertex type of
cardinality at most three by adding isolated labels. The embedding keeps
the original actual edge copies and original incidence classes; neither
an inhabited class type nor a preselected circuit is assumed.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} [Fintype V] (G : Multigraph V E)

/-- On at most three vertices, every nonempty admissible even-degree
edge-copy graph has a safe compatible pair or triangle. -/
theorem exists_safe_circuit_of_card_le_three (hV : Fintype.card V ≤ 3)
    (classOf : V → E → K) (C : Finset E) (hC : C.Nonempty)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    ∃ D ⊆ C, G.IsCircuit D ∧ G.Compatible classOf D ∧
      G.AdmissibleOn classOf (C \ D) ∧ (D.card = 2 ∨ D.card = 3) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 3) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  obtain ⟨D, hDC, hD, hcomp, hsafe, hcard⟩ :=
    (G.embedVertices φ).exists_threeLabel_safe_circuit
      (embedIncidenceClasses φ classOf) C hC
      ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
      (G.embedVertices_even_degrees φ heven)
  exact ⟨D, hDC, hD.of_embedVertices G φ,
    (G.embedVertices_compatible φ classOf D).mp hcomp,
    (G.embedVertices_admissibleOn φ classOf (C \ D)).mp hsafe, hcard⟩

/-- Complete compatible circuit decomposition on any finite vertex type
with at most three vertices, under the original cut and parity conditions. -/
theorem exists_compatibleCircuitPartition_of_card_le_three (hV : Fintype.card V ≤ 3)
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 3) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  obtain ⟨P⟩ := (G.embedVertices φ).exists_threeLabel_compatibleCircuitPartition
    (embedIncidenceClasses φ classOf) C
    ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
    (G.embedVertices_even_degrees φ heven)
  exact ⟨P.of_embedVertices G φ⟩

/-- On at most three vertices with even degrees, admissibility is exactly
the condition for an actual compatible circuit partition. -/
theorem compatibleCircuitPartition_iff_admissible_of_card_le_three
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K) (C : Finset E)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) ↔ G.AdmissibleOn classOf C := by
  constructor
  · rintro ⟨P⟩
    exact P.admissibleOn G
  · intro hadmissible
    exact G.exists_compatibleCircuitPartition_of_card_le_three hV classOf C
      hadmissible heven

end Overfull.Multigraph
