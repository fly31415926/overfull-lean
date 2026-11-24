import Overfull.CompatibleCircuits.FourExistence

/-!
# Exact compatible-circuit criterion on at most four labels

Every actual circuit partition has even degrees, by summing the degrees
of its disjoint parts. Combining this with the already proved necessary
half-cut inequalities and complete four-label existence gives an exact
necessary-and-sufficient criterion.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*} (G : Multigraph V E)

/-- A partition into genuine circuits forces even degree at every vertex,
with parallel multiplicity accounted for by the disjoint actual-copy sum. -/
theorem CompatibleCircuitPartition.even_degrees
    {classOf : V → E → K} {C : Finset E}
    (P : G.CompatibleCircuitPartition classOf C) :
    ∀ v, Even (G.degreeOn C v) := by
  intro v
  have hdegree : G.degreeOn C v = ∑ D ∈ P.parts, G.degreeOn D v := by
    calc
      _ = G.degreeOn (P.parts.biUnion id) v :=
        congrArg (fun D => G.degreeOn D v) P.cover.symm
      _ = _ := G.degreeOn_biUnion_disjoint P.parts id P.disjoint v
  rw [hdegree]
  have hdvd : 2 ∣ ∑ D ∈ P.parts, G.degreeOn D v :=
    Finset.dvd_sum (fun D hD => (IsCircuit.even_degreeOn G (P.circuit D hD) v).two_dvd)
  exact Nat.even_iff.mpr (Nat.mod_eq_zero_of_dvd hdvd)

/-- On at most four finite labels, the original half-cut inequalities
and even degrees are precisely the compatible-circuit partition criterion. -/
theorem compatibleCircuitPartition_iff_admissible_and_even_of_card_le_four
    [Fintype V] (hV : Fintype.card V ≤ 4)
    (classOf : V → E → K) (C : Finset E) :
    Nonempty (G.CompatibleCircuitPartition classOf C) ↔
      G.AdmissibleOn classOf C ∧ ∀ v, Even (G.degreeOn C v) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.admissibleOn G, P.even_degrees G⟩
  · rintro ⟨hadmissible, heven⟩
    exact G.exists_compatibleCircuitPartition_of_card_le_four hV
      classOf C hadmissible heven

/-- The four-label version of the exact original-copy criterion. -/
theorem fourLabel_compatibleCircuitPartition_iff_admissible_and_even
    (Q : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K) (C : Finset E) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) ↔
      Q.AdmissibleOn classOf C ∧ ∀ v, Even (Q.degreeOn C v) :=
  Q.compatibleCircuitPartition_iff_admissible_and_even_of_card_le_four
    (by decide) classOf C

end Overfull.Multigraph
