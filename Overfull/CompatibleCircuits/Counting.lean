import Overfull.CompatibleCircuits.Basic

/-!
# Cut accounting for compatible circuits

The half-cut inequalities are necessary for a compatible circuit
partition.  The proofs count actual copies and apply to every shore,
including shores that meet more than one connected component.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*} (G : Multigraph V E)

/-- The selected copies whose two ends lie in the shore. -/
noncomputable def internalOn (C : Finset E) (X : Finset V) : Finset E :=
  C.filter (fun e => G.firstEnd e ∈ X ∧ G.secondEnd e ∈ X)

/-- The finite-set version of degree-sum counting, without an ambient
finiteness assumption on the edge type. -/
theorem degreeOn_sum_on (C : Finset E) (X : Finset V) :
    (∑ v ∈ X, G.degreeOn C v) =
      2 * (G.internalOn C X).card + (G.cutOn C X).card := by
  have hsum : (∑ v ∈ X, G.degreeOn C v) =
      ∑ e ∈ C, (X.filter (fun v => v ∈ G.edge e)).card := by
    simp only [degreeOn, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hcount (e : E) :
      (X.filter (fun v => v ∈ G.edge e)).card =
        2 * (if G.firstEnd e ∈ X ∧ G.secondEnd e ∈ X then 1 else 0) +
          (if (G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X) then 1 else 0) := by
    have hfilter : X.filter (fun v => v ∈ G.edge e) =
        (if G.firstEnd e ∈ X then {G.firstEnd e} else ∅) ∪
          (if G.secondEnd e ∈ X then {G.secondEnd e} else ∅) := by
      ext v
      by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
        simp [h₁, h₂, G.incident_iff] <;> aesop
    rw [hfilter]
    have hne := G.endpoints_distinct e
    by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
      simp [h₁, h₂, hne.symm]
  rw [hsum]
  simp_rw [hcount]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, internalOn, cutOn, Nat.cast_id]

/-- Every cut of an even-degree edge-copy subgraph has even size. -/
theorem even_cutOn_of_even_degrees {C : Finset E}
    (hdegree : ∀ v, Even (G.degreeOn C v)) (X : Finset V) :
    Even (G.cutOn C X).card := by
  have hsum : 2 ∣ ∑ v ∈ X, G.degreeOn C v :=
    Finset.dvd_sum (fun v _ => (hdegree v).two_dvd)
  rw [G.degreeOn_sum_on] at hsum
  apply Nat.even_iff.mpr
  have hmod := Nat.mod_eq_zero_of_dvd hsum
  omega

theorem IsCircuit.even_degreeOn {C : Finset E} (hC : G.IsCircuit C) (v : V) :
    Even (G.degreeOn C v) := by
  by_cases hv : v ∈ G.edgeSupport C
  · rw [hC.2.1 v hv]
    decide
  · rw [G.degreeOn_eq_zero_of_not_mem hv]
    exact ⟨0, rfl⟩

theorem IsCircuit.even_cutOn {C : Finset E} (hC : G.IsCircuit C) (X : Finset V) :
    Even (G.cutOn C X).card :=
  G.even_cutOn_of_even_degrees hC.even_degreeOn X

/-- Compatibility and even degrees imply the half-cut condition. -/
theorem Compatible.admissibleOn {classOf : V → E → K} {C : Finset E}
    (hC : G.Compatible classOf C) (hdegree : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf C := by
  intro v k X
  have hclass := Compatible.classCutOn_card_le_one G hC v k X
  have hsubset : G.classCutOn classOf C v k X ⊆ G.cutOn C X :=
    Finset.filter_subset _ _
  have hle := Finset.card_le_card hsubset
  obtain ⟨n, hn⟩ := G.even_cutOn_of_even_degrees hdegree X
  omega

theorem IsCircuit.admissibleOn {classOf : V → E → K} {C : Finset E}
    (hC : G.IsCircuit C) (hcompatible : G.Compatible classOf C) :
    G.AdmissibleOn classOf C :=
  Compatible.admissibleOn G hcompatible hC.even_degreeOn

theorem AdmissibleOn.empty (classOf : V → E → K) :
    G.AdmissibleOn classOf ∅ := by
  intro v k X
  simp [classCutOn, cutOn]

/-- Disjoint unions add both sides of every class-cut inequality. -/
theorem AdmissibleOn.union {classOf : V → E → K} {C D : Finset E}
    (hC : G.AdmissibleOn classOf C) (hD : G.AdmissibleOn classOf D)
    (hdisjoint : Disjoint C D) : G.AdmissibleOn classOf (C ∪ D) := by
  intro v k X
  have hcuts : Disjoint (G.cutOn C X) (G.cutOn D X) :=
    hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hclasses : Disjoint (G.classCutOn classOf C v k X)
      (G.classCutOn classOf D v k X) :=
    hcuts.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcut_union : G.cutOn (C ∪ D) X = G.cutOn C X ∪ G.cutOn D X := by
    simp only [cutOn, Finset.filter_union]
  have hclass_union : G.classCutOn classOf (C ∪ D) v k X =
      G.classCutOn classOf C v k X ∪ G.classCutOn classOf D v k X := by
    simp only [classCutOn, hcut_union, Finset.filter_union]
  rw [hcut_union, hclass_union, Finset.card_union_of_disjoint hcuts,
    Finset.card_union_of_disjoint hclasses]
  have h₁ := hC v k X
  have h₂ := hD v k X
  omega

/-- Every actual compatible circuit partition satisfies all of the
Fan--Zhang half-cut inequalities.  This is the necessary direction. -/
theorem CompatibleCircuitPartition.admissibleOn {classOf : V → E → K}
    {C : Finset E} (P : G.CompatibleCircuitPartition classOf C) :
    G.AdmissibleOn classOf C := by
  have hfamily (S : Finset (Finset E))
      (hparts : ∀ D ∈ S, G.AdmissibleOn classOf D)
      (hdisjoint : ∀ D ∈ S, ∀ D' ∈ S, D ≠ D' → Disjoint D D') :
      G.AdmissibleOn classOf (S.biUnion id) := by
    induction S using Finset.induction_on with
    | empty => simpa using AdmissibleOn.empty G classOf
    | @insert D S hDS ih =>
      have htail : G.AdmissibleOn classOf (S.biUnion id) :=
        ih (fun A hA => hparts A (Finset.mem_insert_of_mem hA))
          (fun A hA B hB hne => hdisjoint A (Finset.mem_insert_of_mem hA)
            B (Finset.mem_insert_of_mem hB) hne)
      have hd : Disjoint D (S.biUnion id) := by
        apply Finset.disjoint_left.mpr
        intro e heD heS
        obtain ⟨A, hAS, heA⟩ := Finset.mem_biUnion.mp heS
        have hDA : D ≠ A := fun h => hDS (h.symm ▸ hAS)
        exact Finset.disjoint_left.mp
          (hdisjoint D (Finset.mem_insert_self _ _)
            A (Finset.mem_insert_of_mem hAS) hDA) heD heA
      simpa only [Finset.biUnion_insert, id_eq] using
        AdmissibleOn.union G (hparts D (Finset.mem_insert_self _ _)) htail hd
  rw [← P.cover]
  exact hfamily P.parts (fun D hD =>
    IsCircuit.admissibleOn G (P.circuit D hD) (P.compatible D hD))
    P.disjoint

end Overfull.Multigraph
