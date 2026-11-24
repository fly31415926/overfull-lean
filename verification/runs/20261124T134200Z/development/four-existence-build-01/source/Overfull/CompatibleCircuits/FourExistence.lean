import Overfull.CompatibleCircuits.FourTightShoreCompletion
import Overfull.CompatibleCircuits.FourTightShoreRestriction
import Overfull.CompatibleCircuits.FourStrictSafeSelection
import Overfull.CompatibleCircuits.FourNonlocalReduction

/-!
# Compatible circuit existence on at most four labels

The original half-cut inequalities and even degrees suffice. A tight
nonlocal cut is normalized to a shore of at most two labels and solved by
the two finite three-label constructions with exact original-copy
restoration. If every nonlocal inequality is strict, local coarsening
selects an actual compatible pair or triangle whose deletion preserves
admissibility and even degrees. Strong induction on the number of original
selected copies then completes the construction.

No circuit selector, partition, regularity, degree bound, positive minimum
degree, or finite ambient edge type is an assumption of the final theorem.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (Q : Multigraph (Fin 4) E)

/-- Apply the whole finite tight-shore construction to any selected-copy
set, and restore the exact original copies through the subtype embedding. -/
theorem exists_compatibleCircuitPartition_of_selected_tight_shore
    (classOf : Fin 4 → E → K) (C : Finset E)
    (X : Finset (Fin 4)) (hX : X.Nonempty) (hXcard : X.card ≤ 2)
    (w : Fin 4) (k : K)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) (hw : w ∉ X)
    (htight : 2 * (Q.classCutOn classOf C w k X).card = (Q.cutOn C X).card) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let H := Q.restrictEdges C
  let classes := fun v (e : C) => classOf v e.val
  have hH : H.AdmissibleOn classes univ :=
    (Q.restrictEdges_admissibleOn_univ_iff classOf C).mpr hadmissible
  have hHeven (v : Fin 4) : Even (H.degreeOn univ v) := by
    change Even ((Q.restrictEdges C).degreeOn univ v)
    rw [Q.restrictEdges_degreeOn_univ]
    exact heven v
  have hHtight : 2 * (H.classCutOn classes univ w k X).card =
      (H.cutOn univ X).card := by
    change 2 * ((Q.restrictEdges C).classCutOn (fun v e => classOf v e.val)
      univ w k X).card = ((Q.restrictEdges C).cutOn univ X).card
    rw [Q.restrictEdges_classCutOn_univ_card, Q.restrictEdges_cutOn_univ_card]
    exact htight
  obtain ⟨P⟩ := Overfull.FourOdd.exists_compatibleCircuitPartition_of_tight_shore
    H classes X hX hXcard w k hH hHeven hw hHtight
  exact ⟨P.of_restrictEdges Q classOf C⟩

/-- Complete four-label compatible circuit existence from the original
cut inequalities and even degrees, with every actual copy retained. -/
theorem exists_compatibleCircuitPartition_of_four_label
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases hC : C.Nonempty
    · by_cases hstrict : Q.StrictNonlocalOn classOf C
      · obtain ⟨D, hDC, hD, hcomp, _, hres, hreseven, hless⟩ :=
          Q.exists_safe_short_circuit_of_four_strictNonlocal
            classOf C hC hadmissible heven hstrict
        obtain ⟨P⟩ := ih (C \ D).card (by omega) (C \ D) hres hreseven rfl
        exact ⟨P.insertCircuit Q hDC hD hcomp⟩
      · obtain ⟨w, k, X, hX, hXcard, hw, htight⟩ :=
          Q.exists_small_tight_shore_of_not_four_strictNonlocal
            classOf C hadmissible hstrict
        exact Q.exists_compatibleCircuitPartition_of_selected_tight_shore
          classOf C X hX hXcard w k hadmissible heven hw htight
    · have hzero : C = ∅ := not_nonempty_iff_eq_empty.mp hC
      subst C
      exact ⟨CompatibleCircuitPartition.empty Q classOf⟩

variable [Fintype V] (G : Multigraph V E)

/-- Every finite label type with at most four vertices satisfies complete
compatible circuit existence. Padding changes no actual selected copy. -/
theorem exists_compatibleCircuitPartition_of_card_le_four
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  obtain ⟨P⟩ := (G.embedVertices φ).exists_compatibleCircuitPartition_of_four_label
    (embedIncidenceClasses φ classOf) C
    ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
    (G.embedVertices_even_degrees φ heven)
  exact ⟨P.of_embedVertices G φ⟩

end Overfull.Multigraph
