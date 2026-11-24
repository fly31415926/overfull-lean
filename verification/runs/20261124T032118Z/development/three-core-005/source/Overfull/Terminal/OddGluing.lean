import Overfull.Terminal.CentralMatchings

/-!
# Restoring both odd boundaries from one central coloring

Each odd leaf is relabeled on its actual boundary copies using the colors
of the simultaneous central contraction.  Thus every overlap agrees on the
same original edge copy, including copies between the two odd shores.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical Multigraph BoundaryExtension NativeTerminal

theorem glue_central_and_odd_leaves {V E : Type*} [Fintype E]
    (G : Multigraph V E) (U A B : Finset V) (k : ℕ)
    (hUA : Disjoint U A) (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B)
    (hA : G.cutSize A = k) (hB : G.cutSize B = k)
    (c : (centralGraph G U A).EdgeColoring k)
    (cA : (contract G A).EdgeColoring k) (cB : (contract G B).EdgeColoring k) :
    Nonempty (G.EdgeColoring k) := by
  let labelA := centralBoundaryLabels G U A A k (Sum.inr 0)
    (centralMap_eq_first_apex_iff U A hUA) c
  let labelB := centralBoundaryLabels G U A B k (Sum.inr 1)
    (centralMap_eq_second_apex_iff U A B hUB hAB hcover) c
  obtain ⟨dA,hdA,_⟩ := exists_singleton_boundary_extension G A k cA hA labelA
    (centralBoundaryLabels_injective G U A A k (Sum.inr 0)
      (centralMap_eq_first_apex_iff U A hUA) c)
  obtain ⟨dB,hdB,_⟩ := exists_singleton_boundary_extension G B k cB hB labelB
    (centralBoundaryLabels_injective G U A B k (Sum.inr 1)
      (centralMap_eq_second_apex_iff U A B hUB hAB hcover) c)
  let S : Fin 3 → Finset V := ![U,A,B]
  have hS : ∀ v, ∃ i, v ∈ S i := by
    intro v
    rcases hcover v with h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  let d : ∀ i, PaletteColoring (retainedGraph G (S i)) (Fin k) := by
    refine Fin.cases (centralColoringToRetained G U A k c) ?_
    refine Fin.cases dA ?_
    refine Fin.cases dB ?_
    intro i
    exact i.elim0
  have hagrees : ∀ i j (e : E)
      (hi : ∃ u : S i, u.val ∈ G.edge e)
      (hj : ∃ u : S j, u.val ∈ G.edge e),
      (d i).color ⟨e,hi⟩ = (d j).color ⟨e,hj⟩ := by
    intro i j e hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · have he := (boundary_of_two_retained G U A hUA e hi hj).2
      exact (hdA ⟨e,he⟩).symm
    · have he := (boundary_of_two_retained G U B hUB e hi hj).2
      exact (hdB ⟨e,he⟩).symm
    · have he := (boundary_of_two_retained G U A hUA e hj hi).2
      exact hdA ⟨e,he⟩
    · rfl
    · obtain ⟨heA,heB⟩ := boundary_of_two_retained G A B hAB e hi hj
      exact (hdA ⟨e,heA⟩).trans (hdB ⟨e,heB⟩).symm
    · have he := (boundary_of_two_retained G U B hUB e hj hi).2
      exact hdB ⟨e,he⟩
    · obtain ⟨heA,heB⟩ := boundary_of_two_retained G A B hAB e hj hi
      exact (hdB ⟨e,heB⟩).trans (hdA ⟨e,heA⟩).symm
    · rfl
  obtain ⟨color,_⟩ := exists_glued_retained_coloring G S hS d hagrees
  exact ⟨color.toEdgeColoring⟩

end Overfull.Terminal
