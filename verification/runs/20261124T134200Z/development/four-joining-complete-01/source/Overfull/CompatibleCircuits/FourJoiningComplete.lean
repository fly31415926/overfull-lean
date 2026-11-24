import Overfull.CompatibleCircuits.FourExistence
import Overfull.CompatibleCircuits.FourBoundedJoining

/-!
# Complete even-fiber and two-odd-fiber joining decompositions

The unrestricted four-label circuit theorem removes the small-boundary
hypotheses from both original-host joining constructions. The resulting
families cover all original joining copies exactly. No upper bound is
placed on boundary sizes or parallel multiplicities.

These are the complete circuit-stage outputs. The later robust-core
packing, palette and terminal factorization construction remains separate.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq I]
    (G : Multigraph V E) (label : V → I)

/-- At most four even fibers admit an exact joining decomposition directly
from regularity and the absence of overfull sets, with unrestricted cuts. -/
theorem exists_fourJoining_decomposition_of_even_fibers
    (hI : Fintype.card I ≤ 4) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) :
    Nonempty (FourJoiningDecomposition G label) := by
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_four
    hI ((joiningGraph G label).endpointClass label) univ
    (joiningQuotient_admissible_of_even_fibers G label hregular hno hfibers)
    (joiningQuotient_degree_even_of_even_fibers G label hregular hfibers)
  exact ⟨fourJoiningDecompositionOfPartition G label hI P⟩

/-- An even regular degree and a half-degree bound on each vertex's joining
incidences also suffice on at most four fibers, regardless of fiber parity. -/
theorem exists_fourJoining_decomposition_of_even_degree_bound
    (hI : Fintype.card I ≤ 4) {h D : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X) (heven : Even h)
    (hD : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D) (hhalf : 2 * D ≤ h) :
    Nonempty (FourJoiningDecomposition G label) := by
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_four
    hI ((joiningGraph G label).endpointClass label) univ
    (joiningQuotient_admissible_of_degree_bound G label hregular hno hD hhalf)
    (joiningQuotient_degree_even_of_even_regular G label hregular heven)
  exact ⟨fourJoiningDecompositionOfPartition G label hI P⟩

/-- Exactly two odd fibers give exactly `h` primary matching pieces and
an even-footprint surplus family. All original copies are preserved, with
no small even-fiber boundary or bound on the virtual multiplicity. -/
theorem exists_fourTwoOddJoining_decomposition
    (a b : I) (hab : a ≠ b) (h : ℕ) (hI : Fintype.card I ≤ 4)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i = a ∨ i = b then 1 else 0) :
    Nonempty (FourTwoOddJoiningDecomposition G label a b h) := by
  obtain ⟨P⟩ := (twoOddJoiningQuotient G label a b hab h).exists_compatibleCircuitPartition_of_card_le_four
    hI (twoOddJoiningClasses G label h) univ
    (twoOddJoiningQuotient_admissible G label a b hab h hregular hno hfibers)
    (twoOddJoiningQuotient_even_degrees G label a b hab h hregular hfibers)
  exact ⟨fourTwoOddJoiningDecompositionOfPartition G label a b hab h hI P⟩

end Overfull.FourOdd
