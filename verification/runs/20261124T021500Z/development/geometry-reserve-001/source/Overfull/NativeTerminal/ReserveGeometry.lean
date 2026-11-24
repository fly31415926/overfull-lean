import Overfull.NativeReserve.PackingConstruction
import Overfull.NativeReserve.Residual
import Overfull.ExceptionalPalette.ReserveCopies

/-!
# Geometry of the selected native reserve

All unions and cuts retain the original multigraph edge-copy type. Every
compressed boundary has the same assigned shores as its native parent
signature. Consequently each selected boundary contributes exactly zero
or one old-core crossing copy to either assigned-shore cut.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical NativeReserve AssignedParts
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

/-- The assigned exterior of an old core consists only of exceptions. -/
theorem corePart_sdiff_subset_exceptions (M : Finset E) (Z U : Finset V) :
    corePart G M Z U \\ U ⊆ Z := by
  intro v hv
  obtain ⟨hA,hU⟩ := mem_sdiff.mp hv
  rcases (mem_corePart G M Z U v).mp hA with hvU | ⟨hvZ,_⟩
  · exact (hU hvU).elim
  · exact hvZ

/-- Its order is bounded by the actual exceptional set. -/
theorem corePart_sdiff_card_le (M : Finset E) (Z U : Finset V) :
    (corePart G M Z U \\ U).card ≤ Z.card :=
  card_le_card (corePart_sdiff_subset_exceptions G M Z U)

namespace BoundaryPacking

variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
  (Q : NativeReserve.BoundaryPacking G U₀ U₁ Z M r)
  (hM : G.IsPerfectMatching M)
  (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
  (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)

/-- Compression and common native signature preserve all three actual shores. -/
theorem boundary_assigned_parts (i : Fin r) :
    corePart G (Q.boundary i) Z U₀ = corePart G M Z U₀ ∧
      corePart G (Q.boundary i) Z U₁ = corePart G M Z U₁ ∧
      pairPart G (Q.boundary i) Z = pairPart G M Z := by
  have h := assignedParts_eq_of_signature_eq G (Q.perfect i) hM U₀ U₁ Z
    h01 h0Z h1Z hcover hZ (Q.sameSignature i)
  simpa only [NativeReserve.BoundaryPacking.boundary,
    compressedBoundary_corePart, compressedBoundary_pairPart] using h

/-- The first assigned-shore cut contains exactly the boundary's old-core crossings. -/
theorem boundary_first_cut (i : Fin r) :
    G.cutOn (Q.boundary i) (corePart G M Z U₀) =
      G.cutOn (Q.boundary i) U₀ ∩ G.cutOn (Q.boundary i) U₁ := by
  rw [← (boundary_assigned_parts Q hM h01 h0Z h1Z hcover hZ i).1]
  exact corePart_cutOn_eq_core_crossings G (Q.isMatching i) U₀ U₁ Z
    h01 h0Z h1Z hcover

/-- The two assigned-shore cuts agree copy by copy. -/
theorem boundary_shore_cuts_eq (i : Fin r) :
    G.cutOn (Q.boundary i) (corePart G M Z U₀) =
      G.cutOn (Q.boundary i) (corePart G M Z U₁) := by
  have hp := boundary_assigned_parts Q hM h01 h0Z h1Z hcover hZ i
  rw [← hp.1, ← hp.2.1]
  exact coreParts_cutOn_eq G (Q.isMatching i) U₀ U₁ Z h01 h0Z h1Z hcover

/-- No selected boundary leaves the exceptional pair component. -/
theorem boundary_pair_cut (i : Fin r) :
    G.cutOn (Q.boundary i) (pairPart G M Z) = ∅ := by
  rw [← (boundary_assigned_parts Q hM h01 h0Z h1Z hcover hZ i).2.2]
  exact pairPart_cutOn_eq_empty G (Q.isMatching i) Z

/-- Each compressed boundary contributes the assigned-shore parity, as an exact count. -/
theorem boundary_first_cut_card (i : Fin r) :
    (G.cutOn (Q.boundary i) (corePart G M Z U₀)).card =
      (corePart G M Z U₀).card % 2 := by
  rw [boundary_first_cut Q hM h01 h0Z h1Z hcover hZ i,
    Q.crossing_card hM h01 h0Z h1Z hcover hZ i]
  exact (corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover).symm

/-- Every copy at an assigned exceptional vertex goes to its assigned old core. -/
theorem boundary_otherEnd_mem_core (i : Fin r) (U : Finset V)
    (hU : U = U₀ ∨ U = U₁) {z : V}
    (hz : z ∈ corePart G M Z U \\ U) {e : E}
    (he : e ∈ Q.boundary i) (hze : z ∈ G.edge e) : G.otherEnd z e ∈ U := by
  obtain ⟨hzA,hzU⟩ := mem_sdiff.mp hz
  have hp : corePart G (Q.boundary i) Z U = corePart G M Z U := by
    rcases hU with rfl | rfl
    · exact (boundary_assigned_parts Q hM h01 h0Z h1Z hcover hZ i).1
    · exact (boundary_assigned_parts Q hM h01 h0Z h1Z hcover hZ i).2.1
  rw [← hp] at hzA
  rcases (mem_corePart G (Q.boundary i) Z U z).mp hzA with hzu | ⟨_,f,hf,hzf,hother⟩
  · exact (hzU hzu).elim
  · have hef := Q.isMatching i e he f hf z hze hzf
    simpa only [hef] using hother

/-- A finite selected union of native boundary copies. -/
def selectedUnion {s : ℕ} (q : Fin s → Fin r) : Finset E :=
  univ.biUnion (fun i => Q.boundary (q i))

@[simp] theorem mem_selectedUnion {s : ℕ} (q : Fin s → Fin r) (e : E) :
    e ∈ selectedUnion Q q ↔ ∃ i, e ∈ Q.boundary (q i) := by
  simp [selectedUnion]

/-- Cutting the selected union distributes over its actual boundary classes. -/
theorem selectedUnion_cut {s : ℕ} (q : Fin s → Fin r) (A : Finset V) :
    G.cutOn (selectedUnion Q q) A =
      univ.biUnion (fun i => G.cutOn (Q.boundary (q i)) A) := by
  ext e
  simp only [Multigraph.mem_cutOn, mem_selectedUnion, mem_biUnion,
    mem_univ, true_and]
  tauto

/-- Distinct selected indices preserve disjointness of every boundary copy. -/
theorem selected_cuts_disjoint {s : ℕ} (q : Fin s → Fin r)
    (hq : Function.Injective q) (A : Finset V) :
    Pairwise (fun i j => Disjoint (G.cutOn (Q.boundary (q i)) A)
      (G.cutOn (Q.boundary (q j)) A)) := by
  intro i j hij
  exact (Q.pairwise_disjoint (fun heq => hij (hq heq))).mono
    (filter_subset _ _) (filter_subset _ _)

/-- The selected reserve has exactly `s` crossing copies when the assigned
shore is odd, and none when it is even. -/
theorem selectedUnion_first_cut_card {s : ℕ} (q : Fin s → Fin r)
    (hq : Function.Injective q) :
    (G.cutOn (selectedUnion Q q) (corePart G M Z U₀)).card =
      s * ((corePart G M Z U₀).card % 2) := by
  rw [selectedUnion_cut, card_biUnion]
  · simp_rw [boundary_first_cut_card Q hM h01 h0Z h1Z hcover hZ]
    simp
  · intro i _ j _ hij
    exact selected_cuts_disjoint Q q hq _ hij

/-- Both assigned-shore cuts are precisely the same selected original copies. -/
theorem selectedUnion_shore_cuts_eq {s : ℕ} (q : Fin s → Fin r) :
    G.cutOn (selectedUnion Q q) (corePart G M Z U₀) =
      G.cutOn (selectedUnion Q q) (corePart G M Z U₁) := by
  simp_rw [selectedUnion_cut,
    boundary_shore_cuts_eq Q hM h01 h0Z h1Z hcover hZ]

/-- No edge of the selected union leaves the optional pair component. -/
theorem selectedUnion_pair_cut {s : ℕ} (q : Fin s → Fin r) :
    G.cutOn (selectedUnion Q q) (pairPart G M Z) = ∅ := by
  simp_rw [selectedUnion_cut, boundary_pair_cut Q hM h01 h0Z h1Z hcover hZ]
  simp

/-- All selected incidences at an assigned exception enter its own old core. -/
theorem selectedUnion_otherEnd_mem_core {s : ℕ} (q : Fin s → Fin r)
    (U : Finset V) (hU : U = U₀ ∨ U = U₁) {z : V}
    (hz : z ∈ corePart G M Z U \\ U) {e : E}
    (he : e ∈ selectedUnion Q q) (hze : z ∈ G.edge e) : G.otherEnd z e ∈ U := by
  obtain ⟨i,hi⟩ := (mem_selectedUnion Q q e).mp he
  exact boundary_otherEnd_mem_core Q hM h01 h0Z h1Z hcover hZ (q i) U hU hz hi hze

end BoundaryPacking

end Overfull.NativeTerminal
