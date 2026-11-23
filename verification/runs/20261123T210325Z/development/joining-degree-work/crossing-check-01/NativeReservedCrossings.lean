import Overfull.ResidualPalette.JoiningBounds

/-!
# Actual reserved crossings in the surviving native residual

Odd assigned-core parity gives one original old-core crossing in each
compressed reserved boundary. Disjointness and survival retain all these
copies separately in the residual joining graph, including parallel copies.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts FourOdd

variable {V E : Type*}

/-- A copy crossing both disjoint old cores has one endpoint in each core. -/
theorem coreCrossing_endpoint_cases (G : Multigraph V E) (F : Finset E)
    (U₀ U₁ : Finset V) (h01 : Disjoint U₀ U₁) {e : E}
    (he : e ∈ G.cutOn F U₀ ∩ G.cutOn F U₁) :
    (G.firstEnd e ∈ U₀ ∧ G.secondEnd e ∈ U₁) ∨
      (G.firstEnd e ∈ U₁ ∧ G.secondEnd e ∈ U₀) := by
  have hc₀ := ((G.mem_cutOn F U₀ e).mp (mem_inter.mp he).1).2
  have hc₁ := ((G.mem_cutOn F U₁ e).mp (mem_inter.mp he).2).2
  have hn₀ : ¬ (G.firstEnd e ∈ U₀ ↔ G.secondEnd e ∈ U₀) := fun h => hc₀ (propext h)
  have hn₁ : ¬ (G.firstEnd e ∈ U₁ ↔ G.secondEnd e ∈ U₁) := fun h => hc₁ (propext h)
  have hf : ¬ (G.firstEnd e ∈ U₀ ∧ G.firstEnd e ∈ U₁) :=
    fun h => disjoint_left.mp h01 h.1 h.2
  have hs : ¬ (G.secondEnd e ∈ U₀ ∧ G.secondEnd e ∈ U₁) :=
    fun h => disjoint_left.mp h01 h.1 h.2
  tauto

/-- The old-core crossing is exactly a zero-one edge of the original
representative's assigned quotient. -/
theorem coreCrossing_assigned_label_pair (G : Multigraph V E) {M : Finset E}
    (hM : G.IsMatching M) (F : Finset E) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {e : E} (he : e ∈ G.cutOn F U₀ ∩ G.cutOn F U₁) :
    s(assignedLabel G M U₀ U₁ Z (G.firstEnd e),
      assignedLabel G M U₀ U₁ Z (G.secondEnd e)) = s(0,1) := by
  rcases coreCrossing_endpoint_cases G F U₀ U₁ h01 he with ⟨hf,hs⟩ | ⟨hf,hs⟩
  · rw [assignedLabel_on_core₀ G M U₀ U₁ Z hf,
      assignedLabel_on_core₁ G hM U₀ U₁ Z h01 h0Z h1Z hs]
  · rw [assignedLabel_on_core₁ G hM U₀ U₁ Z h01 h0Z h1Z hf,
      assignedLabel_on_core₀ G M U₀ U₁ Z hs]
    exact Sym2.eq_swap

namespace BoundaryPacking
variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : BoundaryPacking G U₀ U₁ Z M r)

/-- Odd first assigned-core order forces each protected boundary to retain
exactly one of its parent's actual old-core crossing copies. -/
theorem crossing_card_one_of_odd (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hodd : (corePart G M Z U₀).card % 2 = 1) (j : Fin r) :
    (G.cutOn (Q.boundary j) U₀ ∩ G.cutOn (Q.boundary j) U₁).card = 1 := by
  rw [Q.crossing_card hM h01 h0Z h1Z hcover hZ j,
    ← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover]
  exact hodd

variable [Fintype E]

/-- The reserve supplies r distinct surviving joining copies, one from each
actual compressed boundary, with quotient endpoints exactly zero and one. -/
theorem exists_surviving_crossing_family (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    {J : Type*} (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) :
    ∃ f : Fin r → joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z),
      Function.Injective f ∧
      (∀ j, (f j).val.val ∈ G.cutOn (Q.boundary j) U₀ ∩ G.cutOn (Q.boundary j) U₁) ∧
      (∀ j, (joiningQuotient (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)).edge
        (f j) = s(0,1)) := by
  have hex (j : Fin r) : ∃ e,
      e ∈ G.cutOn (Q.boundary j) U₀ ∩ G.cutOn (Q.boundary j) U₁ := by
    apply card_pos.mp
    rw [Q.crossing_card_one_of_odd hM h01 h0Z h1Z hcover hZ hodd j]
    decide
  choose e he using hex
  have heB (j : Fin r) : e j ∈ Q.boundary j :=
    ((G.mem_cutOn _ _ _).mp (mem_inter.mp (he j)).1).1
  have heA (j : Fin r) : e j ∈ removedCopies Q.boundary univ :=
    (mem_removedCopies Q.boundary univ _).mpr ⟨j, mem_univ _, heB j⟩
  have hsurvive (j : Fin r) : e j ∉ removedCopies N T := fun hj =>
    disjoint_left.mp (Q.reserved_disjoint_removed N T havoid) (heA j) hj
  have hpair (j : Fin r) :
      s(assignedLabel G M U₀ U₁ Z (G.firstEnd (e j)),
        assignedLabel G M U₀ U₁ Z (G.secondEnd (e j))) = s(0,1) :=
    coreCrossing_assigned_label_pair G (hM.isMatching G) (Q.boundary j)
      U₀ U₁ Z h01 h0Z h1Z (he j)
  have hjoin (j : Fin r) :
      assignedLabel G M U₀ U₁ Z (G.firstEnd (e j)) ≠
        assignedLabel G M U₀ U₁ Z (G.secondEnd (e j)) := by
    intro hsame
    have hdiag := congrArg Sym2.IsDiag (hpair j)
    rw [hsame] at hdiag
    simp at hdiag
  let f (j : Fin r) : joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) :=
    ⟨⟨e j, hsurvive j⟩, (mem_joiningCopies _ _ _).mpr (hjoin j)⟩
  refine ⟨f, ?_, fun j => he j, fun j => hpair j⟩
  intro i j hij
  have heq : e i = e j := congrArg (fun x => x.val.val) hij
  by_contra hne
  exact disjoint_left.mp (Q.pairwise_disjoint hne) (heB i) (heq.symm ▸ heB j)

/-- Select half of the r surviving original crossing copies as a concrete
set in the residual joining-copy subtype, retaining its original reserve. -/
theorem exists_half_residual_crossing_reserve (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    {J : Type*} (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) :
    ∃ A : Finset (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)),
      A.card = r/2 ∧
      (∀ e ∈ A, e.val.val ∈ removedCopies Q.boundary univ) ∧
      (∀ e ∈ A, (joiningQuotient (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)).edge
        e = s(0,1)) := by
  obtain ⟨f,hf,hsource,hpair⟩ := Q.exists_surviving_crossing_family
    hM h01 h0Z h1Z hcover hZ hodd N T havoid
  have hcard : (univ.image f).card = r := by
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  obtain ⟨A,hAsub,hAcard⟩ := exists_subset_card_eq
    (show r/2 ≤ (univ.image f).card from by rw [hcard]; omega)
  refine ⟨A,hAcard,?_,?_⟩
  · intro e he
    obtain ⟨j,_hj,rfl⟩ := mem_image.mp (hAsub he)
    apply (mem_removedCopies Q.boundary univ _).mpr
    exact ⟨j,mem_univ _,((G.mem_cutOn _ _ _).mp (mem_inter.mp (hsource j)).1).1⟩
  · intro e he
    obtain ⟨j,_hj,rfl⟩ := mem_image.mp (hAsub he)
    exact hpair j

end BoundaryPacking

/-- Half of a reserve no larger than the residual degree leaves enough
room for the forced-primary construction's maximum-incidence budget. -/
theorem half_reserve_palette_room (r h D : ℕ) (hrh : r ≤ h) (hDh : 6*D < h) :
    r/2 ≤ h/2 ∧ D ≤ h-r/2 := by omega

end Overfull.NativeReserve
