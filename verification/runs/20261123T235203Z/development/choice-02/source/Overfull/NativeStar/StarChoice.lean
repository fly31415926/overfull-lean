import Overfull.NativeStar.CommonPalette
import Overfull.WeightedPalette.StarWeights

/-!
# Hall choice for actual exceptional-to-core copies

The forbidden relation is actual endpoint intersection with a color class.
Its row bound follows from vertex color load and its column bound from the
previously verified actual-copy star weight.  In particular, parallel copies
are not collapsed to their common neighbor.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical

variable {V E : Type*} [Fintype E]
variable (G : Multigraph V E) {h : ℕ}

omit [Fintype E] in
/-- Restricting to a remaining palette cannot increase the number of colors
occupied at an old-core endpoint. -/
theorem star_row_conflicts_le (C : Fin h → Finset E) (F : Finset (Fin h))
    (z : V) (e : E) :
    (univ.filter (fun c : F => G.otherEnd z e ∈ G.edgeSupport (C c.val))).card ≤
      (univ.filter (fun c => G.otherEnd z e ∈ G.edgeSupport (C c))).card := by
  apply card_le_card_of_injOn Subtype.val
  · intro c hc
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩
  · intro c _ c' _ heq
    exact Subtype.ext heq

/-- The column conflicts are a subset of the actual blocked-copy pool. -/
theorem star_column_conflicts_le (C : Fin h → Finset E)
    (z : V) (U : Finset V) (A : Finset E)
    (hA : A ⊆ AssignedParts.exceptionCorePool G z U) (c : Fin h) :
    (univ.filter (fun e : A => G.otherEnd z e.val ∈ G.edgeSupport (C c))).card ≤
      WeightedPalette.starWeight G z U (C c) := by
  change _ ≤ (WeightedPalette.starBlockedCopies G z U (C c)).card
  apply card_le_card_of_injOn Subtype.val
  · intro e he
    exact (WeightedPalette.mem_starBlockedCopies G z U (C c) e.val).mpr
      ⟨hA e.property, (mem_filter.mp he).2⟩
  · intro e _ e' _ heq
    exact Subtype.ext heq

omit [Fintype E] in
/-- A star copy can be inserted when its exceptional endpoint and its
old-core endpoint are both free in the existing matching. -/
theorem matching_union_star_singleton (z : V) (M : Finset E) (e : E)
    (hM : G.IsMatching M) (hze : z ∈ G.edge e)
    (hz : z ∉ G.edgeSupport M) (hv : G.otherEnd z e ∉ G.edgeSupport M) :
    G.IsMatching (M ∪ {e}) := by
  apply CircuitPatterns.isMatching_union_of_disjoint_support G M {e} hM
    (by intro a ha b hb _ _ _; exact (mem_singleton.mp ha).trans (mem_singleton.mp hb).symm)
  apply disjoint_left.mpr
  intro v hvM hvE
  obtain ⟨a, ha, hva⟩ := (G.mem_edgeSupport {e} v).mp hvE
  have hae : a = e := mem_singleton.mp ha
  rw [hae, G.edge_eq_otherEnd z e hze, Sym2.mem_iff] at hva
  rcases hva with rfl | rfl
  · exact hz hvM
  · exact hv hvM

/-- Actual star copies receive distinct remaining colors with disjoint
endpoints. The supplied conflict bounds are concrete vertex loads and
copy-weight bounds, and the matching conclusion is derived. -/
theorem exists_star_choice (C : Fin h → Finset E) (z : V) (U : Finset V)
    (A : Finset E) (F : Finset (Fin h)) (D b s : ℕ)
    (hA : A ⊆ AssignedParts.exceptionCorePool G z U)
    (hcard : A.card = F.card) (hlower : h - s - D ≤ A.card)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hs : 2 * s ≤ h)
    (hmatching : ∀ c ∈ F, G.IsMatching (C c))
    (hfree : ∀ c ∈ F, z ∉ G.edgeSupport (C c))
    (hload : ∀ v ∈ U, (univ.filter (fun c => v ∈ G.edgeSupport (C c))).card ≤ D + b)
    (hweight : ∀ c ∈ F, WeightedPalette.starWeight G z U (C c) ≤ h / 8 + b) :
    ∃ f : A ≃ F, ∀ e,
      G.otherEnd z e.val ∉ G.edgeSupport (C (f e).val) ∧
      G.IsMatching (C (f e).val ∪ {e.val}) := by
  classical
  let Allowed : A → F → Prop := fun e c => G.otherEnd z e.val ∉ G.edgeSupport (C c.val)
  have hrow (e : A) : (univ.filter (fun c => ¬ Allowed e c)).card ≤ D + b := by
    have hu : G.otherEnd z e.val ∈ U := (mem_filter.mp (hA e.property)).2.2
    have hcount := (star_row_conflicts_le G C F z e.val).trans (hload _ hu)
    simpa only [Allowed, not_not] using hcount
  have hcol (c : F) : (univ.filter (fun e => ¬ Allowed e c)).card ≤ h / 8 + b := by
    have hcount := (star_column_conflicts_le G C z U A hA c.val).trans (hweight _ c.property)
    simpa only [Allowed, not_not] using hcount
  obtain ⟨f, hf⟩ := CircuitPatterns.exists_star_equiv_of_conflict_bounds Allowed h D b s
    hb hD hs (by simpa only [Fintype.card_coe] using hcard)
    (by simpa only [Fintype.card_coe] using hlower) hrow hcol
  refine ⟨f, fun e => ⟨hf e, ?_⟩⟩
  apply matching_union_star_singleton G z (C (f e).val) e.val
    (hmatching _ (f e).property) ((mem_filter.mp (hA e.property)).2.1)
    (hfree _ (f e).property) (hf e)

end Overfull.NativeStar
