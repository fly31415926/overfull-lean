import Overfull.MultigraphGreedy

/-!
# Greedy extension with prescribed lists

The lists and the proper partial coloring refer to actual edge copies.
Every previously assigned color is retained. This provides the deterministic
repair step when a sparse set of conflicting edges is assigned spare colors.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} {G : Multigraph V E} [Fintype E] {k : ℕ}

namespace PartialEdgeColoring

private theorem extend_over_finset_from_lists (c : G.PartialEdgeColoring k)
    (L : E → Finset (Fin k))
    (hc : ∀ e i, c.color e = some i → i ∈ L e)
    (hbound : ∀ e, c.color e = none → (G.conflictingEdges e).card < (L e).card)
    (F : Finset E) :
    ∃ d : G.PartialEdgeColoring k, d.Extends c ∧
      (∀ e i, d.color e = some i → i ∈ L e) ∧
      ∀ e ∈ F, ∃ i, d.color e = some i := by
  induction F using Finset.induction_on with
  | empty => exact ⟨c, fun _ _ h => h, hc, by simp⟩
  | @insert e F _ ih =>
    obtain ⟨d, hdc, hdL, hF⟩ := ih
    cases hde : d.color e with
    | some i =>
      refine ⟨d, hdc, hdL, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨i, hde⟩
      · exact hF f hf
    | none =>
      have hce : c.color e = none := by
        cases h : c.color e with
        | none => rfl
        | some i => have := hdc e i h; rw [hde] at this; cases this
      have hused : (d.usedColors (G.conflictingEdges e)).card < (L e).card :=
        (d.usedColors_card_le _).trans_lt (hbound e hce)
      obtain ⟨i, hiL, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
      let d' := d.assign e i hi
      have hd'd : d'.Extends d := d.assign_extends e i hde hi
      refine ⟨d', fun f j hf => hd'd f j (hdc f j hf), ?_, ?_⟩
      · intro f j hf
        by_cases hfe : f = e
        · subst f
          have hij : i = j := by simpa [d', assign] using hf
          exact hij ▸ hiL
        · exact hdL f j (by simpa [d', assign, hfe] using hf)
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact ⟨i, by simp [d', assign]⟩
        · obtain ⟨j, hj⟩ := hF f hf
          exact ⟨j, hd'd f j hj⟩

/-- Extend a proper partial coloring from its prescribed lists, preserving
all assigned colors, when every uncolored edge has enough allowed colors. -/
theorem exists_edgeColoring_extending_from_lists (c : G.PartialEdgeColoring k)
    (L : E → Finset (Fin k))
    (hc : ∀ e i, c.color e = some i → i ∈ L e)
    (hbound : ∀ e, c.color e = none → (G.conflictingEdges e).card < (L e).card) :
    ∃ d : G.EdgeColoring k, (∀ e, d.color e ∈ L e) ∧
      ∀ e i, c.color e = some i → d.color e = i := by
  obtain ⟨d, hdc, hdL, hall⟩ := c.extend_over_finset_from_lists L hc hbound Finset.univ
  choose f hf using (fun e => hall e (Finset.mem_univ e))
  refine ⟨⟨f, ?_⟩, ?_, ?_⟩
  · intro e e' v hee' hev he'v
    exact d.proper (hf e) (hee' ▸ hf e') hev he'v
  · intro e
    exact hdL e (f e) (hf e)
  · intro e i he
    exact Option.some.inj ((hf e).symm.trans (hdc e i he))

end PartialEdgeColoring

/-- A list with more colors than conflicting edge copies permits a proper
coloring of every actual edge. -/
theorem exists_edgeColoring_from_lists (L : E → Finset (Fin k))
    (hbound : ∀ e, (G.conflictingEdges e).card < (L e).card) :
    ∃ c : G.EdgeColoring k, ∀ e, c.color e ∈ L e := by
  let empty : G.PartialEdgeColoring k := ⟨fun _ => none, by simp⟩
  obtain ⟨c, hc, _⟩ := empty.exists_edgeColoring_extending_from_lists L
    (by simp [empty]) (by intro e _; exact hbound e)
  exact ⟨c, hc⟩

/-- Greedily color using a fixed available palette while avoiding at most
`b` forbidden labels per edge. No simplicity hypothesis is needed. -/
theorem exists_edgeColoring_avoiding (S : Finset (Fin k))
    (B : E → Finset (Fin k)) (b d : ℕ)
    (hB : ∀ e, (B e).card ≤ b) (hdegree : ∀ v, G.degree v ≤ d)
    (hslack : b + 2 * d < S.card) :
    ∃ c : G.EdgeColoring k, ∀ e, c.color e ∈ S ∧ c.color e ∉ B e := by
  obtain ⟨c, hc⟩ := G.exists_edgeColoring_from_lists (fun e => S \ B e) (by
    intro e
    change (G.conflictingEdges e).card < (S \ B e).card
    have hconf := G.conflictingEdges_card_add_two_le e
    have hu := hdegree (G.firstEnd e)
    have hv := hdegree (G.secondEnd e)
    have hcard := Finset.card_sdiff_add_card_inter S (B e)
    have hinter := Finset.card_le_card (Finset.inter_subset_right : S ∩ B e ⊆ B e)
    have hb := hB e
    omega)
  exact ⟨c, fun e => Finset.mem_sdiff.mp (hc e)⟩

end Overfull.Multigraph
