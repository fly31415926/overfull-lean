import Overfull.Konig

/-!
# Greedy coloring of actual multigraph edge copies

A partial coloring may be extended whenever every uncolored edge has fewer
than `k` conflicting edge copies. In particular, coloring an exceptional
vertex's entire star first proves the one-high-degree criterion.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- A proper partial coloring; `none` means that an edge is uncolored. -/
structure PartialEdgeColoring (k : ℕ) where
  color : E → Option (Fin k)
  proper : ∀ {e f : E} {v : V} {i : Fin k}, color e = some i → color f = some i →
    v ∈ G.edge e → v ∈ G.edge f → e = f

variable [Fintype E]

/-- Other edge copies meeting at least one endpoint of the given edge. -/
noncomputable def conflictingEdges (e : E) : Finset E :=
  (G.incidenceEdges (G.firstEnd e)).erase e ∪
    (G.incidenceEdges (G.secondEnd e)).erase e

theorem mem_conflictingEdges (e f : E) :
    f ∈ G.conflictingEdges e ↔
      f ≠ e ∧ ∃ v : V, v ∈ G.edge e ∧ v ∈ G.edge f := by
  simp only [conflictingEdges, Finset.mem_union, Finset.mem_erase, G.mem_incidenceEdges]
  constructor
  · rintro (⟨hne, hv⟩ | ⟨hne, hv⟩)
    · exact ⟨hne, G.firstEnd e, (G.incident_iff _ _).mpr (Or.inl rfl), hv⟩
    · exact ⟨hne, G.secondEnd e, (G.incident_iff _ _).mpr (Or.inr rfl), hv⟩
  · rintro ⟨hne, v, hve, hvf⟩
    rcases (G.incident_iff e v).mp hve with h | h
    · exact Or.inl ⟨hne, h ▸ hvf⟩
    · exact Or.inr ⟨hne, h ▸ hvf⟩

theorem conflictingEdges_card_add_two_le (e : E) :
    (G.conflictingEdges e).card + 2 ≤
      G.degree (G.firstEnd e) + G.degree (G.secondEnd e) := by
  have hu : e ∈ G.incidenceEdges (G.firstEnd e) := by
    rw [G.mem_incidenceEdges, G.incident_iff]
    exact Or.inl rfl
  have hv : e ∈ G.incidenceEdges (G.secondEnd e) := by
    rw [G.mem_incidenceEdges, G.incident_iff]
    exact Or.inr rfl
  have h₁ := Finset.card_erase_add_one hu
  have h₂ := Finset.card_erase_add_one hv
  have h := Finset.card_union_le
    ((G.incidenceEdges (G.firstEnd e)).erase e)
    ((G.incidenceEdges (G.secondEnd e)).erase e)
  change (G.conflictingEdges e).card ≤ _ at h
  change _ = G.degree (G.firstEnd e) at h₁
  change _ = G.degree (G.secondEnd e) at h₂
  omega

namespace PartialEdgeColoring

variable {G} {k : ℕ}

/-- A refinement preserves every color already assigned. -/
def Extends (c d : G.PartialEdgeColoring k) : Prop :=
  ∀ e i, d.color e = some i → c.color e = some i

noncomputable def usedColors (c : G.PartialEdgeColoring k) (F : Finset E) : Finset (Fin k) :=
  F.biUnion (fun e => (c.color e).toFinset)

omit [Fintype E] in
theorem mem_usedColors (c : G.PartialEdgeColoring k) (F : Finset E) (i : Fin k) :
    i ∈ c.usedColors F ↔ ∃ e ∈ F, c.color e = some i := by
  simp [usedColors]

omit [Fintype E] in
theorem usedColors_card_le (c : G.PartialEdgeColoring k) (F : Finset E) :
    (c.usedColors F).card ≤ F.card := by
  have h := Finset.card_biUnion_le_card_mul F (fun e => (c.color e).toFinset) 1
    (by intro e _; cases h : c.color e <;> simp [h])
  simpa [usedColors] using h

/-- Assign a color unused on every conflicting edge. -/
noncomputable def assign (c : G.PartialEdgeColoring k) (e : E) (i : Fin k)
    (hi : i ∉ c.usedColors (G.conflictingEdges e)) :
    G.PartialEdgeColoring k where
  color f := if f = e then some i else c.color f
  proper := by
    intro a b v j ha hb hva hvb
    by_cases hae : a = e
    · subst a
      by_cases hbe : b = e
      · exact hbe.symm
      · have hij : i = j := by simpa using ha
        have hb' : c.color b = some i := by simpa [hbe, ← hij] using hb
        have hconf : b ∈ G.conflictingEdges e :=
          (G.mem_conflictingEdges e b).mpr ⟨hbe, v, hva, hvb⟩
        exact (hi ((c.mem_usedColors _ _).mpr ⟨b, hconf, hb'⟩)).elim
    · by_cases hbe : b = e
      · subst b
        have hij : i = j := by simpa using hb
        have ha' : c.color a = some i := by simpa [hae, ← hij] using ha
        have hconf : a ∈ G.conflictingEdges e :=
          (G.mem_conflictingEdges e a).mpr ⟨hae, v, hvb, hva⟩
        exact (hi ((c.mem_usedColors _ _).mpr ⟨a, hconf, ha'⟩)).elim
      · exact c.proper (by simpa [hae] using ha) (by simpa [hbe] using hb) hva hvb

theorem assign_extends (c : G.PartialEdgeColoring k) (e : E) (i : Fin k)
    (he : c.color e = none) (hi : i ∉ c.usedColors (G.conflictingEdges e)) :
    (c.assign e i hi).Extends c := by
  intro f j hf
  have hfe : f ≠ e := by intro h; subst f; rw [he] at hf; cases hf
  simpa [assign, hfe] using hf

private theorem extend_over_finset (c : G.PartialEdgeColoring k)
    (hbound : ∀ e, c.color e = none → (G.conflictingEdges e).card < k)
    (F : Finset E) :
    ∃ d : G.PartialEdgeColoring k, d.Extends c ∧ ∀ e ∈ F, ∃ i, d.color e = some i := by
  induction F using Finset.induction_on with
  | empty => exact ⟨c, fun _ _ h => h, by simp⟩
  | @insert e F _ ih =>
    obtain ⟨d, hdc, hF⟩ := ih
    cases hde : d.color e with
    | some i =>
      refine ⟨d, hdc, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨i, hde⟩
      · exact hF f hf
    | none =>
      have hce : c.color e = none := by
        cases h : c.color e with
        | none => rfl
        | some i => have := hdc e i h; rw [hde] at this; cases this
      have hused : (d.usedColors (G.conflictingEdges e)).card < (Finset.univ : Finset (Fin k)).card := by
        simpa using (d.usedColors_card_le _).trans_lt (hbound e hce)
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
      let d' := d.assign e i hi
      have hd'd : d'.Extends d := d.assign_extends e i hde hi
      refine ⟨d', fun f j hf => hd'd f j (hdc f j hf), ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨i, by simp [d', assign]⟩
      · obtain ⟨j, hj⟩ := hF f hf
        exact ⟨j, hd'd f j hj⟩

/-- Complete a partial coloring while preserving all colors already assigned. -/
theorem exists_edgeColoring_extending (c : G.PartialEdgeColoring k)
    (hbound : ∀ e, c.color e = none → (G.conflictingEdges e).card < k) :
    ∃ d : G.EdgeColoring k, ∀ e i, c.color e = some i → d.color e = i := by
  obtain ⟨d, hdc, hall⟩ := c.extend_over_finset hbound Finset.univ
  choose f hf using (fun e => hall e (Finset.mem_univ e))
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro e e' v hee' hev he'v
    exact d.proper (hf e) (hee' ▸ hf e') hev he'v
  · intro e i he
    exact Option.some.inj ((hf e).symm.trans (hdc e i he))

/-- Distinct colors on an arbitrary selected set give a proper partial coloring. -/
noncomputable def ofEmbedding (S : Finset E) (f : S ↪ Fin k) : G.PartialEdgeColoring k where
  color e := if he : e ∈ S then some (f ⟨e, he⟩) else none
  proper := by
    intro e e' _ i he he' _ _
    by_cases heS : e ∈ S
    · by_cases he'S : e' ∈ S
      · have hc : f ⟨e, heS⟩ = f ⟨e', he'S⟩ := by
          simpa only [dif_pos heS, dif_pos he'S, Option.some.injEq] using he.trans he'.symm
        exact congrArg Subtype.val (f.injective hc)
      · simp [he'S] at he'
    · simp [heS] at he

end PartialEdgeColoring

/-- Lemma 2.11: all but one vertex have degree at most `s`, and `k > 2s`.
The low-degree bound may be real; the number of colors is integral. -/
theorem edgeColoring_one_high (k : ℕ) (s : ℝ) (x : V)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hlow : ∀ v, v ≠ x → (G.degree v : ℝ) ≤ s)
    (hks : 2 * s < k) : Nonempty (G.EdgeColoring k) := by
  obtain ⟨f⟩ : Nonempty ((G.incidenceEdges x) ↪ Fin k) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact hdegree x)
  let c := PartialEdgeColoring.ofEmbedding (G := G) (G.incidenceEdges x) f
  obtain ⟨d, _⟩ := c.exists_edgeColoring_extending (by
    intro e he
    have heX : x ∉ G.edge e := by
      intro h
      have heS : e ∈ G.incidenceEdges x := (G.mem_incidenceEdges x e).mpr h
      have hc : c.color e = some (f ⟨e, heS⟩) := by
        simp only [c, PartialEdgeColoring.ofEmbedding, dif_pos heS]
      rw [hc] at he
      cases he
    have hu : G.firstEnd e ≠ x := by
      intro h
      exact heX ((G.incident_iff e x).mpr (Or.inl h))
    have hv : G.secondEnd e ≠ x := by
      intro h
      exact heX ((G.incident_iff e x).mpr (Or.inr h))
    have hc : ((G.conflictingEdges e).card : ℝ) + 2 ≤
        G.degree (G.firstEnd e) + G.degree (G.secondEnd e) := by
      exact_mod_cast G.conflictingEdges_card_add_two_le e
    have hlt : ((G.conflictingEdges e).card : ℝ) < k := by
      linarith [hlow (G.firstEnd e) hu, hlow (G.secondEnd e) hv]
    exact_mod_cast hlt)
  exact ⟨d⟩

end Overfull.Multigraph
