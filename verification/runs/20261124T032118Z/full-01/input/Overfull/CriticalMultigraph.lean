import Overfull.SparseColoring
import Overfull.ColorCoverage

/-!
# Minimal noncolorable multigraphs

Edge deletion removes a specified copy. Degrees, missing colors and all
coloring constructions retain parallel edge copies.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- Delete precisely one edge copy, keeping the vertex type. -/
def deleteEdge (e : E) : Multigraph V {f : E // f ≠ e} where
  edge f := G.edge f.val
  loopless f := G.loopless f.val

variable [Fintype E]

/-- The other end of an edge incident with `x`. The definition is total;
its endpoint assertions are used only under incidence at `x`. -/
noncomputable def otherEnd (x : V) (e : E) : V :=
  if G.firstEnd e = x then G.secondEnd e else G.firstEnd e

omit [Fintype E] in
theorem edge_eq_otherEnd (x : V) (e : E) (hx : x ∈ G.edge e) :
    G.edge e = s(x,G.otherEnd x e) := by
  rcases (G.incident_iff e x).mp hx with h | h
  · unfold otherEnd
    rw [if_pos h, ← h]
    exact (G.edge_eq e).symm
  · have hne : G.firstEnd e ≠ x := by
      intro hh
      exact G.endpoints_distinct e (hh.trans h.symm)
    unfold otherEnd
    rw [if_neg hne, ← h]
    exact (G.edge_eq e).symm.trans Sym2.eq_swap

omit [Fintype E] in
theorem otherEnd_ne (x : V) (e : E) (hx : x ∈ G.edge e) :
    G.otherEnd x e ≠ x := by
  intro hh
  exact G.loopless e (by rw [G.edge_eq_otherEnd x e hx,hh]; simp)

/-- Edge copies from `x` to the indicated vertex set. -/
noncomputable def edgesTo (x : V) (X : Finset V) : Finset E :=
  (G.incidenceEdges x).filter (fun e => G.otherEnd x e ∈ X)

/-- The parallel copies with endpoints `x,v`. -/
noncomputable def parallelEdges (x v : V) : Finset E := G.edgesTo x {v}

@[simp] theorem mem_edgesTo (x : V) (X : Finset V) (e : E) :
    e ∈ G.edgesTo x X ↔ x ∈ G.edge e ∧ G.otherEnd x e ∈ X := by
  simp [edgesTo]

@[simp] theorem mem_parallelEdges (x v : V) (e : E) :
    e ∈ G.parallelEdges x v ↔ x ∈ G.edge e ∧ G.otherEnd x e = v := by
  simp [parallelEdges]

theorem parallelEdges_card_le_degree (x v : V) :
    (G.parallelEdges x v).card ≤ G.degree v := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨hx,hv⟩ := (G.mem_parallelEdges x v e).mp he
  rw [G.mem_incidenceEdges, G.edge_eq_otherEnd x e hx, hv]
  simp

omit [Fintype E] in
theorem otherEnd_eq_of_edge (e : E) (x v : V) (he : G.edge e = s(x,v)) :
    G.otherEnd x e = v := by
  have hx : x ∈ G.edge e := by simp [he]
  have heq := (G.edge_eq_otherEnd x e hx).symm.trans he
  rcases Sym2.eq_iff.mp heq with ⟨_,h⟩ | ⟨h₁,h₂⟩
  · exact h
  · exact h₂.trans h₁

theorem edgesTo_compl_card_add [Fintype V] (x : V) (X : Finset V) :
    (G.edgesTo x Xᶜ).card + (G.edgesTo x X).card = G.degree x := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.incidenceEdges x) (fun e => G.otherEnd x e ∈ X)
  simpa only [edgesTo, Finset.mem_compl, Nat.add_comm, degree] using h

theorem restrictEdges_degree_mono {F H : Finset E} (hFH : F ⊆ H) (v : V) :
    (G.restrictEdges F).degree v ≤ (G.restrictEdges H).degree v := by
  rw [G.restrictEdges_degree, G.restrictEdges_degree]
  exact Finset.card_le_card (Finset.inter_subset_inter_right hFH)

theorem restrictEdges_degree_le (F : Finset E) (v : V) :
    (G.restrictEdges F).degree v ≤ G.degree v := by
  rw [G.restrictEdges_degree]
  exact Finset.card_le_card Finset.inter_subset_right

theorem restrictEdges_edgesTo_card (F : Finset E) (x : V) (X : Finset V) :
    ((G.restrictEdges F).edgesTo x X).card = (F ∩ G.edgesTo x X).card := by
  have heq : ((G.restrictEdges F).edgesTo x X).image Subtype.val =
      F ∩ G.edgesTo x X := by
    ext e
    simp only [Finset.mem_image, mem_edgesTo, Finset.mem_inter]
    change (∃ f : F, (x ∈ G.edge f.val ∧ G.otherEnd x f.val ∈ X) ∧ f.val = e) ↔
      e ∈ F ∧ (x ∈ G.edge e ∧ G.otherEnd x e ∈ X)
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f.property,hf⟩
    · rintro ⟨he,hx⟩
      exact ⟨⟨e,he⟩,hx,rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, heq]

theorem restrictEdges_edgesTo_card_le (F : Finset E) (x : V) (X : Finset V) :
    ((G.restrictEdges F).edgesTo x X).card ≤ (G.edgesTo x X).card := by
  rw [G.restrictEdges_edgesTo_card]
  exact Finset.card_le_card Finset.inter_subset_right

theorem deleteEdge_degree (e : E) (v : V) :
    (G.deleteEdge e).degree v = ((G.incidenceEdges v).erase e).card := by
  have himage : ((G.deleteEdge e).incidenceEdges v).image Subtype.val =
      (G.incidenceEdges v).erase e := by
    ext f
    simp only [Finset.mem_image, mem_incidenceEdges, deleteEdge, Finset.mem_erase]
    constructor
    · rintro ⟨a, hv, rfl⟩
      exact ⟨a.property, hv⟩
    · rintro ⟨hf, hv⟩
      exact ⟨⟨f, hf⟩, hv, rfl⟩
  rw [degree, ← Finset.card_image_of_injective _ Subtype.val_injective, himage]

theorem deleteEdge_degree_add (e : E) (v : V) :
    (G.deleteEdge e).degree v + (if v ∈ G.edge e then 1 else 0) = G.degree v := by
  rw [G.deleteEdge_degree]
  by_cases hv : v ∈ G.edge e
  · rw [if_pos hv]
    exact Finset.card_erase_add_one ((G.mem_incidenceEdges v e).mpr hv)
  · rw [if_neg hv, Finset.erase_eq_of_notMem ((G.mem_incidenceEdges v e).not.mpr hv)]
    exact Nat.add_zero _

/-- The manuscript's `k`-minimality, formulated for actual edge copies. -/
def IsKMinimal (k : ℕ) : Prop :=
  (∀ v, G.degree v ≤ k) ∧ ¬ Nonempty (G.EdgeColoring k) ∧
    ∀ e, Nonempty ((G.deleteEdge e).EdgeColoring k)

namespace EdgeColoring

variable {G} {k : ℕ}

/-- Restrict a coloring to a smaller set of actual edge copies. -/
def restrictEdgesSubset {F H : Finset E} (c : (G.restrictEdges H).EdgeColoring k)
    (hFH : F ⊆ H) : (G.restrictEdges F).EdgeColoring k where
  color e := c.color ⟨e.val,hFH e.property⟩
  proper := by
    intro e f v hef hev hfv
    exact Subtype.ext (congrArg (fun a : H => a.val) (c.proper hef hev hfv))

noncomputable def missingColors (c : G.EdgeColoring k) (v : V) : Finset (Fin k) :=
  univ.filter (fun i => ¬ c.Covers i v)

omit [Fintype E] in
@[simp] theorem mem_missingColors (c : G.EdgeColoring k) (v : V) (i : Fin k) :
    i ∈ c.missingColors v ↔ ¬ c.Covers i v := by simp [missingColors]

theorem missingColors_card_add_degree (c : G.EdgeColoring k) (v : V) :
    (c.missingColors v).card + G.degree v = k := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin k))) (fun i => c.Covers i v)
  rw [c.coveredColors_card] at h
  simpa only [missingColors, Finset.card_univ, Fintype.card_fin, Nat.add_comm] using h

/-- A common missing color restores the deleted edge. -/
noncomputable def restoreMissing (e : E) (x v : V) (he : G.edge e = s(x,v))
    (c : (G.deleteEdge e).EdgeColoring k) (i : Fin k)
    (hx : ¬ c.Covers i x) (hv : ¬ c.Covers i v) : G.EdgeColoring k where
  color f := if hf : f = e then i else c.color ⟨f, hf⟩
  proper := by
    intro a b w hab hwa hwb
    have havoid (f : {f : E // f ≠ e}) (hw : w ∈ G.edge e)
        (hwf : w ∈ G.edge f.val) : c.color f ≠ i := by
      intro hf
      have hwi : w = x ∨ w = v := by simpa only [he, Sym2.mem_iff] using hw
      rcases hwi with rfl | rfl
      · exact hx ⟨f, hf, hwf⟩
      · exact hv ⟨f, hf, hwf⟩
    by_cases ha : a = e
    · subst a
      by_cases hb : b = e
      · exact hb.symm
      · have hbi : c.color ⟨b, hb⟩ = i := by simpa only [dif_pos rfl, dif_neg hb] using hab.symm
        exact (havoid ⟨b, hb⟩ hwa hwb hbi).elim
    · by_cases hb : b = e
      · subst b
        have hai : c.color ⟨a, ha⟩ = i := by simpa only [dif_neg ha, dif_pos rfl] using hab
        exact (havoid ⟨a, ha⟩ hwb hwa hai).elim
      · exact congrArg Subtype.val (c.proper
          (by simpa only [dif_neg ha, dif_neg hb] using hab) hwa hwb)

end EdgeColoring

/-- A noncolorable edge restriction contains a `k`-minimal restriction.
The chosen graph consists of actual original edge copies. -/
theorem exists_kMinimal_subset (k : ℕ) (hdegree : ∀ v, G.degree v ≤ k)
    (H : Finset E) (hH : ¬ Nonempty ((G.restrictEdges H).EdgeColoring k)) :
    ∃ F : Finset E, F ⊆ H ∧ (G.restrictEdges F).IsKMinimal k := by
  classical
  let P : ℕ → Prop := fun n => ∃ F : Finset E, F ⊆ H ∧ F.card = n ∧
    ¬ Nonempty ((G.restrictEdges F).EdgeColoring k)
  have hP : ∃ n, P n := ⟨H.card,H,Finset.Subset.refl _,rfl,hH⟩
  obtain ⟨F,hFH,hFn,hF⟩ := Nat.find_spec hP
  refine ⟨F,hFH,fun v => (G.restrictEdges_degree_le F v).trans (hdegree v),hF,?_⟩
  intro e
  have hcol : Nonempty ((G.restrictEdges (F.erase e.val)).EdgeColoring k) := by
    by_contra hn
    have hmin := Nat.find_min' hP
      (show P (F.erase e.val).card from ⟨F.erase e.val,
        (Finset.erase_subset e.val F).trans hFH,rfl,hn⟩)
    have hcard := Finset.card_erase_add_one e.property
    omega
  obtain ⟨c⟩ := hcol
  let f : {a : F // a ≠ e} → F.erase e.val := fun a =>
    ⟨a.val.val, Finset.mem_erase.mpr ⟨fun hh => a.property (Subtype.ext hh),a.val.property⟩⟩
  refine ⟨⟨fun a => c.color (f a), ?_⟩⟩
  intro a b v hab hva hvb
  have hh := c.proper hab hva hvb
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : F.erase e.val => a.val) hh

namespace IsKMinimal

variable {G} {k : ℕ} (hG : G.IsKMinimal k)

include hG

theorem missing_disjoint (e : E) (x v : V) (he : G.edge e = s(x,v))
    (c : (G.deleteEdge e).EdgeColoring k) :
    Disjoint (c.missingColors x) (c.missingColors v) := by
  apply Finset.disjoint_left.mpr
  intro i hx hv
  exact hG.2.1 ⟨c.restoreMissing e x v he i
    ((c.mem_missingColors x i).mp hx) ((c.mem_missingColors v i).mp hv)⟩

theorem endpoint_degree_sum (e : E) (x v : V) (he : G.edge e = s(x,v)) :
    k + 2 ≤ G.degree x + G.degree v := by
  obtain ⟨c⟩ := hG.2.2 e
  have hdisj := hG.missing_disjoint e x v he c
  have hcard := Finset.card_le_univ (c.missingColors x ∪ c.missingColors v)
  rw [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at hcard
  have hx := c.missingColors_card_add_degree x
  have hv := c.missingColors_card_add_degree v
  have hdx := G.deleteEdge_degree_add e x
  have hdv := G.deleteEdge_degree_add e v
  simp only [he, Sym2.mem_iff, true_or, or_true, if_true] at hdx hdv
  omega

theorem missing_at_endpoint (e : E) (x : V) (hx : x ∈ G.edge e)
    (c : (G.deleteEdge e).EdgeColoring k) :
    ∃ i : Fin k, ¬ c.Covers i x := by
  have hd := G.deleteEdge_degree_add e x
  rw [if_pos hx] at hd
  have hc := c.missingColors_card_add_degree x
  have hbound := hG.1 x
  have hpos : 0 < (c.missingColors x).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (c.mem_missingColors x i).mp hi⟩

end IsKMinimal

end Overfull.Multigraph
