import Overfull.MultigraphGreedy
import Overfull.MultigraphColoring
import Overfull.HallDefect

/-!
# Coloring a multigraph with a sparse vertex deletion

The edge type records every parallel copy. The two-star subgraph is colored
by König's theorem; its color classes are then assigned distinct available
colors after coloring the graph outside the two centres.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E : Type*} (G : Multigraph V E) [Fintype E]

/-- Retain precisely the selected actual edge copies. -/
def restrictEdges (F : Finset E) : Multigraph V F where
  edge e := G.edge e.val
  loopless e := G.loopless e.val

theorem restrictEdges_degree (F : Finset E) (v : V) :
    (G.restrictEdges F).degree v = (F ∩ G.incidenceEdges v).card := by
  have himage : ((G.restrictEdges F).incidenceEdges v).image Subtype.val =
      F ∩ G.incidenceEdges v := by
    ext e
    simp only [Finset.mem_image, mem_incidenceEdges, restrictEdges, Finset.mem_inter]
    constructor
    · rintro ⟨f, hv, rfl⟩
      exact ⟨f.property, hv⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, hv, rfl⟩
  rw [degree, ← Finset.card_image_of_injective _ Subtype.val_injective, himage]

/-- Degree after deleting the edges at `z`; `z` is retained as an isolated
vertex, and the other degrees are those of the vertex-deleted graph. -/
noncomputable def degreeAway (z v : V) : ℕ :=
  ((G.incidenceEdges v) \ (G.incidenceEdges z)).card

theorem degreeAway_add_parallel (z v : V) :
    G.degreeAway z v + (G.incidenceEdges z ∩ G.incidenceEdges v).card = G.degree v := by
  simpa only [degreeAway, degree, Finset.inter_comm] using
    Finset.card_sdiff_add_card_inter (G.incidenceEdges v) (G.incidenceEdges z)

theorem degreeAway_eq_remaining_degree (z v : V) :
    G.degreeAway z v =
      (MultigraphMatchingProbability.remainingGraph G (G.incidenceEdges z)).degree v := by
  have h := MultigraphMatchingProbability.remaining_degree_add_selected
    (G := G) (G.incidenceEdges z) v
  have hf : (G.incidenceEdges z).filter (fun e => v ∈ G.edge e) =
      G.incidenceEdges z ∩ G.incidenceEdges v := by ext e; simp
  rw [hf] at h
  have h' := G.degreeAway_add_parallel z v
  omega

/-- Delete a vertex and every incident edge copy. Both the vertex type and
the edge type are restricted, so this is the actual vertex-deleted graph. -/
noncomputable def deleteVertex (z : V) : Multigraph {u : V // u ≠ z} {e : E // z ∉ G.edge e} where
  edge e := s(⟨G.firstEnd e.val, fun h => e.property
    ((G.incident_iff _ _).mpr (Or.inl h))⟩,
    ⟨G.secondEnd e.val, fun h => e.property
    ((G.incident_iff _ _).mpr (Or.inr h))⟩)
  loopless e := by
    simp only [Sym2.mk_isDiag_iff]
    intro h
    exact G.endpoints_distinct e.val (congrArg Subtype.val h)

omit [Fintype E] in
@[simp] theorem deleteVertex_incident (z : V) (u : {u : V // u ≠ z})
    (e : {e : E // z ∉ G.edge e}) :
    u ∈ (G.deleteVertex z).edge e ↔ u.val ∈ G.edge e.val := by
  simp only [deleteVertex, Sym2.mem_iff, Subtype.ext_iff, G.incident_iff]
  exact or_congr eq_comm eq_comm

theorem deleteVertex_degree (z : V) (u : {u : V // u ≠ z}) :
    (G.deleteVertex z).degree u = G.degreeAway z u.val := by
  have himage : ((G.deleteVertex z).incidenceEdges u).image Subtype.val =
      G.incidenceEdges u.val \ G.incidenceEdges z := by
    ext e
    simp only [Finset.mem_image, mem_incidenceEdges, deleteVertex_incident,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨f, hv, rfl⟩
      exact ⟨hv, f.property⟩
    · rintro ⟨hv, he⟩
      exact ⟨⟨e, he⟩, hv, rfl⟩
  rw [degree, ← Finset.card_image_of_injective _ Subtype.val_injective, himage]
  rfl

omit [Fintype E] in
private theorem incident_three_eq (e : E) {x y z : V}
    (hx : x ∈ G.edge e) (hy : y ∈ G.edge e) (hz : z ∈ G.edge e) :
    x = y ∨ x = z ∨ y = z := by
  rw [G.incident_iff] at hx hy hz
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> aesop

omit [Fintype E] in
private theorem incident_two_endpoints (e : E) {x y : V}
    (hxy : x ≠ y) (hx : x ∈ G.edge e) (hy : y ∈ G.edge e) :
    (G.firstEnd e = x ∧ G.secondEnd e = y) ∨
      (G.firstEnd e = y ∧ G.secondEnd e = x) := by
  rw [G.incident_iff] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> aesop

private theorem exists_injective_available {I : Type*} [Fintype I]
    (k : ℕ) (A : I → Finset (Fin k))
    (hA : ∀ i, Fintype.card I ≤ (A i).card) :
    ∃ f : I ↪ Fin k, ∀ i, f i ∈ A i := by
  have hHall : ∀ S : Finset I, S.card ≤ (S.biUnion A).card := by
    intro S
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi⟩ := hS
      exact (Finset.card_le_univ S).trans ((hA i).trans
        (Finset.card_le_card (Finset.subset_biUnion_of_mem A hi)))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp hHall
  exact ⟨⟨f, hf⟩, hmem⟩

private theorem coloring_of_degree_bound (k q : ℕ)
    (hdegree : ∀ v, G.degree v ≤ q) (hqk : 2 * q < k) :
    Nonempty (G.EdgeColoring k) := by
  let c : G.PartialEdgeColoring k := ⟨fun _ => none, by simp⟩
  obtain ⟨d, _⟩ := c.exists_edgeColoring_extending (by
    intro e _
    have := G.conflictingEdges_card_add_two_le e
    have h₁ := hdegree (G.firstEnd e)
    have h₂ := hdegree (G.secondEnd e)
    omega)
  exact ⟨d⟩

namespace SparseColoring

noncomputable def central (z v : V) : Finset E :=
  G.incidenceEdges z ∩ G.incidenceEdges v

noncomputable def spokes (z v : V) : Finset E :=
  (G.incidenceEdges z ∪ G.incidenceEdges v) \ central G z v

noncomputable def core (z v : V) : Finset E :=
  Finset.univ \ (G.incidenceEdges z ∪ G.incidenceEdges v)

@[simp] theorem mem_central (z v : V) (e : E) :
    e ∈ central G z v ↔ z ∈ G.edge e ∧ v ∈ G.edge e := by
  simp [central]

@[simp] theorem mem_spokes (z v : V) (e : E) :
    e ∈ spokes G z v ↔
      (z ∈ G.edge e ∨ v ∈ G.edge e) ∧ ¬ (z ∈ G.edge e ∧ v ∈ G.edge e) := by
  simp [spokes]

@[simp] theorem mem_core (z v : V) (e : E) :
    e ∈ core G z v ↔ z ∉ G.edge e ∧ v ∉ G.edge e := by
  simp [core]

theorem core_of_not_central_not_spokes (z v : V) {e : E}
    (hc : e ∉ central G z v) (hs : e ∉ spokes G z v) : e ∈ core G z v := by
  simp only [mem_central, mem_spokes, mem_core] at *
  tauto

theorem spokes_bipartite (z v : V) (hzv : z ≠ v) :
    (G.restrictEdges (spokes G z v)).IsBipartite := by
  refine ⟨fun u => decide (u = z ∨ u = v), ?_⟩
  intro e
  change decide (G.firstEnd e.val = z ∨ G.firstEnd e.val = v) ≠
    decide (G.secondEnd e.val = z ∨ G.secondEnd e.val = v)
  have he := (mem_spokes G z v e.val).mp e.property
  simp only [G.incident_iff] at he
  have hne := G.endpoints_distinct e.val
  simp only [ne_eq, decide_eq_decide]
  aesop

theorem central_spokes_disjoint (z v : V) :
    Disjoint (central G z v) (spokes G z v) := by
  apply Finset.disjoint_left.mpr
  intro e hc hs
  exact (Finset.mem_sdiff.mp hs).2 hc

theorem central_subset_star (z v : V) : central G z v ⊆ G.incidenceEdges z :=
  Finset.inter_subset_left

theorem spokes_degree_centres_le (z v : V) (k : ℕ)
    (hdegree : ∀ u, G.degree u ≤ k) :
    ∀ u, u = z ∨ u = v →
      (G.restrictEdges (spokes G z v)).degree u ≤ k - (central G z v).card := by
  intro u hu
  have hsub : central G z v ∪ (spokes G z v ∩ G.incidenceEdges u) ⊆
      G.incidenceEdges u := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have hc := (mem_central G z v e).mp he
      rw [G.mem_incidenceEdges]
      rcases hu with rfl | rfl
      · exact hc.1
      · exact hc.2
    · exact (Finset.mem_inter.mp he).2
  have hdis : Disjoint (central G z v) (spokes G z v ∩ G.incidenceEdges u) :=
    (central_spokes_disjoint G z v).mono_right Finset.inter_subset_left
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hcount
  rw [restrictEdges_degree]
  have hd := hdegree u
  change (G.incidenceEdges u).card ≤ k at hd
  omega

theorem spokes_degree_outside_le (z v : V) (hzv : z ≠ v) (k : ℕ)
    (htriple : ∀ u, u ≠ z → u ≠ v → (G.internalEdges {z, v, u}).card ≤ k) :
    ∀ u, u ≠ z → u ≠ v →
      (G.restrictEdges (spokes G z v)).degree u ≤ k - (central G z v).card := by
  intro u huz huv
  have hsub : central G z v ∪ (spokes G z v ∩ G.incidenceEdges u) ⊆
      G.internalEdges {z, v, u} := by
    intro e he
    rw [G.mem_internalEdges]
    rcases Finset.mem_union.mp he with hc | hs
    · have h := (mem_central G z v e).mp hc
      rcases incident_two_endpoints G e hzv h.1 h.2 with h | h <;> simp [h.1, h.2]
    · have hsu := (Finset.mem_inter.mp hs).2
      rw [G.mem_incidenceEdges] at hsu
      have hs' := ((mem_spokes G z v e).mp (Finset.mem_inter.mp hs).1).1
      rcases hs' with hs' | hs'
      · rcases incident_two_endpoints G e huz.symm hs' hsu with h | h <;>
          simp [h.1, h.2]
      · rcases incident_two_endpoints G e huv.symm hs' hsu with h | h <;>
          simp [h.1, h.2]
  have hdis : Disjoint (central G z v) (spokes G z v ∩ G.incidenceEdges u) :=
    (central_spokes_disjoint G z v).mono_right Finset.inter_subset_left
  have hcount := (Finset.card_le_card hsub).trans (htriple u huz huv)
  rw [Finset.card_union_of_disjoint hdis] at hcount
  rw [restrictEdges_degree]
  omega

theorem core_degree_le (z v : V) (q : ℕ)
    (hdegree : ∀ u, G.degreeAway z u ≤ q) :
    ∀ u, (G.restrictEdges (core G z v)).degree u ≤ q := by
  intro u
  rw [restrictEdges_degree]
  apply le_trans (Finset.card_le_card ?_) (hdegree u)
  intro e he
  have hc := (mem_core G z v e).mp (Finset.mem_inter.mp he).1
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp he).2,
    by simpa only [G.mem_incidenceEdges] using hc.1⟩

theorem core_incidence_centres_empty (z v u : V) (hu : u = z ∨ u = v) :
    (G.restrictEdges (core G z v)).incidenceEdges u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hc := (mem_core G z v e.val).mp e.property
  have he' : u ∈ G.edge e.val :=
    ((G.restrictEdges (core G z v)).mem_incidenceEdges u e).mp he
  rcases hu with rfl | rfl
  · exact hc.1 he'
  · exact hc.2 he'

noncomputable def vertexColors {k : ℕ} (c : G.EdgeColoring k) (u : V) : Finset (Fin k) :=
  (G.incidenceEdges u).image c.color

theorem vertexColors_card_le {k : ℕ} (c : G.EdgeColoring k) (u : V) :
    (vertexColors G c u).card ≤ G.degree u :=
  Finset.card_image_le

theorem color_mem_vertexColors {k : ℕ} (c : G.EdgeColoring k) {e : E} {u : V}
    (hu : u ∈ G.edge e) : c.color e ∈ vertexColors G c u := by
  exact Finset.mem_image.mpr ⟨e, (G.mem_incidenceEdges u e).mpr hu, rfl⟩

theorem core_vertexColors_centres_empty {z v u : V} {k : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k) (hu : u = z ∨ u = v) :
    vertexColors (G.restrictEdges (core G z v)) c u = ∅ := by
  simp [vertexColors, core_incidence_centres_empty G z v u hu]

noncomputable def forbiddenAt {z v : V} {k : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k) (e : E) : Finset (Fin k) :=
  vertexColors (G.restrictEdges (core G z v)) c (G.firstEnd e) ∪
    vertexColors (G.restrictEdges (core G z v)) c (G.secondEnd e)

theorem forbiddenAt_card_le {z v : V} {k q : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    (hdegree : ∀ u, G.degreeAway z u ≤ q) {e : E} (he : e ∈ spokes G z v) :
    (forbiddenAt G c e).card ≤ q := by
  have hlow := core_degree_le G z v q hdegree
  have hc (u : V) := (vertexColors_card_le _ c u).trans (hlow u)
  have he' := ((mem_spokes G z v e).mp he).1
  simp only [G.incident_iff] at he'
  rcases he' with (he' | he') | (he' | he')
  · rw [forbiddenAt, he', core_vertexColors_centres_empty G c (Or.inl rfl), Finset.empty_union]
    exact hc _
  · rw [forbiddenAt, he', core_vertexColors_centres_empty G c (Or.inl rfl), Finset.union_empty]
    exact hc _
  · rw [forbiddenAt, he', core_vertexColors_centres_empty G c (Or.inr rfl), Finset.empty_union]
    exact hc _
  · rw [forbiddenAt, he', core_vertexColors_centres_empty G c (Or.inr rfl), Finset.union_empty]
    exact hc _

theorem color_mem_forbiddenAt {z v : V} {k : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    {e : E} {f : core G z v} {u : V}
    (hue : u ∈ G.edge e) (huf : u ∈ G.edge f.val) :
    c.color f ∈ forbiddenAt G c e := by
  have hf := color_mem_vertexColors (G.restrictEdges (core G z v)) c huf
  rcases (G.incident_iff e u).mp hue with hu | hu
  · exact Finset.mem_union_left _ (hu ▸ hf)
  · exact Finset.mem_union_right _ (hu ▸ hf)

theorem spokes_colorClass_card_le_two {z v : V} {d : ℕ}
    (c : (G.restrictEdges (spokes G z v)).EdgeColoring d) (i : Fin d) :
    (c.colorClass i).card ≤ 2 := by
  have hcount : (c.colorClass i).card ≤ (Finset.univ : Finset Bool).card := by
    apply Finset.card_le_card_of_injOn (fun e => decide (z ∈ G.edge e.val))
    · intro e _
      exact Finset.mem_univ _
    · intro e he f hf hef
      have hcolor : c.color e = c.color f :=
        (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      simp only [decide_eq_decide] at hef
      by_cases hze : z ∈ G.edge e.val
      · exact c.proper hcolor hze (hef.mp hze)
      · have hzf : z ∉ G.edge f.val := fun h => hze (hef.mpr h)
        have hve := ((mem_spokes G z v e.val).mp e.property).1.resolve_left hze
        have hvf := ((mem_spokes G z v f.val).mp f.property).1.resolve_left hzf
        exact c.proper hcolor hve hvf
  simpa using hcount

noncomputable def forbiddenClass {z v : V} {k d : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    (a : (G.restrictEdges (spokes G z v)).EdgeColoring d) (i : Fin d) : Finset (Fin k) :=
  (a.colorClass i).biUnion (fun e => forbiddenAt G c e.val)

theorem forbiddenClass_card_le {z v : V} {k d q : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    (a : (G.restrictEdges (spokes G z v)).EdgeColoring d)
    (hdegree : ∀ u, G.degreeAway z u ≤ q) (i : Fin d) :
    (forbiddenClass G c a i).card ≤ 2 * q := by
  calc
    _ ≤ (a.colorClass i).card * q :=
      Finset.card_biUnion_le_card_mul _ _ q
        (fun e _ => forbiddenAt_card_le G c hdegree e.property)
    _ ≤ 2 * q := Nat.mul_le_mul_right q (spokes_colorClass_card_le_two G a i)

theorem central_core_no_common {z v : V} (hzv : z ≠ v)
    {e f : E} (he : e ∈ central G z v) (hf : f ∈ core G z v) {u : V}
    (hue : u ∈ G.edge e) (huf : u ∈ G.edge f) : False := by
  have hc := (mem_central G z v e).mp he
  have hr := (mem_core G z v f).mp hf
  have h := incident_three_eq G e hc.1 hc.2 hue
  rcases h with h | h | h
  · exact hzv h
  · exact hr.1 (h ▸ huf)
  · exact hr.2 (h ▸ huf)

theorem spoke_core_different {z v : V} {k d : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    (a : (G.restrictEdges (spokes G z v)).EdgeColoring d)
    (f : Fin d ↪ Fin k)
    (hfree : ∀ i, f i ∉ forbiddenClass G c a i)
    (e : spokes G z v) (g : core G z v) {u : V}
    (hue : u ∈ G.edge e.val) (hug : u ∈ G.edge g.val) :
    f (a.color e) ≠ c.color g := by
  intro h
  apply hfree (a.color e)
  rw [h]
  apply Finset.mem_biUnion.mpr
  exact ⟨e, by simp [EdgeColoring.colorClass], color_mem_forbiddenAt G c hue hug⟩

/-- Combine the core coloring, distinct reassigned two-star colors, and
distinct central colors outside the two-star palette. -/
noncomputable def merge {z v : V} (hzv : z ≠ v) {k d : ℕ}
    (c : (G.restrictEdges (core G z v)).EdgeColoring k)
    (a : (G.restrictEdges (spokes G z v)).EdgeColoring d)
    (f : Fin d ↪ Fin k)
    (hfree : ∀ i, f i ∉ forbiddenClass G c a i)
    (b : central G z v ↪ Fin k)
    (hdisjoint : ∀ e i, b e ≠ f i) : G.EdgeColoring k := by
  let h : E → Fin k := fun e =>
    if he : e ∈ central G z v then b ⟨e, he⟩
    else if he' : e ∈ spokes G z v then f (a.color ⟨e, he'⟩)
    else c.color ⟨e, core_of_not_central_not_spokes G z v he he'⟩
  have hc (e : E) (he : e ∈ central G z v) : h e = b ⟨e, he⟩ := by
    simp only [h, dif_pos he]
  have hs (e : E) (he : e ∈ spokes G z v) : h e = f (a.color ⟨e, he⟩) := by
    have hn : e ∉ central G z v := (Finset.mem_sdiff.mp he).2
    simp only [h, dif_neg hn, dif_pos he]
  have hr (e : E) (he : e ∈ core G z v) : h e = c.color ⟨e, he⟩ := by
    have hm := (mem_core G z v e).mp he
    have hn : e ∉ central G z v := by simp only [mem_central]; tauto
    have hn' : e ∉ spokes G z v := by simp only [mem_spokes]; tauto
    simp only [h, dif_neg hn, dif_neg hn']
  refine ⟨h, ?_⟩
  intro e g u heg hue hug
  by_cases hec : e ∈ central G z v
  · by_cases hgc : g ∈ central G z v
    · exact congrArg Subtype.val (b.injective ((hc e hec).symm.trans (heg.trans (hc g hgc))))
    · by_cases hgs : g ∈ spokes G z v
      · exact (hdisjoint ⟨e, hec⟩ (a.color ⟨g, hgs⟩)
          ((hc e hec).symm.trans (heg.trans (hs g hgs)))).elim
      · exact (central_core_no_common G hzv hec
          (core_of_not_central_not_spokes G z v hgc hgs) hue hug).elim
  · by_cases hes : e ∈ spokes G z v
    · by_cases hgc : g ∈ central G z v
      · exact (hdisjoint ⟨g, hgc⟩ (a.color ⟨e, hes⟩)
          ((hc g hgc).symm.trans (heg.symm.trans (hs e hes)))).elim
      · by_cases hgs : g ∈ spokes G z v
        · exact congrArg Subtype.val (a.proper
            (f.injective ((hs e hes).symm.trans (heg.trans (hs g hgs)))) hue hug)
        · have hgr := core_of_not_central_not_spokes G z v hgc hgs
          exact (spoke_core_different G c a f hfree ⟨e, hes⟩ ⟨g, hgr⟩ hue hug
            ((hs e hes).symm.trans (heg.trans (hr g hgr)))).elim
    · have her := core_of_not_central_not_spokes G z v hec hes
      by_cases hgc : g ∈ central G z v
      · exact (central_core_no_common G hzv hgc her hug hue).elim
      · by_cases hgs : g ∈ spokes G z v
        · exact (spoke_core_different G c a f hfree ⟨g, hgs⟩ ⟨e, her⟩ hug hue
            ((hs g hgs).symm.trans (heg.symm.trans (hr e her)))).elim
        · have hgr := core_of_not_central_not_spokes G z v hgc hgs
          exact congrArg Subtype.val (c.proper
            ((hr e her).symm.trans (heg.trans (hr g hgr))) hue hug)

variable [Fintype V]

theorem edgeColoring_two_centres (z v : V) (hzv : z ≠ v) (k q : ℕ)
    (hdegree : ∀ u, G.degree u ≤ k)
    (hlow : ∀ u, G.degreeAway z u ≤ q)
    (htriple : ∀ u, u ≠ z → u ≠ v → (G.internalEdges {z, v, u}).card ≤ k)
    (hlarge : 2 * q ≤ (central G z v).card) (hqk : 2 * q < k) :
    Nonempty (G.EdgeColoring k) := by
  let d := k - (central G z v).card
  have hbk : (central G z v).card ≤ k :=
    (Finset.card_le_card (central_subset_star G z v)).trans (hdegree z)
  obtain ⟨c⟩ := coloring_of_degree_bound (G.restrictEdges (core G z v)) k q
    (core_degree_le G z v q hlow) hqk
  obtain ⟨a⟩ := (G.restrictEdges (spokes G z v)).exists_edgeColoring_of_bipartite
    (spokes_bipartite G z v hzv) d (by
      intro u
      by_cases hu : u = z ∨ u = v
      · exact spokes_degree_centres_le G z v k hdegree u hu
      · exact spokes_degree_outside_le G z v hzv k htriple u
          (fun h => hu (Or.inl h)) (fun h => hu (Or.inr h)))
  obtain ⟨f, hf⟩ := exists_injective_available k
    (fun i : Fin d => (forbiddenClass G c a i)ᶜ) (by
      intro i
      rw [Fintype.card_fin, Finset.card_compl, Fintype.card_fin]
      have hforbid := forbiddenClass_card_le G c a hlow i
      dsimp [d]
      omega)
  have hfree : ∀ i, f i ∉ forbiddenClass G c a i := by
    intro i
    exact Finset.mem_compl.mp (hf i)
  let U : Finset (Fin k) := (Finset.univ.image f)ᶜ
  have hU : U.card = (central G z v).card := by
    simp only [U, Finset.card_compl, Finset.card_image_of_injective _ f.injective,
      Finset.card_univ, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨b⟩ : Nonempty ((central G z v) ↪ U) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, Fintype.card_coe, hU])
  let b' : central G z v ↪ Fin k := b.trans (Function.Embedding.subtype _)
  refine ⟨merge G hzv c a f hfree b' ?_⟩
  intro e i hei
  have hb := (b e).property
  have hmem : f i ∉ Finset.univ.image f := by
    have heq : (b e).val = f i := hei
    simpa only [U, Finset.mem_compl, heq] using hb
  exact hmem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

end SparseColoring

variable [Fintype V]

/-- Lemma 2.12: a vertex deletion of maximum degree at most `q`, together
with the three-vertex obstruction bound and `k > 6q`, gives a `k`-coloring. -/
theorem edgeColoring_sparse_vertex_deletion (z : V) (k q : ℕ)
    (hdegree : ∀ u, G.degree u ≤ k)
    (hlow : ∀ u, G.degreeAway z u ≤ q)
    (htriple : ∀ X : Finset V, X.card = 3 → z ∈ X → (G.internalEdges X).card ≤ k)
    (hqk : 6 * q < k) : Nonempty (G.EdgeColoring k) := by
  by_cases hlarge : ∃ v, v ≠ z ∧ 2 * q ≤ (SparseColoring.central G z v).card
  · obtain ⟨v, hvz, hv⟩ := hlarge
    apply SparseColoring.edgeColoring_two_centres G z v hvz.symm k q hdegree hlow ?_ hv
      (by omega)
    intro u huz huv
    apply htriple {z, v, u}
    · simp [Ne.symm hvz, Ne.symm huz, Ne.symm huv]
    · simp
  · apply G.edgeColoring_one_high k (3 * (q : ℝ)) z hdegree
    · intro u huz
      have hsmall : (G.incidenceEdges z ∩ G.incidenceEdges u).card < 2 * q := by
        by_contra h
        exact hlarge ⟨u, huz, Nat.le_of_not_gt h⟩
      have hcount := G.degreeAway_add_parallel z u
      have hlow' := hlow u
      have hn : G.degree u ≤ 3 * q := by omega
      exact_mod_cast hn
    · have hr : (6 : ℝ) * q < k := by exact_mod_cast hqk
      linarith

/-- The same sparse-deletion criterion permits a real degree bound. -/
theorem edgeColoring_sparse_vertex_deletion_real (z : V) (k : ℕ) (q : ℝ)
    (hdegree : ∀ u, G.degree u ≤ k)
    (hlow : ∀ u, (G.degreeAway z u : ℝ) ≤ q)
    (htriple : ∀ X : Finset V, X.card = 3 → z ∈ X → (G.internalEdges X).card ≤ k)
    (hqk : 6 * q < k) : Nonempty (G.EdgeColoring k) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg (G.degreeAway z z)).trans (hlow z)
  apply G.edgeColoring_sparse_vertex_deletion z k ⌊q⌋₊ hdegree
    (fun u => Nat.le_floor (hlow u)) htriple
  have hfloor : (⌊q⌋₊ : ℝ) ≤ q := Nat.floor_le hq
  have hlt : (6 : ℝ) * ⌊q⌋₊ < k := by linarith
  exact_mod_cast hlt

/-- Lemma 2.12 stated directly using the actual vertex-deleted multigraph. -/
theorem edgeColoring_sparse_deleteVertex (z : V) (k q : ℕ)
    (hdegree : ∀ u, G.degree u ≤ k)
    (hlow : ∀ u, (G.deleteVertex z).degree u ≤ q)
    (htriple : ∀ X : Finset V, X.card = 3 → z ∈ X → (G.internalEdges X).card ≤ k)
    (hqk : 6 * q < k) : Nonempty (G.EdgeColoring k) := by
  apply G.edgeColoring_sparse_vertex_deletion z k q hdegree ?_ htriple hqk
  intro u
  by_cases huz : u = z
  · simp [huz, degreeAway]
  · simpa only [deleteVertex_degree] using hlow ⟨u, huz⟩

end Overfull.Multigraph
