import Overfull.BoundaryExtension.BoundaryData
import Overfull.BoundaryExtension.Packing
import Overfull.OneCore.Complement
import Overfull.MatchingProbability

/-!
# Completing the prescribed boundary classes in the original multigraph

Each class is the union of its original boundary edge copies and the
specified embedded copies of its packed simple-core matching. The
forbidden footprint makes these two matchings vertex-disjoint. All
claims below concern the original host and its individual edge copies.
-/

noncomputable section

namespace Overfull.BoundaryExtension

open Finset Classical SmallCuts MatchingProbability

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {d : ℕ}

namespace BoundaryColoring

/-- A prescribed boundary class, viewed as its original host edge copies. -/
def originalClass (c : BoundaryColoring G U d) (i : Fin d) : Finset E :=
  (c.classEdges i).map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_originalClass (c : BoundaryColoring G U d) (i : Fin d) (e : E) :
    e ∈ c.originalClass i ↔ ∃ b : G.cutEdges U, c.color b = i ∧ b.val = e := by
  simp only [originalClass, mem_map, mem_classEdges, Function.Embedding.coeFn_mk]

@[simp] theorem boundary_mem_originalClass (c : BoundaryColoring G U d)
    (i : Fin d) (e : G.cutEdges U) : e.val ∈ c.originalClass i ↔ c.color e = i := by
  rw [mem_originalClass]
  constructor
  · rintro ⟨b, hb, hbe⟩
    have hh : b = e := Subtype.ext hbe
    simpa only [hh] using hb
  · intro he
    exact ⟨e, he, rfl⟩

theorem originalClass_subset_cut (c : BoundaryColoring G U d) (i : Fin d) :
    c.originalClass i ⊆ G.cutEdges U := by
  intro e he
  obtain ⟨b, _hb, rfl⟩ := (c.mem_originalClass i e).mp he
  exact b.property

theorem originalClass_isMatching (c : BoundaryColoring G U d) (i : Fin d) :
    G.IsMatching (c.originalClass i) := by
  intro e he f hf v hev hfv
  obtain ⟨b, hb, rfl⟩ := (c.mem_originalClass i e).mp he
  obtain ⟨b', hb', rfl⟩ := (c.mem_originalClass i f).mp hf
  exact congrArg Subtype.val (c.proper (hb.trans hb'.symm) hev hfv)

theorem originalClass_disjoint (c : BoundaryColoring G U d) :
    Pairwise (fun i j => Disjoint (c.originalClass i) (c.originalClass j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  obtain ⟨b, hb, rfl⟩ := (c.mem_originalClass i e).mp hei
  exact hij (hb.symm.trans ((c.boundary_mem_originalClass j b).mp hej))

theorem originalClass_footprint (c : BoundaryColoring G U d) (i : Fin d) (u : U) :
    u ∈ c.footprint i ↔ ∃ e ∈ c.originalClass i, u.val ∈ G.edge e := by
  rw [c.mem_footprint]
  constructor
  · rintro ⟨b, hb, hu⟩
    exact ⟨b.val, (c.boundary_mem_originalClass i b).mpr hb, hu⟩
  · rintro ⟨e, he, hu⟩
    obtain ⟨b, hb, rfl⟩ := (c.mem_originalClass i e).mp he
    exact ⟨b, hb, hu⟩

end BoundaryColoring

/-- The original copies chosen for a simple-core subgraph. -/
def coreMatchingCopies (C : Core G U) (Q : C.graph.Subgraph) : Finset E :=
  (matchingEdges Q).map C.edgeMap

omit [Fintype E] in
theorem mem_coreMatchingCopies (C : Core G U) (Q : C.graph.Subgraph) (e : E) :
    e ∈ coreMatchingCopies C Q ↔
      ∃ f ∈ matchingEdges Q, C.edgeMap f = e := by
  simp only [coreMatchingCopies, mem_map]

omit [Fintype E] in
theorem coreMatchingCopies_subset_core (C : Core G U) (Q : C.graph.Subgraph) :
    coreMatchingCopies C Q ⊆ OneCore.coreEdges C := by
  intro e he
  obtain ⟨f, _hf, rfl⟩ := (mem_coreMatchingCopies C Q e).mp he
  exact (OneCore.mem_coreEdges C _).mpr ⟨f, rfl⟩

private theorem simple_matchingEdges_isMatching {W : Type*} [Fintype W]
    (H : SimpleGraph W) (Q : H.Subgraph) (hQ : Q.IsMatching) :
    (Multigraph.ofSimpleGraph H).IsMatching (matchingEdges Q) := by
  intro e he f hf v hev hfv
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hev
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hfv
  change e.val = s(v,x) at hx
  change f.val = s(v,y) at hy
  have hex : Q.Adj v x := by simpa only [hx] using (mem_filter.mp he).2
  have hfy : Q.Adj v y := by simpa only [hy] using (mem_filter.mp hf).2
  have hxy := hQ.eq_of_adj_left hex hfy
  apply Subtype.ext
  rw [hx, hy, hxy]

omit [Fintype E] in
theorem coreMatchingCopies_isMatching (C : Core G U) (Q : C.graph.Subgraph)
    (hQ : Q.IsMatching) : G.IsMatching (coreMatchingCopies C Q) := by
  intro e he f hf v hev hfv
  obtain ⟨a, ha, rfl⟩ := (mem_coreMatchingCopies C Q e).mp he
  obtain ⟨b, hb, rfl⟩ := (mem_coreMatchingCopies C Q f).mp hf
  have hvU : v ∈ U := OneCore.coreEdges_endpoint C
    ((OneCore.mem_coreEdges C _).mpr ⟨a, rfl⟩) hev
  let u : U := ⟨v, hvU⟩
  have hea : u ∈ a.val := (OneCore.core_incident_iff C a u).mp hev
  have heb : u ∈ b.val := (OneCore.core_incident_iff C b u).mp hfv
  exact congrArg C.edgeMap (simple_matchingEdges_isMatching C.graph Q hQ a ha b hb u hea heb)

omit [Fintype E] in
theorem coreMatchingCopies_incident_verts (C : Core G U) (Q : C.graph.Subgraph)
    {e : E} (he : e ∈ coreMatchingCopies C Q) (u : U)
    (hu : u.val ∈ G.edge e) : u ∈ Q.verts := by
  obtain ⟨f, hf, rfl⟩ := (mem_coreMatchingCopies C Q e).mp he
  obtain ⟨v, hv⟩ := Sym2.mem_iff_exists.mp ((OneCore.core_incident_iff C f u).mp hu)
  have hadj : Q.Adj u v := by simpa only [hv] using (mem_filter.mp hf).2
  exact Q.edge_vert hadj

omit [Fintype E] in
theorem coreMatchingCopies_covers (C : Core G U) (Q : C.graph.Subgraph)
    (hQ : Q.IsMatching) (u : U) (hu : u ∈ Q.verts) :
    ∃ e ∈ coreMatchingCopies C Q, u.val ∈ G.edge e := by
  obtain ⟨v, hv, _hunique⟩ := hQ hu
  let f : C.graph.edgeSet := ⟨s(u,v), Q.adj_sub hv⟩
  refine ⟨C.edgeMap f, (mem_coreMatchingCopies C Q _).mpr ⟨f, ?_, rfl⟩, ?_⟩
  · exact mem_filter.mpr ⟨mem_univ _, hv⟩
  · exact (OneCore.core_incident_iff C f u).mpr (Sym2.mem_mk_left _ _)

omit [Fintype E] in
theorem coreMatchingCopies_disjoint (C : Core G U) (Q R : C.graph.Subgraph)
    (hQR : Disjoint Q.spanningCoe R.spanningCoe) :
    Disjoint (coreMatchingCopies C Q) (coreMatchingCopies C R) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, ha, rfl⟩ := (mem_coreMatchingCopies C Q e).mp he
  obtain ⟨b, hb, hba⟩ := (mem_coreMatchingCopies C R _).mp hf
  have hba' : b = a := C.edgeMap.injective hba
  subst b
  exact Set.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mpr hQR)
    (mem_filter.mp ha).2 (mem_filter.mp hb).2

theorem boundary_coreCopies_disjoint (c : BoundaryColoring G U d) (i : Fin d)
    (C : Core G U) (Q : C.graph.Subgraph) :
    Disjoint (c.originalClass i) (coreMatchingCopies C Q) := by
  exact (OneCore.coreEdges_disjoint_cut C).symm.mono
    (c.originalClass_subset_cut i) (coreMatchingCopies_subset_core C Q)

private theorem boundary_coreCopies_no_common (c : BoundaryColoring G U d) (i : Fin d)
    (C : Core G U) (Q : C.graph.Subgraph)
    (hverts : Q.verts = (c.footprint i : Set U)ᶜ)
    {e f : E} (he : e ∈ c.originalClass i) (hf : f ∈ coreMatchingCopies C Q)
    {v : V} (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : False := by
  have hvU := OneCore.coreEdges_endpoint C (coreMatchingCopies_subset_core C Q hf) hfv
  let u : U := ⟨v, hvU⟩
  have hfoot : u ∈ c.footprint i := (c.originalClass_footprint i u).mpr ⟨e, he, hev⟩
  have hver := coreMatchingCopies_incident_verts C Q hf u hfv
  rw [hverts] at hver
  exact hver hfoot

section Completed

variable {q : ℕ} {θ σ : ℝ}
variable (c : BoundaryColoring G U d) (C : Core G U) (labels : Fin q ↪ Fin d)
variable (P : CorePacking C.graph q (fun j => c.footprint (labels j)) θ σ)

/-- A completed prescribed color, with all original host copies retained. -/
def completedColor (j : Fin q) : Finset E :=
  c.originalClass (labels j) ∪ coreMatchingCopies C (P.matching j)

theorem completedColor_isMatching (j : Fin q) : G.IsMatching (completedColor c C labels P j) := by
  intro e he f hf v hev hfv
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact c.originalClass_isMatching (labels j) e he f hf v hev hfv
  · exact (boundary_coreCopies_no_common c (labels j) C (P.matching j)
      (P.verts j) he hf hev hfv).elim
  · exact (boundary_coreCopies_no_common c (labels j) C (P.matching j)
      (P.verts j) hf he hfv hev).elim
  · exact coreMatchingCopies_isMatching C (P.matching j) (P.isMatching j) e he f hf v hev hfv

/-- Each core vertex is covered by its boundary edge or its packed core edge. -/
theorem completedColor_covers (j : Fin q) (u : U) :
    ∃ e ∈ completedColor c C labels P j, u.val ∈ G.edge e := by
  by_cases hu : u ∈ c.footprint (labels j)
  · obtain ⟨e, he, hev⟩ := (c.originalClass_footprint (labels j) u).mp hu
    exact ⟨e, mem_union_left _ he, hev⟩
  · have hver : u ∈ (P.matching j).verts := by
      rw [P.verts j]
      exact hu
    obtain ⟨e, he, hev⟩ := coreMatchingCopies_covers C (P.matching j) (P.isMatching j) u hver
    exact ⟨e, mem_union_right _ he, hev⟩

theorem completedColor_covers_uniquely (j : Fin q) (u : U) :
    ∃! e, e ∈ completedColor c C labels P j ∧ u.val ∈ G.edge e := by
  obtain ⟨e, he, hev⟩ := completedColor_covers c C labels P j u
  refine ⟨e, ⟨he, hev⟩, ?_⟩
  intro f hf
  exact completedColor_isMatching c C labels P j f hf.1 e he u.val hf.2 hev

/-- No new boundary copy is introduced by an internal completion. -/
theorem completedColor_boundary (j : Fin q) (e : G.cutEdges U) :
    e.val ∈ completedColor c C labels P j ↔ c.color e = labels j := by
  constructor
  · intro he
    rcases mem_union.mp he with hb | hc
    · exact (c.boundary_mem_originalClass (labels j) e).mp hb
    · exact (Finset.disjoint_left.mp (OneCore.coreEdges_disjoint_cut C)
        (coreMatchingCopies_subset_core C (P.matching j) hc) e.property).elim
  · intro he
    exact mem_union_left _ ((c.boundary_mem_originalClass (labels j) e).mpr he)

theorem completedColor_boundary_inter (j : Fin q) :
    completedColor c C labels P j ∩ G.cutEdges U = c.originalClass (labels j) := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hcut⟩ := mem_inter.mp he
    exact (c.boundary_mem_originalClass (labels j) ⟨e,hcut⟩).mpr
      ((completedColor_boundary c C labels P j ⟨e,hcut⟩).mp he)
  · intro he
    exact mem_inter.mpr ⟨mem_union_left _ he, c.originalClass_subset_cut (labels j) he⟩

/-- The original labels and the packed core disjointness together rule
out overlap of every pair of completed classes. -/
theorem completedColor_disjoint :
    Pairwise (fun i j => Disjoint (completedColor c C labels P i)
      (completedColor c C labels P j)) := by
  intro i j hij
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_union_right.mpr
    exact ⟨c.originalClass_disjoint (fun h => hij (labels.injective h)),
      boundary_coreCopies_disjoint c (labels i) C (P.matching j)⟩
  · apply Finset.disjoint_union_right.mpr
    exact ⟨(boundary_coreCopies_disjoint c (labels j) C (P.matching i)).symm,
      coreMatchingCopies_disjoint C (P.matching i) (P.matching j) (P.disjoint hij)⟩

/-- Every completed edge copy belongs to the actual incident-edge problem. -/
theorem completedColor_retained (j : Fin q) {e : E}
    (he : e ∈ completedColor c C labels P j) : ∃ u : U, u.val ∈ G.edge e := by
  rcases mem_union.mp he with hb | hc
  · obtain ⟨b, _hb, rfl⟩ := (c.mem_originalClass (labels j) e).mp hb
    exact ⟨boundaryEnd G U b, boundaryEnd_incident G U b⟩
  · have hinc : G.firstEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
    exact ⟨⟨G.firstEnd e, OneCore.coreEdges_endpoint C
      (coreMatchingCopies_subset_core C (P.matching j) hc) hinc⟩, hinc⟩

/-- Exactly one original edge copy per completed class is deleted at each core vertex. -/
theorem completedColor_incidence_card (j : Fin q) (u : U) :
    ((completedColor c C labels P j).filter (fun e => u.val ∈ G.edge e)).card = 1 := by
  apply Nat.le_antisymm
  · exact (G.isMatching_iff_incident_card_le_one _).mp
      (completedColor_isMatching c C labels P j) u.val
  · obtain ⟨e, he, hev⟩ := completedColor_covers c C labels P j u
    exact Finset.one_le_card.mpr ⟨e, mem_filter.mpr ⟨he, hev⟩⟩

end Completed
end Overfull.BoundaryExtension
