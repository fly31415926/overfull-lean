import Overfull.SmallCuts
import Overfull.MultigraphFanApplications
import Overfull.ForeignEdges.RefinementCore

/-!
# Coloring the exceptional complement of a one-apex core

The simple core is represented by its actual embedded edge copies.  Its
complement has at most one vertex of large degree, so it is colorable by
the proved greedy theorem.  Moving one core vertex outside then uses the
proved bounded-core-move theorem.  These are prerequisites for ordinary
core factorization; no factorization theorem is asserted here.
-/

noncomputable section
namespace Overfull.OneCore

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V}

/-- The actual host copies belonging to the specified simple core. -/
def coreEdges (C : Core G U) : Finset E :=
  (univ : Finset C.graph.edgeSet).map C.edgeMap

omit [Fintype E] in
@[simp] theorem mem_coreEdges (C : Core G U) (e : E) :
    e ∈ coreEdges C ↔ ∃ f : C.graph.edgeSet, C.edgeMap f = e := by
  simp [coreEdges]

omit [Fintype E] in
/-- Every endpoint of a core copy is a vertex of the core. -/
theorem coreEdges_endpoint (C : Core G U) {e : E} (he : e ∈ coreEdges C)
    {v : V} (hv : v ∈ G.edge e) : v ∈ U := by
  obtain ⟨f,rfl⟩ := (mem_coreEdges C e).mp he
  rw [C.map_edge,Sym2.mem_map] at hv
  obtain ⟨w,_hw,rfl⟩ := hv
  exact w.property

theorem coreEdges_subset_internal (C : Core G U) :
    coreEdges C ⊆ G.internalEdges U := by
  intro e he
  apply (G.mem_internalEdges U e).mpr
  constructor
  · exact coreEdges_endpoint C he ((G.incident_iff e _).mpr (Or.inl rfl))
  · exact coreEdges_endpoint C he ((G.incident_iff e _).mpr (Or.inr rfl))

omit [Fintype E] in
/-- Distinct core copies have distinct unordered endpoint pairs. -/
theorem coreEdges_simple (C : Core G U) : Set.InjOn G.edge (coreEdges C) := by
  intro e he f hf hef
  obtain ⟨e',rfl⟩ := (mem_coreEdges C e).mp he
  obtain ⟨f',rfl⟩ := (mem_coreEdges C f).mp hf
  rw [C.map_edge,C.map_edge] at hef
  have hh : e'.val = f'.val :=
    (Function.Embedding.subtype (fun v => v ∈ U)).sym2Map.injective hef
  exact congrArg C.edgeMap (Subtype.ext hh)

omit [Fintype E] in
theorem core_incident_iff (C : Core G U) (e : C.graph.edgeSet) (v : U) :
    v.val ∈ G.edge (C.edgeMap e) ↔ v ∈ e.val := by
  rw [C.map_edge,Sym2.mem_map]
  constructor
  · rintro ⟨w,hw,hwv⟩
    have hh : w = v := Subtype.ext hwv
    exact hh ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

/-- Incidence is preserved exactly, including the original host copies. -/
theorem core_degree (C : Core G U) (v : U) :
    (G.restrictEdges (coreEdges C)).degree v.val = C.graph.degree v := by
  have heq : ((Multigraph.ofSimpleGraph C.graph).incidenceEdges v).map C.edgeMap =
      coreEdges C ∩ G.incidenceEdges v.val := by
    ext e
    simp only [Finset.mem_map,Multigraph.mem_incidenceEdges,Finset.mem_inter,
      mem_coreEdges,Multigraph.ofSimpleGraph]
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact ⟨⟨f,rfl⟩,(core_incident_iff C f v).mpr hf⟩
    · rintro ⟨⟨f,rfl⟩,hf⟩
      exact ⟨f,(core_incident_iff C f v).mp hf,rfl⟩
  rw [Multigraph.restrictEdges_degree,← heq,Finset.card_map]
  exact Multigraph.ofSimpleGraph_degree C.graph v

/-- Splitting the actual host copies into a set and its complement splits
the degree exactly. -/
theorem complement_degree_add (G : Multigraph V E) (F : Finset E) (v : V) :
    (G.restrictEdges Fᶜ).degree v + (G.restrictEdges F).degree v = G.degree v := by
  rw [Multigraph.restrictEdges_degree,Multigraph.restrictEdges_degree]
  have heq : Fᶜ ∩ G.incidenceEdges v = G.incidenceEdges v \ F := by
    ext e
    simp [and_comm]
  rw [heq,Finset.inter_comm F]
  exact Finset.card_sdiff_add_card_inter (G.incidenceEdges v) F

/-- The exact core/complement degree identity used in boundary budgets. -/
theorem complement_degree_add_core (C : Core G U) (v : U) :
    (G.restrictEdges (coreEdges C)ᶜ).degree v.val + C.graph.degree v = G.degree v.val := by
  rw [← core_degree C v]
  exact complement_degree_add G (coreEdges C) v.val

theorem core_degree_le (C : Core G U) (v : U) :
    C.graph.degree v ≤ G.degree v.val := by
  have hh := complement_degree_add_core C v
  omega

/-- A core copy never crosses its own vertex boundary. -/
theorem coreEdges_disjoint_cut (C : Core G U) :
    Disjoint (coreEdges C) (G.cutEdges U) := by
  apply Finset.disjoint_left.mpr
  intro e he hcut
  obtain ⟨hfirst,hsecond⟩ := (G.mem_internalEdges U e).mp (coreEdges_subset_internal C he)
  exact (G.mem_cutEdges U e).mp hcut (propext ⟨fun _ => hsecond,fun _ => hfirst⟩)

/-- Each boundary incidence is one of the actual complementary incidences. -/
theorem boundary_incidence_le_complement (C : Core G U) (v : V) :
    ((G.cutEdges U) ∩ G.incidenceEdges v).card ≤
      (G.restrictEdges (coreEdges C)ᶜ).degree v := by
  rw [Multigraph.restrictEdges_degree]
  apply Finset.card_le_card
  intro e he
  refine Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr ?_,(Finset.mem_inter.mp he).2⟩
  intro heC
  exact Finset.disjoint_left.mp (coreEdges_disjoint_cut C) heC (Finset.mem_inter.mp he).1

theorem complement_degree_le_error (C : Core G U) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) (v : U) :
    ((G.restrictEdges (coreEdges C)ᶜ).degree v.val : ℝ) ≤ a := by
  have hh := complement_degree_add_core C v
  rw [hregular] at hh
  have hh' : ((G.restrictEdges (coreEdges C)ᶜ).degree v.val : ℝ) + C.graph.degree v = k := by
    exact_mod_cast hh
  linarith only [hh',hdegree v]

/-- Before moving a vertex, the apex is the only potentially large-degree
vertex of the exceptional complement. -/
theorem one_apex_complement_colorable
    (G : Multigraph V E) (U : Finset V) (H : Finset E) (z : V) (k : ℕ) (a : ℝ)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hcover : ∀ v, v ∈ U ∨ v = z)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hka : 2*a < k) : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  apply (G.restrictEdges Hᶜ).edgeColoring_one_high k a z
    (fun v => (G.restrictEdges_degree_le Hᶜ v).trans (hdegree v))
  · intro v hv
    exact hcore v ((hcover v).resolve_right hv)
  · exact hka

/-- Moving one vertex out of a simple core preserves actual complement
colorability and increases the degree error by at most one. -/
theorem move_one_complement_colorable [Fintype V]
    (G : Multigraph V E) (U : Finset V) (H : Finset E) (z x : V) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hcover : ∀ v, v ∈ U ∨ v = z)
    (hsupport : H ⊆ G.internalEdges U) (hsimple : Set.InjOn G.edge H)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hka : 3*(a+1) < k) :
    Nonempty ((G.restrictEdges (H ∩ G.internalEdges (U \ {x}))ᶜ).EdgeColoring k) ∧
      ∀ v ∈ U \ {x}, ((G.restrictEdges (H ∩ G.internalEdges (U \ {x}))ᶜ).degree v : ℝ)
        ≤ a+1 := by
  have hc := one_apex_complement_colorable G U H z k a
    (fun v => (hregular v).le) hcover hcore (by linarith only [hka])
  simpa only [Finset.card_singleton,Nat.cast_one] using
    G.bounded_core_move_full k a U {x} H hregular hsupport hsimple hcore hc
      (by simpa only [Finset.card_singleton,Nat.cast_one] using hka)

/-- The induced surviving simple core, embedded by the same host copies. -/
def restrictCore (C : Core G U) (W : Finset V) : Core G (U \ W) where
  graph := ForeignRefinement.survivingCore U W C.graph
  edgeMap := (SimpleGraph.Embedding.comap
    (ForeignRefinement.survivingInclusion U W) C.graph).mapEdgeSet.trans C.edgeMap
  map_edge e := by
    rw [Function.Embedding.trans_apply,C.map_edge]
    change Sym2.map Subtype.val
      (Sym2.map (ForeignRefinement.survivingInclusion U W) e.val) = _
    rw [Sym2.map_map]
    rfl

/-- Restriction retains exactly the original core copies with both ends
among the surviving vertices. -/
theorem restrictCore_edges (C : Core G U) (W : Finset V) :
    coreEdges (restrictCore C W) = coreEdges C ∩ G.internalEdges (U \ W) := by
  apply Finset.Subset.antisymm
  · intro e he
    refine Finset.mem_inter.mpr ⟨?_,coreEdges_subset_internal (restrictCore C W) he⟩
    obtain ⟨f,rfl⟩ := (mem_coreEdges (restrictCore C W) e).mp he
    exact (mem_coreEdges C _).mpr
      ⟨(SimpleGraph.Embedding.comap
        (ForeignRefinement.survivingInclusion U W) C.graph).mapEdgeSet f,rfl⟩
  · intro e he
    obtain ⟨heC,heW⟩ := Finset.mem_inter.mp he
    obtain ⟨f,rfl⟩ := (mem_coreEdges C e).mp heC
    let u := (Multigraph.ofSimpleGraph C.graph).firstEnd f
    let v := (Multigraph.ofSimpleGraph C.graph).secondEnd f
    have hf : s(u,v) = f.val := (Multigraph.ofSimpleGraph C.graph).edge_eq f
    have hsub : (G.edge (C.edgeMap f)).toFinset ⊆ U \ W :=
      (Finset.mem_filter.mp heW).2
    have hu : u.val ∈ U \ W := hsub (Sym2.mem_toFinset.mpr
      ((core_incident_iff C f u).mpr (by rw [← hf]; simp)))
    have hv : v.val ∈ U \ W := hsub (Sym2.mem_toFinset.mpr
      ((core_incident_iff C f v).mpr (by rw [← hf]; simp)))
    let u' : ↥(U \ W) := ⟨u.val,hu⟩
    let v' : ↥(U \ W) := ⟨v.val,hv⟩
    have hadj : C.graph.Adj u v := by
      have hh := f.property
      rw [← hf] at hh
      exact hh
    let f' : (restrictCore C W).graph.edgeSet := ⟨s(u',v'),hadj⟩
    apply (mem_coreEdges (restrictCore C W) _).mpr
    refine ⟨f',?_⟩
    change C.edgeMap _ = C.edgeMap f
    apply congrArg C.edgeMap
    apply Subtype.ext
    change s(u,v) = f.val
    exact hf

omit [Fintype E] in
/-- One moved vertex loses at most one simple-core neighbor. -/
theorem restrictCore_one_degree (C : Core G U) (x : V) (k : ℕ) (a : ℝ)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) :
    ∀ v, (k : ℝ)-(a+1) ≤ ((restrictCore C {x}).graph.degree v : ℝ) := by
  intro v
  have hh := (ForeignRefinement.survivingCore_degree_bounds U {x} C.graph v).2
  simp only [Finset.card_singleton] at hh
  have hh' : (C.graph.degree (ForeignRefinement.survivingInclusion U {x} v) : ℝ) ≤
      (restrictCore C {x}).graph.degree v + 1 := by exact_mod_cast hh
  linarith only [hh',hdegree (ForeignRefinement.survivingInclusion U {x} v)]

omit [Fintype E] in
/-- The surviving actual core has fixed robust parameters after the move. -/
theorem restrictCore_one_robust (C : Core G U) (x : V) (ν τ : ℝ)
    (hrobust : IsRobustExpander C.graph ν τ)
    (hν : 0 ≤ ν) (hνone : ν ≤ 1) (hτ : 0 ≤ τ) (hτquarter : τ < 1/4)
    (hlarge : 2 ≤ ν*U.card) :
    IsRobustExpander (restrictCore C {x}).graph (ν/2) (2*τ) := by
  exact ForeignRefinement.survivingCore_robust_one U {x} C.graph ν τ
    hrobust hν hνone hτ hτquarter (by simp) hlarge

/-- The entire even-core reduction is proved from the original odd core.
Its exceptional complement is actually colorable and its two exterior
vertices are precisely the old apex and the moved vertex. -/
theorem even_core_complement [Fintype V]
    (C : Core G U) (z x : V) (k : ℕ) (a ν τ : ℝ)
    (hregular : ∀ v, G.degree v = k) (hout : Uᶜ = {z})
    (hodd : U.card % 2 = 1) (hx : x ∈ U)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ))
    (hka : 3*(a+1) < k)
    (hrobust : IsRobustExpander C.graph ν τ)
    (hν : 0 ≤ ν) (hνone : ν ≤ 1) (hτ : 0 ≤ τ) (hτquarter : τ < 1/4)
    (hlarge : 2 ≤ ν*U.card) :
    (U \ {x}).card % 2 = 0 ∧
      (U \ {x})ᶜ = {z,x} ∧ (U \ {x})ᶜ.card = 2 ∧
      Nonempty ((G.restrictEdges (coreEdges (restrictCore C {x}))ᶜ).EdgeColoring k) ∧
      (∀ v, (k : ℝ)-(a+1) ≤ ((restrictCore C {x}).graph.degree v : ℝ)) ∧
      IsRobustExpander (restrictCore C {x}).graph (ν/2) (2*τ) := by
  have hz : z ∉ U := Finset.mem_compl.mp (by rw [hout]; simp)
  have hzx : z ≠ x := by rintro rfl; exact hz hx
  have hcover : ∀ v, v ∈ U ∨ v = z := by
    intro v
    by_cases hv : v ∈ U
    · exact Or.inl hv
    · exact Or.inr (Finset.mem_singleton.mp (hout ▸ Finset.mem_compl.mpr hv))
  have hcore : ∀ v ∈ U, ((G.restrictEdges (coreEdges C)ᶜ).degree v : ℝ) ≤ a := by
    intro v hv
    exact complement_degree_le_error C k a hregular hdegree ⟨v,hv⟩
  obtain ⟨hcolor,_herror⟩ := move_one_complement_colorable G U (coreEdges C) z x k a
    hregular hcover (coreEdges_subset_internal C) (coreEdges_simple C) hcore hka
  have hnewout : (U \ {x})ᶜ = {z,x} := by
    ext v
    simp only [Finset.mem_compl,Finset.mem_sdiff,Finset.mem_singleton,
      Finset.mem_insert]
    have hv : v ∉ U ↔ v = z := by
      simpa only [Finset.mem_compl,Finset.mem_singleton] using
        (show v ∈ Uᶜ ↔ v ∈ ({z} : Finset V) by rw [hout])
    tauto
  refine ⟨?_,hnewout,?_,?_,restrictCore_one_degree C x k a hdegree,
    restrictCore_one_robust C x ν τ hrobust hν hνone hτ hτquarter hlarge⟩
  · have hh := Finset.card_erase_add_one hx
    rw [Finset.sdiff_singleton_eq_erase]
    omega
  · rw [hnewout]
    simp [hzx]
  · rwa [restrictCore_edges]

end Overfull.OneCore
