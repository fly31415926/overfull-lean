import Overfull.ForeignEdges.ColorClasses
import Overfull.SafePrescription.Counting

/-!
# Assigning exceptional vertices to cores

The assignment maximizes the actual number of neighbours in a core of the
same cluster.  The foreign graph is constructed from the resulting host
edges.  Its exceptional degrees are bounded by three quarters of the host
degree, and its core degrees by the actual exterior degrees.
-/

namespace Overfull.ForeignAssignment

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V I C : Type*} [Fintype V] [Fintype I]

noncomputable def coreNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (v : V) (i : I) : Finset V := G.neighborFinset v ∩ U i

noncomputable def clusterCores (c : V → C) (p : I → C) (v : V) : Finset I :=
  univ.filter (fun i => p i = c v)

omit [Fintype I] in
@[simp] theorem mem_coreNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (v w : V) (i : I) :
    w ∈ coreNeighbors G U v i ↔ G.Adj v w ∧ w ∈ U i := by
  simp [coreNeighbors]

omit [Fintype V] in
@[simp] theorem mem_clusterCores (c : V → C) (p : I → C) (v : V) (i : I) :
    i ∈ clusterCores c p v ↔ p i = c v := by
  simp [clusterCores]

/-- A maximum is attained in the actual same-cluster cores.  The assignment
is defined on all vertices; only its values on the exceptional set matter. -/
theorem exists_max_assignment [Nonempty I] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C)
    (hrepresented : ∀ v ∈ E, ∃ i, p i = c v) :
    ∃ a : V → I, ∀ v ∈ E,
      p (a v) = c v ∧
      ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
        (coreNeighbors G U v (a v)).card := by
  have hex (v : V) : ∃ i : I, v ∈ E →
      p i = c v ∧ ∀ j, p j = c v →
        (coreNeighbors G U v j).card ≤ (coreNeighbors G U v i).card := by
    by_cases hv : v ∈ E
    · have hnonempty : (clusterCores c p v).Nonempty := by
        obtain ⟨i,hi⟩ := hrepresented v hv
        exact ⟨i,(mem_clusterCores c p v i).mpr hi⟩
      obtain ⟨i,hi,hmax⟩ := (clusterCores c p v).exists_max_image
        (fun j => (coreNeighbors G U v j).card) hnonempty
      refine ⟨i,fun _ => ⟨(mem_clusterCores c p v i).mp hi,?_⟩⟩
      exact fun j hj => hmax j ((mem_clusterCores c p v j).mpr hj)
    · exact ⟨Classical.choice inferInstance,fun h => False.elim (hv h)⟩
  choose a ha using hex
  exact ⟨a,ha⟩

/-- Actual same-cluster exceptional-to-core edges outside the assigned core. -/
def foreignGraph (G : SimpleGraph V) (U : I → Finset V) (E : Finset V)
    (c : V → C) (p : I → C) (a : V → I) : SimpleGraph V where
  Adj u v := G.Adj u v ∧
    ((u ∈ E ∧ ∃ i, v ∈ U i ∧ p i = c u ∧ i ≠ a u) ∨
     (v ∈ E ∧ ∃ i, u ∈ U i ∧ p i = c v ∧ i ≠ a v))
  symm := by rintro u v ⟨h,h'⟩; exact ⟨h.symm,h'.symm⟩
  loopless := by intro v h; exact G.loopless v h.1

omit [Fintype V] [Fintype I] in
theorem foreignGraph_le (G : SimpleGraph V) (U : I → Finset V) (E : Finset V)
    (c : V → C) (p : I → C) (a : V → I) : foreignGraph G U E c p a ≤ G :=
  fun _ _ h => h.1

omit [Fintype I] in
theorem coreNeighbors_disjoint (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j))) (v : V) :
    Pairwise (fun i j => Disjoint (coreNeighbors G U v i) (coreNeighbors G U v j)) := by
  intro i j hij
  exact (hdisjoint hij).mono inter_subset_right inter_subset_right

noncomputable def sameClusterNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (c : V → C) (p : I → C) (v : V) : Finset V :=
  (clusterCores c p v).biUnion (coreNeighbors G U v)

theorem sameClusterNeighbors_card_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (c : V → C) (p : I → C) (v : V) :
    (sameClusterNeighbors G U c p v).card ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hw
  exact (G.mem_neighborFinset v w).mpr ((mem_coreNeighbors G U v w i).mp hi).1

theorem sameClusterNeighbors_card_le_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (c : V → C) (p : I → C) (v : V) (i : I)
    (hcount : Fintype.card I ≤ 4)
    (hmax : ∀ j, p j = c v → (coreNeighbors G U v j).card ≤
      (coreNeighbors G U v i).card) :
    (sameClusterNeighbors G U c p v).card ≤ 4*(coreNeighbors G U v i).card := by
  have hnum : (clusterCores c p v).card ≤ 4 := (card_le_univ _).trans hcount
  calc
    _ ≤ ∑ j ∈ clusterCores c p v, (coreNeighbors G U v j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ clusterCores c p v, (coreNeighbors G U v i).card := by
      apply sum_le_sum
      intro j hj
      exact hmax j ((mem_clusterCores c p v j).mp hj)
    _ = (clusterCores c p v).card * (coreNeighbors G U v i).card := by simp
    _ ≤ 4*(coreNeighbors G U v i).card := Nat.mul_le_mul_right _ hnum

/-- At an exceptional vertex the foreign neighbours are precisely its
same-cluster core neighbours minus the neighbours in its assigned core. -/
theorem foreignGraph_neighbors_exceptional (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (v : V) (hv : v ∈ E) :
    (foreignGraph G U E c p a).neighborFinset v =
      sameClusterNeighbors G U c p v \ coreNeighbors G U v (a v) := by
  ext w
  constructor
  · intro hw
    have hw' := (foreignGraph G U E c p a).mem_neighborFinset v w |>.mp hw
    obtain ⟨hG,(⟨_,i,hi,hpi,hia⟩ | ⟨_,i,hi,_,_⟩)⟩ := hw'
    · refine mem_sdiff.mpr ⟨mem_biUnion.mpr
        ⟨i,(mem_clusterCores c p v i).mpr hpi,(mem_coreNeighbors G U v w i).mpr ⟨hG,hi⟩⟩,?_⟩
      intro hwA
      exact disjoint_left.mp (hdisjoint hia) hi ((mem_coreNeighbors G U v w (a v)).mp hwA).2
    · exact False.elim (disjoint_left.mp (hUE i) hi hv)
  · intro hw
    obtain ⟨hwT,hwA⟩ := mem_sdiff.mp hw
    obtain ⟨i,hi,hwN⟩ := mem_biUnion.mp hwT
    obtain ⟨hG,hwU⟩ := (mem_coreNeighbors G U v w i).mp hwN
    apply ((foreignGraph G U E c p a).mem_neighborFinset v w).mpr
    refine ⟨hG,Or.inl ⟨hv,i,hwU,(mem_clusterCores c p v i).mp hi,?_⟩⟩
    intro hia
    exact hwA (hia ▸ hwN)

/-- Maximizing among at most four cores gives the required three-quarter
bound, with the host degree itself on the right. -/
theorem foreignGraph_degree_exceptional (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (hcount : Fintype.card I ≤ 4)
    (v : V) (hv : v ∈ E) (ha : p (a v) = c v)
    (hmax : ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
      (coreNeighbors G U v (a v)).card) :
    4*(foreignGraph G U E c p a).degree v ≤ 3*G.degree v := by
  have hsubset : coreNeighbors G U v (a v) ⊆ sameClusterNeighbors G U c p v := by
    intro w hw
    exact mem_biUnion.mpr ⟨a v,(mem_clusterCores c p v (a v)).mpr ha,hw⟩
  have hsum := card_sdiff_add_card_eq_card hsubset
  have hfour := sameClusterNeighbors_card_le_four G U c p v (a v) hcount hmax
  have hdegree := sameClusterNeighbors_card_le_degree G U c p v
  rw [← (foreignGraph G U E c p a).card_neighborFinset_eq_degree,
    foreignGraph_neighbors_exceptional G U E c p a hdisjoint hUE v hv]
  omega

omit [Fintype I] in
/-- At a core vertex every foreign neighbour lies outside that core. -/
theorem foreignGraph_degree_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hUE : ∀ i, Disjoint (U i) E) (i : I) (v : V) (hv : v ∈ U i) :
    (foreignGraph G U E c p a).degree v ≤ (G.neighborFinset v \ U i).card := by
  rw [← (foreignGraph G U E c p a).card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  have hw' := ((foreignGraph G U E c p a).mem_neighborFinset v w).mp hw
  obtain ⟨hG,(⟨hvE,_⟩ | ⟨hwE,_⟩)⟩ := hw'
  · exact False.elim (disjoint_left.mp (hUE i) hv hvE)
  · refine mem_sdiff.mpr ⟨(G.mem_neighborFinset v w).mpr hG,?_⟩
    exact fun hwU => disjoint_left.mp (hUE i) hwU hwE

omit [Fintype I] in
/-- Vertices outside both the exceptional set and all cores are isolated
in the foreign graph.  In particular no covering assumption is hidden in
the degree argument. -/
theorem foreignGraph_degree_other (G : SimpleGraph V)
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (v : V) (hvE : v ∉ E) (hvU : ∀ i, v ∉ U i) :
    (foreignGraph G U E c p a).degree v = 0 := by
  rw [← (foreignGraph G U E c p a).card_neighborFinset_eq_degree,card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hw' := ((foreignGraph G U E c p a).mem_neighborFinset v w).mp hw
  rcases hw'.2 with ⟨hv,_⟩ | ⟨_,i,hi,_⟩
  · exact hvE hv
  · exact hvU i hi

/-- The two degree estimates combine to bound the actual foreign graph. -/
theorem foreignGraph_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (hcount : Fintype.card I ≤ 4)
    (hmax : ∀ v ∈ E, p (a v) = c v ∧
      ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
        (coreNeighbors G U v (a v)).card)
    (h : ℕ) (hdegree : ∀ v, G.degree v ≤ h)
    (hexterior : ∀ i v, v ∈ U i → 4*(G.neighborFinset v \ U i).card ≤ 3*h)
    (v : V) : 4*(foreignGraph G U E c p a).degree v ≤ 3*h := by
  by_cases hvE : v ∈ E
  · exact (foreignGraph_degree_exceptional G U E c p a hdisjoint hUE hcount
      v hvE (hmax v hvE).1 (hmax v hvE).2).trans (Nat.mul_le_mul_left _ (hdegree v))
  · by_cases hvU : ∃ i, v ∈ U i
    · obtain ⟨i,hi⟩ := hvU
      exact (Nat.mul_le_mul_left 4 (foreignGraph_degree_core G U E c p a hUE i v hi)).trans
        (hexterior i v hi)
    · rw [foreignGraph_degree_other G U E c p a v hvE (by simpa using hvU)]
      exact Nat.zero_le _

/-- The actual original host-edge copies belonging to the foreign graph. -/
noncomputable def foreignEdges (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V)
    (E : Finset V) (c : V → C) (p : I → C) (a : V → I) : Finset G.edgeSet :=
  univ.filter (fun e => e.val ∈ (foreignGraph G U E c p a).edgeSet)

omit [Fintype I] in
@[simp] theorem mem_foreignEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (e : G.edgeSet) :
    e ∈ foreignEdges G U E c p a ↔ e.val ∈ (foreignGraph G U E c p a).edgeSet := by
  simp [foreignEdges]

omit [Fintype V] [Fintype I] in
/-- With the assignment fixed, passing to a subgraph just intersects the
foreign graph with that subgraph. -/
theorem foreignGraph_subgraph_eq (G R : SimpleGraph V) (hR : R ≤ G)
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I) :
    foreignGraph R U E c p a = R ⊓ foreignGraph G U E c p a := by
  ext u v
  constructor
  · intro huv
    exact ⟨huv.1,hR huv.1,huv.2⟩
  · intro huv
    exact ⟨huv.1,huv.2.2⟩

omit [Fintype I] in
/-- On original host-edge copies, the current foreign edges are exactly
the phase-start foreign edges that survive the deletions. -/
theorem foreignEdges_surviving (G R : SimpleGraph V) [DecidableRel G.Adj]
    (hR : R ≤ G) (U : I → Finset V) (E : Finset V)
    (c : V → C) (p : I → C) (a : V → I) :
    (foreignEdges G U E c p a).filter (fun e => e.val ∈ R.edgeSet) =
      (univ : Finset G.edgeSet).filter
        (fun e => e.val ∈ (foreignGraph R U E c p a).edgeSet) := by
  ext e
  rw [foreignGraph_subgraph_eq G R hR]
  simp only [mem_filter,mem_univ,true_and,mem_foreignEdges,SimpleGraph.edgeSet_inf,Set.mem_inter_iff]
  exact and_comm

omit [Fintype I] in
theorem foreignEdges_incidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (v : V) :
    ((foreignEdges G U E c p a).filter (fun e => v ∈ e.val)).card =
      (foreignGraph G U E c p a).degree v := by
  have heq : ((foreignEdges G U E c p a).filter (fun e => v ∈ e.val)).card =
      MatchingProbability.incidentCount (foreignEdges G U E c p a) v := by
    simp only [MatchingProbability.incidentCount,FractionalMatching.incident_iff]
  rw [heq]
  simpa only [foreignEdges] using SafePrescription.incidentCount_subgraph_edges G
    (foreignGraph G U E c p a) (foreignGraph_le G U E c p a) v

omit [Fintype I] in
/-- The actual host-edge restriction has exceptional vertices on one side
and core vertices on the other. -/
theorem foreignEdges_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hUE : ∀ i, Disjoint (U i) E) :
    ((Multigraph.ofSimpleGraph G).restrictEdges (foreignEdges G U E c p a)).IsBipartite := by
  refine ⟨fun v => decide (v ∈ E),?_⟩
  intro e
  change decide (FractionalMatching.firstEnd e.val ∈ E) ≠
    decide (FractionalMatching.secondEnd e.val ∈ E)
  have he : e.val.val ∈ (foreignGraph G U E c p a).edgeSet := (mem_filter.mp e.property).2
  rw [← FractionalMatching.edge_eq e.val] at he
  change (foreignGraph G U E c p a).Adj
    (FractionalMatching.firstEnd e.val) (FractionalMatching.secondEnd e.val) at he
  rcases he.2 with ⟨hv,i,hw,_⟩ | ⟨hw,i,hv,_⟩
  · have hn : FractionalMatching.secondEnd e.val ∉ E :=
      fun h => disjoint_left.mp (hUE i) hw h
    simp [hv,hn]
  · have hn : FractionalMatching.firstEnd e.val ∉ E :=
      fun h => disjoint_left.mp (hUE i) hv h
    simp [hw,hn]

/-- Fresh maximizing assignments and actual König classes for a phase.
The matchings partition precisely the currently foreign host edges. -/
theorem exists_assignment_color_classes [Nonempty I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (hcount : Fintype.card I ≤ 4)
    (hrepresented : ∀ v ∈ E, ∃ i, p i = c v)
    (h : ℕ) (hdegree : ∀ v, G.degree v ≤ h)
    (hexterior : ∀ i v, v ∈ U i → 4*(G.neighborFinset v \ U i).card ≤ 3*h) :
    ∃ a : V → I,
      (∀ v ∈ E, p (a v) = c v ∧
        ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
          (coreNeighbors G U v (a v)).card) ∧
      ∃ M : Fin (3*h/4) → G.Subgraph,
        (∀ i, (M i).IsMatching) ∧
        Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        univ.biUnion (fun i => MatchingProbability.matchingEdges (M i)) = foreignEdges G U E c p a ∧
        BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) univ =
          (Compression.selectedMatching G (foreignEdges G U E c p a)).spanningCoe := by
  obtain ⟨a,ha⟩ := exists_max_assignment G U E c p hrepresented
  have hd (v : V) : 4*((foreignEdges G U E c p a).filter (fun e => v ∈ e.val)).card ≤ 3*h := by
    rw [foreignEdges_incidence]
    exact foreignGraph_degree_bound G U E c p a hdisjoint hUE hcount ha h hdegree hexterior v
  obtain ⟨_,M,hM,_,_,hdisj,hunion,hgraph⟩ :=
    ForeignColoring.exists_three_quarter_color_classes G (foreignEdges G U E c p a)
      (foreignEdges_bipartite G U E c p a hUE) h hd
  exact ⟨a,ha,M,hM,hdisj,hunion,hgraph⟩

omit [Fintype I] in
/-- An actual embedded core of degree at least `h-ε` bounds the number of
neighbours outside that core by `ε`. -/
theorem exterior_degree_le_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (h : ℕ) (ε : ℝ) (hregular : ∀ v, G.degree v = h)
    (hcore : ∀ v, (h : ℝ)-ε ≤ (H.degree v : ℝ)) (v : U) :
    ((G.neighborFinset v.val \ U).card : ℝ) ≤ ε := by
  have hsub : G.neighborFinset v.val \ U ⊆
      (G \ Replacement.lift U H).neighborFinset v.val := by
    intro w hw
    obtain ⟨hG,hwU⟩ := mem_sdiff.mp hw
    apply ((G \ Replacement.lift U H).mem_neighborFinset v.val w).mpr
    refine ⟨(G.mem_neighborFinset v.val w).mp hG,?_⟩
    exact fun h => hwU (Replacement.lift_adj_mem U H h).2
  have hle : (G.neighborFinset v.val \ U).card ≤ (G \ Replacement.lift U H).degree v.val := by
    rw [← (G \ Replacement.lift U H).card_neighborFinset_eq_degree]
    exact card_le_card hsub
  have hsum := BipartitePackingAccounting.degree_sdiff_add_of_le G
    (Replacement.lift U H) (Replacement.lift_le U H G hH) v.val
  rw [Replacement.lift_degree] at hsum
  have hreg := hregular v.val
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hsum hreg
  rw [hreg] at hsum
  have hsumNat : (G \ Replacement.lift U H).degree v.val + H.degree v = h := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hsum
  have hsumR : ((G \ Replacement.lift U H).degree v.val : ℝ)+(H.degree v : ℝ) = h := by
    exact_mod_cast hsumNat
  have hleR : ((G.neighborFinset v.val \ U).card : ℝ) ≤
      ((G \ Replacement.lift U H).degree v.val : ℝ) := by exact_mod_cast hle
  have hbound := hcore v
  linarith

/-- The phase construction with its exterior-degree premise discharged by
the actual embedded near-regular cores. -/
theorem exists_assignment_color_classes_of_cores [Nonempty I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (E : Finset V) (c : V → C) (p : I → C)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUE : ∀ i, Disjoint (U i) E) (hcount : Fintype.card I ≤ 4)
    (hrepresented : ∀ v ∈ E, ∃ i, p i = c v)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (h : ℕ) (ε : ℝ) (hregular : ∀ v, G.degree v = h)
    (hcore : ∀ i v, (h : ℝ)-ε ≤ ((H i).degree v : ℝ))
    (hsmall : 4*ε ≤ 3*h) :
    ∃ a : V → I,
      (∀ v ∈ E, p (a v) = c v ∧
        ∀ i, p i = c v → (coreNeighbors G U v i).card ≤
          (coreNeighbors G U v (a v)).card) ∧
      ∃ M : Fin (3*h/4) → G.Subgraph,
        (∀ i, (M i).IsMatching) ∧
        Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        univ.biUnion (fun i => MatchingProbability.matchingEdges (M i)) = foreignEdges G U E c p a ∧
        BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) univ =
          (Compression.selectedMatching G (foreignEdges G U E c p a)).spanningCoe := by
  apply exists_assignment_color_classes G U E c p hdisjoint hUE hcount hrepresented
    h (fun v => (hregular v).le)
  intro i v hv
  have hex := exterior_degree_le_error G (U i) (H i) (hH i) h ε hregular (hcore i) ⟨v,hv⟩
  have hbound : 4*((G.neighborFinset v \ U i).card : ℝ) ≤ 3*h := by linarith
  exact_mod_cast hbound

end Overfull.ForeignAssignment
