import Overfull.Compression.SelectedEdges
import Overfull.MultigraphColoring
import Overfull.SparseColoring

namespace Overfull.ForeignColoring

open Finset Classical SimpleGraph MatchingProbability Compression
open BipartitePackingAccounting

variable {V : Type*}

/-- A matching of actual host-edge copies gives the corresponding matching
subgraph, with exactly the selected endpoints as its vertices. -/
theorem selectedMatching_isMatching_of_edge_copies (G : SimpleGraph V)
    (A : Finset G.edgeSet) (hA : (Multigraph.ofSimpleGraph G).IsMatching A) :
    (selectedMatching G A).IsMatching := by
  rintro v ⟨w,hvw,he⟩
  refine ⟨w,⟨hvw,he⟩,?_⟩
  rintro z ⟨hvz,hf⟩
  have heq := hA (⟨s(v,z),hvz⟩ : G.edgeSet) hf
    (⟨s(v,w),hvw⟩ : G.edgeSet) he v (by simp [Multigraph.ofSimpleGraph])
    (by simp [Multigraph.ofSimpleGraph])
  have heq' : s(v,z) = s(v,w) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp heq' with ⟨_,hzw⟩ | ⟨hvw,hzv⟩
  · exact hzw
  · exact hzv.trans hvw

theorem selectedMatching_spanning_disjoint (G : SimpleGraph V)
    (A B : Finset G.edgeSet) (hAB : Disjoint A B) :
    Disjoint (selectedMatching G A).spanningCoe (selectedMatching G B).spanningCoe := by
  apply disjoint_iff_inf_le.mpr
  rintro u v ⟨⟨huv,ha⟩,⟨_,hb⟩⟩
  exact disjoint_left.mp hAB ha hb

/-- Map a color class of the restricted graph back to its original host
edge copies. The map is injective. -/
noncomputable def hostColorClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k)
    (i : Fin k) : Finset G.edgeSet :=
  (c.colorClass i).image Subtype.val

theorem mem_hostColorClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k)
    (i : Fin k) (e : G.edgeSet) :
    e ∈ hostColorClass G A c i ↔ ∃ he : e ∈ A, c.color ⟨e,he⟩ = i := by
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact ⟨f.property,(mem_filter.mp hf).2⟩
  · rintro ⟨he,hc⟩
    exact mem_image.mpr ⟨⟨e,he⟩,mem_filter.mpr ⟨mem_univ _,hc⟩,rfl⟩

theorem hostColorClass_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k)
    (i : Fin k) : hostColorClass G A c i ⊆ A := by
  intro e he
  exact ((mem_hostColorClass G A c i e).mp he).choose

theorem hostColorClass_isMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k)
    (i : Fin k) : (Multigraph.ofSimpleGraph G).IsMatching (hostColorClass G A c i) := by
  intro e he f hf v hev hfv
  obtain ⟨heA,hei⟩ := (mem_hostColorClass G A c i e).mp he
  obtain ⟨hfA,hfi⟩ := (mem_hostColorClass G A c i f).mp hf
  have hef : (⟨e,heA⟩ : A) = ⟨f,hfA⟩ := c.proper (hei.trans hfi.symm) hev hfv
  exact congrArg Subtype.val hef

theorem hostColorClass_pairwise_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k) :
    Pairwise (fun i j => Disjoint (hostColorClass G A c i) (hostColorClass G A c j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨heA,hei⟩ := (mem_hostColorClass G A c i e).mp he
  obtain ⟨_,hej⟩ := (mem_hostColorClass G A c j e).mp hf
  exact hij (hei.symm.trans hej)

theorem hostColorClass_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) {k : ℕ}
    (c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k) :
    univ.biUnion (hostColorClass G A c) = A := by
  ext e
  constructor
  · intro he
    obtain ⟨i,_,hei⟩ := mem_biUnion.mp he
    exact hostColorClass_subset G A c i hei
  · intro he
    refine mem_biUnion.mpr ⟨c.color ⟨e,he⟩,mem_univ _,?_⟩
    exact (mem_hostColorClass G A c _ e).mpr ⟨he,rfl⟩

theorem selectedMatching_edgeUnion (G : SimpleGraph V) {k : ℕ}
    (A : Fin k → Finset G.edgeSet) :
    edgeUnion (fun i => (selectedMatching G (A i)).spanningCoe) univ =
      (selectedMatching G (univ.biUnion A)).spanningCoe := by
  ext u v
  constructor
  · rintro ⟨i,hi,huv,he⟩
    exact ⟨huv,mem_biUnion.mpr ⟨i,hi,he⟩⟩
  · rintro ⟨huv,he⟩
    obtain ⟨i,hi,hei⟩ := mem_biUnion.mp he
    exact ⟨i,hi,huv,hei⟩

variable [Fintype V]

/-- König's coloring produces actual pairwise edge-disjoint matching
subgraphs partitioning exactly the specified host edges. -/
theorem exists_color_classes (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet)
    (hA : ((Multigraph.ofSimpleGraph G).restrictEdges A).IsBipartite)
    (k : ℕ) (hdegree : ∀ v, (A.filter (fun e => v ∈ e.val)).card ≤ k) :
    ∃ c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring k,
      ∃ M : Fin k → G.Subgraph,
        (∀ i, (M i).IsMatching) ∧
        (∀ i, matchingEdges (M i) = hostColorClass G A c i) ∧
        (∀ i, (M i).edgeSet.ncard = (hostColorClass G A c i).card) ∧
        Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        univ.biUnion (fun i => matchingEdges (M i)) = A ∧
        edgeUnion (fun i => (M i).spanningCoe) univ = (selectedMatching G A).spanningCoe := by
  have hdegree' : ∀ v, ((Multigraph.ofSimpleGraph G).restrictEdges A).degree v ≤ k := by
    intro v
    rw [Multigraph.restrictEdges_degree]
    simpa only [Multigraph.incidenceEdges,Multigraph.ofSimpleGraph,
      Finset.inter_filter,Finset.inter_univ] using hdegree v
  obtain ⟨c⟩ := Multigraph.exists_edgeColoring_of_bipartite
    ((Multigraph.ofSimpleGraph G).restrictEdges A) hA k hdegree'
  let M : Fin k → G.Subgraph := fun i => selectedMatching G (hostColorClass G A c i)
  have hM (i : Fin k) : (M i).IsMatching :=
    selectedMatching_isMatching_of_edge_copies G _ (hostColorClass_isMatching G A c i)
  have hEdges (i : Fin k) : matchingEdges (M i) = hostColorClass G A c i :=
    selectedMatching_edges G _
  refine ⟨c,M,hM,hEdges,?_,?_,?_,?_⟩
  · intro i
    exact selectedMatching_edgeSet_card G _
  · intro i j hij
    exact selectedMatching_spanning_disjoint G _ _ (hostColorClass_pairwise_disjoint G A c hij)
  · simp_rw [hEdges]
    exact hostColorClass_union G A c
  · change edgeUnion (fun i => (selectedMatching G (hostColorClass G A c i)).spanningCoe) univ = _
    rw [selectedMatching_edgeUnion,hostColorClass_union]

/-- The integer form of the three-quarter degree bound gives the exact
phase horizon, including the zero-color case. -/
theorem exists_three_quarter_color_classes (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet)
    (hA : ((Multigraph.ofSimpleGraph G).restrictEdges A).IsBipartite)
    (h₀ : ℕ) (hdegree : ∀ v, 4*(A.filter (fun e => v ∈ e.val)).card ≤ 3*h₀) :
    ∃ c : ((Multigraph.ofSimpleGraph G).restrictEdges A).EdgeColoring (3*h₀/4),
      ∃ M : Fin (3*h₀/4) → G.Subgraph,
        (∀ i, (M i).IsMatching) ∧
        (∀ i, matchingEdges (M i) = hostColorClass G A c i) ∧
        (∀ i, (M i).edgeSet.ncard = (hostColorClass G A c i).card) ∧
        Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        univ.biUnion (fun i => matchingEdges (M i)) = A ∧
        edgeUnion (fun i => (M i).spanningCoe) univ = (selectedMatching G A).spanningCoe := by
  apply exists_color_classes G A hA (3*h₀/4)
  intro v
  have hv := hdegree v
  omega

end Overfull.ForeignColoring
