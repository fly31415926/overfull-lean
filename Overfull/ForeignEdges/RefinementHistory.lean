import Overfull.ForeignEdges.SmallCutRefinement

/-!
# Actual recorded-cut histories through refinement

The empty history starts with constant labels.  A refinement appends its
actual current graph and cut shore, then transports the complete shore-bit
equality relation through the constructed `Fin 4` encoding.  Edge deletions
preserve the recorded host containments.  The number of recorded cuts and
the accumulated marked set are bounded by the actual occupied core groups.
-/

namespace Overfull.ForeignRefinement

open Finset Classical SimpleGraph SafePrescription MatchingProbability FractionalMatching
open scoped BigOperators

variable {V C D I : Type*}

/-- Counting selected host copies agrees with counting edges of the
actual intercluster subgraph. -/
theorem clusterCrossingEdges_card_eq_graph [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → C) (Z₀ : Finset V) :
    (clusterCrossingEdges G c Z₀).card = (clusterCrossingGraph G c Z₀).edgeSet.ncard := by
  classical
  have hs : Subtype.val '' (clusterCrossingEdges G c Z₀ : Set G.edgeSet) =
      (clusterCrossingGraph G c Z₀).edgeSet := by
    ext e
    constructor
    · rintro ⟨f,hf,rfl⟩
      rw [← edge_eq f]
      exact ⟨endpoint_adj f,(mem_filter.mp hf).2⟩
    · intro he
      have heG : e ∈ G.edgeSet := edgeSet_mono (show clusterCrossingGraph G c Z₀ ≤ G
        from fun _ _ h => h.1) he
      let f : G.edgeSet := ⟨e,heG⟩
      refine ⟨f,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
      change f.val ∈ (clusterCrossingGraph G c Z₀).edgeSet at he
      rw [← edge_eq f] at he
      exact he.2
  rw [← hs,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]

/-- For fixed labels and marks, deleting ambient edges cannot increase
the actual number of intercluster edges. -/
theorem clusterCrossingEdges_card_mono_graph [Fintype V]
    (R G : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel G.Adj]
    (c : V → C) (Z₀ : Finset V) (hRG : R ≤ G) :
    (clusterCrossingEdges R c Z₀).card ≤ (clusterCrossingEdges G c Z₀).card := by
  classical
  rw [clusterCrossingEdges_card_eq_graph,clusterCrossingEdges_card_eq_graph]
  exact Set.ncard_le_ncard (edgeSet_mono (fun _ _ h => ⟨hRG h.1,h.2⟩))

/-- The intercluster neighbor count at each vertex decreases under
ambient edge deletion with fixed labels and marks. -/
theorem filtered_neighbor_crossing_card_mono_graph [Fintype V]
    (R G : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel G.Adj]
    (c : V → C) (Z₀ : Finset V) (hRG : R ≤ G) (v : V) :
    ((R.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card ≤
      ((G.neighborFinset v).filter (fun w => w ∉ Z₀ ∧ c w ≠ c v)).card := by
  classical
  apply card_le_card
  intro w hw
  obtain ⟨hR,hw⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨(G.mem_neighborFinset v w).mpr (hRG ((R.mem_neighborFinset v w).mp hR)),hw⟩

/-- Actual graphs and shores, together with the exact equality relation of
their shore bits on the unmarked vertices.  No cut is charged in a graph
chosen after the cut was recorded. -/
structure CutHistory (k₀ : ℕ) (G : SimpleGraph V) (Z₀ : Finset V) (c : V → C) where
  length : ℕ
  recorded : Fin length → SimpleGraph V
  shores : Fin length → Finset V
  host_le : ∀ j, G ≤ recorded j
  cut_le : ∀ j, (cutGraph (recorded j) (shores j)).edgeSet.ncard ≤ 2*k₀
  label_eq : ∀ u v, u ∉ Z₀ → v ∉ Z₀ →
    (c u = c v ↔ ∀ j, (u ∈ shores j ↔ v ∈ shores j))

namespace CutHistory

variable {k₀ : ℕ} {G R : SimpleGraph V} {Z₀ Z₁ : Finset V} {c : V → C}

/-- The initial constant labeling carries no recorded cuts. -/
def initial (k₀ : ℕ) (G : SimpleGraph V) (Z₀ : Finset V) (q : C) :
    CutHistory k₀ G Z₀ (fun _ => q) where
  length := 0
  recorded := Fin.elim0
  shores := Fin.elim0
  host_le := by intro j; exact j.elim0
  cut_le := by intro j; exact j.elim0
  label_eq := by
    intro u v _ _
    exact ⟨fun _ j => Fin.elim0 j, fun _ => rfl⟩

/-- Deleting ambient edges keeps the original recorded hosts. -/
def mono_graph (A : CutHistory k₀ G Z₀ c) (hRG : R ≤ G) :
    CutHistory k₀ R Z₀ c where
  length := A.length
  recorded := A.recorded
  shores := A.shores
  host_le := fun j => hRG.trans (A.host_le j)
  cut_le := A.cut_le
  label_eq := A.label_eq

/-- Marking more vertices and re-encoding the remaining label equality
relation does not change the actual recorded cuts. -/
def relabel_marking (A : CutHistory k₀ G Z₀ c) (d : V → D)
    (hmarks : Z₀ ⊆ Z₁)
    (hlabels : ∀ u v, u ∉ Z₁ → v ∉ Z₁ → (d u = d v ↔ c u = c v)) :
    CutHistory k₀ G Z₁ d where
  length := A.length
  recorded := A.recorded
  shores := A.shores
  host_le := A.host_le
  cut_le := A.cut_le
  label_eq := by
    intro u v hu hv
    exact (hlabels u v hu hv).trans
      (A.label_eq u v (fun h => hu (hmarks h)) (fun h => hv (hmarks h)))

/-- Append the actual current graph and actual cut, retaining all old
shore bits and adding precisely the new bit. -/
noncomputable def append (A : CutHistory k₀ G Z₀ c) (X : Finset V)
    (hmarks : Z₀ ⊆ Z₁)
    (hcut : (cutGraph G X).edgeSet.ncard ≤ 2*k₀) :
    CutHistory k₀ G Z₁ (refineVertex c X) where
  length := A.length+1
  recorded := Fin.snoc A.recorded G
  shores := Fin.snoc A.shores X
  host_le := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last] using (le_refl G)
    · simpa only [Fin.snoc_castSucc] using A.host_le i
  cut_le := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last] using hcut
    · simpa only [Fin.snoc_castSucc] using A.cut_le i
  label_eq := by
    intro u v hu hv
    rw [refineVertex_eq_iff,
      A.label_eq u v (fun h => hu (hmarks h)) (fun h => hv (hmarks h))]
    constructor
    · rintro ⟨hold,hnew⟩ j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last] using hnew
      · simpa only [Fin.snoc_castSucc] using hold i
    · intro hall
      exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using hall i.castSucc,
        by simpa only [Fin.snoc_last] using hall (Fin.last A.length)⟩

/-- The separating recorded cut is derived from the maintained exact
shore-bit equality relation. -/
theorem separates (A : CutHistory k₀ G Z₀ c)
    (u v : V) (hu : u ∉ Z₀) (hv : v ∉ Z₀) (hne : c u ≠ c v) :
    ∃ j, (u ∈ A.shores j) ≠ (v ∈ A.shores j) := by
  classical
  by_contra hn
  apply hne
  apply (A.label_eq u v hu hv).mpr
  intro j
  have hj : (u ∈ A.shores j) = (v ∈ A.shores j) := by
    by_contra hj
    exact hn ⟨j,hj⟩
  exact Iff.of_eq hj

/-- Each current intercluster edge lies in an actual recorded cut in its
recorded host graph. -/
theorem edge_separated (A : CutHistory k₀ G Z₀ c)
    (u v : V) (hG : G.Adj u v) (hu : u ∉ Z₀) (hv : v ∉ Z₀) (hne : c u ≠ c v) :
    ∃ j, (cutGraph (A.recorded j) (A.shores j)).Adj u v := by
  obtain ⟨j,hj⟩ := A.separates u v hu hv hne
  exact ⟨j,A.host_le j hG,hj⟩

/-- Each actual recorded cut contributes at most `2*k₀` edges, so the
current crossing count is bounded at every history length. -/
theorem crossing_card_le [Fintype V] [DecidableRel G.Adj]
    (A : CutHistory k₀ G Z₀ c) :
    (clusterCrossingEdges G c Z₀).card ≤ A.length*(2*k₀) := by
  classical
  have hcount := clusterCrossingEdges_card_le_history G c Z₀ A.recorded A.shores
    A.host_le A.separates
  have hcut (j : Fin A.length) :
      cutCount (univ : Finset (A.recorded j).edgeSet) (A.shores j) ≤ 2*k₀ := by
    rw [← cutGraph_card]
    exact A.cut_le j
  have hsum : (∑ j, cutCount (univ : Finset (A.recorded j).edgeSet) (A.shores j)) ≤
      A.length*(2*k₀) := by
    simpa using sum_le_sum (s := univ) (fun j _ => hcut j)
  exact hcount.trans hsum

/-- The actual crossing-edge bound follows from the stored cuts and the
derived separation, without an additional separation hypothesis. -/
theorem crossing_card_le_six [Fintype V] [DecidableRel G.Adj]
    (A : CutHistory k₀ G Z₀ c) (hlength : A.length ≤ 3) :
    (clusterCrossingEdges G c Z₀).card ≤ 6*k₀ := by
  have hbound := A.crossing_card_le
  have hmul := Nat.mul_le_mul_right (2*k₀) hlength
  omega

end CutHistory

/-- The cut history and mark budget used by the outer process.  Each
recorded cut has strictly increased the actual occupied core-group count.
The mark threshold is fixed across the at most three refinements. -/
structure RefinementHistory [Fintype I] (k₀ : ℕ) (θ : ℝ) (initialMarked : Finset V)
    (G : SimpleGraph V) (Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4)
    extends CutHistory k₀ G Z₀ c where
  groups : length+1 ≤ (univ.image p).card
  initial_subset : initialMarked ⊆ Z₀
  marked_card : (Z₀.card : ℝ) ≤ initialMarked.card + (length : ℝ)*(1+12/θ)

namespace RefinementHistory

variable [Fintype I]
variable {k₀ : ℕ} {θ : ℝ} {initialMarked Z₀ : Finset V}
variable {G R : SimpleGraph V} {c : V → Fin 4} {p : I → Fin 4}

/-- The initial state has one occupied group, no cuts, and exactly its
initial marked set. -/
noncomputable def initial [Nonempty I] (k₀ : ℕ) (θ : ℝ) (initialMarked : Finset V)
    (G : SimpleGraph V) (q : Fin 4) :
    RefinementHistory k₀ θ initialMarked G initialMarked (fun _ => q) (fun _ : I => q) where
  toCutHistory := CutHistory.initial k₀ G initialMarked q
  groups := by
    change 1 ≤ (univ.image (fun _ : I => q)).card
    exact card_pos.mpr (univ_nonempty.image _)
  initial_subset := subset_rfl
  marked_card := by simp

/-- A matching-deletion prefix leaves this entire refinement history and
mark budget valid in its actual residual graph. -/
def mono_graph (A : RefinementHistory k₀ θ initialMarked G Z₀ c p) (hRG : R ≤ G) :
    RefinementHistory k₀ θ initialMarked R Z₀ c p where
  toCutHistory := A.toCutHistory.mono_graph hRG
  groups := A.groups
  initial_subset := A.initial_subset
  marked_card := A.marked_card

/-- Four actual cores permit at most three recorded refinements. -/
theorem length_le_three (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
    (hI : Fintype.card I ≤ 4) : A.length ≤ 3 := by
  have hgroups := A.groups
  have hcard : (univ.image p).card ≤ 4 := card_image_le.trans (by simpa using hI)
  omega

/-- The strict group-count conclusion of an actual refinement is
impossible once three cuts have already been recorded. -/
theorem length_lt_three_of_group_increase
    (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
    (q : I → Fin 4) (hI : Fintype.card I ≤ 4)
    (hinc : (univ.image p).card < (univ.image q).card) : A.length < 3 := by
  have hgroups := A.groups
  have hcard : (univ.image q).card ≤ 4 := card_image_le.trans (by simpa using hI)
  omega

/-- The current edge budget is a consequence of the constructed history. -/
theorem crossing_card_le_six [Fintype V] [DecidableRel G.Adj]
    (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
    (hI : Fintype.card I ≤ 4) :
    (clusterCrossingEdges G c Z₀).card ≤ 6*k₀ :=
  A.toCutHistory.crossing_card_le_six (A.length_le_three hI)

/-- Three refinements give the complete accumulated marked-set bound. -/
theorem marked_card_le (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
    (hI : Fintype.card I ≤ 4) (hθ : 0 < θ) :
    (Z₀.card : ℝ) ≤ initialMarked.card + 3*(1+12/θ) := by
  have hlength : (A.length : ℝ) ≤ 3 := by exact_mod_cast A.length_le_three hI
  have hcost : 0 ≤ 1+(12 : ℝ)/θ := by positivity
  exact A.marked_card.trans (add_le_add_left (mul_le_mul_of_nonneg_right hlength hcost) _)

/-- In the initially unmarked state this is the absolute marked-set
bound needed for the uniform safe-prescription constants. -/
theorem marked_card_le_of_initial_empty
    (A : RefinementHistory k₀ θ (∅ : Finset V) G Z₀ c p)
    (hI : Fintype.card I ≤ 4) (hθ : 0 < θ) :
    (Z₀.card : ℝ) ≤ 3*(1+12/θ) := by
  simpa using A.marked_card_le hI hθ

/-- The history records the actual refinement cut.  Its increased group
count first bounds the new pre-mark crossing graph, which then proves the
actual heavy-mark increment; neither conclusion is assumed as an input. -/
noncomputable def append [Fintype V] [DecidableRel G.Adj]
    (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z X : Finset V) (h : ℕ) (a ν τ : ℝ)
    (S : RefinementStep G U H Z Z₀ c p X h a ν τ (θ*k₀))
    (hI : Fintype.card I ≤ 4) (hZ₀ : Z₀ ⊆ Z) (hθ : 0 < θ) (hk : 0 < k₀)
    (hcut : cutCount (univ : Finset G.edgeSet) X ≤ 2*k₀) :
    RefinementHistory k₀ θ initialMarked G S.marked S.vertexLabel S.coreLabel := by
  classical
  have hcut' : (cutGraph G X).edgeSet.ncard ≤ 2*k₀ := by
    rw [cutGraph_card]
    exact hcut
  let B := A.toCutHistory.append X (show Z₀ ⊆ Z₀ ∪ S.moved from subset_union_left) hcut'
  have hgroups : B.length+1 ≤ (univ.image S.coreLabel).card := by
    have hold := A.groups
    have hinc := S.groups_increase
    change A.length+1+1 ≤ (univ.image S.coreLabel).card
    omega
  have hlength : B.length ≤ 3 := by
    have hcard : (univ.image S.coreLabel).card ≤ 4 :=
      card_image_le.trans (by simpa using hI)
    omega
  have hcross : (clusterCrossingEdges G (refineVertex c X) (Z₀ ∪ S.moved)).card ≤ 6*k₀ :=
    B.crossing_card_le_six hlength
  let D := B.relabel_marking S.vertexLabel S.marked_old S.label_eq
  refine {
    toCutHistory := D
    groups := hgroups
    initial_subset := A.initial_subset.trans (subset_union_left.trans S.marked_old)
    marked_card := ?_
  }
  have hbound := RefinementStep.marked_card_growth G U H Z Z₀ c p X h k₀ a ν τ θ
    S hZ₀ hθ hk hcross
  change (S.marked.card : ℝ) ≤ initialMarked.card + ((A.length+1 : ℕ) : ℝ)*(1+12/θ)
  calc
    _ ≤ (Z₀.card : ℝ)+1+12/θ := hbound
    _ ≤ initialMarked.card + (A.length : ℝ)*(1+12/θ)+1+12/θ := by
      linarith only [A.marked_card]
    _ = _ := by push_cast; ring

section AppendFacts

variable [Fintype V] [DecidableRel G.Adj]
variable (A : RefinementHistory k₀ θ initialMarked G Z₀ c p)
variable (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
variable (Z X : Finset V) (h : ℕ) (a ν τ : ℝ)
variable (S : RefinementStep G U H Z Z₀ c p X h a ν τ (θ*k₀))
variable (hI : Fintype.card I ≤ 4) (hZ₀ : Z₀ ⊆ Z) (hθ : 0 < θ) (hk : 0 < k₀)
variable (hcut : cutCount (univ : Finset G.edgeSet) X ≤ 2*k₀)

/-- The appended history contains exactly one more actual cut. -/
@[simp] theorem append_length :
    (A.append U H Z X h a ν τ S hI hZ₀ hθ hk hcut).length = A.length+1 := rfl

/-- Every old recorded host is retained, and the appended host is the
actual ambient graph in which this refinement occurred. -/
theorem append_recorded :
    (A.append U H Z X h a ν τ S hI hZ₀ hθ hk hcut).recorded =
      Fin.snoc A.recorded G := rfl

/-- Every old shore is retained, and the appended shore is the actual
triggering shore of the supplied refinement step. -/
theorem append_shores :
    (A.append U H Z X h a ν τ S hI hZ₀ hθ hk hcut).shores =
      Fin.snoc A.shores X := rfl

end AppendFacts

/-- A natural-number marked budget follows directly from the history
constructed from an initially empty marked set. -/
theorem marked_card_le_nat
    (A : RefinementHistory k₀ θ (∅ : Finset V) G Z₀ c p)
    (hI : Fintype.card I ≤ 4) (hθ : 0 < θ) (t₀ : ℕ)
    (hbudget : 3*(1+12/θ) ≤ (t₀ : ℝ)) : Z₀.card ≤ t₀ := by
  exact_mod_cast (A.marked_card_le_of_initial_empty hI hθ).trans hbudget

end RefinementHistory

end Overfull.ForeignRefinement
