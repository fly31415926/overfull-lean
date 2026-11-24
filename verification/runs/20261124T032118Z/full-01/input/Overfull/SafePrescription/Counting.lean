import Overfull.ForceMatching.Cuts
import Overfull.Replacement.Graph

namespace Overfull.SafePrescription

open Finset Classical MatchingProbability FractionalMatching

variable {V C : Type*} [Fintype V]

/-- The actual subgraph consisting of the edges crossing a shore. -/
def cutGraph (G : SimpleGraph V) (X : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ X) ≠ (v ∈ X))
  symm := by
    rintro u v ⟨hG,hX⟩
    exact ⟨hG.symm,Ne.symm hX⟩
  loopless := by intro v h; exact h.2 rfl

theorem incidentCount_subgraph_edges (G R : SimpleGraph V) [DecidableRel G.Adj]
    (hR : R ≤ G) (v : V) :
    incidentCount ((univ : Finset G.edgeSet).filter (fun e => e.val ∈ R.edgeSet)) v =
      R.degree v := by
  let A := ((univ : Finset G.edgeSet).filter (fun e => e.val ∈ R.edgeSet)).filter
    (fun e => firstEnd e = v ∨ secondEnd e = v)
  have hA : A.image Subtype.val = R.incidenceFinset v := by
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      obtain ⟨hfR,hfv⟩ := mem_filter.mp hf
      exact (R.mem_incidenceFinset v f.val).mpr
        ⟨(mem_filter.mp hfR).2,(incident_iff f v).mpr hfv⟩
    · intro he
      obtain ⟨heR,hev⟩ := (R.mem_incidenceFinset v e).mp he
      have heG : e ∈ G.edgeSet := SimpleGraph.edgeSet_mono hR heR
      refine mem_image.mpr ⟨⟨e,heG⟩,?_,rfl⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,heR⟩,
        (incident_iff ⟨e,heG⟩ v).mp hev⟩
  change A.card = R.degree v
  rw [← card_image_of_injective A Subtype.val_injective,hA]
  exact R.card_incidenceFinset_eq_degree v

theorem cutGraph_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (v : V) :
    (cutGraph G X).degree v = incidentCount (cutEdges (univ : Finset G.edgeSet) X) v := by
  have hR : cutGraph G X ≤ G := fun _ _ h => h.1
  have heq : (univ : Finset G.edgeSet).filter
      (fun e => e.val ∈ (cutGraph G X).edgeSet) = cutEdges univ X := by
    ext e
    simp only [mem_filter,mem_univ,true_and,cutEdges,Lovasz.BMatch.cut]
    rw [← edge_eq e]
    change (G.Adj (firstEnd e) (secondEnd e) ∧
      ((firstEnd e ∈ X) ≠ (secondEnd e ∈ X))) ↔
      ((firstEnd e ∈ X) ≠ (secondEnd e ∈ X))
    exact and_iff_right (endpoint_adj e)
  rw [← heq]
  exact (incidentCount_subgraph_edges G (cutGraph G X) hR v).symm

theorem cut_incident_eq_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (v : V) :
    incidentCount (cutEdges (univ : Finset G.edgeSet) X) v =
      ((G.neighborFinset v).filter (fun w => (v ∈ X) ≠ (w ∈ X))).card := by
  rw [← cutGraph_degree G X v,← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [cutGraph]

/-- At a core vertex, every crossing edge lies outside the embedded core. -/
theorem cut_incident_core_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (U X : Finset V) (H : SimpleGraph U) (hH : H ≤ G.induce (U : Set V))
    (hwhole : U ⊆ X ∨ Disjoint U X) (h : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = h)
    (hdegree : ∀ v, (h : ℝ)-a ≤ (H.degree v : ℝ)) (v : U) :
    (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v.val : ℝ) ≤ a := by
  have hcut : cutGraph G X ≤ G \ Replacement.lift U H := by
    intro u w huw
    refine ⟨huw.1,?_⟩
    intro hcore
    obtain ⟨hu,hw⟩ := Replacement.lift_adj_mem U H hcore
    apply huw.2
    apply propext
    rcases hwhole with hh | hh
    · exact iff_of_true (hh hu) (hh hw)
    · exact iff_of_false (fun hX => disjoint_left.mp hh hu hX)
        (fun hX => disjoint_left.mp hh hw hX)
  have hle := (cutGraph G X).degree_le_of_le (v := v.val) hcut
  have hsum := BipartitePackingAccounting.degree_sdiff_add_of_le G
    (Replacement.lift U H) (Replacement.lift_le U H G hH) v.val
  rw [Replacement.lift_degree] at hsum
  have hreg := hregular v.val
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hsum hreg
  rw [hreg] at hsum
  rw [cutGraph_degree] at hle
  have hleR : (incidentCount (cutEdges (univ : Finset G.edgeSet) X) v.val : ℝ) ≤
      ((G \ Replacement.lift U H).degree v.val : ℝ) := by exact_mod_cast hle
  have hsumR : ((G \ Replacement.lift U H).degree v.val : ℝ)+(H.degree v : ℝ) = h := by
    have hsumNat : (G \ Replacement.lift U H).degree v.val + H.degree v = h := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hsum
    exact_mod_cast hsumNat
  have hd := hdegree v
  linarith

/-- At an unmarked vertex, a crossing edge either meets the marked set
or goes to another cluster. -/
theorem cut_incident_cluster_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → C) (Z0 X : Finset V) (v : V) (hv : v ∉ Z0)
    (hwhole : ∀ u w, u ∉ Z0 → w ∉ Z0 → c u = c w → (u ∈ X ↔ w ∈ X)) :
    incidentCount (cutEdges (univ : Finset G.edgeSet) X) v ≤
      Z0.card + ((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card := by
  rw [cut_incident_eq_neighbors]
  have hsub : (G.neighborFinset v).filter (fun w => (v ∈ X) ≠ (w ∈ X)) ⊆
      Z0 ∪ (G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v) := by
    intro w hw
    obtain ⟨hwG,hwX⟩ := mem_filter.mp hw
    by_cases hwZ : w ∈ Z0
    · exact mem_union_left _ hwZ
    · apply mem_union_right
      refine mem_filter.mpr ⟨hwG,hwZ,?_⟩
      intro hc
      exact hwX (propext (hwhole v w hv hwZ hc.symm))
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- Neighbor counting with the exceptional set and other clusters removed. -/
theorem same_cluster_neighbors_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z Z0 : Finset V) (hZ0 : Z0 ⊆ Z) (c : V → C) (v : V) :
    G.degree v ≤
      ({w | G.Adj v w ∧ w ∉ Z ∧ c v = c w} : Set V).ncard + Z.card +
      ((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card := by
  let A := (G.neighborFinset v).filter (fun w => w ∉ Z ∧ c v = c w)
  let B := (G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)
  have hsub : G.neighborFinset v ⊆ (A ∪ Z) ∪ B := by
    intro w hw
    by_cases hwZ : w ∈ Z
    · exact mem_union_left _ (mem_union_right _ hwZ)
    · by_cases hc : c v = c w
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw,hwZ,hc⟩))
      · exact mem_union_right _ (mem_filter.mpr
          ⟨hw,(fun h => hwZ (hZ0 h)),Ne.symm hc⟩)
  have hA : A.card = ({w | G.Adj v w ∧ w ∉ Z ∧ c v = c w} : Set V).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [A]
  have hcard := card_le_card hsub
  have hfirst := card_union_le A Z
  have hsecond := card_union_le (A ∪ Z) B
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  rw [← hA]
  change G.degree v ≤ A.card + Z.card + B.card
  omega

/-- The cover by cores identifies the neighbors counted in the preceding
partition with actual vertices of the cores in the same cluster. -/
theorem same_cluster_core_neighbors_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Type*} (U : I → Finset V) (Z Z0 : Finset V) (hZ0 : Z0 ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (c : V → C) (v : V) :
    G.degree v ≤
      ((G.neighborFinset v).filter (fun w => (∃ i, w ∈ U i) ∧ c w = c v)).card +
      Z.card + ((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card := by
  let A := (G.neighborFinset v).filter (fun w => (∃ i, w ∈ U i) ∧ c w = c v)
  let B := (G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)
  have hsub : G.neighborFinset v ⊆ (A ∪ Z) ∪ B := by
    intro w hw
    by_cases hwZ : w ∈ Z
    · exact mem_union_left _ (mem_union_right _ hwZ)
    · obtain ⟨i,hi⟩ := (hcover w).resolve_left hwZ
      by_cases hc : c w = c v
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw,⟨i,hi⟩,hc⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hw,(fun h => hwZ (hZ0 h)),hc⟩)
  have hcard := card_le_card hsub
  have hfirst := card_union_le A Z
  have hsecond := card_union_le (A ∪ Z) B
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  dsimp only [A,B] at hfirst hsecond hcard
  omega

end Overfull.SafePrescription
