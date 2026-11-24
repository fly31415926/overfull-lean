import Overfull.TerminalFourOdd.ProfileCounts
import Overfull.TerminalFourOdd.MultiGeometry
import Overfull.Terminal.CentralMatchings

/-! Actual shore geometry when every surviving primary has the same center. -/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd Multigraph Multi

abbrev LeafLabel (c : Fin 4) := {i : Fin 4 // i ≠ c}

def defaultLeaf (c : Fin 4) : LeafLabel c :=
  if hc : c = 0 then ⟨1, by omega⟩ else ⟨0, Ne.symm hc⟩

def leafLabel {V : Type*} (label : V → Fin 4) (c : Fin 4) (v : V) : LeafLabel c :=
  if hv : label v ≠ c then ⟨label v,hv⟩ else defaultLeaf c

@[simp] theorem leafLabel_card (c : Fin 4) : Fintype.card (LeafLabel c) = 3 := by
  change Fintype.card {i : Fin 4 // ¬ i = c} = 3
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  decide

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype E] in
theorem leaf_fiber (label : V → Fin 4) (c : Fin 4) (i : LeafLabel c) (v : V) :
    Multi.centralMap (labelShore label {c}) (leafLabel label c) v = Sum.inr i ↔
      v ∈ labelShore label {i.val} := by
  by_cases hv : label v = c
  · have hvi : label v ≠ i.val := by
      intro hi
      exact i.property (hi.symm.trans hv)
    simp [Multi.centralMap, mem_labelShore, hv, hvi]
  · simp [Multi.centralMap, mem_labelShore, leafLabel, hv, Subtype.ext_iff]

omit [Fintype E] in
theorem label_shores_disjoint (label : V → Fin 4) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (labelShore label {i}) (labelShore label {j}) := by
  apply disjoint_left.mpr
  intro v hi hj
  have hi' : label v = i := by simpa only [mem_labelShore, mem_singleton] using hi
  have hj' : label v = j := by simpa only [mem_labelShore, mem_singleton] using hj
  exact hij (hi'.symm.trans hj')

omit [Fintype E] in
theorem center_and_leaves_cover (label : V → Fin 4) (c : Fin 4) (v : V) :
    v ∈ labelShore label {c} ∨ ∃ i : LeafLabel c, v ∈ labelShore label {i.val} := by
  by_cases hv : label v = c
  · exact Or.inl (by simpa only [mem_labelShore, mem_singleton] using hv)
  · exact Or.inr ⟨⟨label v,hv⟩,by simp⟩

/-- A primary with three center crossings and at most three copies
consists exactly of those center crossings. -/
omit [Fintype E] in
theorem primary_eq_center_cut (G : Multigraph V E) (label : V → Fin 4)
    (M : Finset E) (c : Fin 4) (hsize : M.card ≤ 3)
    (hcut : (G.cutOn M (labelShore label {c})).card = 3) :
    G.cutOn M (labelShore label {c}) = M := by
  apply eq_of_subset_of_card_le (filter_subset _ _)
  rw [hcut]
  exact hsize

/-- No joining edge outside the center survives a common-center primary
family; every edge with both endpoints outside has equal leaf labels. -/
theorem common_center_exterior_labels (G : Multigraph V E) (label : V → Fin 4)
    (k : ℕ) (M : Fin k → Finset E) (c : Fin 4)
    (hcover : univ.biUnion M = joiningCopies G label)
    (hsize : ∀ j, (M j).card ≤ 3)
    (hcut : ∀ j, (G.cutOn (M j) (labelShore label {c})).card = 3) :
    ∀ e, G.firstEnd e ∉ labelShore label {c} → G.secondEnd e ∉ labelShore label {c} →
      leafLabel label c (G.firstEnd e) = leafLabel label c (G.secondEnd e) := by
  intro e hf hs
  have heq : label (G.firstEnd e) = label (G.secondEnd e) := by
    by_contra hne
    have hj : e ∈ joiningCopies G label := (mem_joiningCopies G label e).mpr hne
    rw [← hcover] at hj
    obtain ⟨j,_,hej⟩ := mem_biUnion.mp hj
    have hc : e ∈ G.cutOn (M j) (labelShore label {c}) := by
      rw [primary_eq_center_cut G label (M j) c (hsize j) (hcut j)]
      exact hej
    exact ((G.mem_cutOn _ _ _).mp hc).2 (propext (iff_of_false hf hs))
  simp only [leafLabel, heq]

theorem common_center_leaf_cutSize (G : Multigraph V E) (label : V → Fin 4)
    (k : ℕ) (M : Fin k → Finset E) (c : Fin 4)
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hcover : univ.biUnion M = joiningCopies G label)
    (hprofile : ∀ j, PrimaryProfile G label (M j))
    (hcut : ∀ j, (G.cutOn (M j) (labelShore label {c})).card = 3)
    (i : LeafLabel c) : G.cutSize (labelShore label {i.val}) = k := by
  apply Terminal.cutSize_of_matching_partition G (labelShore label {i.val}) k M hdisj
  · intro e he
    have hj : e ∈ joiningCopies G label := cut_labelShore_subset_joining G label {i.val}
      ((G.mem_cutOn univ _ _).mpr ⟨mem_univ _, (G.mem_cutEdges _ _).mp he⟩)
    rw [← hcover] at hj
    obtain ⟨j,_,hej⟩ := mem_biUnion.mp hj
    exact ⟨j,hej⟩
  · intro j
    have hset : M j ∩ G.cutEdges (labelShore label {i.val}) =
        G.cutOn (M j) (labelShore label {i.val}) := by
      ext e
      simp only [mem_inter, Multigraph.mem_cutEdges, Multigraph.mem_cutOn]
    rw [hset]
    rcases (hprofile j).cut_one_or_three i.val with hs | ht
    · exact hs
    · exact (i.property ((hprofile j).triple_unique ht (hcut j))).elim

end Overfull.TerminalFourOdd
