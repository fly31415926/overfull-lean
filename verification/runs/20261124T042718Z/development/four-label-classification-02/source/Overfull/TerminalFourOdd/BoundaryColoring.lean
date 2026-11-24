import Overfull.TerminalFourOdd.Decomposition
import Overfull.BoundaryExtension.Full
import Overfull.NativeTerminal.ColoringGlue

/-!
# Consistent boundary colors from the actual primary matchings

Every joining copy receives the unique index of its primary matching.
Restriction to any part gives the same prescribed label on a shared copy,
and each boundary color class has exactly its original cut cardinality.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd BoundaryExtension

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq I]
variable (G : Multigraph V E) (label : V → I) (k : ℕ) (M : Fin k → Finset E)
variable (hcover : univ.biUnion M = joiningCopies G label)

private theorem exists_primary_index (e : joiningCopies G label) : ∃ j, e.val ∈ M j := by
  have he : e.val ∈ univ.biUnion M := by rw [hcover]; exact e.property
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp he
  exact ⟨j, hj⟩

def primaryIndex (e : joiningCopies G label) : Fin k :=
  (exists_primary_index G label k M hcover e).choose

theorem primaryIndex_mem (e : joiningCopies G label) :
    e.val ∈ M (primaryIndex G label k M hcover e) :=
  (exists_primary_index G label k M hcover e).choose_spec

theorem primaryIndex_eq_iff
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (e : joiningCopies G label) (j : Fin k) :
    primaryIndex G label k M hcover e = j ↔ e.val ∈ M j := by
  constructor
  · intro heq
    simpa only [heq] using primaryIndex_mem G label k M hcover e
  · intro he
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (primaryIndex_mem G label k M hcover e) he

def primaryBoundaryColoring (i : I)
    (hM : ∀ j, G.IsMatching (M j)) : BoundaryColoring G (labelShore label {i}) k where
  color e := primaryIndex G label k M hcover
    ⟨e.val, cut_labelShore_subset_joining G label {i}
      ((G.mem_cutOn univ _ _).mpr ⟨mem_univ _, (G.mem_cutEdges _ _).mp e.property⟩)⟩
  proper := by
    intro e f v hc hev hfv
    apply Subtype.ext
    apply hM (primaryIndex G label k M hcover
      ⟨e.val, cut_labelShore_subset_joining G label {i}
        ((G.mem_cutOn univ _ _).mpr ⟨mem_univ _, (G.mem_cutEdges _ _).mp e.property⟩)⟩)
      e.val (primaryIndex_mem G label k M hcover _) f.val
    · rw [hc]
      exact primaryIndex_mem G label k M hcover _
    · exact hev
    · exact hfv

theorem primaryBoundaryColoring_color_eq_iff (i : I)
    (hM : ∀ j, G.IsMatching (M j))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (e : G.cutEdges (labelShore label {i})) (j : Fin k) :
    (primaryBoundaryColoring G label k M hcover i hM).color e = j ↔ e.val ∈ M j :=
  primaryIndex_eq_iff G label k M hcover hdisj _ j

theorem primaryBoundaryColoring_class_image (i : I)
    (hM : ∀ j, G.IsMatching (M j))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j))) (j : Fin k) :
    ((primaryBoundaryColoring G label k M hcover i hM).classEdges j).image Subtype.val =
      G.cutOn (M j) (labelShore label {i}) := by
  ext e
  simp only [mem_image, BoundaryColoring.mem_classEdges, Multigraph.mem_cutOn]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(primaryBoundaryColoring_color_eq_iff G label k M hcover i hM hdisj f j).mp hf,
      (G.mem_cutEdges _ _).mp f.property⟩
  · rintro ⟨heM, hecut⟩
    let f : G.cutEdges (labelShore label {i}) := ⟨e, (G.mem_cutEdges _ _).mpr hecut⟩
    exact ⟨f, (primaryBoundaryColoring_color_eq_iff G label k M hcover i hM hdisj f j).mpr heM, rfl⟩

theorem primaryBoundaryColoring_class_card (i : I)
    (hM : ∀ j, G.IsMatching (M j))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j))) (j : Fin k) :
    ((primaryBoundaryColoring G label k M hcover i hM).classEdges j).card =
      (G.cutOn (M j) (labelShore label {i})).card := by
  rw [← primaryBoundaryColoring_class_image G label k M hcover i hM hdisj j,
    card_image_of_injective _ Subtype.val_injective]

theorem primaryBoundaryColoring_singletonColors (i : I)
    (hM : ∀ j, G.IsMatching (M j))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j))) :
    (primaryBoundaryColoring G label k M hcover i hM).singletonColors =
      univ.filter (fun j => (G.cutOn (M j) (labelShore label {i})).card = 1) := by
  ext j
  simp only [BoundaryColoring.singletonColors, mem_filter, mem_univ, true_and,
    primaryBoundaryColoring_class_card G label k M hcover i hM hdisj j]

theorem primaryBoundaryColoring_agrees (i j : I)
    (hM : ∀ q, G.IsMatching (M q)) (e : E)
    (hi : e ∈ G.cutEdges (labelShore label {i}))
    (hj : e ∈ G.cutEdges (labelShore label {j})) :
    (primaryBoundaryColoring G label k M hcover i hM).color ⟨e,hi⟩ =
      (primaryBoundaryColoring G label k M hcover j hM).color ⟨e,hj⟩ := rfl

end Overfull.TerminalFourOdd
