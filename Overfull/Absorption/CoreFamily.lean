import Overfull.Absorption.Core

/-!
# Absorbing assigned vertices into a family of actual cores

The absorbed sets form the assignment fibers of one actual subset of the
exceptional vertices. These lemmas keep the ambient partition explicit.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- The vertices in the selected set assigned to core `i`. -/
def absorbedAt (B : Finset V) (assignment : V → I) (i : I) : Finset V :=
  B.filter (fun v => assignment v = i)

omit [DecidableEq V] in
@[simp] theorem mem_absorbedAt (B : Finset V) (assignment : V → I) (i : I) (v : V) :
    v ∈ absorbedAt B assignment i ↔ v ∈ B ∧ assignment v = i := by
  simp [absorbedAt]

omit [DecidableEq V] in
theorem absorbedAt_subset (B : Finset V) (assignment : V → I) (i : I) :
    absorbedAt B assignment i ⊆ B := filter_subset _ _

omit [DecidableEq V] in
theorem absorbedAt_card_le (B : Finset V) (assignment : V → I) (i : I) :
    (absorbedAt B assignment i).card ≤ B.card :=
  card_le_card (absorbedAt_subset B assignment i)

/-- Actual enlarged vertex sets, with their original labels. -/
def enlargedSets (U : I → Finset V) (B : Finset V) (assignment : V → I) (i : I) :
    Finset V := U i ∪ absorbedAt B assignment i

theorem old_subset_enlarged (U : I → Finset V) (B : Finset V)
    (assignment : V → I) (i : I) : U i ⊆ enlargedSets U B assignment i :=
  subset_union_left

omit [DecidableEq V] in
theorem absorbedAt_disjoint_old (U : I → Finset V) (Z B : Finset V)
    (assignment : V → I) (hUZ : ∀ i, Disjoint (U i) Z) (hBZ : B ⊆ Z) (i j : I) :
    Disjoint (U i) (absorbedAt B assignment j) :=
  (hUZ i).mono_right ((absorbedAt_subset B assignment j).trans hBZ)

/-- Distinct enlarged cores remain disjoint. -/
theorem enlargedSets_pairwise_disjoint (U : I → Finset V) (Z B : Finset V)
    (assignment : V → I)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z) (hBZ : B ⊆ Z) :
    Pairwise (fun i j => Disjoint (enlargedSets U B assignment i)
      (enlargedSets U B assignment j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro v hvi hvj
  rcases mem_union.mp hvi with hvi | hvi
  · rcases mem_union.mp hvj with hvj | hvj
    · exact disjoint_left.mp (hdisj hij) hvi hvj
    · exact disjoint_left.mp (absorbedAt_disjoint_old U Z B assignment hUZ hBZ i j) hvi hvj
  · rcases mem_union.mp hvj with hvj | hvj
    · exact disjoint_left.mp (absorbedAt_disjoint_old U Z B assignment hUZ hBZ j i) hvj hvi
    · have hi := (mem_absorbedAt B assignment i v).mp hvi
      have hj := (mem_absorbedAt B assignment j v).mp hvj
      exact hij (hi.2.symm.trans hj.2)

/-- Enlarged cores avoid exactly the exceptional vertices left over. -/
theorem enlargedSets_disjoint_remaining (U : I → Finset V) (Z B : Finset V)
    (assignment : V → I) (hUZ : ∀ i, Disjoint (U i) Z) (i : I) :
    Disjoint (enlargedSets U B assignment i) (Z \ B) := by
  apply disjoint_left.mpr
  intro v hv hrem
  rcases mem_sdiff.mp hrem with ⟨hvZ,hvB⟩
  rcases mem_union.mp hv with hvU | hvA
  · exact disjoint_left.mp (hUZ i) hvU hvZ
  · exact hvB ((mem_absorbedAt B assignment i v).mp hvA).1

/-- Absorption preserves the covering partition of the ambient vertex set. -/
theorem enlargedSets_cover (U : I → Finset V) (Z B : Finset V)
    (assignment : V → I) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    ∀ v, v ∈ Z \ B ∨ ∃ i, v ∈ enlargedSets U B assignment i := by
  intro v
  rcases hcover v with hvZ | ⟨i,hvi⟩
  · by_cases hvB : v ∈ B
    · exact Or.inr ⟨assignment v,mem_union_right _
        ((mem_absorbedAt B assignment (assignment v) v).mpr ⟨hvB,rfl⟩)⟩
    · exact Or.inl (mem_sdiff.mpr ⟨hvZ,hvB⟩)
  · exact Or.inr ⟨i,old_subset_enlarged U B assignment i hvi⟩

theorem enlargedSets_card_bounds (U : I → Finset V) (B : Finset V)
    (assignment : V → I) (i : I) :
    (U i).card ≤ (enlargedSets U B assignment i).card ∧
      (enlargedSets U B assignment i).card ≤ (U i).card+B.card := by
  constructor
  · exact card_le_card (old_subset_enlarged U B assignment i)
  · exact (card_union_le _ _).trans (Nat.add_le_add_left (absorbedAt_card_le B assignment i) _)

variable [Fintype V]

/-- Every neighbor lies in the assigned old core, in another old core,
or in the old exceptional set. This bounds the actual assigned-core
degree without assuming anything about absorption. -/
theorem assigned_core_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (assignment : V → I)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (v : V) :
    G.degree v ≤ (G.neighborFinset v ∩ U (assignment v)).card +
      ((G.neighborFinset v).filter (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment v)).card +
      Z.card := by
  let Q := (G.neighborFinset v).filter (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment v)
  have hs : G.neighborFinset v ⊆ (G.neighborFinset v ∩ U (assignment v)) ∪ Q ∪ Z := by
    intro w hw
    rcases hcover w with hwZ | ⟨i,hwi⟩
    · exact mem_union_right _ hwZ
    · apply mem_union_left
      by_cases hi : i = assignment v
      · exact mem_union_left _ (mem_inter.mpr ⟨hw,hi ▸ hwi⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hw,⟨i,hwi,hi⟩⟩)
  have hc := card_le_card hs
  have h1 := card_union_le ((G.neighborFinset v ∩ U (assignment v)) ∪ Q) Z
  have h2 := card_union_le (G.neighborFinset v ∩ U (assignment v)) Q
  rw [card_neighborFinset_eq_degree] at hc
  change G.degree v ≤ _ + Q.card + Z.card
  omega

/-- A bound on the old foreign degree gives the required degree into the
assigned old core, with only the original exceptional order as extra loss. -/
theorem assigned_core_degree_lower_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (assignment : V → I)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (h : ℕ) (b : ℝ)
    (hregular : ∀ v, G.degree v = h) (v : V)
    (hforeign : (((G.neighborFinset v).filter
      (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment v)).card : ℝ) ≤ b) :
    (h : ℝ)-b-Z.card ≤ ((G.neighborFinset v ∩ U (assignment v)).card : ℝ) := by
  have hc := assigned_core_degree_lower G U Z assignment hcover v
  rw [hregular v] at hc
  have hR : (h : ℝ) ≤ (G.neighborFinset v ∩ U (assignment v)).card +
      ((G.neighborFinset v).filter (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment v)).card + Z.card := by
    exact_mod_cast hc
  linarith

/-- The actual graph attached to every enlarged vertex set. -/
def enlargedGraphs (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (B : Finset V) (assignment : V → I) (i : I) :
    SimpleGraph (enlargedSets U B assignment i) :=
  enlargedCore G (U i) (absorbedAt B assignment i) (H i)

omit [Fintype V] in
theorem enlargedGraphs_le_ambient (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (B : Finset V) (assignment : V → I)
    (hH : ∀ i, H i ≤ G.induce (U i : Set V)) :
    ∀ i, enlargedGraphs G U H B assignment i ≤
      G.induce (enlargedSets U B assignment i : Set V) := by
  intro i
  exact enlargedCore_le_ambient G (U i) (absorbedAt B assignment i) (H i) (hH i)

theorem enlargedGraphs_degree_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (B : Finset V) (assignment : V → I) (h : ℕ)
    (hH : ∀ i, H i ≤ G.induce (U i : Set V)) (hregular : ∀ v, G.degree v = h) :
    ∀ i v, (enlargedGraphs G U H B assignment i).degree v ≤ h := by
  intro i v
  exact (enlargedCore_degree_upper G (U i) (absorbedAt B assignment i) (H i)
    (hH i) v).trans_eq (hregular v.val)

/-- One common error works for all first-enlarged cores. -/
theorem enlargedGraphs_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z B : Finset V) (assignment : V → I) (h : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hregular : ∀ v, G.degree v = h)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hforeign : ∀ v ∈ B, (((G.neighborFinset v).filter
      (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment v)).card : ℝ) ≤ b) :
    ∀ i v, (h : ℝ)-(a+b+Z.card) ≤
      ((enlargedGraphs G U H B assignment i).degree v : ℝ) := by
  intro i
  apply enlargedCore_degree_lower G (U i) (absorbedAt B assignment i) (H i)
  · intro v
    have hZ : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
    linarith [hdegree i v]
  · intro v hv
    obtain ⟨hvB,hvi⟩ := (mem_absorbedAt B assignment i v).mp hv
    have hl := assigned_core_degree_lower_real G U Z assignment hcover h b hregular v
      (hforeign v hvB)
    rw [hvi] at hl
    linarith

/-- The second absorption uses the degree bound into the current assigned
core directly. It does not incur another exceptional-set loss. -/
theorem enlargedGraphs_degree_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (B : Finset V) (assignment : V → I) (h : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hnew : ∀ v ∈ B, (h : ℝ)-b ≤
      ((G.neighborFinset v ∩ U (assignment v)).card : ℝ)) :
    ∀ i v, (h : ℝ)-(a+b) ≤ ((enlargedGraphs G U H B assignment i).degree v : ℝ) := by
  intro i
  apply enlargedCore_degree_error G (U i) (absorbedAt B assignment i) (H i) h a b ha hb
    (hdegree i)
  intro v hv
  obtain ⟨hvB,hvi⟩ := (mem_absorbedAt B assignment i v).mp hv
  simpa only [hvi] using hnew v hvB

omit [Fintype V] in
/-- All enlarged cores inherit the same fixed robust parameters from the
same bound on the original exceptional order. -/
theorem enlargedGraphs_robust (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z B : Finset V) (assignment : V → I) (ν τ : ℝ)
    (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4) (hBZ : B ⊆ Z)
    (hsmall : ∀ i, (Z.card : ℝ) ≤ ν*(U i).card/4)
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ) :
    ∀ i, IsRobustExpander (enlargedGraphs G U H B assignment i) (ν/4) (2*τ) := by
  intro i
  apply enlargedCore_robust G (U i) (absorbedAt B assignment i) (H i)
    ν τ hν hντ hτ
  · have hc : ((absorbedAt B assignment i).card : ℝ) ≤ Z.card := by
      exact_mod_cast card_le_card ((absorbedAt_subset B assignment i).trans hBZ)
    exact hc.trans (hsmall i)
  · exact hrobust i

omit [Fintype V] in
theorem enlargedGraphs_robust_smaller_range (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (Z B : Finset V) (assignment : V → I) (η ν τ σ : ℝ)
    (hη : 0 < η) (hηone : η ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 2*τ ≤ η/4) (hσ : 0 < σ) (hστ : σ ≤ 2*τ) (hBZ : B ⊆ Z)
    (hsmall : ∀ i, (Z.card : ℝ) ≤ ν*(U i).card/4)
    (hdegree : ∀ i v, η*(enlargedSets U B assignment i).card ≤
      ((enlargedGraphs G U H B assignment i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ) :
    ∀ i, IsRobustExpander (enlargedGraphs G U H B assignment i)
      (min (ν/4) (η*σ/2)) σ := by
  intro i
  apply enlargedCore_robust_smaller_range G (U i) (absorbedAt B assignment i) (H i)
    η ν τ σ hη hηone hν hντ hτ hσ hστ
  · have hc : ((absorbedAt B assignment i).card : ℝ) ≤ Z.card := by
      exact_mod_cast card_le_card ((absorbedAt_subset B assignment i).trans hBZ)
    exact hc.trans (hsmall i)
  · exact hdegree i
  · exact hrobust i

end Overfull.Absorption
