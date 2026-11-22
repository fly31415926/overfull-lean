import Overfull.Compression.Parity

/-!
# The possible joining forests when all four parts are odd

The perfect matchings are listed as their actual unordered label pairs.
A star is the set of all three label pairs containing its center. The
finite classifications below are checked by kernel reduction.
-/

namespace Overfull.CircuitPatterns

open Finset Compression

/-- The three perfect matchings on the four fixed core labels. -/
def labelPerfectMatchings : Finset (Finset LabelPair) :=
  {{⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩},
   {⟨{0, 2}, by decide⟩, ⟨{1, 3}, by decide⟩},
   {⟨{0, 3}, by decide⟩, ⟨{1, 2}, by decide⟩}}

/-- All three unordered label pairs incident with a fixed center. -/
def labelStar (center : Fin 4) : Finset LabelPair :=
  univ.filter (fun p => center ∈ p.val)

@[simp] theorem mem_labelStar (center : Fin 4) (p : LabelPair) :
    p ∈ labelStar center ↔ center ∈ p.val := by
  simp [labelStar]

/-- The exact two shapes allowed in the all-odd four-part conclusion. -/
def LabelForestShape (F : Finset LabelPair) : Prop :=
  F ∈ labelPerfectMatchings ∨ ∃ center : Fin 4, F = labelStar center

instance (F : Finset LabelPair) : Decidable (LabelForestShape F) := by
  unfold LabelForestShape
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A forest on four labels whose four degrees are odd is one of the
three explicit perfect matchings or one of the four explicit stars. -/
theorem odd_leafForest_classification :
    ∀ F : Finset LabelPair, LeafForest F →
      (∀ i : Fin 4, pairDegree F i % 2 = 1) → LabelForestShape F := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The listed matching sets have exactly two edges, are disjoint at
their endpoints, and cover each of the four labels once. -/
theorem labelPerfectMatching_spec :
    ∀ F : Finset LabelPair, F ∈ labelPerfectMatchings →
      F.card = 2 ∧ (∀ i : Fin 4, pairDegree F i = 1) ∧
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f → Disjoint e.val f.val) ∧ LeafForest F := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A star has exactly three edges, degree three at its center, and
degree one at each of the other three labels. -/
theorem labelStar_spec :
    ∀ center : Fin 4, (labelStar center).card = 3 ∧
      (∀ i : Fin 4, pairDegree (labelStar center) i = if i = center then 3 else 1) ∧
      LeafForest (labelStar center) := by
  decide

/-- The explicit classification is equivalent to being an all-odd forest. -/
theorem labelForestShape_iff (F : Finset LabelPair) :
    LabelForestShape F ↔ LeafForest F ∧ ∀ i : Fin 4, pairDegree F i % 2 = 1 := by
  constructor
  · rintro (hF | ⟨center, rfl⟩)
    · obtain ⟨_, hdegree, _, hforest⟩ := labelPerfectMatching_spec F hF
      exact ⟨hforest, fun i => by rw [hdegree i]⟩
    · obtain ⟨_, hdegree, hforest⟩ := labelStar_spec center
      refine ⟨hforest, fun i => ?_⟩
      rw [hdegree i]
      split_ifs <;> decide
  · rintro ⟨hforest, hodd⟩
    exact odd_leafForest_classification F hforest hodd

/-- The number of label pairs crossing a label shore. -/
def forestCutCount (F : Finset LabelPair) (S : Finset (Fin 4)) : ℕ :=
  (F.filter (fun p => (p.val ∩ S).card = 1)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forestCutCount_singleton :
    ∀ (F : Finset LabelPair) (i : Fin 4), forestCutCount F {i} = pairDegree F i := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The star cut has one edge for each label on the shore opposite its
center. This uses actual finite pair sets, not an abstract degree code. -/
theorem labelStar_cutCount :
    ∀ (center : Fin 4) (S : Finset (Fin 4)),
      forestCutCount (labelStar center) S =
        if center ∈ S then 4 - S.card else S.card := by
  decide

end Overfull.CircuitPatterns
