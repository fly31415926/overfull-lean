import Overfull.ForceMatching.Probability

/-!
# An actual decreasing potential for exceptional-star forcing

The assigned enlarged cores remain fixed during the phase.  Every edge
from a selected exceptional vertex to the complement of its assigned
core is counted, including edges to other exceptional vertices.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph ForceMatching
open scoped BigOperators

variable {V I : Type*} [Fintype V]

noncomputable def outsideNeighbors (G : SimpleGraph V) (W : Finset V) (z : V) : Finset V := by
  classical
  exact G.neighborFinset z \ W

theorem mem_outsideNeighbors (G : SimpleGraph V) (W : Finset V) (z w : V) :
    w ∈ outsideNeighbors G W z ↔ G.Adj z w ∧ w ∉ W := by
  classical
  simp only [outsideNeighbors,mem_sdiff,SimpleGraph.mem_neighborFinset]

noncomputable def outsideDegree (G : SimpleGraph V) (W : Finset V) (z : V) : ℕ :=
  (outsideNeighbors G W z).card

noncomputable def forcingPotential (G : SimpleGraph V) (B : Finset V)
    (W : V → Finset V) : ℕ := ∑ z ∈ B, outsideDegree G (W z) z

noncomputable def outsideStar (G : SimpleGraph V) (W : Finset V) (z : V) :
    Finset G.edgeSet := by
  classical
  exact univ.filter (fun e => ∃ w ∈ outsideNeighbors G W z, e.val = s(z,w))

theorem mem_outsideStar (G : SimpleGraph V) (W : Finset V) (z : V) (e : G.edgeSet) :
    e ∈ outsideStar G W z ↔ ∃ w ∈ outsideNeighbors G W z, e.val = s(z,w) := by
  classical
  simp [outsideStar]

theorem outsideStar_incident (G : SimpleGraph V) (W : Finset V) (z : V) :
    ∀ e ∈ outsideStar G W z, z ∈ e.val := by
  intro e he
  obtain ⟨w,_hw,heq⟩ := (mem_outsideStar G W z e).mp he
  rw [heq]
  simp

theorem outsideStar_card (G : SimpleGraph V) (W : Finset V) (z : V) :
    (outsideStar G W z).card = outsideDegree G W z := by
  classical
  let f : (outsideNeighbors G W z) → G.edgeSet := fun w =>
    ⟨s(z,w.val),((mem_outsideNeighbors G W z w.val).mp w.property).1⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have he : s(z,u.val) = s(z,v.val) := congrArg Subtype.val huv
    rcases Sym2.eq_iff.mp he with ⟨_,heq⟩ | ⟨h₁,h₂⟩
    · exact heq
    · exact h₂.trans h₁
  have himage : (univ : Finset (outsideNeighbors G W z)).image f = outsideStar G W z := by
    ext e
    constructor
    · intro he
      obtain ⟨w,_hw,rfl⟩ := mem_image.mp he
      exact (mem_outsideStar G W z _).mpr ⟨w.val,w.property,rfl⟩
    · intro he
      obtain ⟨w,hw,heq⟩ := (mem_outsideStar G W z e).mp he
      exact mem_image.mpr ⟨⟨w,hw⟩,mem_univ _,Subtype.ext heq.symm⟩
  rw [← himage,card_image_of_injective _ hf,card_univ,Fintype.card_coe]
  rfl

theorem outsideNeighbors_mono (R G : SimpleGraph V) (hRG : R ≤ G)
    (W : Finset V) (z : V) : outsideNeighbors R W z ⊆ outsideNeighbors G W z := by
  classical
  intro w hw
  obtain ⟨hwR,hwW⟩ := mem_sdiff.mp hw
  exact mem_sdiff.mpr ⟨(G.mem_neighborFinset z w).mpr
    (hRG ((R.mem_neighborFinset z w).mp hwR)),hwW⟩

theorem outsideDegree_mono (R G : SimpleGraph V) (hRG : R ≤ G)
    (W : Finset V) (z : V) : outsideDegree R W z ≤ outsideDegree G W z :=
  card_le_card (outsideNeighbors_mono R G hRG W z)

theorem forcingPotential_mono (R G : SimpleGraph V) (hRG : R ≤ G)
    (B : Finset V) (W : V → Finset V) :
    forcingPotential R B W ≤ forcingPotential G B W :=
  sum_le_sum (fun z _ => outsideDegree_mono R G hRG (W z) z)

/-- Meeting the full outside star strictly decreases its actual outside
degree. No perfectness or maximality hypothesis is needed for this count. -/
theorem outsideDegree_decreases (G : SimpleGraph V) (N : G.Subgraph)
    (W : Finset V) (z : V) (hhit : StarHit N (outsideStar G W z)) :
    outsideDegree (G \ N.spanningCoe) W z < outsideDegree G W z := by
  classical
  obtain ⟨e,he,heN⟩ := hhit
  obtain ⟨w,hw,heq⟩ := (mem_outsideStar G W z e).mp he
  have hN : N.Adj z w := by
    change s(z,w) ∈ N.edgeSet
    simpa only [heq] using heN
  have hnot : w ∉ outsideNeighbors (G \ N.spanningCoe) W z := by
    intro hwR
    have hadj := ((mem_outsideNeighbors (G \ N.spanningCoe) W z w).mp hwR).1
    exact hadj.2 hN
  apply card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨outsideNeighbors_mono _ G sdiff_le W z,fun heq' => hnot (heq'.symm ▸ hw)⟩

/-- Every forced deletion removes at least one counted incidence, even
when the chosen edge is counted at two exceptional endpoints. -/
theorem forcingPotential_decreases (G : SimpleGraph V) (N : G.Subgraph)
    (B : Finset V) (W : V → Finset V) (z : V) (hz : z ∈ B)
    (hhit : StarHit N (outsideStar G (W z) z)) :
    forcingPotential (G \ N.spanningCoe) B W < forcingPotential G B W := by
  apply sum_lt_sum
  · intro v _hv
    exact outsideDegree_mono _ G sdiff_le (W v) v
  · exact ⟨z,hz,outsideDegree_decreases G N (W z) z hhit⟩

noncomputable def originalForeignNeighbors (G : SimpleGraph V) (U : I → Finset V)
    (assignment : V → I) (z : V) : Finset V := by
  classical
  exact (G.neighborFinset z).filter (fun w => ∃ i, w ∈ U i ∧ i ≠ assignment z)

/-- The extra incidences created by enlarging the partition are bounded
by the entire original exceptional set, including its internal edges. -/
theorem outsideDegree_le_originalForeign_add (G : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V) (assignment : V → I)
    (W : V → Finset V) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hUW : ∀ z, U (assignment z) ⊆ W z) (z : V) :
    outsideDegree G (W z) z ≤ (originalForeignNeighbors G U assignment z).card+Z.card := by
  classical
  have hsub : outsideNeighbors G (W z) z ⊆ originalForeignNeighbors G U assignment z ∪ Z := by
    intro w hw
    obtain ⟨hwG,hwW⟩ := mem_sdiff.mp hw
    rcases hcover w with hwZ | ⟨i,hi⟩
    · exact mem_union_right _ hwZ
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨hwG,i,hi,?_⟩
      intro heq
      subst i
      exact hwW (hUW z hi)
  exact (card_le_card hsub).trans (card_union_le _ _)

theorem forcingPotential_le_originalForeign_add (G : SimpleGraph V)
    (U : I → Finset V) (Z B : Finset V) (assignment : V → I)
    (W : V → Finset V) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hUW : ∀ z, U (assignment z) ⊆ W z) :
    forcingPotential G B W ≤
      (∑ z ∈ B, (originalForeignNeighbors G U assignment z).card)+B.card*Z.card := by
  calc
    _ ≤ ∑ z ∈ B, ((originalForeignNeighbors G U assignment z).card+Z.card) :=
      sum_le_sum (fun z _ => outsideDegree_le_originalForeign_add G U Z assignment W hcover hUW z)
    _ = _ := by simp [sum_add_distrib]

/-- At termination the degree in the assigned core is the regular degree
minus at most the forced-star threshold. -/
theorem assigned_neighbors_lower (G : SimpleGraph V) (W : Finset V)
    (z : V) (h d : ℕ) (hregular : G.degree z = h)
    (hout : outsideDegree G W z ≤ d) :
    h ≤ (G.neighborFinset z ∩ W).card+d := by
  classical
  have hc := card_sdiff_add_card_inter (G.neighborFinset z) W
  rw [G.card_neighborFinset_eq_degree,hregular] at hc
  change (G.neighborFinset z \ W).card ≤ d at hout
  omega

end Overfull.Absorption
