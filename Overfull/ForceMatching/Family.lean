import Overfull.ForceMatching.Probability
import Overfull.SmallCuts

namespace Overfull.ForceMatching

open Finset Classical MatchingProbability

variable {V I : Type*}

theorem eq_or_toggle_of_difference_card_le_one (X Y : Finset V)
    (hcard : ((X \ Y) ∪ (Y \ X)).card ≤ 1) :
    X = Y ∨ ∃ v, X = toggle Y v := by
  classical
  by_cases heq : X = Y
  · exact Or.inl heq
  have hnonempty : ((X \ Y) ∪ (Y \ X)).Nonempty := by
    by_contra h
    have hz : (X \ Y) ∪ (Y \ X) = ∅ := not_nonempty_iff_eq_empty.mp h
    apply heq
    ext v
    have hv : v ∉ (X \ Y) ∪ (Y \ X) := by rw [hz]; simp
    simp only [mem_union,mem_sdiff] at hv
    tauto
  obtain ⟨v,hv⟩ := hnonempty
  have hunique := card_le_one.mp hcard
  refine Or.inr ⟨v,?_⟩
  ext w
  by_cases hwv : w = v
  · subst w
    simp only [mem_union,mem_sdiff] at hv
    rcases hv with ⟨hvX,hvY⟩ | ⟨hvY,hvX⟩ <;> simp [toggle,hvX,hvY]
  · have hagree : w ∈ X ↔ w ∈ Y := by
      constructor
      · intro hwX
        by_contra hwY
        exact hwv (hunique w (mem_union_left _ (mem_sdiff.mpr ⟨hwX,hwY⟩)) v hv)
      · intro hwY
        by_contra hwX
        exact hwv (hunique w (mem_union_right _ (mem_sdiff.mpr ⟨hwY,hwX⟩)) v hv)
    by_cases hvY : v ∈ Y <;> simp [toggle,hvY,hwv,hagree]

theorem even_of_toggle_odd (Y : Finset V) (v : V)
    (hodd : (toggle Y v).card % 2 = 1) : Y.card % 2 = 0 := by
  classical
  by_cases hv : v ∈ Y
  · have hp : 0 < Y.card := card_pos.mpr ⟨v,hv⟩
    simp only [toggle,if_pos hv,card_erase_of_mem hv] at hodd
    omega
  · simp only [toggle,if_neg hv,card_insert_of_notMem hv] at hodd
    omega

variable [Fintype I]

/-- Every member of the actual finite family contains each core wholly
or not at all. -/
theorem wholeUnions_whole (U : I → Finset V) (Z X : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hX : X ∈ wholeUnions U Z) :
    ∀ i, U i ⊆ X ∨ Disjoint (U i) X := by
  classical
  obtain ⟨A,B,hB,rfl⟩ := (mem_wholeUnions U Z X).mp hX
  intro i
  by_cases hi : i ∈ A
  · exact Or.inl (fun v hv => mem_union_left _ (mem_biUnion.mpr ⟨i,hi,hv⟩))
  · apply Or.inr
    apply disjoint_left.mpr
    intro v hv hVX
    rcases mem_union.mp hVX with hVA | hVB
    · obtain ⟨j,hj,hvj⟩ := mem_biUnion.mp hVA
      have hij : i ≠ j := by intro heq; exact hi (heq ▸ hj)
      exact disjoint_left.mp (hdisj hij) hv hvj
    · exact disjoint_left.mp (hZ i) hv (hB hVB)

/-- A shore with total core minority at most one is a tested union or
a one-vertex change of such a union. Exceptional vertices are retained
with exactly their original membership. -/
theorem classified_of_minority (U : I → Finset V) (Z X : Finset V)
    (hZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1) :
    X ∈ wholeUnions U Z ∨ ∃ Y ∈ wholeUnions U Z, ∃ v, X = toggle Y v := by
  classical
  obtain ⟨A,hA⟩ := SmallCuts.union_of_cores_close U X hminority
  let Y := A.biUnion U ∪ (X ∩ Z)
  have hY : Y ∈ wholeUnions U Z :=
    (mem_wholeUnions U Z Y).mpr ⟨A,X ∩ Z,inter_subset_right,rfl⟩
  have hdiff : (X \ Y) ∪ (Y \ X) =
      ((X ∩ univ.biUnion U) \ A.biUnion U) ∪
        (A.biUnion U \ (X ∩ univ.biUnion U)) := by
    ext v
    by_cases hvZ : v ∈ Z
    · have hvU : v ∉ univ.biUnion U := by
        intro hv
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
        exact disjoint_left.mp (hZ i) hi hvZ
      have hvA : v ∉ A.biUnion U := by
        intro hv
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
        exact disjoint_left.mp (hZ i) hi hvZ
      simp [Y,hvZ,hvU,hvA]
    · obtain ⟨i,hi⟩ := (hcover v).resolve_left hvZ
      have hvU : v ∈ univ.biUnion U := mem_biUnion.mpr ⟨i,mem_univ _,hi⟩
      simp [Y,hvZ,hvU]
  have hcard : ((X \ Y) ∪ (Y \ X)).card ≤ 1 := by rw [hdiff]; exact hA
  rcases eq_or_toggle_of_difference_card_le_one X Y hcard with heq | ⟨v,hv⟩
  · exact Or.inl (heq ▸ hY)
  · exact Or.inr ⟨Y,hY,v,hv⟩

/-- On odd shores the classification is precisely one of the conditions
tested by the finite-family probability bound. -/
theorem safe_cut_of_classified {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (M : G.Subgraph) (k : ℕ) (𝓧 : Finset (Finset V))
    (hsafe : ¬ FamilyFailure M k 𝓧) (X : Finset V) (hodd : X.card % 2 = 1)
    (hclass : X ∈ 𝓧 ∨ ∃ Y ∈ 𝓧, ∃ v, X = toggle Y v) : ¬ CutFailure M k X := by
  intro hbad
  apply hsafe
  rcases hclass with hX | ⟨Y,hY,v,rfl⟩
  · exact ⟨X,hX,Or.inl ⟨hodd,hbad⟩⟩
  · exact ⟨Y,hY,Or.inr ⟨even_of_toggle_odd Y v hodd,v,hbad⟩⟩

end Overfull.ForceMatching
