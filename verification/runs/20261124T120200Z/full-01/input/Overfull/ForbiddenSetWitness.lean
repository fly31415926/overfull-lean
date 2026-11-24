import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Bounded witnesses against small forbidden sets

From any finite family of sets of order at most `L`, retain a bounded
subfamily that preserves the existence of a member avoiding any set of
order at most `k`. Taking the union gives the vertex witness used for the
six pairs of cores in the prescribed-matching lemma.
-/

namespace Overfull.ForbiddenSetWitness

open Finset Classical
open scoped BigOperators

variable {V I : Type*} [DecidableEq V]

/-- The number of nodes in a rooted branching tree of depth `k` and
branching bound `L`. -/
def branchCount (L k : ℕ) : ℕ := ∑ j ∈ range (k + 1), L ^ j

@[simp] theorem branchCount_zero (L : ℕ) : branchCount L 0 = 1 := by
  simp [branchCount]

theorem branchCount_succ (L k : ℕ) :
    branchCount L (k + 1) = 1 + L * branchCount L k := by
  unfold branchCount
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero, ← Finset.sum_mul]
  ring

/-- The retained members are actual members of the original finite family. -/
theorem exists_subfamily (F : Finset (Finset V)) (L k : ℕ)
    (hsize : ∀ P ∈ F, P.card ≤ L) :
    ∃ R : Finset (Finset V), R ⊆ F ∧ R.card ≤ branchCount L k ∧
      ∀ Y : Finset V, Y.card ≤ k → (∃ P ∈ F, Disjoint P Y) →
        ∃ P ∈ R, Disjoint P Y := by
  induction k generalizing F with
  | zero =>
      by_cases hF : F.Nonempty
      · obtain ⟨P, hP⟩ := hF
        refine ⟨{P}, Finset.singleton_subset_iff.mpr hP, by simp, ?_⟩
        intro Y hY _
        have hY0 : Y = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hY)
        exact ⟨P, Finset.mem_singleton_self P, by simp [hY0]⟩
      · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
        intro Y _ hPY
        obtain ⟨P, hP, _⟩ := hPY
        exact False.elim (hF ⟨P, hP⟩)
  | succ k ih =>
      by_cases hF : F.Nonempty
      · obtain ⟨P, hP⟩ := hF
        have hchildren (v : V) :
            ∃ R : Finset (Finset V), R ⊆ F.filter (fun Q => v ∉ Q) ∧
              R.card ≤ branchCount L k ∧
              ∀ Y : Finset V, Y.card ≤ k →
                (∃ Q ∈ F.filter (fun Q => v ∉ Q), Disjoint Q Y) →
                  ∃ Q ∈ R, Disjoint Q Y := by
          exact ih (F.filter (fun Q => v ∉ Q))
            (fun Q hQ => hsize Q (Finset.mem_filter.mp hQ).1)
        choose R hRsub hRcard hRavoid using hchildren
        let R₀ := {P} ∪ P.biUnion R
        have hR₀sub : R₀ ⊆ F := by
          intro Q hQ
          rcases Finset.mem_union.mp hQ with hQ | hQ
          · exact (Finset.mem_singleton.mp hQ) ▸ hP
          · obtain ⟨v, _, hvQ⟩ := Finset.mem_biUnion.mp hQ
            exact (Finset.mem_filter.mp (hRsub v hvQ)).1
        have hR₀card : R₀.card ≤ branchCount L (k + 1) := by
          calc
            _ ≤ ({P} : Finset (Finset V)).card + (P.biUnion R).card :=
              Finset.card_union_le _ _
            _ ≤ 1 + ∑ v ∈ P, (R v).card := by
              simpa using Nat.add_le_add_left Finset.card_biUnion_le 1
            _ ≤ 1 + P.card * branchCount L k := by
              gcongr
              simpa using (Finset.sum_le_sum (fun v (_ : v ∈ P) => hRcard v))
            _ ≤ 1 + L * branchCount L k := by
              gcongr
              exact hsize P hP
            _ = _ := (branchCount_succ L k).symm
        refine ⟨R₀, hR₀sub, hR₀card, ?_⟩
        intro Y hY havoid
        by_cases hPY : Disjoint P Y
        · exact ⟨P, Finset.mem_union_left _ (Finset.mem_singleton_self P), hPY⟩
        · obtain ⟨v, hvP, hvY⟩ := Finset.not_disjoint_iff.mp hPY
          have hYsmall : (Y.erase v).card ≤ k := by
            have hh := Finset.card_erase_add_one hvY
            omega
          have hchild : ∃ Q ∈ F.filter (fun Q => v ∉ Q),
              Disjoint Q (Y.erase v) := by
            obtain ⟨Q, hQ, hQY⟩ := havoid
            refine ⟨Q, Finset.mem_filter.mpr ⟨hQ, ?_⟩, ?_⟩
            · exact fun hvQ => Finset.disjoint_left.mp hQY hvQ hvY
            · exact hQY.mono_right (Finset.erase_subset _ _)
          obtain ⟨Q, hQR, hQY⟩ := hRavoid v (Y.erase v) hYsmall hchild
          have hvQ : v ∉ Q := (Finset.mem_filter.mp (hRsub v hQR)).2
          refine ⟨Q, Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨v, hvP, hQR⟩), ?_⟩
          apply Finset.disjoint_left.mpr
          intro x hxQ hxY
          by_cases hxv : x = v
          · exact hvQ (hxv ▸ hxQ)
          · exact Finset.disjoint_left.mp hQY hxQ (Finset.mem_erase.mpr ⟨hxv, hxY⟩)
      · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
        intro Y _ hPY
        obtain ⟨P, hP, _⟩ := hPY
        exact False.elim (hF ⟨P, hP⟩)

/-- A bounded vertex set contains an admissible witness whenever one exists
outside the prescribed small forbidden set. -/
theorem exists_vertex_witness (F : Finset (Finset V)) (L k : ℕ)
    (hsize : ∀ P ∈ F, P.card ≤ L) :
    ∃ W : Finset V, W.card ≤ L * branchCount L k ∧
      ∀ Y : Finset V, Y.card ≤ k → (∃ P ∈ F, Disjoint P Y) →
        ∃ P ∈ F, P ⊆ W ∧ Disjoint P Y := by
  obtain ⟨R, hRF, hRcard, hRavoid⟩ := exists_subfamily F L k hsize
  refine ⟨R.biUnion id, ?_, ?_⟩
  · calc
      _ ≤ ∑ P ∈ R, P.card := Finset.card_biUnion_le
      _ ≤ R.card * L := by
        simpa using (Finset.sum_le_sum (fun P hP => hsize P (hRF hP)))
      _ ≤ branchCount L k * L := Nat.mul_le_mul_right L hRcard
      _ = _ := Nat.mul_comm _ _
  · intro Y hY havoid
    obtain ⟨P, hP, hPY⟩ := hRavoid Y hY havoid
    exact ⟨P, hRF hP, Finset.subset_biUnion_of_mem id hP, hPY⟩

/-- A single vertex witness works simultaneously for a finite list of
families; the size bound is additive over the families. -/
theorem exists_common_witness [DecidableEq I] (T : Finset I)
    (F : I → Finset (Finset V)) (L k : ℕ)
    (hsize : ∀ i ∈ T, ∀ P ∈ F i, P.card ≤ L) :
    ∃ W : Finset V, W.card ≤ T.card * (L * branchCount L k) ∧
      ∀ i ∈ T, ∀ Y : Finset V, Y.card ≤ k →
        (∃ P ∈ F i, Disjoint P Y) →
          ∃ P ∈ F i, P ⊆ W ∧ Disjoint P Y := by
  have hall (i : T) : ∃ W : Finset V, W.card ≤ L * branchCount L k ∧
      ∀ Y : Finset V, Y.card ≤ k → (∃ P ∈ F i, Disjoint P Y) →
        ∃ P ∈ F i, P ⊆ W ∧ Disjoint P Y :=
    exists_vertex_witness (F i) L k (hsize i i.property)
  choose W hWcard hWavoid using hall
  refine ⟨univ.biUnion W, ?_, ?_⟩
  · calc
      _ ≤ ∑ i : T, (W i).card := Finset.card_biUnion_le
      _ ≤ T.card * (L * branchCount L k) := by
        simpa using (Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset T)) => hWcard i))
  · intro i hi Y hY havoid
    obtain ⟨P, hP, hPW, hPY⟩ := hWavoid ⟨i, hi⟩ Y hY havoid
    exact ⟨P, hP, hPW.trans (Finset.subset_biUnion_of_mem W (Finset.mem_univ _)), hPY⟩

theorem twelve_vertex_bound : 12 * branchCount 12 3 = 22620 := by
  norm_num [branchCount, Finset.sum_range_succ]

theorem six_twelve_vertex_bound : 6 * (12 * branchCount 12 3) = 135720 := by
  rw [twelve_vertex_bound]

/-- The bound used for at most six pairs of cores: each admissible path
has at most twelve vertices and the forbidden set has order at most three. -/
theorem exists_six_family_witness [DecidableEq I] (T : Finset I)
    (F : I → Finset (Finset V)) (hT : T.card ≤ 6)
    (hsize : ∀ i ∈ T, ∀ P ∈ F i, P.card ≤ 12) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ i ∈ T, ∀ Y : Finset V, Y.card ≤ 3 →
        (∃ P ∈ F i, Disjoint P Y) →
          ∃ P ∈ F i, P ⊆ W ∧ Disjoint P Y := by
  obtain ⟨W, hWcard, hWavoid⟩ := exists_common_witness T F 12 3 hsize
  refine ⟨W, ?_, hWavoid⟩
  calc
    _ ≤ T.card * (12 * branchCount 12 3) := hWcard
    _ ≤ 6 * (12 * branchCount 12 3) := Nat.mul_le_mul_right _ hT
    _ = _ := six_twelve_vertex_bound

end Overfull.ForbiddenSetWitness
