import Overfull.CompatibleCircuits.SmallKernel

/-! Every class partition of four incidences with class size at most two
refines one of the three balanced pair partitions. -/

namespace Overfull.CompatibleCircuits

open Finset Classical

theorem four_incidence_pair_coarsening {K : Type*} (f : Fin 4 → K)
    (hbound : ∀ k, (univ.filter (fun i => f i = k)).card ≤ 2) :
    ∃ q : Fin 3, ∀ i j, f i = f j →
      SmallKernel.pairClass q i.val = SmallKernel.pairClass q j.val := by
  have hthree (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬ (f i = f j ∧ f i = f k) := by
    rintro ⟨h₁,h₂⟩
    have hsub : {i,j,k} ⊆ univ.filter (fun x => f x = f i) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp_all
    have hcard : ({i,j,k} : Finset (Fin 4)).card = 3 := by simp [hij,hik,hjk]
    have hh := (card_le_card hsub).trans (hbound (f i))
    omega
  have h012 := hthree 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hthree 0 1 3 (by decide) (by decide) (by decide)
  have h023 := hthree 0 2 3 (by decide) (by decide) (by decide)
  have h123 := hthree 1 2 3 (by decide) (by decide) (by decide)
  by_cases h01 : f 0 = f 1
  · refine ⟨0,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]
  by_cases h02 : f 0 = f 2
  · refine ⟨1,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]
  by_cases h03 : f 0 = f 3
  · refine ⟨2,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]
  by_cases h12 : f 1 = f 2
  · refine ⟨2,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]
  by_cases h13 : f 1 = f 3
  · refine ⟨1,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]
  · refine ⟨0,?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [SmallKernel.pairClass]

end Overfull.CompatibleCircuits
