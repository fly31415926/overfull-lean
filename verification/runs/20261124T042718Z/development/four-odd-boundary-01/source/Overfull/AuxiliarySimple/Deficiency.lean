import Overfull.ForceMatching.Residual
import Overfull.OneCore.Complement

/-! Total deficiency and the actual auxiliary-core error from covering cores. -/

noncomputable section

namespace Overfull.AuxiliarySimple

open Finset Classical SimpleGraph

variable {V I : Type*} [Fintype V]

/-- Every vertex outside the exceptional set has deficiency at most the
core error; exceptional vertices each contribute at most the host order. -/
theorem total_deficiency_le (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (Z : Finset V) (k : ℕ) (a : ℝ)
    (hdegree : ∀ v, G.degree v ≤ k) (hk : k ≤ Fintype.card V)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hcore : ∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) (ha : 0 ≤ a) :
    (∑ v, ((k - G.degree v : ℕ) : ℝ)) ≤
      Fintype.card V * (a + (Z.card : ℝ)) := by
  have hlocal (v : V) : ((k - G.degree v : ℕ) : ℝ) ≤
      a + if v ∈ Z then (Fintype.card V : ℝ) else 0 := by
    by_cases hz : v ∈ Z
    · rw [if_pos hz]
      have hh : k - G.degree v ≤ Fintype.card V := (Nat.sub_le _ _).trans hk
      have hr : ((k - G.degree v : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hh
      linarith only [hr, ha]
    · rw [if_neg hz, add_zero, Nat.cast_sub (hdegree v)]
      obtain ⟨i, hi⟩ := (hcover v).resolve_left hz
      let C := ForceMatching.embeddedCore G (U i) (H i) (hembed i)
      have hh := OneCore.core_degree_le C (⟨v, hi⟩ : U i)
      have hupper : (H i).degree ⟨v, hi⟩ ≤ G.degree v := by
        simpa only [C, ForceMatching.embeddedCore, Multigraph.ofSimpleGraph_degree] using hh
      have hupperR : ((H i).degree ⟨v, hi⟩ : ℝ) ≤ G.degree v := by exact_mod_cast hupper
      linarith only [hcore i ⟨v, hi⟩, hupperR]
  calc
    (∑ v, ((k - G.degree v : ℕ) : ℝ)) ≤
        ∑ v, (a + if v ∈ Z then (Fintype.card V : ℝ) else 0) :=
      sum_le_sum (fun v _ => hlocal v)
    _ = Fintype.card V * (a + (Z.card : ℝ)) := by
      simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      rw [sum_ite_mem]
      simp only [sum_const, nsmul_eq_mul, sum_const_zero, add_zero]
      ring

/-- The ceiling of average total deficiency gives the required auxiliary
minimum-degree error, bounded by the original combined error budget. -/
theorem ceil_average_deficiency_le (G : SimpleGraph V) (U : I → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (Z : Finset V) (k : ℕ) (a : ℝ)
    (hn : 0 < Fintype.card V) (hdegree : ∀ v, G.degree v ≤ k)
    (hk : k ≤ Fintype.card V) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hcore : ∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) (ha : 0 ≤ a) :
    (⌈(∑ v, ((k - G.degree v : ℕ) : ℝ)) / Fintype.card V⌉₊ : ℝ) ≤
      a + (Z.card : ℝ) + 1 := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have htotal := total_deficiency_le G U H Z k a hdegree hk hcover hembed hcore ha
  have havg : (∑ v, ((k - G.degree v : ℕ) : ℝ)) / Fintype.card V ≤
      a + (Z.card : ℝ) := by
    apply (div_le_iff₀ hnR).mpr
    simpa only [mul_comm] using htotal
  have hnonneg : 0 ≤ (∑ v, ((k - G.degree v : ℕ) : ℝ)) / Fintype.card V := by positivity
  exact (Nat.ceil_lt_add_one hnonneg).le.trans (by linarith only [havg])

end Overfull.AuxiliarySimple
