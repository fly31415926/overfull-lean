import Overfull.AuxiliaryCompletion.BalancedIncidence
import Overfull.AuxiliaryCompletion.Order
import Overfull.Multigraph
import Overfull.RobustRealization

/-!
# Construction of the robust auxiliary core

The constants in this construction precede the original graph. The
incidences are actual finite neighbor sets, and the auxiliary core is an
actual simple graph with its prescribed degrees. No odd-set hypothesis is
needed until the subsequent proof that the completed graph has no
overfull set.
-/

namespace Overfull.AuxiliaryCompletion

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The sum of the degrees counts every edge copy twice. -/
theorem multigraph_degree_sum (G : Multigraph V E) :
    (∑ v, G.degree v) = 2 * Fintype.card E := by
  classical
  have hi : G.internalEdges (univ : Finset V) = univ := by ext e; simp
  have hc : G.cutSize (univ : Finset V) = 0 := by
    simp [Multigraph.cutSize, Multigraph.cutEdges]
  simpa only [hi, hc, Finset.card_univ, add_zero] using G.degree_sum_on univ

/-- Removing the incidences from the requested auxiliary degrees leaves
an even sum, because the two vertex orders have the same parity. -/
theorem auxiliary_degree_sum_even (G : Multigraph V E) (k m : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k) (hparity : m % 2 = Fintype.card V % 2)
    (N : V → Finset (Fin m)) (hload : ∀ z, rightLoad N z ≤ k)
    (hsum : (∑ z : Fin m, rightLoad N z) = ∑ v : V, (k - G.degree v)) :
    Even (∑ z : Fin m, (k - rightLoad N z : ℕ)) := by
  classical
  have hdef : (∑ v : V, (k - G.degree v)) + (∑ v, G.degree v) =
      Fintype.card V * k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v : V, k := Finset.sum_congr rfl
        (fun v _ => Nat.sub_add_cancel (hdegree v))
      _ = _ := by simp
  have hcore : (∑ z : Fin m, (k - rightLoad N z)) + (∑ z, rightLoad N z) =
      m*k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _z : Fin m, k := Finset.sum_congr rfl
        (fun z _ => Nat.sub_add_cancel (hload z))
      _ = _ := by simp
  rw [multigraph_degree_sum] at hdef
  rw [hsum] at hcore
  have hmod : (m*k) % 2 = (Fintype.card V*k) % 2 := by
    rw [Nat.mul_mod m k 2, Nat.mul_mod (Fintype.card V) k 2, hparity]
  rw [Nat.even_iff]
  omega

/-- The average auxiliary load is small for the uniform deficiency
bound used below. The additive error from the ceiling is absorbed by the
order threshold. -/
theorem auxiliary_load_bound (α : ℝ) (n k m s : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hm : n ≤ m)
    (hlarge : 32 ≤ α*n) (hk : α*n ≤ k)
    (hs : (s : ℝ) ≤ (α/32)*(n : ℝ)^2) :
    8 * Nat.ceil ((s : ℝ)/m) ≤ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hnR hmR
  have hmean : (s : ℝ)/m ≤ (α/32)*n := by
    apply (div_le_iff₀ hmpos).mpr
    have hmul := mul_le_mul_of_nonneg_left hmR
      (show 0 ≤ (α/32)*n by positivity)
    nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (s : ℝ)/m by positivity)
  have hbound : (8 : ℝ) * Nat.ceil ((s : ℝ)/m) ≤ k := by linarith
  exact_mod_cast hbound

set_option maxHeartbeats 800000 in
/-- Uniform constants produce the incidences and the robust auxiliary
simple graph needed in Lemma 2.22. The least permitted order is used, and
the prescribed degrees and all estimates refer to the constructed graph. -/
theorem exists_auxiliary_core (α τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hτ : 0 < τ) (hτα : τ < α/24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ),
        n₀ ≤ Fintype.card V → (∀ v, G.degree v ≤ k) →
        α * Fintype.card V ≤ (k : ℝ) → k ≤ 2 * Fintype.card V →
        (∑ v, ((k - G.degree v : ℕ) : ℝ)) ≤ ε * (Fintype.card V : ℝ)^2 →
        let m := auxiliaryOrder (Fintype.card V) k
        let b := Nat.ceil ((∑ v, ((k - G.degree v : ℕ) : ℝ)) / m)
        ∃ N : V → Finset (Fin m), ∃ H : SimpleGraph (Fin m),
          ValidIncidences (fun v => k - G.degree v) N ∧
          (∀ x y, rightLoad N x ≤ rightLoad N y + 1) ∧
          (∀ z, rightLoad N z ≤ b) ∧
          (∀ z, H.degree z = k - rightLoad N z) ∧
          IsRobustExpander H ν τ ∧
          (∀ z, (k : ℝ) - b ≤ (H.degree z : ℝ)) ∧
          8*b ≤ k ∧ m ≤ 3 * Fintype.card V ∧
          (k : ℝ) < ν^2 * (m : ℝ)^2 := by
  classical
  obtain ⟨ν, hν, n₁, hrealize⟩ := balanced_robust_realization (α/4) τ
    (by positivity) (by linarith) hτ (by linarith)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (max (32/α) (2/ν^2))
  refine ⟨ν, α/32, hν, by positivity, max n₁ (max 2 n₂), ?_⟩
  intro V E _ _ G k hn hdegree hk hkupper hdef
  let n := Fintype.card V
  let m := auxiliaryOrder n k
  let b := Nat.ceil ((∑ v, ((k - G.degree v : ℕ) : ℝ)) / m)
  change ∃ N : V → Finset (Fin m), ∃ H : SimpleGraph (Fin m), _
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂' : max 2 n₂ ≤ n := (le_max_right _ _).trans hn
  have hnlarge : 2 ≤ n := (le_max_left _ _).trans hn₂'
  have hn₂'' : n₂ ≤ n := (le_max_right _ _).trans hn₂'
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn₂R : (n₂ : ℝ) ≤ n := by exact_mod_cast hn₂''
  have hthreshold : max (32/α) (2/ν^2) < (n : ℝ) := hn₂.trans_le hn₂R
  have hαn : 32 ≤ α*n := by
    have hh := (div_lt_iff₀ hα).mp ((le_max_left _ _).trans_lt hthreshold)
    nlinarith
  have hνn : 2 < ν^2*n := by
    have hh := (div_lt_iff₀ (sq_pos_of_pos hν)).mp
      ((le_max_right _ _).trans_lt hthreshold)
    nlinarith
  have hnm : n ≤ m := le_auxiliaryOrder n k
  have hkm : k < m := lt_auxiliaryOrder n k
  have hmupper : m ≤ 3*n := auxiliaryOrder_le_three_mul n k hnlarge hkupper
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hmupperR : (m : ℝ) ≤ 3*n := by exact_mod_cast hmupper
  have hb : 8*b ≤ k := by
    have hh := auxiliary_load_bound α n k m (∑ v : V, (k - G.degree v)) hα hnpos hnm
      hαn hk (by simpa only [Nat.cast_sum] using hdef)
    simpa only [Nat.cast_sum] using hh
  have hbk : b ≤ k := by omega
  have hbR : (8 : ℝ)*b ≤ k := by exact_mod_cast hb
  obtain ⟨N, hN, hbalance, hload, hsum⟩ :=
    exists_auxiliary_neighbors (fun v => k - G.degree v) m hnm
      (fun v => (Nat.sub_le k (G.degree v)).trans hkm.le)
  have hloadb (z : Fin m) : rightLoad N z ≤ b := hload z
  have hloadk (z : Fin m) : rightLoad N z ≤ k := (hloadb z).trans hbk
  have hlower (z : Fin m) : (α/4)*m ≤ (k - rightLoad N z : ℕ) := by
    have hz : (rightLoad N z : ℝ) ≤ b := by exact_mod_cast hloadb z
    rw [Nat.cast_sub (hloadk z)]
    have hmα := mul_le_mul_of_nonneg_left hmupperR hα.le
    nlinarith
  have hupper (z : Fin m) : k - rightLoad N z ≤ m-1 := by omega
  have hspread (x y : Fin m) : k - rightLoad N x ≤ k - rightLoad N y + 1 := by
    have hh := hbalance y x
    have hx := hloadk x
    have hy := hloadk y
    omega
  have heven := auxiliary_degree_sum_even G k m hdegree
    (auxiliaryOrder_mod_two n k) N hloadk hsum
  obtain ⟨H, hHdegree, hHrobust⟩ := hrealize m (hn₁.trans hnm)
    (fun z => k - rightLoad N z) hlower hupper hspread heven
  refine ⟨N, H, hN, hbalance, hload, hHdegree, hHrobust, ?_, hb, hmupper, ?_⟩
  · intro z
    have hz : (rightLoad N z : ℝ) ≤ b := by exact_mod_cast hloadb z
    rw [hHdegree z, Nat.cast_sub (hloadk z)]
    linarith
  · have hkR : (k : ℝ) ≤ 2*n := by exact_mod_cast hkupper
    have hscale := mul_lt_mul_of_pos_right hνn hnR
    have hsq := mul_self_le_mul_self (Nat.cast_nonneg n) hnmR
    have hsqν := mul_le_mul_of_nonneg_left hsq (sq_nonneg ν)
    nlinarith

end Overfull.AuxiliaryCompletion
