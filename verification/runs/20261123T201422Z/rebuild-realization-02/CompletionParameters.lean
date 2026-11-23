import Overfull.BoundaryExtension.Packing

/-!
# Uniform numerical budgets for native reserve completion

Parameters are chosen before the reserve and accepted family. The same
choice supplies the initial packing hypotheses and the later retained
degree and order margins.
-/

noncomputable section

namespace Overfull.NativeReserve

theorem packing_density_and_horizon (α : ℝ) (hα : 0 ≤ α)
    (n u k r h q : ℕ) (hu : u ≤ n) (hdensity : α*n ≤ k)
    (hreserve : (k : ℝ)/30 ≤ r) (hrh : r ≤ h) (hdegree : h+q = k) :
    α*u ≤ k ∧ (α/30)*u ≤ h ∧ q ≤ Nat.floor ((k : ℝ)-(α/30)*u) := by
  have huR : (u : ℝ) ≤ n := by exact_mod_cast hu
  have hd : α*u ≤ k := (mul_le_mul_of_nonneg_left huR hα).trans hdensity
  have hrhR : (r : ℝ) ≤ h := by exact_mod_cast hrh
  have hretain : (α/30)*u ≤ h := by linarith
  have hdegreeR : (h : ℝ)+q = k := by exact_mod_cast hdegree
  exact ⟨hd, hretain, Nat.le_floor (by linarith)⟩

theorem completion_admissibility_budgets (ε u a d degree load size : ℝ)
    (ha : a ≤ ε*u) (hsix : 6 ≤ ε*u)
    (hdegreeLower : d-a ≤ degree) (hdegreeUpper : degree ≤ d)
    (hload : load ≤ a) (hsize : size ≤ 6) :
    |degree-d| ≤ ε*u ∧ load ≤ ε*u ∧ size ≤ ε*u := by
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hload.trans ha, hsize.trans hsix⟩

theorem exists_completion_parameters (α c ε δ : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hε : 0 < ε) (hδ : 0 < δ) (m₀ : ℕ) :
    ∃ η ξ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n u k r h q : ℕ, ∀ a : ℝ,
        n₀ ≤ n → c*n ≤ u → u ≤ n → α*n ≤ k → 0 ≤ a → a ≤ ξ*n →
        (k : ℝ)/30 ≤ r → r ≤ h → h+q = k →
        (h : ℝ) ≤ r + η*k + 5 + 104*a/η →
        30 ≤ k ∧ m₀ ≤ u ∧ 6 ≤ ε*u ∧ a ≤ ε*u ∧ a ≤ n ∧
          α*u ≤ k ∧ (α/30)*u ≤ h ∧ q ≤ Nat.floor ((k : ℝ)-(α/30)*u) ∧
          (h : ℝ)-r ≤ δ*k ∧ a ≤ (k : ℝ)/60 ∧ (α/60)*u ≤ (h : ℝ)-a := by
  let η := min 1 (δ/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : η ≤ δ/4 := min_le_right _ _
  let ξ := min 1 (min (c*ε) (min (α/60) (δ*η*α/416)))
  have hξ : 0 < ξ := lt_min (by norm_num)
    (lt_min (mul_pos hc hε) (lt_min (by positivity) (by positivity)))
  have hξ1 : ξ ≤ 1 := min_le_left _ _
  have hξε : ξ ≤ c*ε := (min_le_right _ _).trans (min_le_left _ _)
  have hξrest : ξ ≤ min (α/60) (δ*η*α/416) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hξα : ξ ≤ α/60 := hξrest.trans (min_le_left _ _)
  have hξδ : ξ ≤ δ*η*α/416 := hξrest.trans (min_le_right _ _)
  let T : ℝ := max 1 (max (30/α) (max ((m₀ : ℝ)/c)
    (max (6/(ε*c)) (20/(δ*α)))))
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge T
  have hn₀pos : 1 ≤ n₀ := by
    have h : (1 : ℝ) ≤ n₀ := (le_max_left _ _).trans hn₀
    exact_mod_cast h
  refine ⟨η, ξ, hη, hη1, hξ, hξ1, n₀, hn₀pos, ?_⟩
  intro n u k r h q a hn hcore hu hdensity _ha ha hreserve hrh hdegree hsurplus
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hT : T ≤ (n : ℝ) := hn₀.trans hnR
  have hb : (1 : ℝ) ≤ n ∧ 30/α ≤ n ∧ (m₀ : ℝ)/c ≤ n ∧
      6/(ε*c) ≤ n ∧ 20/(δ*α) ≤ n := by
    simpa only [T, max_le_iff] using hT
  have hk30 : (30 : ℝ) ≤ k := by
    have hh := (div_le_iff₀ hα).mp hb.2.1
    linarith
  have hm : (m₀ : ℝ) ≤ u := by
    have hh := (div_le_iff₀ hc).mp hb.2.2.1
    linarith
  have hfoot : (6 : ℝ) ≤ ε*u := by
    have hh := (div_le_iff₀ (mul_pos hε hc)).mp hb.2.2.2.1
    have hmul := mul_le_mul_of_nonneg_left hcore hε.le
    nlinarith only [hh, hmul]
  have haCore : a ≤ ε*u := by
    have hmul := mul_le_mul_of_nonneg_left hcore hε.le
    have hξn := mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [ha, hmul, hξn]
  have haOrder : a ≤ n := by
    have hξn := mul_le_mul_of_nonneg_right hξ1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [ha, hξn]
  have hpack := packing_density_and_horizon α hα.le n u k r h q hu hdensity
    hreserve hrh hdegree
  have hηterm : η*k ≤ δ*k/4 := by
    have hh := mul_le_mul_of_nonneg_right hηδ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [hh]
  have hconstant : (5 : ℝ) ≤ δ*k/4 := by
    have hh := (div_le_iff₀ (mul_pos hδ hα)).mp hb.2.2.2.2
    have hmul := mul_le_mul_of_nonneg_left hdensity hδ.le
    nlinarith only [hh, hmul]
  have hdefect : 104*a/η ≤ δ*k/4 := by
    apply (div_le_iff₀ hη).mpr
    have hξn := mul_le_mul_of_nonneg_right hξδ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hmul := mul_le_mul_of_nonneg_left hdensity (mul_nonneg hδ.le hη.le)
    nlinarith only [ha, hξn, hmul]
  have hmargin : (h : ℝ)-r ≤ δ*k := by
    have hnonneg := mul_nonneg hδ.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have haSmall : a ≤ (k : ℝ)/60 := by
    have hξn := mul_le_mul_of_nonneg_right hξα (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [ha, hξn, hdensity]
  have hretainCore : (α/60)*u ≤ (h : ℝ)-a := by
    have hrhR : (r : ℝ) ≤ h := by exact_mod_cast hrh
    nlinarith only [hpack.1, hreserve, hrhR, haSmall]
  exact ⟨by exact_mod_cast hk30, by exact_mod_cast hm, hfoot, haCore, haOrder,
    hpack.1, hpack.2.1, hpack.2.2, hmargin, haSmall, hretainCore⟩

theorem exists_completion_setup_parameters (α c ε δ : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hε : 0 < ε) (hδ : 0 < δ) (m₀ : ℕ) :
    ∃ η ξ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n u k : ℕ, ∀ a : ℝ,
        n₀ ≤ n → c*n ≤ u → u ≤ n → α*n ≤ k → 0 ≤ a → a ≤ ξ*n →
        30 ≤ k ∧ m₀ ≤ u ∧ 6 ≤ ε*u ∧ a ≤ ε*u ∧ a ≤ n ∧ α*u ≤ k ∧
          a ≤ (k : ℝ)/60 ∧
          ∀ r h q : ℕ, (k : ℝ)/30 ≤ r → r ≤ h → h+q = k →
            (h : ℝ) ≤ r + η*k + 5 + 104*a/η →
            (α/30)*u ≤ h ∧ q ≤ Nat.floor ((k : ℝ)-(α/30)*u) ∧
              (h : ℝ)-r ≤ δ*k ∧ (α/60)*u ≤ (h : ℝ)-a := by
  obtain ⟨η, ξ, hη, hη1, hξ, hξ1, n₀, hn₀, hparams⟩ :=
    exists_completion_parameters α c ε δ hα hc hε hδ m₀
  refine ⟨η, ξ, hη, hη1, hξ, hξ1, n₀, hn₀, ?_⟩
  intro n u k a hn hcore hu hdensity ha haSmall
  have hreserve : (k : ℝ)/30 ≤ k := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hsurplus : (k : ℝ) ≤ k+η*k+5+104*a/η := by
    have hround : 0 ≤ η*(k : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
    have hdefect : 0 ≤ 104*a/η := div_nonneg (mul_nonneg (by norm_num) ha) hη.le
    linarith
  obtain ⟨hk30, hm, hfoot, haCore, haOrder, hd, _, _, _, haDegree, _⟩ :=
    hparams n u k k k 0 a hn hcore hu hdensity ha haSmall
      hreserve le_rfl (by omega) hsurplus
  refine ⟨hk30, hm, hfoot, haCore, haOrder, hd, haDegree, ?_⟩
  intro r h q hreserve hrh hdegree hsurplus
  obtain ⟨_, _, _, _, _, _, hretained, hhorizon, hmargin, _, hretainedCore⟩ :=
    hparams n u k r h q a hn hcore hu hdensity ha haSmall
      hreserve hrh hdegree hsurplus
  exact ⟨hretained, hhorizon, hmargin, hretainedCore⟩

theorem margin_of_degree_upper (δ κ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (n k h r : ℕ) (hdegree : (k : ℝ) ≤ κ*n)
    (hmargin : (h : ℝ)-r ≤ (δ/κ)*k) : (h : ℝ)-r ≤ δ*n := by
  have hh := mul_le_mul_of_nonneg_left hdegree (div_nonneg hδ hκ.le)
  have heq : (δ/κ)*(κ*(n : ℝ)) = δ*n := by
    field_simp
  rw [heq] at hh
  exact hmargin.trans hh

theorem degree_le_twice_order (n u k : ℕ) (a d : ℝ)
    (hu : u ≤ n) (ha : a ≤ n) (hcoreUpper : d ≤ u) (hdefect : (k : ℝ)-a ≤ d) :
    (k : ℝ) ≤ 2*n := by
  have huR : (u : ℝ) ≤ n := by exact_mod_cast hu
  linarith

end Overfull.NativeReserve
