import Overfull.BipartiteFactorization.BlockProductSampling
import Overfull.Probability.ProductMoments

/-!
# Vertex and edge inclusion in independently sampled blocks

Disjoint parts identify every vertex with its actual coordinate. Exact
one- and two-vertex laws give a lower bound for the expected number of
original internal edge copies, including parallel copies separately.
-/

noncomputable section

namespace Overfull.Hypergeometric

open Finset Classical FiniteProbability

variable {E : Type*} [Fintype E]

/-- Exact simultaneous inclusion of two distinct population members. -/
theorem mean_pair_indicator_eq (s : ℕ) (hs : s ≤ Fintype.card E)
    (hs₂ : 2 ≤ s) (x y : E) (hxy : x ≠ y) :
    mean (weight s) (fun T => if x ∈ T ∧ y ∈ T then 1 else 0) =
      (s : ℝ) * ((s : ℝ) - 1) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ) - 1)) := by
  have hN₂ : 2 ≤ Fintype.card E := hs₂.trans hs
  have hNchoose : (Nat.choose (Fintype.card E) s : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hs
  have htwochoose : (Nat.choose (Fintype.card E) 2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hN₂
  have hratio : (Nat.choose (Fintype.card E - 2) (s - 2) : ℝ) /
      Nat.choose (Fintype.card E) s =
        (Nat.choose s 2 : ℝ) / Nat.choose (Fintype.card E) 2 := by
    apply (div_eq_div_iff hNchoose htwochoose).mpr
    have hc : (Nat.choose (Fintype.card E) s : ℝ) * Nat.choose s 2 =
        (Nat.choose (Fintype.card E) 2 : ℝ) *
          Nat.choose (Fintype.card E - 2) (s - 2) := by
      exact_mod_cast Nat.choose_mul hs hs₂
    nlinarith
  have htwo (n : ℕ) (hn : 1 ≤ n) :
      (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 2
    norm_num [Nat.descFactorial_succ] at h
    have hc : ((n - 1 : ℕ) : ℝ) * n = 2 * (Nat.choose n 2 : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hn] at hc
    norm_num at hc
    nlinarith
  have hpair := probability_containing ({x, y} : Finset E) s
    (by simpa only [Finset.card_pair hxy] using hs₂)
  simp only [Finset.card_pair hxy, Finset.insert_subset_iff,
    Finset.singleton_subset_iff] at hpair
  rw [mean_indicator]
  change probability s (fun T => x ∈ T ∧ y ∈ T) = _
  rw [hpair, hratio, htwo s (by omega), htwo (Fintype.card E) (by omega)]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

/-- Selecting at least two vertices gives half the independent pair rate. -/
theorem mean_pair_indicator_ge_half (s : ℕ) (hs : s ≤ Fintype.card E)
    (hs₂ : 2 ≤ s) (x y : E) (hxy : x ≠ y) (p : ℝ)
    (hfraction : (s : ℝ) = p * Fintype.card E) :
    p ^ 2 / 2 ≤ mean (weight s) (fun T => if x ∈ T ∧ y ∈ T then 1 else 0) := by
  have hN₂ : 2 ≤ Fintype.card E := hs₂.trans hs
  have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs₂
  have hNreal : (2 : ℝ) ≤ Fintype.card E := by exact_mod_cast hN₂
  rw [mean_pair_indicator_eq s hs hs₂ x y hxy]
  apply (le_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
  calc
    p ^ 2 / 2 * ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ) - 1)) ≤
        p ^ 2 / 2 * ((Fintype.card E : ℝ) * Fintype.card E) := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · positivity
    _ = (s : ℝ) ^ 2 / 2 := by rw [hfraction]; ring
    _ ≤ (s : ℝ) * ((s : ℝ) - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hsreal (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]

end Overfull.Hypergeometric

namespace Overfull.BipartiteFactorization.BlockProductSampling

open Finset Classical FiniteProbability

variable {V E ι : Type*} [Fintype ι]

/-- Exact one-vertex inclusion law, with all other coordinates integrated out. -/
theorem mean_member_part (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card) (i : ι) (x : D i) :
    mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => if x.val ∈ sampledBlock D τ then 1 else 0) =
        (s i : ℝ) / (D i).card := by
  simp_rw [sampledBlock_mem_part D hdisj]
  rw [mean_pi_coordinate (fun k => Hypergeometric.weight (E := ↥(D k)) (s k))
    (fun j => Hypergeometric.sum_weight (E := ↥(D j)) (s j) (by simpa using hs j)) i
    (fun T : Finset (D i) => if x ∈ T then 1 else 0)]
  have h := Hypergeometric.mean_member_indicator (s i)
    (by simpa only [Fintype.card_coe] using hs i) x
  simp only [Fintype.card_coe] at h
  convert h using 1
  congr 1
  funext T
  by_cases hx : x ∈ T <;> simp [hx]

/-- Exact pair inclusion when the two original vertices are in one part. -/
theorem mean_pair_same_part (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (i : ι) (hsi : 2 ≤ s i) (x y : D i) (hxy : x ≠ y) :
    mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => if x.val ∈ sampledBlock D τ ∧ y.val ∈ sampledBlock D τ
        then 1 else 0) =
      (s i : ℝ) * ((s i : ℝ) - 1) /
        (((D i).card : ℝ) * (((D i).card : ℝ) - 1)) := by
  simp_rw [sampledBlock_mem_part D hdisj]
  rw [mean_pi_coordinate (fun k => Hypergeometric.weight (E := ↥(D k)) (s k))
    (fun j => Hypergeometric.sum_weight (E := ↥(D j)) (s j) (by simpa using hs j)) i
    (fun T : Finset (D i) => if x ∈ T ∧ y ∈ T then 1 else 0)]
  have h := Hypergeometric.mean_pair_indicator_eq (s i)
    (by simpa only [Fintype.card_coe] using hs i) hsi x y hxy
  simp only [Fintype.card_coe] at h
  convert h using 1
  congr 1
  funext T
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]

/-- Vertices in different parts have exactly independent inclusion events. -/
theorem mean_pair_distinct_parts (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (i j : ι) (hij : i ≠ j) (x : D i) (y : D j) :
    mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => if x.val ∈ sampledBlock D τ ∧ y.val ∈ sampledBlock D τ
        then 1 else 0) =
      ((s i : ℝ) / (D i).card) * ((s j : ℝ) / (D j).card) := by
  simp_rw [sampledBlock_mem_part D hdisj]
  have hpoint (τ : ∀ k, Finset (D k)) :
      (if x ∈ τ i ∧ y ∈ τ j then (1 : ℝ) else 0) =
        (if x ∈ τ i then 1 else 0) * (if y ∈ τ j then 1 else 0) := by
    by_cases hx : x ∈ τ i <;> by_cases hy : y ∈ τ j <;> simp [hx, hy]
  simp_rw [hpoint]
  rw [mean_pi_mul_coordinates (fun k => Hypergeometric.weight (E := ↥(D k)) (s k))
    (fun k => Hypergeometric.sum_weight (E := ↥(D k)) (s k) (by simpa using hs k)) i j hij
    (fun T : Finset (D i) => if x ∈ T then 1 else 0)
    (fun T : Finset (D j) => if y ∈ T then 1 else 0)]
  have hmember (k : ι) (v : D k) :
      mean (Hypergeometric.weight (s k))
        (fun T : Finset (D k) => if v ∈ T then 1 else 0) =
          (s k : ℝ) / (D k).card := by
    have h := Hypergeometric.mean_member_indicator (s k)
      (by simpa only [Fintype.card_coe] using hs k) v
    simp only [Fintype.card_coe] at h
    convert h using 1
    congr 1
    funext T
    by_cases hv : v ∈ T <;> simp [hv]
  rw [hmember i x, hmember j y]

/-- A common sampling fraction gives the stated marginal for every vertex. -/
theorem mean_member_eq (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (v : V) (hv : v ∈ B) :
    mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => if v ∈ sampledBlock D τ then 1 else 0) = p₀ := by
  rw [← hcover] at hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  have hn : ((D i).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨v, hi⟩).ne'
  simpa only [hfraction i, mul_div_cancel_right₀ _ hn] using
    mean_member_part D hdisj s hs i ⟨v, hi⟩

/-- Every distinct pair in the covered side has at least half the
independent inclusion rate. Empty parts impose no lower sample size. -/
theorem mean_pair_ge_half (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (u v : V) (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v) :
    p₀ ^ 2 / 2 ≤
      mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
        (fun τ => if u ∈ sampledBlock D τ ∧ v ∈ sampledBlock D τ
          then 1 else 0) := by
  rw [← hcover] at hu hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
  by_cases hij : i = j
  · subst j
    have hxy : (⟨u, hi⟩ : D i) ≠ ⟨v, hj⟩ := fun h => huv (congrArg Subtype.val h)
    rw [mean_pair_same_part D hdisj s hs i (hselect i ⟨u, hi⟩)
      ⟨u, hi⟩ ⟨v, hj⟩ hxy]
    have h := Hypergeometric.mean_pair_indicator_ge_half (E := ↥(D i)) (s i)
      (by simpa using hs i) (hselect i ⟨u, hi⟩) ⟨u, hi⟩ ⟨v, hj⟩ hxy p₀
      (by simpa only [Fintype.card_coe] using hfraction i)
    rw [Hypergeometric.mean_pair_indicator_eq (E := ↥(D i)) (s i) (by simpa using hs i)
      (hselect i ⟨u, hi⟩) ⟨u, hi⟩ ⟨v, hj⟩ hxy] at h
    simpa only [Fintype.card_coe] using h
  · have hni : ((D i).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨u, hi⟩).ne'
    have hnj : ((D j).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨v, hj⟩).ne'
    have heq := mean_pair_distinct_parts D hdisj s hs i j hij ⟨u, hi⟩ ⟨v, hj⟩
    simp only [hfraction i, hfraction j, mul_div_cancel_right₀ _ hni,
      mul_div_cancel_right₀ _ hnj] at heq
    rw [heq]
    nlinarith [sq_nonneg p₀]

variable [Fintype E] (G : Multigraph V E)

/-- The expectation counts every original internal edge copy. Parallel
copies contribute separately and require no independence between edges. -/
theorem mean_internalEdges_ge (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i) :
    (p₀ ^ 2 / 2) * (G.internalEdges B).card ≤
      mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
        (fun τ => ((G.internalEdges (sampledBlock D τ)).card : ℝ)) := by
  let p := piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i))
  let X : E → (∀ i, Finset (D i)) → ℝ := fun e τ =>
    if G.firstEnd e ∈ sampledBlock D τ ∧ G.secondEnd e ∈ sampledBlock D τ
      then 1 else 0
  have hcard (T : Finset V) : ((G.internalEdges T).card : ℝ) =
      ∑ e : E, if G.firstEnd e ∈ T ∧ G.secondEnd e ∈ T then (1 : ℝ) else 0 := by
    have hset : (univ : Finset E).filter
        (fun e => G.firstEnd e ∈ T ∧ G.secondEnd e ∈ T) = G.internalEdges T := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G.mem_internalEdges]
    rw [← Finset.sum_filter]
    simp only [hset, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hp : ∀ τ, 0 ≤ p τ := piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg (s i))
  have hnonneg (e : E) : 0 ≤ mean p (X e) :=
    mean_nonneg p hp (X e) (fun _ => by dsimp only [X]; split_ifs <;> norm_num)
  calc
    _ = ∑ _e ∈ G.internalEdges B, p₀ ^ 2 / 2 := by simp [mul_comm]
    _ ≤ ∑ e ∈ G.internalEdges B, mean p (X e) := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨hu, hv⟩ := (G.mem_internalEdges B e).mp he
      exact mean_pair_ge_half D hdisj B hcover s hs p₀ hfraction hselect
        (G.firstEnd e) (G.secondEnd e) hu hv (G.endpoints_distinct e)
    _ ≤ ∑ e : E, mean p (X e) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun e _ _ => hnonneg e)
    _ = _ := by
      simp_rw [hcard, mean_sum]
      rfl

end Overfull.BipartiteFactorization.BlockProductSampling
