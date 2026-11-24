import Overfull.Probability.WeightedSampling

/-!
# Exact moments of finite product laws

Independent coordinate laws are the actual product weights. Normalization
is required only when unused coordinates are integrated out.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- The expectation of a product of coordinate statistics factors exactly. -/
theorem mean_pi_product (p : ∀ i, κ i → ℝ) (f : ∀ i, κ i → ℝ) :
    mean (piWeight p) (fun x => ∏ i, f i (x i)) =
      ∏ i, mean (p i) (f i) := by
  classical
  simp only [mean, piWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => p i x * f i x)).symm

private def coordinateFactor (i : ι) (f : κ i → ℝ) (j : ι) (x : κ j) : ℝ :=
  if h : j = i then f (h ▸ x) else 1

omit [Fintype ι] [∀ i, Fintype (κ i)] in
private theorem coordinateFactor_self (i : ι) (f : κ i → ℝ) :
    coordinateFactor i f i = f := by
  funext x
  simp [coordinateFactor]

omit [Fintype ι] [∀ i, Fintype (κ i)] in
private theorem coordinateFactor_other (i : ι) (f : κ i → ℝ) (j : ι) (hji : j ≠ i) :
    coordinateFactor i f j = fun _ => 1 := by
  funext x
  simp [coordinateFactor, hji]

omit [∀ i, Fintype (κ i)] in
private theorem prod_coordinateFactor (i : ι) (f : κ i → ℝ) (x : ∀ j, κ j) :
    (∏ j, coordinateFactor i f j (x j)) = f (x i) := by
  rw [Finset.prod_eq_single i]
  · rw [coordinateFactor_self]
  · intro j _ hji
    rw [coordinateFactor_other i f j hji]
  · simp

private theorem prod_mean_coordinateFactor (p : ∀ i, κ i → ℝ)
    (hp : ∀ i, (∑ x, p i x) = 1) (i : ι) (f : κ i → ℝ) :
    (∏ j, mean (p j) (coordinateFactor i f j)) = mean (p i) f := by
  rw [Finset.prod_eq_single i]
  · rw [coordinateFactor_self]
  · intro j _ hji
    rw [coordinateFactor_other i f j hji]
    exact mean_const (p j) (hp j) 1
  · simp

/-- Integrating a statistic of one coordinate gives that coordinate's law. -/
theorem mean_pi_coordinate (p : ∀ i, κ i → ℝ)
    (hp : ∀ i, (∑ x, p i x) = 1) (i : ι) (f : κ i → ℝ) :
    mean (piWeight p) (fun x => f (x i)) = mean (p i) f := by
  calc
    _ = mean (piWeight p) (fun x => ∏ j, coordinateFactor i f j (x j)) := by
      congr 1
      funext x
      exact (prod_coordinateFactor i f x).symm
    _ = ∏ j, mean (p j) (coordinateFactor i f j) := mean_pi_product p _
    _ = _ := prod_mean_coordinateFactor p hp i f

/-- The exact mean of a sum of coordinate statistics. -/
theorem mean_pi_sum (p : ∀ i, κ i → ℝ)
    (hp : ∀ i, (∑ x, p i x) = 1) (f : ∀ i, κ i → ℝ) :
    mean (piWeight p) (fun x => ∑ i, f i (x i)) =
      ∑ i, mean (p i) (f i) := by
  rw [mean_sum]
  exact Finset.sum_congr rfl (fun i _ => mean_pi_coordinate p hp i (f i))

/-- Distinct coordinates are independent for arbitrary real statistics. -/
theorem mean_pi_mul_coordinates (p : ∀ i, κ i → ℝ)
    (hp : ∀ i, (∑ x, p i x) = 1) (i j : ι) (hij : i ≠ j)
    (f : κ i → ℝ) (g : κ j → ℝ) :
    mean (piWeight p) (fun x => f (x i) * g (x j)) =
      mean (p i) f * mean (p j) g := by
  have hfactor (k : ι) :
      mean (p k) (fun x => coordinateFactor i f k x * coordinateFactor j g k x) =
        mean (p k) (coordinateFactor i f k) *
          mean (p k) (coordinateFactor j g k) := by
    by_cases hki : k = i
    · subst k
      rw [coordinateFactor_self, coordinateFactor_other j g i hij]
      simp only [mul_one, mean_const (p i) (hp i)]
    · rw [coordinateFactor_other i f k hki]
      simp only [one_mul, mean_const (p k) (hp k)]
  calc
    _ = mean (piWeight p) (fun x => ∏ k,
        coordinateFactor i f k (x k) * coordinateFactor j g k (x k)) := by
      congr 1
      funext x
      rw [Finset.prod_mul_distrib, prod_coordinateFactor, prod_coordinateFactor]
    _ = ∏ k, mean (p k)
        (fun x => coordinateFactor i f k x * coordinateFactor j g k x) :=
      mean_pi_product p (fun k x => coordinateFactor i f k x * coordinateFactor j g k x)
    _ = (∏ k, mean (p k) (coordinateFactor i f k)) *
        (∏ k, mean (p k) (coordinateFactor j g k)) := by
      simp only [hfactor, Finset.prod_mul_distrib]
    _ = _ := by rw [prod_mean_coordinateFactor p hp, prod_mean_coordinateFactor p hp]

end Overfull.FiniteProbability
