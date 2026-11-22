import Overfull.Probability.WeightedSampling

/-!
# Translation invariance and additive product variance

These finite identities retain the coefficient one for weighted exceptional
rows sampled independently in vertex parts.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

variable {Ω : Type*} [Fintype Ω]

/-- Adding a constant does not change a centered second moment under a
normalized finite law. -/
theorem variance_add_const (p : Ω → ℝ) (hp : (∑ x, p x) = 1)
    (f : Ω → ℝ) (c : ℝ) :
    variance p (fun x => f x + c) = variance p f := by
  unfold variance
  rw [mean_add, mean_const p hp]
  congr 1
  funext x
  congr 1
  ring

theorem variance_const_add (p : Ω → ℝ) (hp : (∑ x, p x) = 1)
    (f : Ω → ℝ) (c : ℝ) :
    variance p (fun x => c + f x) = variance p f := by
  simpa only [add_comm c] using variance_add_const p hp f c

/-- The variance of a sum of independent coordinate statistics is bounded
by the sum of their actual variances. -/
theorem variance_pi_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ∀ i, κ i → ℝ) (hp : ∀ i x, 0 ≤ p i x)
    (hpsum : ∀ i, (∑ x, p i x) = 1) (f : ∀ i, κ i → ℝ) :
    variance (piWeight p) (fun x => ∑ i, f i (x i)) ≤
      ∑ i, variance (p i) (f i) := by
  apply variance_pi_le p hp hpsum _ (fun i => variance (p i) (f i))
  intro i x
  have hsection : (fun y => ∑ j, f j (Function.update x i y j)) =
      (fun y => f i y + ∑ j ∈ univ.erase i, f j (x j)) := by
    funext y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (f j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 y x)
  rw [hsection, variance_add_const (p i) (hpsum i)]

end Overfull.FiniteProbability
