import Overfull.Probability.ProductMoments
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Exact event laws for coordinate maps of finite product samples

Each coordinate map pushes its actual source weights to the stated target
weights. Factoring the mass of one full tuple then transfers every joint
event, including events depending on several or all coordinates.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

section FiniteMap

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- Finite fiberwise grouping transfers an arbitrary real statistic when
the mass of every target fiber is known exactly. -/
theorem mean_map_of_fibers (p : Ω → ℝ) (q : Λ → ℝ) (f : Ω → Λ)
    (hf : ∀ y, MatchingProbability.probability p (fun x => f x = y) = q y)
    (g : Λ → ℝ) : mean p (fun x => g (f x)) = mean q g := by
  classical
  unfold mean
  calc
    (∑ x, p x * g (f x)) =
        ∑ y, ∑ x ∈ univ.filter (fun x => f x = y), p x * g (f x) := by
      exact (Finset.sum_fiberwise univ f (fun x => p x * g (f x))).symm
    _ = ∑ y, (∑ x ∈ univ.filter (fun x => f x = y), p x) * g y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ y, q y * g y := by
      apply Finset.sum_congr rfl
      intro y _
      have hy : (∑ x ∈ univ.filter (fun x => f x = y), p x) = q y := hf y
      rw [hy]

/-- Exact target-fiber masses transfer every event, without any condition
on the shape of that event. -/
theorem probability_map_of_fibers (p : Ω → ℝ) (q : Λ → ℝ) (f : Ω → Λ)
    (hf : ∀ y, MatchingProbability.probability p (fun x => f x = y) = q y)
    (Q : Λ → Prop) :
    MatchingProbability.probability p (fun x => Q (f x)) =
      MatchingProbability.probability q Q := by
  classical
  have h := mean_map_of_fibers p q f hf (fun y => if Q y then 1 else 0)
  simpa only [mean_indicator] using h

end FiniteMap

section Product

variable {ι : Type*} [Fintype ι] {Ω Λ : ι → Type*}
  [∀ i, Fintype (Ω i)] [∀ i, Fintype (Λ i)]

omit [∀ i, Fintype (Λ i)] in
/-- The mass of each full mapped tuple factors into the exact coordinate
fiber masses under the actual product weight. -/
theorem probability_pi_map_eq (a : ∀ i, Ω i → ℝ) (b : ∀ i, Λ i → ℝ)
    (f : ∀ i, Ω i → Λ i)
    (hf : ∀ i y, MatchingProbability.probability (a i) (fun x => f i x = y) = b i y)
    (y : ∀ i, Λ i) :
    MatchingProbability.probability (piWeight a)
      (fun x => (fun i => f i (x i)) = y) = piWeight b y := by
  classical
  have hindicator :
      (fun x : ∀ i, Ω i => if (fun i => f i (x i)) = y then (1 : ℝ) else 0) =
        (fun x => ∏ i, if f i (x i) = y i then (1 : ℝ) else 0) := by
    funext x
    rw [Fintype.prod_boole]
    simp only [funext_iff]
  rw [← mean_indicator, hindicator,
    mean_pi_product a (fun i z => if f i z = y i then (1 : ℝ) else 0)]
  unfold piWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [mean_indicator, hf]

/-- Arbitrary joint statistics have the same expectation after coordinate
maps with the stated exact finite pushforward laws. -/
theorem mean_pi_map (a : ∀ i, Ω i → ℝ) (b : ∀ i, Λ i → ℝ)
    (f : ∀ i, Ω i → Λ i)
    (hf : ∀ i y, MatchingProbability.probability (a i) (fun x => f i x = y) = b i y)
    (g : (∀ i, Λ i) → ℝ) :
    mean (piWeight a) (fun x => g (fun i => f i (x i))) = mean (piWeight b) g := by
  exact mean_map_of_fibers (piWeight a) (piWeight b) (fun x i => f i (x i))
    (probability_pi_map_eq a b f hf) g

/-- Every event of all mapped coordinates has the exact target product law.
The event need not factor by coordinate. -/
theorem probability_pi_map (a : ∀ i, Ω i → ℝ) (b : ∀ i, Λ i → ℝ)
    (f : ∀ i, Ω i → Λ i)
    (hf : ∀ i y, MatchingProbability.probability (a i) (fun x => f i x = y) = b i y)
    (Q : (∀ i, Λ i) → Prop) :
    MatchingProbability.probability (piWeight a) (fun x => Q (fun i => f i (x i))) =
      MatchingProbability.probability (piWeight b) Q := by
  exact probability_map_of_fibers (piWeight a) (piWeight b) (fun x i => f i (x i))
    (probability_pi_map_eq a b f hf) Q

end Product

end Overfull.FiniteProbability
