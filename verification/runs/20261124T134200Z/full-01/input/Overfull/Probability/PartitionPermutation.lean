import Overfull.Probability.ProductMap
import Overfull.Probability.PermutationSampling

/-!
# One permutation in every part, shared by all block labels

Each part is permuted independently. Every fixed tuple of position sets
has the exact product fixed-size subset law, even for events depending on
all parts. Different members of a family use the same permutations;
their position sets may overlap, as fine blocks and their coarse unions do.
-/

noncomputable section

namespace Overfull.PartitionPermutation

open Finset Classical FiniteProbability

variable {ι : Type*} {E : ι → Type*}

/-- Apply one actual permutation in each part to a tuple of position sets. -/
def sample (S : ∀ i, Finset (E i)) (σ : ∀ i, Equiv.Perm (E i)) :
    ∀ i, Finset (E i) := fun i => PermutationSampling.sample (S i) (σ i)

@[simp] theorem sample_card (S : ∀ i, Finset (E i))
    (σ : ∀ i, Equiv.Perm (E i)) (i : ι) :
    (sample S σ i).card = (S i).card := PermutationSampling.sample_card _ _

@[simp] theorem mem_sample (S : ∀ i, Finset (E i))
    (σ : ∀ i, Equiv.Perm (E i)) (i : ι) (x : E i) :
    x ∈ sample S σ i ↔ (σ i).symm x ∈ S i := PermutationSampling.mem_sample _ _ _

/-- Every supplied coordinate inclusion is preserved by the shared permutations. -/
theorem sample_mono {S T : ∀ i, Finset (E i)}
    (hST : ∀ i, S i ⊆ T i) (σ : ∀ i, Equiv.Perm (E i)) :
    ∀ i, sample S σ i ⊆ sample T σ i := by
  intro i x hx
  exact (mem_sample T σ i x).mpr (hST i ((mem_sample S σ i x).mp hx))

/-- Only the disjointness present in the position sets is required or asserted. -/
theorem sample_disjoint (S T : ∀ i, Finset (E i))
    (σ : ∀ i, Equiv.Perm (E i)) (hST : ∀ i, Disjoint (S i) (T i)) :
    ∀ i, Disjoint (sample S σ i) (sample T σ i) := by
  intro i
  exact PermutationSampling.sample_disjoint _ _ _ (hST i)

/-- A coarse union of position sets is exactly the union of their actual images. -/
theorem sample_biUnion {γ : Type*} (J : Finset γ)
    (S : γ → ∀ i, Finset (E i)) (σ : ∀ i, Equiv.Perm (E i)) :
    sample (fun i => J.biUnion (fun j => S j i)) σ =
      fun i => J.biUnion (fun j => sample (S j) σ i) := by
  classical
  funext i
  ext x
  simp only [mem_sample, Finset.mem_biUnion]

@[simp] theorem sample_univ [∀ i, Fintype (E i)] (σ : ∀ i, Equiv.Perm (E i)) :
    sample (fun _ => univ) σ = fun _ => univ := by
  classical
  funext i
  ext x
  simp only [mem_sample, Finset.mem_univ]

section Probability

variable [Fintype ι] [∀ i, Fintype (E i)]

/-- Actual independent uniform-permutation weights for the finite parts. -/
def weight (σ : ∀ i, Equiv.Perm (E i)) : ℝ :=
  piWeight (fun i => PermutationSampling.weight (E := E i)) σ

def probability (P : (∀ i, Equiv.Perm (E i)) → Prop) : ℝ :=
  MatchingProbability.probability weight P

theorem weight_nonneg (σ : ∀ i, Equiv.Perm (E i)) : 0 ≤ weight σ :=
  piWeight_nonneg _ (fun _ => PermutationSampling.weight_nonneg) σ

theorem sum_weight : (∑ σ : ∀ i, Equiv.Perm (E i), weight σ) = 1 := by
  classical
  exact sum_piWeight _ (fun _ => PermutationSampling.sum_weight)

/-- Every joint event of one tuple of sampled position sets has exactly
the independent fixed-size subset law. -/
theorem probability_sample (S : ∀ i, Finset (E i))
    (Q : (∀ i, Finset (E i)) → Prop) :
    probability (fun σ => Q (sample S σ)) =
      MatchingProbability.probability
        (piWeight (fun i => Hypergeometric.weight (S i).card)) Q := by
  classical
  exact probability_pi_map
    (fun i => PermutationSampling.weight (E := E i))
    (fun i => Hypergeometric.weight (S i).card)
    (fun i => PermutationSampling.sample (S i))
    (fun i T => PermutationSampling.probability_sample_eq (S i) T) Q

/-- A family of arbitrary, possibly overlapping position tuples has one
shared tuple of permutations making every image good whenever the sum of
its marginal bad-event bounds is below one. -/
theorem exists_good_images {γ : Type*} [Fintype γ]
    (S : γ → ∀ i, Finset (E i))
    (bad : γ → (∀ i, Finset (E i)) → Prop) (ε : γ → ℝ)
    (hbad : ∀ j, MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (S j i).card)) (bad j) ≤ ε j)
    (hε : (∑ j, ε j) < 1) :
    ∃ σ : ∀ i, Equiv.Perm (E i), ∀ j, ¬ bad j (sample (S j) σ) := by
  classical
  let P := fun σ : ∀ i, Equiv.Perm (E i) => ∃ j, bad j (sample (S j) σ)
  have hbound : probability P < 1 := by
    have hu := MatchingProbability.probability_exists_le_sum weight weight_nonneg univ
      (fun j σ => bad j (sample (S j) σ))
    have hu' : probability P ≤ ∑ j, probability (fun σ => bad j (sample (S j) σ)) := by
      simpa only [probability, P, Finset.mem_univ, true_and] using hu
    apply lt_of_le_of_lt hu'
    calc
      _ ≤ ∑ j, ε j := by
        apply Finset.sum_le_sum
        intro j _
        rw [probability_sample]
        exact hbad j
      _ < 1 := hε
  have hex : ∃ σ : ∀ i, Equiv.Perm (E i), ¬ P σ := by
    by_contra h
    push_neg at h
    have heq : probability P = 1 := by
      unfold probability MatchingProbability.probability
      simp only [Finset.sum_filter, h, if_true]
      exact sum_weight
    rw [heq] at hbound
    exact lt_irrefl _ hbound
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨σ, ?_⟩
  intro j hj
  exact hσ ⟨j, hj⟩

omit [Fintype ι] in
/-- Prescribed sizes fitting in every coordinate population admit actual
position tuples that are pairwise disjoint in every coordinate. -/
theorem exists_positions {γ : Type*} [Fintype γ] (n : γ → ι → ℕ)
    (hn : ∀ i, (∑ j, n j i) ≤ Fintype.card (E i)) :
    ∃ S : γ → ∀ i, Finset (E i),
      (∀ j i, (S j i).card = n j i) ∧
      ∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i) := by
  classical
  have hex (i : ι) := PermutationSampling.exists_positions
    (E := E i) (fun j => n j i) (hn i)
  choose S hcard hdisj using hex
  refine ⟨fun j i => S i j, ?_, ?_⟩
  · intro j i
    exact hcard i j
  · intro j l hjl i
    exact hdisj i j l hjl

/-- A disjoint family with prescribed coordinate sizes and all requested
properties exists from its explicit marginal product-sampling budgets. -/
theorem exists_disjoint_samples {γ : Type*} [Fintype γ]
    (n : γ → ι → ℕ) (hn : ∀ i, (∑ j, n j i) ≤ Fintype.card (E i))
    (bad : γ → (∀ i, Finset (E i)) → Prop) (ε : γ → ℝ)
    (hbad : ∀ j, MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (n j i))) (bad j) ≤ ε j)
    (hε : (∑ j, ε j) < 1) :
    ∃ T : γ → ∀ i, Finset (E i),
      (∀ j i, (T j i).card = n j i) ∧
      (∀ j l, j ≠ l → ∀ i, Disjoint (T j i) (T l i)) ∧
      ∀ j, ¬ bad j (T j) := by
  classical
  obtain ⟨S, hcard, hdisj⟩ := exists_positions (E := E) n hn
  have hbad' : ∀ j, MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (S j i).card)) (bad j) ≤ ε j := by
    intro j
    simpa only [hcard] using hbad j
  obtain ⟨σ, hgood⟩ := exists_good_images S bad ε hbad' hε
  refine ⟨fun j => sample (S j) σ, ?_, ?_, hgood⟩
  · intro j i
    exact (sample_card (S j) σ i).trans (hcard j i)
  · intro j l hjl
    exact sample_disjoint (S j) (S l) σ (hdisj j l hjl)

end Probability

end Overfull.PartitionPermutation
