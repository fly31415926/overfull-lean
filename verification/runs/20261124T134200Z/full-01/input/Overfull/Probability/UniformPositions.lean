import Overfull.Probability.PartitionPermutation

/-!
# Actual equal fine positions and their coarse unions

Divisibility of each population, rather than an assumed family of subsets,
produces a partition into equally sized fine position sets. Grouping the
fine labels constructs the coarse positions. Both levels use exactly the
fractions and the two-selected-vertices condition required for the common
permutation experiment.
-/

noncomputable section

namespace Overfull.PartitionPermutation

open Finset Classical

variable {ι γ : Type*} {E : ι → Type*}

/-- Equal positions exhaust every population when its cardinality is divisible
by the number of labels. No ordering of any population is prescribed. -/
theorem exists_equal_positions [Fintype γ] [∀ i, Fintype (E i)]
    (hdiv : ∀ i, Fintype.card γ ∣ Fintype.card (E i)) :
    ∃ S : γ → ∀ i, Finset (E i),
      (∀ j i, (S j i).card = Fintype.card (E i) / Fintype.card γ) ∧
      (∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i)) ∧
      ∀ i, univ.biUnion (fun j => S j i) = univ := by
  have hsum (i : ι) :
      (∑ _j : γ, Fintype.card (E i) / Fintype.card γ) = Fintype.card (E i) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact Nat.mul_div_cancel' (hdiv i)
  obtain ⟨S, hcard, hdisj⟩ := exists_positions (E := E)
    (fun (_ : γ) i => Fintype.card (E i) / Fintype.card γ)
    (fun i => (hsum i).le)
  refine ⟨S, hcard, hdisj, ?_⟩
  intro i
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion]
  · simpa only [hcard] using hsum i
  · intro j _ l _ hjl
    exact hdisj j l hjl i

variable {c t : ℕ}

/-- One coarse position set is the union of all fine sets with its first label. -/
def coarsePositions (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (j : Fin c) (i : ι) : Finset (E i) :=
  univ.biUnion (fun l : Fin t => S (j, l) i)

/-- Fine and coarse labels share one family, as required by simultaneous sampling. -/
def combinedPositions (S : (Fin c × Fin t) → ∀ i, Finset (E i)) :
    ((Fin c × Fin t) ⊕ Fin c) → ∀ i, Finset (E i) :=
  Sum.elim S (coarsePositions S)

/-- The exact sampling fraction for either level of the labelled partition. -/
def positionFraction (c t : ℕ) : ((Fin c × Fin t) ⊕ Fin c) → ℝ :=
  Sum.elim (fun _ => 1 / ((c : ℝ) * t)) (fun _ => 1 / (c : ℝ))

/-- The fine fraction is a positive common lower bound for both levels. -/
theorem positionFraction_lower (hc : 0 < c) (ht : 0 < t)
    (j : (Fin c × Fin t) ⊕ Fin c) :
    1 / ((c : ℝ) * t) ≤ positionFraction c t j := by
  cases j with
  | inl _ => rfl
  | inr _ =>
      change 1 / ((c : ℝ) * t) ≤ 1 / (c : ℝ)
      have hcR : (0 : ℝ) < c := by exact_mod_cast hc
      have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
      exact one_div_le_one_div_of_le hcR (by nlinarith)

/-- The fine labels viewed inside the joint fine/coarse label type. -/
def fineLabels (c t : ℕ) : Finset ((Fin c × Fin t) ⊕ Fin c) :=
  univ.image Sum.inl

/-- The coarse labels viewed inside the joint fine/coarse label type. -/
def coarseLabels (c t : ℕ) : Finset ((Fin c × Fin t) ⊕ Fin c) :=
  univ.image Sum.inr

/-- The fine labels belonging to one prescribed coarse label. -/
def coarseFineLabels (t : ℕ) (j : Fin c) : Finset ((Fin c × Fin t) ⊕ Fin c) :=
  univ.image (fun l : Fin t => Sum.inl (j, l))

/-- The exact coarse-union relation in the combined-label notation. -/
theorem combined_coarse_union (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (j : Fin c) (i : ι) :
    combinedPositions S (Sum.inr j) i =
      (coarseFineLabels t j).biUnion (fun l => combinedPositions S l i) := by
  ext x
  simp [combinedPositions, coarsePositions, coarseFineLabels]

/-- Every fine set lies in the corresponding coarse position. -/
theorem fine_subset_coarse (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (j : Fin c) (l : Fin t) (i : ι) :
    S (j, l) i ⊆ coarsePositions S j i := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hx⟩

/-- Disjoint fine positions give disjoint coarse positions. -/
theorem coarsePositions_disjoint (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (hdisj : ∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i))
    (j l : Fin c) (hjl : j ≠ l) (i : ι) :
    Disjoint (coarsePositions S j i) (coarsePositions S l i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hy
  exact Finset.disjoint_left.mp
    (hdisj (j, a) (l, b) (fun h => hjl (congrArg Prod.fst h)) i) hxa hxb

/-- Taking all coarse unions preserves the exact population coverage. -/
theorem coarsePositions_cover [∀ i, Fintype (E i)]
    (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (hcover : ∀ i, univ.biUnion (fun j => S j i) = univ) (i : ι) :
    univ.biUnion (fun j => coarsePositions S j i) = univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    have hx : x ∈ univ.biUnion (fun j => S j i) := by rw [hcover]; simp
    obtain ⟨⟨j, l⟩, _, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hx⟩⟩

/-- Exact coverage by fine labels in the combined family. -/
theorem combined_fine_cover [∀ i, Fintype (E i)]
    (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (hcover : ∀ i, univ.biUnion (fun j => S j i) = univ) (i : ι) :
    (fineLabels c t).biUnion (fun j => combinedPositions S j i) = univ := by
  simpa [fineLabels, Finset.image_biUnion, combinedPositions] using hcover i

/-- Exact coverage by coarse labels in the combined family. -/
theorem combined_coarse_cover [∀ i, Fintype (E i)]
    (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (hcover : ∀ i, univ.biUnion (fun j => S j i) = univ) (i : ι) :
    (coarseLabels c t).biUnion (fun j => combinedPositions S j i) = univ := by
  simpa [coarseLabels, Finset.image_biUnion, combinedPositions] using coarsePositions_cover S hcover i

/-- The size of an actual coarse position is the number of fine labels in it
multiplied by their common cardinality. -/
theorem coarsePositions_card (S : (Fin c × Fin t) → ∀ i, Finset (E i))
    (n : ι → ℕ) (hcard : ∀ j i, (S j i).card = n i)
    (hdisj : ∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i))
    (j : Fin c) (i : ι) : (coarsePositions S j i).card = t * n i := by
  unfold coarsePositions
  rw [Finset.card_biUnion]
  · simp [hcard]
  · intro a _ b _ hab
    exact hdisj (j, a) (j, b) (fun h => hab (congrArg Prod.snd h)) i

/-- Actual fine positions, with coarse unions, derived from divisible integer
population sizes. The joint family has exact common fractions in every part,
and every label selects at least two vertices in every nonempty part. -/
theorem exists_uniform_fine_coarse_positions [∀ i, Fintype (E i)]
    (hc : 0 < c) (ht : 0 < t)
    (hdiv : ∀ i, c * t ∣ Fintype.card (E i))
    (hsize : ∀ i, Nonempty (E i) → 2 * (c * t) ≤ Fintype.card (E i)) :
    ∃ S : (Fin c × Fin t) → ∀ i, Finset (E i),
      (∀ j i, (S j i).card = Fintype.card (E i) / (c * t)) ∧
      (∀ j l, j ≠ l → ∀ i, Disjoint (S j i) (S l i)) ∧
      (∀ i, univ.biUnion (fun j => S j i) = univ) ∧
      (∀ j i, (coarsePositions S j i).card = Fintype.card (E i) / c) ∧
      (∀ j l, j ≠ l → ∀ i, Disjoint (coarsePositions S j i) (coarsePositions S l i)) ∧
      (∀ i, univ.biUnion (fun j => coarsePositions S j i) = univ) ∧
      (∀ j, 0 < positionFraction c t j ∧ positionFraction c t j ≤ 1) ∧
      (∀ j i, ((combinedPositions S j i).card : ℝ) =
        positionFraction c t j * Fintype.card (E i)) ∧
      ∀ j i, Nonempty (E i) → 2 ≤ (combinedPositions S j i).card := by
  have hct : 0 < c * t := Nat.mul_pos hc ht
  obtain ⟨S, hcard, hdisj, hcover⟩ := exists_equal_positions
    (E := E) (γ := Fin c × Fin t) (by simpa using hdiv)
  have hcard' : ∀ j i, (S j i).card = Fintype.card (E i) / (c * t) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hcard
  have hmul (i : ι) : c * t * (Fintype.card (E i) / (c * t)) = Fintype.card (E i) :=
    Nat.mul_div_cancel' (hdiv i)
  have hcoarse (j : Fin c) (i : ι) :
      (coarsePositions S j i).card = Fintype.card (E i) / c := by
    rw [coarsePositions_card S _ hcard' hdisj j i]
    have h := congrArg (fun n : ℕ => n / c) (hmul i)
    simpa only [Nat.mul_assoc, Nat.mul_div_right _ hc] using h
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  refine ⟨S, hcard', hdisj, hcover, hcoarse,
    coarsePositions_disjoint S hdisj, coarsePositions_cover S hcover, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl j =>
        change 0 < 1 / ((c : ℝ) * t) ∧ 1 / ((c : ℝ) * t) ≤ 1
        constructor
        · positivity
        · exact (div_le_one (mul_pos hcR htR)).mpr (by nlinarith)
    | inr j =>
        change 0 < 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ 1
        exact ⟨by positivity, (div_le_one hcR).mpr hc1⟩
  · intro j i
    have hm : (c : ℝ) * t * (Fintype.card (E i) / (c * t) : ℕ) =
        Fintype.card (E i) := by exact_mod_cast hmul i
    cases j with
    | inl j =>
        change ((S j i).card : ℝ) = 1 / ((c : ℝ) * t) * Fintype.card (E i)
        rw [hcard', ← hm]
        field_simp
    | inr j =>
        change ((coarsePositions S j i).card : ℝ) = 1 / (c : ℝ) * Fintype.card (E i)
        rw [coarsePositions_card S _ hcard' hdisj j i, Nat.cast_mul, ← hm]
        field_simp
  · intro j i hne
    have htwo : 2 ≤ Fintype.card (E i) / (c * t) :=
      (Nat.le_div_iff_mul_le hct).mpr (hsize i hne)
    cases j with
    | inl j => simpa only [combinedPositions, Sum.elim_inl, hcard'] using htwo
    | inr j =>
        change 2 ≤ (coarsePositions S j i).card
        rw [coarsePositions_card S _ hcard' hdisj j i]
        nlinarith

end Overfull.PartitionPermutation
