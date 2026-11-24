import Overfull.ExceptionalPalette.PairColoring
import Overfull.WeightedPalette.AsymmetricHall

/-!
# Common bundle colors and the exact remaining star balance

Internal copies between two exceptional vertices must avoid the protected
colors and the joining colors used at either endpoint.  Their multiplicity
is controlled by the combined incidence budget, with no old-core
multiplicity bound on this bundle.  The second part records the exact
copy/color balance after removing distinct protected copies and the colors
already used by the joining and internal parts.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical

variable {E : Type*} {h D : ℕ}

/-- The labels available simultaneously at both exceptional endpoints. -/
def commonBundleColors (Q J₀ J₁ : Finset (Fin h)) : Finset (Fin h) :=
  univ \ (Q ∪ J₀ ∪ J₁)

@[simp] theorem mem_commonBundleColors (Q J₀ J₁ : Finset (Fin h)) (c : Fin h) :
    c ∈ commonBundleColors Q J₀ J₁ ↔ c ∉ Q ∧ c ∉ J₀ ∧ c ∉ J₁ := by
  simp [commonBundleColors, not_or, and_assoc]

/-- The union bound suffices; joining palettes at the endpoints may overlap. -/
theorem commonBundleColors_card_lower (Q J₀ J₁ : Finset (Fin h)) :
    h - Q.card - J₀.card - J₁.card ≤ (commonBundleColors Q J₀ J₁).card := by
  have h₀ := card_union_le Q J₀
  have h₁ := card_union_le (Q ∪ J₀) J₁
  rw [commonBundleColors, card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  omega

/-- Color each actual internal bundle copy distinctly in the common free
palette. No restriction is imposed on the bundle's endpoint multiplicity. -/
theorem exists_common_bundle_coloring (B : Finset E) (Q J₀ J₁ : Finset (Fin h))
    (hbudget : B.card + J₀.card + J₁.card ≤ h - Q.card) :
    ∃ c : B → Fin h, Function.Injective c ∧
      ∀ e, c e ∉ Q ∧ c e ∉ J₀ ∧ c e ∉ J₁ := by
  have hQ : Q.card ≤ h := by simpa only [card_univ, Fintype.card_fin] using card_le_univ Q
  have h₀ := card_union_le Q J₀
  have h₁ := card_union_le (Q ∪ J₀) J₁
  have havail : B.card ≤ (commonBundleColors Q J₀ J₁).card := by
    rw [commonBundleColors, card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card B ≤ Fintype.card (commonBundleColors Q J₀ J₁) by
      simpa only [Fintype.card_coe] using havail)
  refine ⟨fun e => (f e).val, ?_, ?_⟩
  · intro e e' he
    exact f.injective (Subtype.ext he)
  · intro e
    exact (mem_commonBundleColors Q J₀ J₁ (f e).val).mp (f e).property

/-- The two combined endpoint bounds imply enough common colors for the
entire internal exceptional bundle when at most half the palette is protected. -/
theorem exists_common_bundle_coloring_of_combined_bounds
    (B : Finset E) (Q J₀ J₁ : Finset (Fin h))
    (hx : J₀.card + B.card ≤ D) (hy : J₁.card + B.card ≤ D)
    (hD : 4 * D ≤ h) (hQ : 2 * Q.card ≤ h) :
    ∃ c : B → Fin h, Function.Injective c ∧
      ∀ e, c e ∉ Q ∧ c e ∉ J₀ ∧ c e ∉ J₁ := by
  apply exists_common_bundle_coloring B Q J₀ J₁
  omega

/-- The exact set of colors left for an exceptional-to-core star. -/
def remainingStarColors (Q J B : Finset (Fin h)) : Finset (Fin h) :=
  univ \ (Q ∪ J ∪ B)

@[simp] theorem mem_remainingStarColors (Q J B : Finset (Fin h)) (c : Fin h) :
    c ∈ remainingStarColors Q J B ↔ c ∉ Q ∧ c ∉ J ∧ c ∉ B := by
  simp [remainingStarColors, not_or, and_assoc]

/-- Distinct protected, joining-used, and bundle-used colors give an exact
partition of the original palette. -/
theorem remainingStarColors_card_add (Q J B : Finset (Fin h))
    (hQJ : Disjoint Q J) (hQB : Disjoint Q B) (hJB : Disjoint J B) :
    (remainingStarColors Q J B).card + Q.card + J.card + B.card = h := by
  have hs := card_sdiff_add_card_eq_card (subset_univ (Q ∪ J ∪ B))
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hQB, hJB⟩),
    card_union_of_disjoint hQJ, card_univ, Fintype.card_fin] at hs
  change (remainingStarColors Q J B).card + (Q.card + J.card + B.card) = h at hs
  omega

/-- Remove exactly one distinct star copy for each protected color. The
degree partition then proves the exact remaining-copy/free-color balance. -/
theorem remaining_star_card_eq_colors [DecidableEq E]
    (A R : Finset E) (Q J B : Finset (Fin h))
    (hR : R ⊆ A) (hRQ : R.card = Q.card)
    (hbalance : J.card + A.card + B.card = h)
    (hQJ : Disjoint Q J) (hQB : Disjoint Q B) (hJB : Disjoint J B) :
    (A \ R).card = (remainingStarColors Q J B).card := by
  have hcolors := remainingStarColors_card_add Q J B hQJ hQB hJB
  have hcopies := card_sdiff_add_card_eq_card hR
  omega

/-- Both sides of the exact star balance retain the native Hall margin. -/
theorem remaining_star_card_eq_colors_and_lower [DecidableEq E]
    (A R : Finset E) (Q J B : Finset (Fin h))
    (hR : R ⊆ A) (hRQ : R.card = Q.card)
    (hbalance : J.card + A.card + B.card = h)
    (hcombined : J.card + B.card ≤ D)
    (hQJ : Disjoint Q J) (hQB : Disjoint Q B) (hJB : Disjoint J B) :
    (A \ R).card = (remainingStarColors Q J B).card ∧
      h - Q.card - D ≤ (A \ R).card := by
  refine ⟨remaining_star_card_eq_colors A R Q J B hR hRQ hbalance hQJ hQB hJB, ?_⟩
  have hcopies := card_sdiff_add_card_eq_card hR
  omega

/-- The actual balanced residual sets are now admissible inputs to the
asymmetric Hall theorem, once their two conflict counts are established. -/
theorem exists_remaining_star_equiv [DecidableEq E]
    (A R : Finset E) (Q J B : Finset (Fin h)) (b : ℕ)
    (hR : R ⊆ A) (hRQ : R.card = Q.card)
    (hbalance : J.card + A.card + B.card = h)
    (hcombined : J.card + B.card ≤ D)
    (hQJ : Disjoint Q J) (hQB : Disjoint Q B) (hJB : Disjoint J B)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hQ : 2 * Q.card ≤ h)
    (Allowed : (A \ R) → remainingStarColors Q J B → Prop)
    (hleft : ∀ e, (univ.filter (fun c => ¬ Allowed e c)).card ≤ D + b)
    (hright : ∀ c, (univ.filter (fun e => ¬ Allowed e c)).card ≤ h / 8 + b) :
    ∃ f : (A \ R) ≃ remainingStarColors Q J B, ∀ e, Allowed e (f e) := by
  obtain ⟨hcard, hlower⟩ := remaining_star_card_eq_colors_and_lower
    A R Q J B hR hRQ hbalance hcombined hQJ hQB hJB
  exact CircuitPatterns.exists_star_equiv_of_conflict_bounds Allowed h D b Q.card
    hb hD hQ (by simpa only [Fintype.card_coe] using hcard)
    (by simpa only [Fintype.card_coe] using hlower) hleft hright

end Overfull.NativeStar
