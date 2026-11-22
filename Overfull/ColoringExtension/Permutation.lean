import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite permutation counts for prescribed labels

Restriction fibers are translates of permutations supported on the complement
of the prescribed source labels. Their sizes, and the resulting bounds for
coordinate-wise forbidden labels, are counted directly as finite sets.
-/

namespace Overfull.ColoringExtension

open Finset Classical
open scoped BigOperators

variable {A I : Type*} [Fintype A] [DecidableEq A]

/-- Permutations with specified values at a family of source labels. -/
noncomputable def restrictionFiber (source target : I → A) : Finset (Equiv.Perm A) :=
  univ.filter (fun σ => ∀ i, σ (source i) = target i)

@[simp] theorem mem_restrictionFiber (source target : I → A) (σ : Equiv.Perm A) :
    σ ∈ restrictionFiber source target ↔ ∀ i, σ (source i) = target i := by
  simp [restrictionFiber]

/-- Support in the complement is exactly pointwise fixation of the source set. -/
theorem mem_perms_compl_iff (S : Finset A) (σ : Equiv.Perm A) :
    σ ∈ permsOfFinset Sᶜ ↔ ∀ x ∈ S, σ x = x := by
  rw [mem_perms_of_finset_iff]
  constructor
  · intro h x hx
    by_contra hne
    exact (Finset.mem_compl.mp (h hne)) hx
  · intro h x hx
    apply Finset.mem_compl.mpr
    intro hxS
    exact hx (h x hxS)

variable [Fintype I]

/-- A nonempty restriction fiber is a translate of permutations fixing all
source labels. This identity preserves the actual permutations. -/
theorem restrictionFiber_eq_image (source : I ↪ A) (target : I → A)
    (σ₀ : Equiv.Perm A) (hσ₀ : ∀ i, σ₀ (source i) = target i) :
    restrictionFiber source target =
      (permsOfFinset (univ.map source)ᶜ).image (fun τ => σ₀ * τ) := by
  ext σ
  simp only [mem_restrictionFiber, Finset.mem_image]
  constructor
  · intro hσ
    refine ⟨σ₀⁻¹ * σ, ?_, by simp⟩
    apply (mem_perms_compl_iff (univ.map source) (σ₀⁻¹ * σ)).mpr
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    change σ₀.symm (σ (source i)) = source i
    rw [hσ i, ← hσ₀ i]
    exact σ₀.symm_apply_apply _
  · rintro ⟨τ, hτ, rfl⟩
    intro i
    have hfix := (mem_perms_compl_iff (univ.map source) τ).mp hτ
      (source i) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    rw [Equiv.Perm.mul_apply, hfix, hσ₀ i]

/-- Every nonempty restriction fiber has the exact factorial size. -/
theorem restrictionFiber_card_of_mem (source : I ↪ A) (target : I → A)
    (σ₀ : Equiv.Perm A) (hσ₀ : ∀ i, σ₀ (source i) = target i) :
    (restrictionFiber source target).card =
      (Fintype.card A - Fintype.card I).factorial := by
  rw [restrictionFiber_eq_image source target σ₀ hσ₀,
    Finset.card_image_of_injective _ (by intro τ ρ h; exact mul_left_cancel h),
    card_perms_of_finset, Finset.card_compl, Finset.card_map, Finset.card_univ]

/-- The fiber bound also covers assignments with repeated target labels. -/
theorem restrictionFiber_card_le (source : I ↪ A) (target : I → A) :
    (restrictionFiber source target).card ≤
      (Fintype.card A - Fintype.card I).factorial := by
  by_cases h : (restrictionFiber source target).Nonempty
  · obtain ⟨σ, hσ⟩ := h
    exact (restrictionFiber_card_of_mem source target σ
      ((mem_restrictionFiber source target σ).mp hσ)).le
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
    exact Nat.zero_le _

/-- Injective prescribed target labels always have an extension, so their
restriction fiber has the exact factorial size. -/
theorem restrictionFiber_card (source target : I ↪ A) :
    (restrictionFiber source target).card =
      (Fintype.card A - Fintype.card I).factorial := by
  let e : Set.range source ≃ Set.range target :=
    source.toEquivRange.symm.trans target.toEquivRange
  let σ₀ : Equiv.Perm A := e.extendSubtype
  apply restrictionFiber_card_of_mem source target σ₀
  intro i
  change e.extendSubtype (source i) = target i
  rw [Equiv.extendSubtype_apply_of_mem e (source i) ⟨i, rfl⟩]
  change (target.toEquivRange (source.toEquivRange.symm ⟨source i, _⟩)).val = target i
  rw [Function.Embedding.toEquivRange_symm_apply_self]
  rfl

/-- Permutations sending every prescribed source label into its specified set. -/
noncomputable def permutationsMem (source : I → A) (B : I → Finset A) :
    Finset (Equiv.Perm A) :=
  univ.filter (fun σ => ∀ i, σ (source i) ∈ B i)

@[simp] theorem mem_permutationsMem (source : I → A) (B : I → Finset A)
    (σ : Equiv.Perm A) :
    σ ∈ permutationsMem source B ↔ ∀ i, σ (source i) ∈ B i := by
  simp [permutationsMem]

/-- Coordinate restrictions are counted by all target tuples, including
noninjective ones; each tuple has at most one factorial-sized fiber. -/
theorem permutations_mem_card_le (source : I ↪ A) (B : I → Finset A) :
    (permutationsMem source B).card ≤
      (Fintype.card A - Fintype.card I).factorial * ∏ i, (B i).card := by
  let f : Equiv.Perm A → I → A := fun σ i => σ (source i)
  have hmap : ∀ σ ∈ permutationsMem source B, f σ ∈ Fintype.piFinset B := by
    intro σ hσ
    exact Fintype.mem_piFinset.mpr ((mem_permutationsMem source B σ).mp hσ)
  have hfiber (target : I → A) (_htarget : target ∈ Fintype.piFinset B) :
      ((permutationsMem source B).filter (fun σ => f σ = target)).card ≤
        (Fintype.card A - Fintype.card I).factorial := by
    apply (Finset.card_le_card ?_).trans (restrictionFiber_card_le source target)
    intro σ hσ
    apply (mem_restrictionFiber source target σ).mpr
    intro i
    exact congrFun (Finset.mem_filter.mp hσ).2 i
  have h := Finset.card_le_mul_card_image_of_maps_to hmap
    (Fintype.card A - Fintype.card I).factorial hfiber
  simpa only [Fintype.card_piFinset] using h

/-- A uniform bound on the allowed target sets gives a power bound. -/
theorem permutations_mem_card_le_pow (source : I ↪ A) (B : I → Finset A)
    (b : ℕ) (hB : ∀ i, (B i).card ≤ b) :
    (permutationsMem source B).card ≤
      (Fintype.card A - Fintype.card I).factorial * b ^ Fintype.card I := by
  apply (permutations_mem_card_le source B).trans
  apply Nat.mul_le_mul_left
  simpa only [Finset.card_univ] using
    Finset.prod_le_pow_card (univ : Finset I) (fun i => (B i).card) b (fun i _ => hB i)

end Overfull.ColoringExtension
