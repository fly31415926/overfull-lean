import Overfull.NativeReserve.Residual
import Overfull.ExceptionalPalette.ReserveCopies

/-!
# Selecting and completing all nonprotected boundary colors

An injectively prescribed protected palette has exactly `h-s` remaining
colors. Reindexing by those colors preserves actual matching classes and
separates their copy union from the protected boundaries. Completing only
these classes with copies outside the external set leaves exactly the
original prescribed external copies in the actual residual copy type.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical NativeReserve

variable {h s : ℕ}

/-- Colors outside the actual protected image. -/
def protectedComplement (f : Fin s → Fin h) : Finset (Fin h) := univ \ univ.image f

@[simp] theorem mem_protectedComplement (f : Fin s → Fin h) (j : Fin h) :
    j ∈ protectedComplement f ↔ j ∉ univ.image f := by
  simp [protectedComplement]

/-- An injective protected prescription occupies exactly `s` colors. -/
theorem protected_image_card (f : Fin s → Fin h) (hf : Function.Injective f) :
    (univ.image f).card = s := by
  rw [card_image_of_injective _ hf,card_univ,Fintype.card_fin]

theorem protected_size_le (f : Fin s → Fin h) (hf : Function.Injective f) : s ≤ h := by
  have hc := card_le_univ (univ.image f)
  simpa only [protected_image_card f hf,Fintype.card_fin] using hc

/-- The complement therefore has exactly the intended prefix length. -/
theorem protectedComplement_card (f : Fin s → Fin h) (hf : Function.Injective f) :
    (protectedComplement f).card = h-s := by
  rw [protectedComplement,card_sdiff_of_subset (subset_univ _),
    card_univ,Fintype.card_fin,protected_image_card f hf]

/-- The remaining colors have a canonical finite indexing for this proof. -/
def unprotectedEquiv (f : Fin s → Fin h) (hf : Function.Injective f) :
    Fin (h-s) ≃ protectedComplement f :=
  ((protectedComplement f).equivFinOfCardEq (protectedComplement_card f hf)).symm

/-- The actual original color selected at each prefix index. -/
def unprotectedColor (f : Fin s → Fin h) (hf : Function.Injective f) :
    Fin (h-s) → Fin h := fun j => (unprotectedEquiv f hf j).val

theorem unprotectedColor_injective (f : Fin s → Fin h) (hf : Function.Injective f) :
    Function.Injective (unprotectedColor f hf) :=
  Subtype.val_injective.comp (unprotectedEquiv f hf).injective

/-- Every selected color lies outside every actual protected color. -/
theorem unprotectedColor_not_protected (f : Fin s → Fin h) (hf : Function.Injective f)
    (j : Fin (h-s)) : unprotectedColor f hf j ∉ univ.image f :=
  (mem_protectedComplement f _).mp (unprotectedEquiv f hf j).property

theorem unprotectedColor_ne_protected (f : Fin s → Fin h) (hf : Function.Injective f)
    (j : Fin (h-s)) (i : Fin s) : unprotectedColor f hf j ≠ f i := by
  intro heq
  exact unprotectedColor_not_protected f hf j (heq ▸ mem_image_of_mem f (mem_univ i))

/-- The selector uses every nonprotected original label exactly once. -/
theorem unprotectedColor_image (f : Fin s → Fin h) (hf : Function.Injective f) :
    univ.image (unprotectedColor f hf) = protectedComplement f := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    exact (unprotectedEquiv f hf i).property
  · intro hj
    obtain ⟨i,hi⟩ := (unprotectedEquiv f hf).surjective ⟨j,hj⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

/-- Every original color is selected or protected, including empty palettes. -/
theorem color_selected_or_protected (f : Fin s → Fin h) (hf : Function.Injective f)
    (j : Fin h) :
    (∃ k, unprotectedColor f hf k = j) ∨ ∃ i, f i = j := by
  by_cases hj : j ∈ univ.image f
  · obtain ⟨i,_,hi⟩ := mem_image.mp hj
    exact Or.inr ⟨i,hi⟩
  · have hc : j ∈ univ.image (unprotectedColor f hf) := by
      rw [unprotectedColor_image]
      exact (mem_protectedComplement f j).mpr hj
    obtain ⟨k,_,hk⟩ := mem_image.mp hc
    exact Or.inl ⟨k,hk⟩

variable {V E : Type*}

/-- The complete family of nonprotected original boundary classes. -/
def unprotectedClasses (F : Fin h → Finset E) (f : Fin s → Fin h)
    (hf : Function.Injective f) : Fin (h-s) → Finset E :=
  fun j => F (unprotectedColor f hf j)

theorem unprotectedClasses_matching (G : Multigraph V E)
    (F : Fin h → Finset E) (f : Fin s → Fin h) (hf : Function.Injective f)
    (hF : ∀ j, G.IsMatching (F j)) :
    ∀ j, G.IsMatching (unprotectedClasses F f hf j) :=
  fun j => hF (unprotectedColor f hf j)

theorem unprotectedClasses_disjoint (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j))) :
    Pairwise (fun i j => Disjoint (unprotectedClasses F f hf i)
      (unprotectedClasses F f hf j)) := by
  intro i j hij
  exact hF (fun heq => hij (unprotectedColor_injective f hf heq))

/-- Each selected boundary is disjoint from the full protected-copy union. -/
theorem unprotectedClasses_disjoint_reserve (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i) (j : Fin (h-s)) :
    Disjoint (unprotectedClasses F f hf j) (univ.biUnion R) := by
  apply disjoint_left.mpr
  intro e heB heR
  obtain ⟨i,_,hei⟩ := mem_biUnion.mp heR
  rw [← hprescribed i] at hei
  exact disjoint_left.mp (hF (unprotectedColor_ne_protected f hf j i)) heB hei

/-- The full palette union is partitioned by the selected and prescribed
original classes; no actual copy is identified during reindexing. -/
theorem palette_union_selected_reserve (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hprescribed : ∀ i, F (f i) = R i) :
    univ.biUnion F = univ.biUnion (unprotectedClasses F f hf) ∪ univ.biUnion R := by
  ext e
  constructor
  · intro he
    obtain ⟨j,_,hej⟩ := mem_biUnion.mp he
    rcases color_selected_or_protected f hf j with ⟨k,hk⟩ | ⟨i,hi⟩
    · refine mem_union_left _ (mem_biUnion.mpr ⟨k,mem_univ _,?_⟩)
      change e ∈ F (unprotectedColor f hf k)
      rw [hk]
      exact hej
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,
        hprescribed i ▸ (hi.symm ▸ hej)⟩)
  · intro he
    rcases mem_union.mp he with heB | heR
    · obtain ⟨j,_,hej⟩ := mem_biUnion.mp heB
      exact mem_biUnion.mpr ⟨unprotectedColor f hf j,mem_univ _,hej⟩
    · obtain ⟨i,_,hei⟩ := mem_biUnion.mp heR
      exact mem_biUnion.mpr ⟨f i,mem_univ _,(hprescribed i).symm ▸ hei⟩

theorem selected_union_disjoint_reserve (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i) :
    Disjoint (univ.biUnion (unprotectedClasses F f hf)) (univ.biUnion R) := by
  apply disjoint_left.mpr
  intro e heB heR
  obtain ⟨j,_,hej⟩ := mem_biUnion.mp heB
  exact disjoint_left.mp (unprotectedClasses_disjoint_reserve F f hf R hF hprescribed j)
    hej heR

/-- Removing every nonprotected class leaves exactly the prescribed
protected original copies. -/
theorem palette_remainder_eq_reserve (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i) :
    (univ.biUnion F) \ univ.biUnion (unprotectedClasses F f hf) = univ.biUnion R := by
  rw [palette_union_selected_reserve F f hf R hprescribed]
  have hd := selected_union_disjoint_reserve F f hf R hF hprescribed
  ext e
  constructor
  · intro he
    exact (mem_union.mp (mem_sdiff.mp he).1).resolve_left (mem_sdiff.mp he).2
  · intro he
    exact mem_sdiff.mpr ⟨mem_union_right _ he,fun heB => disjoint_left.mp hd heB he⟩

/-- Completing the selected boundaries with copies outside the external
set deletes exactly their original external copies. -/
theorem completed_prefix_external_trace (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f)
    (X K : Finset E) (hX : X = univ.biUnion F) (hKX : Disjoint K X)
    (N : Fin (h-s) → Finset E)
    (hcontains : ∀ j, unprotectedClasses F f hf j ⊆ N j)
    (hadded : ∀ j, N j ⊆ unprotectedClasses F f hf j ∪ K) :
    removedCopies N univ ∩ X = univ.biUnion (unprotectedClasses F f hf) := by
  ext e
  constructor
  · intro he
    obtain ⟨j,_,hej⟩ := (mem_removedCopies N univ e).mp (mem_inter.mp he).1
    rcases mem_union.mp (hadded j hej) with heB | heK
    · exact mem_biUnion.mpr ⟨j,mem_univ _,heB⟩
    · exact (disjoint_left.mp hKX heK (mem_inter.mp he).2).elim
  · intro he
    obtain ⟨j,_,hej⟩ := mem_biUnion.mp he
    refine mem_inter.mpr ⟨(mem_removedCopies N univ e).mpr
      ⟨j,mem_univ _,hcontains j hej⟩,?_⟩
    rw [hX]
    exact mem_biUnion.mpr ⟨unprotectedColor f hf j,mem_univ _,hej⟩

/-- After actual selected-class completion, the external remainder is
precisely the prescribed reserve, including every parallel copy. -/
theorem completed_prefix_external_remainder (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i)
    (X K : Finset E) (hX : X = univ.biUnion F) (hKX : Disjoint K X)
    (N : Fin (h-s) → Finset E)
    (hcontains : ∀ j, unprotectedClasses F f hf j ⊆ N j)
    (hadded : ∀ j, N j ⊆ unprotectedClasses F f hf j ∪ K) :
    X \ removedCopies N univ = univ.biUnion R := by
  have htrace := completed_prefix_external_trace F f hf X K hX hKX N hcontains hadded
  have hrestrict : X \ removedCopies N univ =
      X \ univ.biUnion (unprotectedClasses F f hf) := by
    rw [← htrace]
    ext e
    simp only [mem_sdiff,mem_inter]
    constructor
    · rintro ⟨heX,heN⟩
      exact ⟨heX,fun he => heN he.1⟩
    · rintro ⟨heX,heN⟩
      exact ⟨heX,fun he => heN ⟨he,heX⟩⟩
  rw [hrestrict,hX]
  exact palette_remainder_eq_reserve F f hf R hF hprescribed

/-- The completed nonprotected prefix avoids the full reserve union. -/
theorem completed_prefix_disjoint_reserve (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i)
    (X K : Finset E) (hX : X = univ.biUnion F) (hKX : Disjoint K X)
    (N : Fin (h-s) → Finset E)
    (hcontains : ∀ j, unprotectedClasses F f hf j ⊆ N j)
    (hadded : ∀ j, N j ⊆ unprotectedClasses F f hf j ∪ K) :
    Disjoint (removedCopies N univ) (univ.biUnion R) := by
  have hrem := completed_prefix_external_remainder F f hf R hF hprescribed
    X K hX hKX N hcontains hadded
  apply disjoint_left.mpr
  intro e heN heR
  rw [← hrem] at heR
  exact (mem_sdiff.mp heR).2 heN

variable [Fintype E]

/-- The exact external remainder is retained in the actual residual edge
subtype, rather than only as an equality of endpoint pairs. -/
theorem completed_prefix_surviving_external (F : Fin h → Finset E)
    (f : Fin s → Fin h) (hf : Function.Injective f) (R : Fin s → Finset E)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hprescribed : ∀ i, F (f i) = R i)
    (X K : Finset E) (hX : X = univ.biUnion F) (hKX : Disjoint K X)
    (N : Fin (h-s) → Finset E)
    (hcontains : ∀ j, unprotectedClasses F f hf j ⊆ N j)
    (hadded : ∀ j, N j ⊆ unprotectedClasses F f hf j ∪ K) :
    survivingCopies (removedCopies N univ) X =
      survivingCopies (removedCopies N univ) (univ.biUnion R) ∧
      (survivingCopies (removedCopies N univ) X).image Subtype.val = univ.biUnion R := by
  have hrem := completed_prefix_external_remainder F f hf R hF hprescribed
    X K hX hKX N hcontains hadded
  have hdisj := completed_prefix_disjoint_reserve F f hf R hF hprescribed
    X K hX hKX N hcontains hadded
  have heq : survivingCopies (removedCopies N univ) X =
      survivingCopies (removedCopies N univ) (univ.biUnion R) := by
    ext e
    rw [mem_survivingCopies,mem_survivingCopies]
    have hm := Finset.ext_iff.mp hrem e.val
    simp only [mem_sdiff] at hm
    constructor
    · intro he
      exact hm.mp ⟨he,e.property⟩
    · intro he
      exact (hm.mpr he).1
  exact ⟨heq,by rw [heq]; exact survivingCopies_image _ _ hdisj.symm⟩

/-- A protected reserve of size at least `γm` supplies the exact room
needed for the nonprotected prefix in the robust core packing theorem. -/
theorem nonprotected_prefix_le_floor (h s m : ℕ) (γ : ℝ) (hsh : s ≤ h)
    (hreserve : γ*m ≤ s) : h-s ≤ ⌊(h : ℝ)-γ*m⌋₊ := by
  apply Nat.le_floor
  rw [Nat.cast_sub hsh]
  linarith

/-- The native linear reserve supplies room for the selected prefix in
either original core. The displayed order bound absorbs the integral
rounding loss in `r/2`. -/
theorem half_reserve_prefix_room (α : ℝ) (n r h m : ℕ)
    (hα : 0 < α) (hr : α*n/30 ≤ r) (hrh : r ≤ h)
    (hm : m ≤ n) (hn : 120/α ≤ n) :
    (α/120)*m ≤ (r/2 : ℕ) ∧
      h-r/2 ≤ ⌊(h : ℝ)-(α/120)*m⌋₊ := by
  have hnα : 120 ≤ α*n := by
    have hh := (div_le_iff₀ hα).mp hn
    nlinarith only [hh]
  have hround : (r : ℝ) ≤ 2*(r/2 : ℕ)+1 := by
    exact_mod_cast (show r ≤ 2*(r/2)+1 by omega)
  have hreserveN : (α/120)*n ≤ (r/2 : ℕ) := by
    nlinarith only [hr,hnα,hround]
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hreserve : (α/120)*m ≤ (r/2 : ℕ) :=
    (mul_le_mul_of_nonneg_left hmR (by positivity)).trans hreserveN
  exact ⟨hreserve,nonprotected_prefix_le_floor h (r/2) m (α/120)
    ((Nat.div_le_self r 2).trans hrh) hreserve⟩

end Overfull.NativeCore
