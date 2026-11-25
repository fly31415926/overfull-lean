import Overfull.NativeAssembly.TwoPairs
import Overfull.NativeAssembly.OtherCases

/-!
# Two pair completions together with whole reserved star boundaries

The pair seed construction permits additional nonjoining copies in a reserved
boundary.  Combining the resulting pair classes with the actual reserve
extension retains that whole boundary, including its separately assigned star
copy.  Away from the pairs, every class has exactly the reserve extension's
footprint.  No bound on the total exceptional set is assumed.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E I K : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L d : ℕ} {p : K → ℕ}
    {C : JoiningPalette G label h D L p} {U₀ U₁ : Finset V}
    {R : I → Finset E} {f : I → Fin h}

/-- Copies internal to one actual assigned fiber are not joining copies. -/
theorem internalOn_fiber_disjoint_joining (k : K) (U : Finset V)
    (hfiber : labelShore label {k} = U) :
    Disjoint (G.internalOn univ U) (joiningCopies G label) := by
  apply internalCopies_disjoint_joining
  intro e he
  have hx := (mem_filter.mp he).2.1
  have hy := (mem_filter.mp he).2.2
  rw [← hfiber] at hx hy
  simp only [mem_labelShore, mem_singleton] at hx hy
  exact hx.trans hy.symm

/-- Construct both pair seed colorings even when the actual reserved
boundaries contain additional nonjoining copies.  Only the pair projection
is asserted equal to the pair-completed protected class. -/
theorem exists_reserved_two_pair_completion_with_extra
    (C : JoiningPalette G label h D L p) (k₀ k₁ : K) (hk : k₀ ≠ k₁)
    (U₀ U₁ : Finset V) (hcard₀ : U₀.card = 2) (hcard₁ : U₁.card = 2)
    (hfiber₀ : labelShore label {k₀} = U₀)
    (hfiber₁ : labelShore label {k₁} = U₁)
    (hp₀ : p k₀ = 0) (hp₁ : p k₁ = 0)
    (hregular₀ : ∀ v ∈ U₀, G.degree v = h)
    (hregular₁ : ∀ v ∈ U₁, G.degree v = h)
    (R : I → Finset E) (hR : ∀ i, G.IsMatching (R i))
    (f : I → Fin h) (hf : Function.Injective f)
    (g₀ : I → G.internalOn univ U₀) (g₁ : I → G.internalOn univ U₁)
    (hg₀ : Function.Injective g₀) (hg₁ : Function.Injective g₁)
    (hmem₀ : ∀ i, (g₀ i).val ∈ R i) (hmem₁ : ∀ i, (g₁ i).val ∈ R i)
    (htrace : ∀ i, R i ∩ joiningCopies G label = C.classes (f i)) :
    ∃ B : TwoPairFiberCompletion C U₀ U₁,
      (∀ i, B.first.color (g₀ i) = f i) ∧
      (∀ i, B.second.color (g₁ i) = f i) ∧
      (∀ i, B.classes (f i) = C.classes (f i) ∪ {(g₀ i).val, (g₁ i).val}) ∧
      ∀ i, B.classes (f i) ⊆ R i := by
  let R' : I → Finset E := fun i => C.classes (f i) ∪ {(g₀ i).val, (g₁ i).val}
  have hsub (i : I) : R' i ⊆ R i := by
    intro e he
    rcases mem_union.mp he with he | he
    · rw [← htrace i] at he
      exact (mem_inter.mp he).1
    · rcases mem_insert.mp he with rfl | he
      · exact hmem₀ i
      · exact (mem_singleton.mp he).symm ▸ hmem₁ i
  have hmatch (i : I) : G.IsMatching (R' i) := by
    intro e he a ha v hev hav
    exact hR i e (hsub i he) a (hsub i ha) v hev hav
  have htrace' (i : I) : R' i ∩ joiningCopies G label = C.classes (f i) := by
    apply subset_antisymm
    · intro e he
      exact htrace i ▸ mem_inter.mpr ⟨hsub i (mem_inter.mp he).1, (mem_inter.mp he).2⟩
    · intro e he
      exact mem_inter.mpr ⟨mem_union_left _ he, C.classes_subset_joining _ he⟩
  have hcont (i : I) : R' i ⊆ joiningCopies G label ∪
      exceptionalCopies G univ (U₀ ∪ U₁) := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (C.classes_subset_joining _ he)
    · apply mem_union_right
      rcases mem_insert.mp he with rfl | he
      · exact (mem_exceptionalCopies G univ _ _).mpr
          ⟨mem_univ _, Or.inl (mem_union_left _ (mem_filter.mp (g₀ i).property).2.1)⟩
      · rw [mem_singleton] at he
        subst e
        exact (mem_exceptionalCopies G univ _ _).mpr
          ⟨mem_univ _, Or.inl (mem_union_right _ (mem_filter.mp (g₁ i).property).2.1)⟩
  obtain ⟨B, hB₀, hB₁, hB⟩ := exists_reserved_two_pair_completion C k₀ k₁ hk
    U₀ U₁ hcard₀ hcard₁ hfiber₀ hfiber₁ hp₀ hp₁ hregular₀ hregular₁
    R' hmatch f hf g₀ g₁ hg₀ hg₁
    (fun i => mem_union_right _ (mem_insert_self _ _))
    (fun i => mem_union_right _ (mem_insert_of_mem (mem_singleton_self _)))
    hcont htrace'
  exact ⟨B, hB₀, hB₁, hB, fun i => (hB i) ▸ hsub i⟩

/-- Add the two completed pair pools to the whole actual reserve extension. -/
def pairReserveClasses (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (j : Fin h) : Finset E :=
  P.classes j ∪ B.classes j

theorem pairReserveClasses_prescribed (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i) (i : I) :
    pairReserveClasses P B (f i) = R i := by
  rw [pairReserveClasses, P.prescribed, union_eq_left.mpr (hprotected i)]

theorem pairReserveClasses_other (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (j : Fin h)
    (hj : j ∉ univ.image f) : pairReserveClasses P B j = B.classes j := by
  rw [pairReserveClasses, reserveExtension_eq_of_not_protected P j hj,
    union_eq_right.mpr (B.contains_joining j)]

theorem pairReserveClasses_matching (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i) (j : Fin h) :
    G.IsMatching (pairReserveClasses P B j) := by
  by_cases hj : j ∈ univ.image f
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    rw [pairReserveClasses_prescribed P B hprotected, ← P.prescribed]
    exact P.matching _
  · rw [pairReserveClasses_other P B j hj]
    exact B.matching j

/-- Every pair-pool copy already present in a reserve class has its same
color in the pair completion.  Saturation and matching uniqueness enforce
this, even for a reserved boundary containing an extra star copy. -/
theorem pairReserve_pair_copy_mem (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i)
    (j : Fin h) (e : E) (he : e ∈ P.classes j)
    (hpair : e ∈ G.internalOn univ U₀ ∪ G.internalOn univ U₁) :
    e ∈ B.classes j := by
  by_cases hj : j ∈ univ.image f
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    have hv : G.firstEnd e ∈ U₀ ∪ U₁ := by
      rcases mem_union.mp hpair with he | he
      · exact mem_union_left _ (mem_filter.mp he).2.1
      · exact mem_union_right _ (mem_filter.mp he).2.1
    obtain ⟨a, ha, hva⟩ := (G.mem_edgeSupport _ _).mp (B.covers (f i) hv)
    have haP : a ∈ P.classes (f i) := by
      rw [P.prescribed]
      exact hprotected i ha
    have hae : a = e := P.matching (f i) a haP e he (G.firstEnd e) hva
      ((G.incident_iff e _).mpr (Or.inl rfl))
    exact hae ▸ ha
  · rw [reserveExtension_eq_of_not_protected P j hj] at he
    exact B.contains_joining j he

theorem pairReserveClasses_disjoint (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i) :
    Pairwise (fun j k => Disjoint (pairReserveClasses P B j) (pairReserveClasses P B k)) := by
  have hcross (j k : Fin h) (hjk : j ≠ k) (e : E)
      (he : e ∈ B.classes j) (hk : e ∈ P.classes k) : False := by
    have hall : e ∈ joiningCopies G label ∪ G.internalOn univ U₀ ∪ G.internalOn univ U₁ := by
      rw [← B.cover]
      exact mem_biUnion.mpr ⟨j, mem_univ _, he⟩
    rcases mem_union.mp hall with hall | hi₁
    · rcases mem_union.mp hall with hjoin | hi₀
      · have hc : e ∈ C.classes k := P.joining k ▸ mem_inter.mpr ⟨hk, hjoin⟩
        exact disjoint_left.mp (B.disjoint hjk) he (B.contains_joining k hc)
      · exact disjoint_left.mp (B.disjoint hjk) he
          (pairReserve_pair_copy_mem P B hprotected k e hk (mem_union_left _ hi₀))
    · exact disjoint_left.mp (B.disjoint hjk) he
        (pairReserve_pair_copy_mem P B hprotected k e hk (mem_union_right _ hi₁))
  intro j k hjk
  apply disjoint_left.mpr
  intro e he hk
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hk with hk | hk
  · exact disjoint_left.mp (P.disjoint hjk) he hk
  · exact hcross k j (Ne.symm hjk) e hk he
  · exact hcross j k hjk e he hk
  · exact disjoint_left.mp (B.disjoint hjk) he hk

theorem pairReserveClasses_cover (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) :
    univ.biUnion (pairReserveClasses P B) =
      joiningCopies G label ∪ G.internalOn univ U₀ ∪ G.internalOn univ U₁ ∪ univ.biUnion R := by
  have heq : univ.biUnion (pairReserveClasses P B) = univ.biUnion P.classes ∪ univ.biUnion B.classes := by
    ext e
    simp only [pairReserveClasses, mem_biUnion, mem_univ, true_and, mem_union]
    aesop
  rw [heq, P.cover, B.cover]
  ext e
  simp only [mem_union]
  tauto

theorem pairReserveClasses_covers (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (j : Fin h) :
    U₀ ∪ U₁ ⊆ G.edgeSupport (pairReserveClasses P B j) := by
  intro v hv
  obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp (B.covers j hv)
  exact (G.mem_edgeSupport _ v).mpr ⟨e, mem_union_right _ he, hve⟩

theorem pairReserveClasses_cut_eq (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (j : Fin h) (k : K) :
    G.cutOn (pairReserveClasses P B j) (labelShore label {k}) =
      G.cutOn (C.classes j) (labelShore label {k}) := by
  change (P.classes j ∪ B.classes j).filter _ = _
  rw [filter_union]
  change G.cutOn (P.classes j) _ ∪ G.cutOn (B.classes j) _ = _
  rw [P.cut_eq j {k}, B.cut_eq j k, union_self]

theorem pairReserveClasses_card_le (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i) (j : Fin h) :
    (pairReserveClasses P B j).card ≤ max (3*L+2) d := by
  by_cases hj : j ∈ univ.image f
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    rw [pairReserveClasses_prescribed P B hprotected, ← P.prescribed]
    exact (P.card_le _).trans (Nat.max_le_max (by omega) le_rfl)
  · rw [pairReserveClasses_other P B j hj]
    exact (B.card_le j).trans (le_max_left _ _)

theorem pairReserveClasses_support_card_le (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i) (j : Fin h) :
    (G.edgeSupport (pairReserveClasses P B j)).card ≤ 2*max (3*L+2) d :=
  (G.edgeSupport_card_le _).trans (Nat.mul_le_mul_left 2 (pairReserveClasses_card_le P B hprotected j))

/-- Pair insertion does not alter any footprint outside the two pair fibers. -/
theorem pairReserveClasses_support_outside_iff (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (j : Fin h) (v : V)
    (hv : v ∉ U₀ ∪ U₁) :
    v ∈ G.edgeSupport (pairReserveClasses P B j) ↔ v ∈ G.edgeSupport (P.classes j) := by
  constructor
  · intro hm
    obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
    rcases mem_union.mp he with he | he
    · exact (G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩
    · have hc := (B.support_outside_iff j v hv).mp ((G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩)
      obtain ⟨a, ha, hva⟩ := (G.mem_edgeSupport _ v).mp hc
      exact (G.mem_edgeSupport _ v).mpr ⟨a, P.contains_original j ha, hva⟩
  · intro hm
    obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
    exact (G.mem_edgeSupport _ v).mpr ⟨e, mem_union_left _ he, hve⟩

end Overfull.NativeAssembly
