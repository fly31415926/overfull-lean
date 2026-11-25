import Overfull.ExceptionalPalette.PairAssigned

/-!
# Simultaneous completion of two assigned exceptional pairs

Both pair completions use the same original joining palette. Their inserted
copies have disjoint vertex supports, so they may share protected colors.
The union preserves every original fiber cut and every prescribed copy,
while adding at most two copies to each joining class.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd AssignedParts

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
variable {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}
variable {C : JoiningPalette G label h D L p} {U U₀ U₁ : Finset V}

/-- A pair completion adds only internal copies, retaining the original
color of every joining copy. -/
theorem PairFiberCompletion.classes_subset_base_internal
    (B : PairFiberCompletion C U) (j : Fin h) :
    B.classes j ⊆ C.classes j ∪ G.internalOn univ U := by
  intro e he
  have hall : e ∈ joiningCopies G label ∪ G.internalOn univ U := by
    rw [← B.cover]
    exact mem_biUnion.mpr ⟨j, mem_univ _, he⟩
  rcases mem_union.mp hall with hj | hi
  · rw [← C.cover] at hj
    obtain ⟨k, _, hk⟩ := mem_biUnion.mp hj
    by_cases hkj : k = j
    · exact mem_union_left _ (hkj ▸ hk)
    · exact (disjoint_left.mp (B.disjoint hkj)
        (B.contains_joining k hk) he).elim
  · exact mem_union_right _ hi

/-- Exact separation into the unchanged joining class and its inserted
internal copies. -/
theorem PairFiberCompletion.class_eq_base_union_internal
    (B : PairFiberCompletion C U) (j : Fin h) :
    B.classes j = C.classes j ∪ G.internalOn (B.classes j) U := by
  apply subset_antisymm
  · intro e he
    rcases mem_union.mp (B.classes_subset_base_internal j he) with hc | hi
    · exact mem_union_left _ hc
    · exact mem_union_right _ (mem_filter.mpr ⟨he, (mem_filter.mp hi).2⟩)
  · intro e he
    rcases mem_union.mp he with hc | hi
    · exact B.contains_joining j hc
    · exact (mem_filter.mp hi).1

/-- Outside the completed pair, each color has exactly its old footprint. -/
theorem PairFiberCompletion.support_outside_iff
    (B : PairFiberCompletion C U) (j : Fin h) (v : V) (hv : v ∉ U) :
    v ∈ G.edgeSupport (B.classes j) ↔ v ∈ G.edgeSupport (C.classes j) := by
  constructor
  · intro hm
    obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
    rcases mem_union.mp (B.classes_subset_base_internal j he) with hc | hi
    · exact (G.mem_edgeSupport _ v).mpr ⟨e, hc, hve⟩
    · exact (hv (G.edgeSupport_internalOn_subset univ U
        ((G.mem_edgeSupport _ v).mpr ⟨e, hi, hve⟩))).elim
  · intro hm
    obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
    exact (G.mem_edgeSupport _ v).mpr ⟨e, B.contains_joining j he, hve⟩

/-- Two completions on disjoint pairs can share colors without creating
an incidence conflict. -/
theorem PairFiberCompletion.union_isMatching
    (B₀ : PairFiberCompletion C U₀) (B₁ : PairFiberCompletion C U₁)
    (h01 : Disjoint U₀ U₁) (j : Fin h) :
    G.IsMatching (B₀.classes j ∪ B₁.classes j) := by
  have hcross (e : E) (he : e ∈ B₀.classes j)
      (f : E) (hf : f ∈ B₁.classes j) (v : V)
      (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : e = f := by
    rcases mem_union.mp (B₀.classes_subset_base_internal j he) with hc | hi
    · exact B₁.matching j e (B₁.contains_joining j hc) f hf v hev hfv
    · rcases mem_union.mp (B₁.classes_subset_base_internal j hf) with hc | hk
      · exact B₀.matching j e he f (B₀.contains_joining j hc) v hev hfv
      · have hv0 := G.edgeSupport_internalOn_subset univ U₀
          ((G.mem_edgeSupport _ v).mpr ⟨e, hi, hev⟩)
        have hv1 := G.edgeSupport_internalOn_subset univ U₁
          ((G.mem_edgeSupport _ v).mpr ⟨f, hk, hfv⟩)
        exact (disjoint_left.mp h01 hv0 hv1).elim
  intro e he f hf v hev hfv
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact B₀.matching j e he f hf v hev hfv
  · exact hcross e he f hf v hev hfv
  · exact (hcross f hf e he v hfv hev).symm
  · exact B₁.matching j e he f hf v hev hfv

/-- Combining two disjoint pair completions never repeats an actual copy
in distinct colors. -/
theorem PairFiberCompletion.union_disjoint
    (B₀ : PairFiberCompletion C U₀) (B₁ : PairFiberCompletion C U₁)
    (h01 : Disjoint U₀ U₁) :
    Pairwise (fun j k => Disjoint
      (B₀.classes j ∪ B₁.classes j) (B₀.classes k ∪ B₁.classes k)) := by
  have hcross (j k : Fin h) (hjk : j ≠ k) (e : E)
      (he : e ∈ B₀.classes j) (hf : e ∈ B₁.classes k) : False := by
    rcases mem_union.mp (B₀.classes_subset_base_internal j he) with hc | hi
    · exact disjoint_left.mp (B₁.disjoint hjk) (B₁.contains_joining j hc) hf
    · rcases mem_union.mp (B₁.classes_subset_base_internal k hf) with hc | hk
      · exact disjoint_left.mp (B₀.disjoint hjk) he (B₀.contains_joining k hc)
      · exact disjoint_left.mp h01 (mem_filter.mp hi).2.1 (mem_filter.mp hk).2.1
  intro j k hjk
  apply disjoint_left.mpr
  intro e he hf
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact disjoint_left.mp (B₀.disjoint hjk) he hf
  · exact hcross j k hjk e he hf
  · exact hcross k j (Ne.symm hjk) e hf he
  · exact disjoint_left.mp (B₁.disjoint hjk) he hf

/-- The second pair adds at most one further copy to the first completed
class; the common joining class is counted only once. -/
theorem PairFiberCompletion.union_card_le
    (B₀ : PairFiberCompletion C U₀) (B₁ : PairFiberCompletion C U₁)
    (hU₁ : U₁.card ≤ 2) (j : Fin h) :
    (B₀.classes j ∪ B₁.classes j).card ≤ 3*L+2 := by
  have heq : B₀.classes j ∪ B₁.classes j =
      B₀.classes j ∪ G.internalOn (B₁.classes j) U₁ := by
    rw [B₁.class_eq_base_union_internal j, ← union_assoc,
      union_eq_left.mpr (B₀.contains_joining j)]
  rw [heq]
  have hi := internalOn_card_le_one G (B₁.matching j) U₁ hU₁
  have hu := card_union_le (B₀.classes j) (G.internalOn (B₁.classes j) U₁)
  have hb := B₀.card_le j
  omega

/-- Complete two disjoint exceptional pairs against one fixed joining
palette, retaining both independent copy colorings. -/
structure TwoPairFiberCompletion (C : JoiningPalette G label h D L p)
    (U₀ U₁ : Finset V) where
  first : PairFiberCompletion C U₀
  second : PairFiberCompletion C U₁
  classes : Fin h → Finset E
  classes_eq : ∀ j, classes j = first.classes j ∪ second.classes j
  contains_joining : ∀ j, C.classes j ⊆ classes j
  matching : ∀ j, G.IsMatching (classes j)
  disjoint : Pairwise (fun j k => Disjoint (classes j) (classes k))
  cover : univ.biUnion classes =
    joiningCopies G label ∪ G.internalOn univ U₀ ∪ G.internalOn univ U₁
  covers : ∀ j, U₀ ∪ U₁ ⊆ G.edgeSupport (classes j)
  cut_eq : ∀ j k, G.cutOn (classes j) (labelShore label {k}) =
    G.cutOn (C.classes j) (labelShore label {k})
  card_le : ∀ j, (classes j).card ≤ 3*L+2
  support_card_le : ∀ j, (G.edgeSupport (classes j)).card ≤ 6*L+4
  support_outside_iff : ∀ j v, v ∉ U₀ ∪ U₁ →
    (v ∈ G.edgeSupport (classes j) ↔ v ∈ G.edgeSupport (C.classes j))
  outside_load_le : ∀ v, v ∉ U₀ ∪ U₁ →
    (univ.filter (fun j => v ∈ G.edgeSupport (classes j))).card ≤ D

/-- Assemble two completions relative to the original palette. The first
completed family is never treated as a new joining palette. -/
def PairFiberCompletion.combine
    (B₀ : PairFiberCompletion C U₀) (B₁ : PairFiberCompletion C U₁)
    (h01 : Disjoint U₀ U₁) (hU₁ : U₁.card ≤ 2) :
    TwoPairFiberCompletion C U₀ U₁ := by
  have hout (j : Fin h) (v : V) (hv : v ∉ U₀ ∪ U₁) :
      v ∈ G.edgeSupport (B₀.classes j ∪ B₁.classes j) ↔
        v ∈ G.edgeSupport (C.classes j) := by
    have hv0 : v ∉ U₀ := fun hh => hv (mem_union_left _ hh)
    have hv1 : v ∉ U₁ := fun hh => hv (mem_union_right _ hh)
    constructor
    · intro hm
      obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
      rcases mem_union.mp he with he | he
      · exact (B₀.support_outside_iff j v hv0).mp
          ((G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩)
      · exact (B₁.support_outside_iff j v hv1).mp
          ((G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩)
    · intro hm
      obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hm
      exact (G.mem_edgeSupport _ v).mpr
        ⟨e, mem_union_left _ (B₀.contains_joining j he), hve⟩
  refine {
    first := B₀
    second := B₁
    classes := fun j => B₀.classes j ∪ B₁.classes j
    classes_eq := fun _ => rfl
    contains_joining := fun j => (B₀.contains_joining j).trans subset_union_left
    matching := B₀.union_isMatching B₁ h01
    disjoint := B₀.union_disjoint B₁ h01
    cover := ?_
    covers := ?_
    cut_eq := ?_
    card_le := B₀.union_card_le B₁ hU₁
    support_card_le := ?_
    support_outside_iff := hout
    outside_load_le := ?_
  }
  · have hu : univ.biUnion (fun j => B₀.classes j ∪ B₁.classes j) =
        univ.biUnion B₀.classes ∪ univ.biUnion B₁.classes := by
      ext e
      simp only [mem_biUnion, mem_univ, true_and, mem_union]
      aesop
    rw [hu, B₀.cover, B₁.cover]
    ext e
    simp only [mem_union]
    tauto
  · intro j v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp (B₀.covers j hv)
      exact (G.mem_edgeSupport _ v).mpr ⟨e, mem_union_left _ he, hve⟩
    · obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp (B₁.covers j hv)
      exact (G.mem_edgeSupport _ v).mpr ⟨e, mem_union_right _ he, hve⟩
  · intro j k
    change (B₀.classes j ∪ B₁.classes j).filter _ = _
    rw [filter_union]
    change G.cutOn (B₀.classes j) (labelShore label {k}) ∪
      G.cutOn (B₁.classes j) (labelShore label {k}) = _
    rw [B₀.cut_eq j k, B₁.cut_eq j k, union_self]
  · intro j
    have hs := (B₀.union_isMatching B₁ h01 j).edgeSupport_card G
    have hc := B₀.union_card_le B₁ hU₁ j
    omega
  · intro v hv
    have hs : univ.filter (fun j => v ∈ G.edgeSupport (B₀.classes j ∪ B₁.classes j)) =
        univ.filter (fun j => v ∈ G.edgeSupport (C.classes j)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, hout j v hv]
    rw [hs]
    exact C.vertex_load_le v

/-- Each first-pair copy retains its assigned color in the combined family. -/
theorem TwoPairFiberCompletion.first_copy_mem
    (B : TwoPairFiberCompletion C U₀ U₁) (e : G.internalOn univ U₀) :
    e.val ∈ B.classes (B.first.color e) := by
  rw [B.classes_eq, B.first.class_of_copy]
  exact mem_union_left _ (mem_union_right _ (mem_singleton_self _))

/-- Each second-pair copy retains its assigned color in the combined family. -/
theorem TwoPairFiberCompletion.second_copy_mem
    (B : TwoPairFiberCompletion C U₀ U₁) (e : G.internalOn univ U₁) :
    e.val ∈ B.classes (B.second.color e) := by
  rw [B.classes_eq, B.second.class_of_copy]
  exact mem_union_right _ (mem_union_right _ (mem_singleton_self _))

/-- When both internal copies receive one protected color, the combined
class is exactly the original joining class together with those two copies. -/
theorem TwoPairFiberCompletion.class_of_two_copies
    (B : TwoPairFiberCompletion C U₀ U₁)
    (e₀ : G.internalOn univ U₀) (e₁ : G.internalOn univ U₁) (j : Fin h)
    (h₀ : B.first.color e₀ = j) (h₁ : B.second.color e₁ = j) :
    B.classes j = C.classes j ∪ {e₀.val, e₁.val} := by
  have hb0 : B.first.classes j = C.classes j ∪ {e₀.val} := by
    rw [← h₀]
    exact B.first.class_of_copy e₀
  have hb1 : B.second.classes j = C.classes j ∪ {e₁.val} := by
    rw [← h₁]
    exact B.second.class_of_copy e₁
  rw [B.classes_eq j, hb0, hb1]
  ext e
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

/-- Independent seed prescriptions may use the same protected color.
The complete protected class then contains exactly the two prescribed copies. -/
theorem TwoPairFiberCompletion.prescribed_class
    (B : TwoPairFiberCompletion C U₀ U₁)
    (S₀ : Finset (G.internalOn univ U₀)) (S₁ : Finset (G.internalOn univ U₁))
    (seed₀ : G.internalOn univ U₀ → Fin h) (seed₁ : G.internalOn univ U₁ → Fin h)
    (hseed₀ : ∀ e ∈ S₀, B.first.color e = seed₀ e)
    (hseed₁ : ∀ e ∈ S₁, B.second.color e = seed₁ e)
    (e₀ : G.internalOn univ U₀) (he₀ : e₀ ∈ S₀)
    (e₁ : G.internalOn univ U₁) (he₁ : e₁ ∈ S₁) (j : Fin h)
    (hj₀ : seed₀ e₀ = j) (hj₁ : seed₁ e₁ = j) :
    B.classes j = C.classes j ∪ {e₀.val, e₁.val} :=
  B.class_of_two_copies e₀ e₁ j ((hseed₀ e₀ he₀).trans hj₀)
    ((hseed₁ e₁ he₁).trans hj₁)

/-- Simultaneously complete two distinct actual assigned pair fibers.
Each seed is injective only within its own pair pool; common protected colors
across the two pools are allowed. -/
theorem JoiningPalette.exists_two_pairFiber_completion
    (C : JoiningPalette G label h D L p) (i₀ i₁ : K) (hi : i₀ ≠ i₁)
    (U₀ U₁ : Finset V) (hU₀ : U₀.card = 2) (hU₁ : U₁.card = 2)
    (hfiber₀ : labelShore label {i₀} = U₀) (hfiber₁ : labelShore label {i₁} = U₁)
    (hp₀ : p i₀ = 0) (hp₁ : p i₁ = 0)
    (hregular₀ : ∀ v ∈ U₀, G.degree v = h)
    (hregular₁ : ∀ v ∈ U₁, G.degree v = h)
    (S₀ : Finset (G.internalOn univ U₀)) (S₁ : Finset (G.internalOn univ U₁))
    (seed₀ : G.internalOn univ U₀ → Fin h) (seed₁ : G.internalOn univ U₁ → Fin h)
    (hfree₀ : ∀ e ∈ S₀, ∀ v ∈ U₀, v ∉ G.edgeSupport (C.classes (seed₀ e)))
    (hfree₁ : ∀ e ∈ S₁, ∀ v ∈ U₁, v ∉ G.edgeSupport (C.classes (seed₁ e)))
    (hinj₀ : Set.InjOn seed₀ S₀) (hinj₁ : Set.InjOn seed₁ S₁) :
    ∃ B : TwoPairFiberCompletion C U₀ U₁,
      (∀ e ∈ S₀, B.first.color e = seed₀ e) ∧
      (∀ e ∈ S₁, B.second.color e = seed₁ e) := by
  obtain ⟨B₀, hs₀⟩ := C.exists_pairFiber_completion i₀ U₀ hU₀ hfiber₀ hp₀
    hregular₀ S₀ seed₀ hfree₀ hinj₀
  obtain ⟨B₁, hs₁⟩ := C.exists_pairFiber_completion i₁ U₁ hU₁ hfiber₁ hp₁
    hregular₁ S₁ seed₁ hfree₁ hinj₁
  have h01 : Disjoint U₀ U₁ := by
    rw [← hfiber₀, ← hfiber₁]
    apply disjoint_left.mpr
    intro v hv₀ hv₁
    simp only [mem_labelShore, mem_singleton] at hv₀ hv₁
    exact hi (hv₀.symm.trans hv₁)
  exact ⟨B₀.combine B₁ h01 (by omega), hs₀, hs₁⟩

end Overfull.NativeReserve
