import Overfull.ExceptionalPalette.PairColoring

/-!
# Complete the internal exceptional pair without changing its joining palette

The constructed bijection colors every actual parallel copy. The enlarged
classes remain matchings, retain their exact fiber-cut parity, and cover both
exceptional vertices in every color. Prescribed reserve copies keep their
prescribed labels.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
variable {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- Insert the actual pair copies in the colors furnished by the bijection. -/
def JoiningPalette.pairExtendedClasses (C : JoiningPalette G label h D L p)
    (x y : V) (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) : Finset E :=
  C.classes j ∪ pairColorClass G x y (fun e => (f e).val) j

theorem JoiningPalette.classes_subset_joining (C : JoiningPalette G label h D L p)
    (j : Fin h) : C.classes j ⊆ joiningCopies G label := by
  intro e he
  rw [← C.cover]
  exact mem_biUnion.mpr ⟨j,mem_univ _,he⟩

theorem JoiningPalette.classes_subset_pairExtended
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    C.classes j ⊆ C.pairExtendedClasses x y f j := subset_union_left

/-- The class assigned to a pair copy is exactly the old joining class
with that one original copy inserted. -/
theorem JoiningPalette.pairExtended_class_of_copy
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (e : pairFiberCopies G x y) :
    C.pairExtendedClasses x y f (f e).val = C.classes (f e).val ∪ {e.val} := by
  unfold JoiningPalette.pairExtendedClasses
  rw [pairColorClass_eq_singleton G x y (fun q => (f q).val)
    (Subtype.val_injective.comp f.injective) e]

/-- The added actual pair copy has both endpoints free in its assigned color. -/
theorem JoiningPalette.pairAdded_disjoint_support
    (C : JoiningPalette G label h D L p) (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    Disjoint (G.edgeSupport (C.classes j))
      (G.edgeSupport (pairColorClass G x y (fun e => (f e).val) j)) := by
  apply disjoint_left.mpr
  intro v hvC hvA
  obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hvA
  obtain ⟨q,hq,rfl⟩ := (mem_pairColorClass G x y _ j e).mp he
  have hj : j ∈ C.freeColors x := hq ▸ (f q).property
  have hx : x ∉ G.edgeSupport (C.classes j) := (C.mem_freeColors x j).mp hj
  have hy : y ∉ G.edgeSupport (C.classes j) :=
    fun hy => hx ((C.pair_support_iff i x y hxy hfiber hp j).mpr hy)
  rcases (pairFiberCopies_incident G q.property v).mp hve with rfl | rfl
  · exact hx hvC
  · exact hy hvC

/-- Every enlarged color class is an actual matching. -/
theorem JoiningPalette.pairExtended_isMatching
    (C : JoiningPalette G label h D L p) (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    G.IsMatching (C.pairExtendedClasses x y f j) := by
  have hA := pairColorClass_isMatching G x y (fun e => (f e).val)
    (Subtype.val_injective.comp f.injective) j
  have hd := C.pairAdded_disjoint_support i x y hxy hfiber hp f j
  intro e he e' he' v hev he'v
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp he' with he' | he'
  · exact C.matching j e he e' he' v hev he'v
  · exact (disjoint_left.mp hd ((G.mem_edgeSupport _ v).mpr ⟨e,he,hev⟩)
      ((G.mem_edgeSupport _ v).mpr ⟨e',he',he'v⟩)).elim
  · exact (disjoint_left.mp hd ((G.mem_edgeSupport _ v).mpr ⟨e',he',he'v⟩)
      ((G.mem_edgeSupport _ v).mpr ⟨e,he,hev⟩)).elim
  · exact hA e he e' he' v hev he'v

/-- Different enlarged color classes still use disjoint original copies. -/
theorem JoiningPalette.pairExtended_disjoint
    (C : JoiningPalette G label h D L p) (i : K) (x y : V)
    (hfiber : labelShore label {i} = {x,y})
    (f : pairFiberCopies G x y ≃ C.freeColors x) :
    Pairwise (fun j k => Disjoint
      (C.pairExtendedClasses x y f j) (C.pairExtendedClasses x y f k)) := by
  have hPJ := pairFiberCopies_disjoint_joining G label i x y hfiber
  intro j k hjk
  apply disjoint_left.mpr
  intro e he hf
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact disjoint_left.mp (C.disjoint hjk) he hf
  · exact disjoint_left.mp hPJ (pairColorClass_subset G x y _ k hf)
      (C.classes_subset_joining j he)
  · exact disjoint_left.mp hPJ (pairColorClass_subset G x y _ j he)
      (C.classes_subset_joining k hf)
  · exact disjoint_left.mp (pairColorClass_disjoint G x y _ hjk) he hf

/-- Exact accounting: the joining copies and the full internal parallel pool
are colored, with every other copy left untouched. -/
theorem JoiningPalette.pairExtended_cover (C : JoiningPalette G label h D L p)
    (x y : V) (f : pairFiberCopies G x y ≃ C.freeColors x) :
    univ.biUnion (C.pairExtendedClasses x y f) =
      joiningCopies G label ∪ pairFiberCopies G x y := by
  rw [← C.cover, ← pairColorClass_cover G x y (fun e => (f e).val)]
  ext e
  simp only [mem_biUnion, mem_univ, true_and, JoiningPalette.pairExtendedClasses, mem_union]
  aesop

/-- Every color now covers both exceptional vertices. -/
theorem JoiningPalette.pairExtended_covers_pair
    (C : JoiningPalette G label h D L p) (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    {x,y} ⊆ G.edgeSupport (C.pairExtendedClasses x y f j) := by
  by_cases hj : j ∈ C.freeColors x
  · have hh := pairColorClass_covers_free C x y f j hj
    intro v hv
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp (hh hv)
    exact (G.mem_edgeSupport _ v).mpr ⟨e,mem_union_right _ he,hve⟩
  · have hx : x ∈ G.edgeSupport (C.classes j) := by
      simpa only [JoiningPalette.mem_freeColors, not_not] using hj
    have hy := (C.pair_support_iff i x y hxy hfiber hp j).mp hx
    intro v hv
    have hvC : v ∈ G.edgeSupport (C.classes j) := by
      rcases mem_insert.mp hv with rfl | hv
      · exact hx
      · exact (mem_singleton.mp hv) ▸ hy
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hvC
    exact (G.mem_edgeSupport _ v).mpr ⟨e,mem_union_left _ he,hve⟩

/-- Added pair copies are internal to one assigned fiber, so every original
fiber cut is preserved as an exact set of copies. -/
theorem JoiningPalette.pairExtended_cut_eq
    (C : JoiningPalette G label h D L p) (i : K) (x y : V)
    (hfiber : labelShore label {i} = {x,y})
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) (k : K) :
    G.cutOn (C.pairExtendedClasses x y f j) (labelShore label {k}) =
      G.cutOn (C.classes j) (labelShore label {k}) := by
  have hPJ := pairFiberCopies_disjoint_joining G label i x y hfiber
  ext e
  simp only [Multigraph.mem_cutOn, JoiningPalette.pairExtendedClasses, mem_union]
  constructor
  · rintro ⟨he | he,hcut⟩
    · exact ⟨he,hcut⟩
    · have hsame : label (G.firstEnd e) = label (G.secondEnd e) := by
        by_contra hn
        exact disjoint_left.mp hPJ (pairColorClass_subset G x y _ j he)
          ((mem_joiningCopies G label e).mpr hn)
      have hmem : (G.firstEnd e ∈ labelShore label {k}) =
          (G.secondEnd e ∈ labelShore label {k}) := by
        simp only [mem_labelShore, hsame]
      exact (hcut hmem).elim
  · intro he
    exact ⟨Or.inl he.1,he.2⟩

theorem JoiningPalette.pairExtended_cut_parity
    (C : JoiningPalette G label h D L p) (i : K) (x y : V)
    (hfiber : labelShore label {i} = {x,y})
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) (k : K) :
    (G.cutOn (C.pairExtendedClasses x y f j) (labelShore label {k})).card % 2 = p k := by
  rw [C.pairExtended_cut_eq i x y hfiber f j k]
  exact C.cut_parity j k

/-- Inserting the pair colors adds at most one original copy to any class. -/
theorem JoiningPalette.pairExtended_card_le
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    (C.pairExtendedClasses x y f j).card ≤ (C.classes j).card+1 := by
  have hu := card_union_le (C.classes j) (pairColorClass G x y (fun e => (f e).val) j)
  have ha := pairColorClass_card_le_one G x y (fun e => (f e).val)
    (Subtype.val_injective.comp f.injective) j
  exact hu.trans (Nat.add_le_add_left ha _)

/-- At most the two exceptional vertices are added to a class footprint. -/
theorem JoiningPalette.pairExtended_support_card_le
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h) :
    (G.edgeSupport (C.pairExtendedClasses x y f j)).card ≤
      (G.edgeSupport (C.classes j)).card+2 := by
  have hs : G.edgeSupport (C.pairExtendedClasses x y f j) ⊆
      G.edgeSupport (C.classes j) ∪ {x,y} := by
    intro v hv
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ ((G.mem_edgeSupport _ v).mpr ⟨e,he,hve⟩)
    · exact mem_union_right _ (pairColorClass_support_subset G x y _ j
        ((G.mem_edgeSupport _ v).mpr ⟨e,he,hve⟩))
  have hp : ({x,y} : Finset V).card ≤ 2 := by
    exact (card_insert_le x {y}).trans (by simp)
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left hp _))

/-- Every old-core footprint and hence its color load is unchanged. -/
theorem JoiningPalette.pairExtended_support_outside
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x) (j : Fin h)
    (v : V) (hvx : v ≠ x) (hvy : v ≠ y) :
    v ∈ G.edgeSupport (C.pairExtendedClasses x y f j) ↔
      v ∈ G.edgeSupport (C.classes j) := by
  constructor
  · intro hv
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
    rcases mem_union.mp he with he | he
    · exact (G.mem_edgeSupport _ v).mpr ⟨e,he,hve⟩
    · have hvpair := pairColorClass_support_subset G x y _ j
        ((G.mem_edgeSupport _ v).mpr ⟨e,he,hve⟩)
      simp only [mem_insert, mem_singleton] at hvpair
      exact (hvpair.elim hvx hvy).elim
  · intro hv
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
    exact (G.mem_edgeSupport _ v).mpr ⟨e,mem_union_left _ he,hve⟩

theorem JoiningPalette.pairExtended_outside_load_le
    (C : JoiningPalette G label h D L p) (x y : V)
    (f : pairFiberCopies G x y ≃ C.freeColors x)
    (v : V) (hvx : v ≠ x) (hvy : v ≠ y) :
    (univ.filter (fun j => v ∈ G.edgeSupport (C.pairExtendedClasses x y f j))).card ≤ D := by
  have hs : (univ.filter (fun j => v ∈ G.edgeSupport (C.pairExtendedClasses x y f j))) =
      univ.filter (fun j => v ∈ G.edgeSupport (C.classes j)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and,
      C.pairExtended_support_outside x y f j v hvx hvy]
  rw [hs]
  exact C.vertex_load_le v

/-- Construct the full internal pair coloring while retaining any supplied
injective reserve prescription. No residual coloring is assumed. -/
theorem JoiningPalette.exists_pair_extension
    (C : JoiningPalette G label h D L p) (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0)
    (hdegree : G.degree x = h)
    (S : Finset (pairFiberCopies G x y))
    (seed : pairFiberCopies G x y → Fin h)
    (hfree : ∀ e ∈ S, seed e ∈ C.freeColors x)
    (hinj : Set.InjOn seed S) :
    ∃ (f : pairFiberCopies G x y ≃ C.freeColors x) (B : Fin h → Finset E),
      (∀ e ∈ S, (f e).val = seed e) ∧
      (∀ j, B j = C.pairExtendedClasses x y f j) ∧
      (∀ j, C.classes j ⊆ B j) ∧
      (∀ e ∈ S, e.val ∈ B (seed e)) ∧
      (∀ j, G.IsMatching (B j)) ∧
      Pairwise (fun j k => Disjoint (B j) (B k)) ∧
      univ.biUnion B = joiningCopies G label ∪ pairFiberCopies G x y ∧
      (∀ j, {x,y} ⊆ G.edgeSupport (B j)) ∧
      (∀ j k, G.cutOn (B j) (labelShore label {k}) =
        G.cutOn (C.classes j) (labelShore label {k})) ∧
      (∀ j, (B j).card ≤ 3*L+1) ∧
      (∀ j, (G.edgeSupport (B j)).card ≤ 6*L+2) ∧
      (∀ v, v ≠ x → v ≠ y →
        (univ.filter (fun j => v ∈ G.edgeSupport (B j))).card ≤ D) := by
  obtain ⟨f,hf⟩ := C.exists_pair_bijection i x y hfiber hdegree S seed hfree hinj
  refine ⟨f,C.pairExtendedClasses x y f,hf,fun _ => rfl,
    C.classes_subset_pairExtended x y f,?_,
    C.pairExtended_isMatching i x y hxy hfiber hp f,
    C.pairExtended_disjoint i x y hfiber f,
    C.pairExtended_cover x y f,
    C.pairExtended_covers_pair i x y hxy hfiber hp f,
    C.pairExtended_cut_eq i x y hfiber f,?_,?_,
    C.pairExtended_outside_load_le x y f⟩
  · intro e he
    apply mem_union_right
    rw [← hf e he]
    exact pairColorClass_contains_prescribed G x y (fun q => (f q).val) e
  · intro j
    exact (C.pairExtended_card_le x y f j).trans (Nat.add_le_add_right (C.card_le j) 1)
  · intro j
    exact (C.pairExtended_support_card_le x y f j).trans
      (Nat.add_le_add_right (C.support_card_le j) 2)

end Overfull.NativeReserve
