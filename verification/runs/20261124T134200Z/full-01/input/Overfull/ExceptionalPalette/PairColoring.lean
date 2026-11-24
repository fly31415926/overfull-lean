import Overfull.ExceptionalPalette.PairFree
import Mathlib.Data.Fintype.Sum

/-!
# A bijection from actual pair copies to the common free palette

Any injective prescription of reserved parallel copies to free colors is
retained. Every unprescribed copy is assigned one of the remaining colors,
with no identification of distinct parallel copies.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd

variable {V E K : Type*} [Fintype E] [DecidableEq K]
variable {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- Extend an injective prescription on actual pair copies to the exact
common free palette. Cardinality is proved from the host degree. -/
theorem JoiningPalette.exists_pair_bijection [Fintype V]
    (C : JoiningPalette G label h D L p) (i : K) (x y : V)
    (hfiber : labelShore label {i} = {x,y}) (hdegree : G.degree x = h)
    (S : Finset (pairFiberCopies G x y))
    (seed : pairFiberCopies G x y → Fin h)
    (hfree : ∀ e ∈ S, seed e ∈ C.freeColors x)
    (hinj : Set.InjOn seed S) :
    ∃ f : pairFiberCopies G x y ≃ C.freeColors x,
      ∀ e ∈ S, (f e).val = seed e := by
  apply Finset.exists_equiv_extend_of_card_eq
    (show Fintype.card (pairFiberCopies G x y) = (C.freeColors x).card from by
      rw [Fintype.card_coe, C.pair_freeColors_card i x y hfiber hdegree])
    (by
      intro j hj
      obtain ⟨e,he,rfl⟩ := mem_image.mp hj
      exact hfree e he)
    hinj

/-- The pair copies assigned one color, retaining their original identities. -/
def pairColorClass (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (j : Fin h) : Finset E :=
  (univ.filter (fun e => c e = j)).image Subtype.val

@[simp] theorem mem_pairColorClass (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (j : Fin h) (e : E) :
    e ∈ pairColorClass G x y c j ↔
      ∃ q : pairFiberCopies G x y, c q = j ∧ q.val = e := by
  simp only [pairColorClass, mem_image, mem_filter, mem_univ, true_and]

theorem pairColorClass_subset (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (j : Fin h) :
    pairColorClass G x y c j ⊆ pairFiberCopies G x y := by
  intro e he
  obtain ⟨q,_,rfl⟩ := (mem_pairColorClass G x y c j e).mp he
  exact q.property

/-- Injectivity gives at most one actual parallel copy per color. -/
theorem pairColorClass_card_le_one (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (hc : Function.Injective c) (j : Fin h) :
    (pairColorClass G x y c j).card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨q,hq,rfl⟩ := (mem_pairColorClass G x y c j e).mp he
  obtain ⟨q',hq',rfl⟩ := (mem_pairColorClass G x y c j f).mp hf
  exact congrArg Subtype.val (hc (hq.trans hq'.symm))

theorem pairColorClass_isMatching (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (hc : Function.Injective c) (j : Fin h) :
    G.IsMatching (pairColorClass G x y c j) := by
  intro e he f hf _ _ _
  exact card_le_one.mp (pairColorClass_card_le_one G x y c hc j) e he f hf

theorem pairColorClass_support_subset (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (j : Fin h) :
    G.edgeSupport (pairColorClass G x y c j) ⊆ {x,y} := by
  intro v hv
  obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
  have hh := (pairFiberCopies_incident G
    (pairColorClass_subset G x y c j he) v).mp hve
  simpa only [mem_insert, mem_singleton] using hh

/-- Different colors use disjoint actual parallel copies. -/
theorem pairColorClass_disjoint (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) :
    Pairwise (fun i j => Disjoint (pairColorClass G x y c i) (pairColorClass G x y c j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨q,hq,hqe⟩ := (mem_pairColorClass G x y c i e).mp he
  obtain ⟨q',hq',hq'e⟩ := (mem_pairColorClass G x y c j e).mp hf
  have hqq : q = q' := Subtype.ext (hqe.trans hq'e.symm)
  exact hij (hq.symm.trans (hqq ▸ hq'))

/-- Every actual parallel copy occurs in its assigned color class. -/
theorem pairColorClass_cover (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) :
    univ.biUnion (pairColorClass G x y c) = pairFiberCopies G x y := by
  ext e
  constructor
  · intro he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    exact pairColorClass_subset G x y c j hj
  · intro he
    let q : pairFiberCopies G x y := ⟨e,he⟩
    exact mem_biUnion.mpr ⟨c q,mem_univ _,
      (mem_pairColorClass G x y c (c q) e).mpr ⟨q,rfl,rfl⟩⟩

/-- A bijection assigns a pair copy to every free color. -/
theorem pairColorClass_covers_free [Fintype V] (C : JoiningPalette G label h D L p)
    (x y : V) (f : pairFiberCopies G x y ≃ C.freeColors x)
    (j : Fin h) (hj : j ∈ C.freeColors x) :
    {x,y} ⊆ G.edgeSupport (pairColorClass G x y (fun e => (f e).val) j) := by
  let q : pairFiberCopies G x y := f.symm ⟨j,hj⟩
  have hcolor : (f q).val = j := congrArg Subtype.val (f.apply_symm_apply ⟨j,hj⟩)
  have hq : q.val ∈ pairColorClass G x y (fun e => (f e).val) j :=
    (mem_pairColorClass G x y _ j q.val).mpr ⟨q,hcolor,rfl⟩
  intro v hv
  apply (G.mem_edgeSupport _ v).mpr
  refine ⟨q.val,hq,(pairFiberCopies_incident G q.property v).mpr ?_⟩
  simpa only [mem_insert, mem_singleton] using hv

/-- A prescribed copy receives its exact prescribed color. -/
theorem pairColorClass_contains_prescribed (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (e : pairFiberCopies G x y) :
    e.val ∈ pairColorClass G x y c (c e) :=
  (mem_pairColorClass G x y c (c e) e.val).mpr ⟨e,rfl,rfl⟩

/-- An injective coloring puts exactly the prescribed original copy in its color. -/
theorem pairColorClass_eq_singleton (G : Multigraph V E) (x y : V)
    (c : pairFiberCopies G x y → Fin h) (hc : Function.Injective c)
    (e : pairFiberCopies G x y) :
    pairColorClass G x y c (c e) = {e.val} := by
  ext a
  constructor
  · intro ha
    apply mem_singleton.mpr
    exact card_le_one.mp (pairColorClass_card_le_one G x y c hc (c e))
      a ha e.val (pairColorClass_contains_prescribed G x y c e)
  · intro ha
    rw [mem_singleton.mp ha]
    exact pairColorClass_contains_prescribed G x y c e

end Overfull.NativeReserve
