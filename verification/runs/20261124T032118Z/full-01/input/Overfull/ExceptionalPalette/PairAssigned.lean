import Overfull.ExceptionalPalette.PairExtension

/-!
# Complete the actual assigned exceptional pair in a residual host

The representative lives in the original multigraph. The palette and the
parallel copies live in the residual host on the same vertices. The actual
pair fiber is derived from the original representative's assignment.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd AssignedParts

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
variable {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- A complete coloring of the actual internal pair copies together with
the original joining palette, retaining its colors and exact fiber cuts. -/
structure PairFiberCompletion (C : JoiningPalette G label h D L p) (U : Finset V) where
  color : G.internalOn univ U → Fin h
  color_injective : Function.Injective color
  classes : Fin h → Finset E
  class_of_copy : ∀ e, classes (color e) = C.classes (color e) ∪ {e.val}
  contains_joining : ∀ j, C.classes j ⊆ classes j
  matching : ∀ j, G.IsMatching (classes j)
  disjoint : Pairwise (fun j k => Disjoint (classes j) (classes k))
  cover : univ.biUnion classes = joiningCopies G label ∪ G.internalOn univ U
  covers : ∀ j, U ⊆ G.edgeSupport (classes j)
  cut_eq : ∀ j k, G.cutOn (classes j) (labelShore label {k}) =
    G.cutOn (C.classes j) (labelShore label {k})
  card_le : ∀ j, (classes j).card ≤ 3*L+1
  support_card_le : ∀ j, (G.edgeSupport (classes j)).card ≤ 6*L+2
  outside_load_le : ∀ v, v ∉ U →
    (univ.filter (fun j => v ∈ G.edgeSupport (classes j))).card ≤ D

/-- Prescribed copies retain both their exact labels and their exact
one-copy enlargement of the old joining class. -/
theorem PairFiberCompletion.prescribed_class
    {C : JoiningPalette G label h D L p} {U : Finset V}
    (B : PairFiberCompletion C U) (S : Finset (G.internalOn univ U))
    (seed : G.internalOn univ U → Fin h)
    (hseed : ∀ e ∈ S, B.color e = seed e) (e : G.internalOn univ U) (he : e ∈ S) :
    B.classes (seed e) = C.classes (seed e) ∪ {e.val} := by
  rw [← hseed e he]
  exact B.class_of_copy e

/-- The pair completion for an actual two-vertex fiber, without a chosen
ordering of its vertices. All seed conditions concern actual copies. -/
theorem JoiningPalette.exists_pairFiber_completion
    (C : JoiningPalette G label h D L p) (i : K) (U : Finset V)
    (hU : U.card = 2) (hfiber : labelShore label {i} = U) (hp : p i = 0)
    (hregular : ∀ v ∈ U, G.degree v = h)
    (S : Finset (G.internalOn univ U)) (seed : G.internalOn univ U → Fin h)
    (hfree : ∀ e ∈ S, ∀ v ∈ U, v ∉ G.edgeSupport (C.classes (seed e)))
    (hinj : Set.InjOn seed S) :
    ∃ B : PairFiberCompletion C U, ∀ e ∈ S, B.color e = seed e := by
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hU
  have hfreeX : ∀ e ∈ S, seed e ∈ C.freeColors x := by
    intro e he
    exact (C.mem_freeColors x (seed e)).mpr (hfree e he x (mem_insert_self _ _))
  obtain ⟨f,B,hseed,hB,hbase,_hpres,hmatch,hdisj,hcover,hcovered,hcuts,hcard,hsupport,hload⟩ :=
    C.exists_pair_extension i x y hxy hfiber hp
      (hregular x (mem_insert_self _ _)) S seed hfreeX hinj
  refine ⟨{
    color := fun e => (f e).val
    color_injective := Subtype.val_injective.comp f.injective
    classes := B
    class_of_copy := ?_
    contains_joining := hbase
    matching := hmatch
    disjoint := hdisj
    cover := hcover
    covers := hcovered
    cut_eq := hcuts
    card_le := hcard
    support_card_le := hsupport
    outside_load_le := ?_
  }, hseed⟩
  · intro e
    rw [hB, C.pairExtended_class_of_copy x y f e]
  · intro v hv
    have hn : v ≠ x ∧ v ≠ y := by
      simpa only [mem_insert, mem_singleton, not_or] using hv
    exact hload v hn.1 hn.2

end Overfull.NativeReserve

namespace Overfull.AssignedParts

open Finset Classical FourOdd NativeReserve

variable {V E F : Type*} [Fintype V] [Fintype F]

/-- Apply the pair construction to the original representative's actual
pair part in any regular residual host on the same vertices. The original
matching need not survive in that residual. -/
theorem exists_assigned_pair_completion
    (G : Multigraph V E) (H : Multigraph V F) {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hpair : (pairPart G M Z).card = 2)
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette H (assignedLabel G M U₀ U₁ Z) h D L p)
    (hp : p 2 = 0) (hregular : ∀ v, H.degree v = h)
    (S : Finset (H.internalOn univ (pairPart G M Z)))
    (seed : H.internalOn univ (pairPart G M Z) → Fin h)
    (hfree : ∀ e ∈ S, ∀ v ∈ pairPart G M Z,
      v ∉ H.edgeSupport (C.classes (seed e)))
    (hinj : Set.InjOn seed S) :
    ∃ B : PairFiberCompletion C (pairPart G M Z),
      (∀ e ∈ S, B.color e = seed e) ∧
      (∀ e ∈ S, B.classes (seed e) = C.classes (seed e) ∪ {e.val}) := by
  have hfiber : labelShore (assignedLabel G M U₀ U₁ Z) {2} = pairPart G M Z := by
    simpa only [labelShore, mem_singleton] using
      (assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover).2.2
  obtain ⟨B,hB⟩ := C.exists_pairFiber_completion 2 (pairPart G M Z)
    hpair hfiber hp (fun v _ => hregular v) S seed hfree hinj
  exact ⟨B,hB,fun e he => B.prescribed_class S seed hB e he⟩

end Overfull.AssignedParts
