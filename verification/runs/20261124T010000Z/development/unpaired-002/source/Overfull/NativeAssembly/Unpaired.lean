import Overfull.NativeAssembly.NativeTwoStars
import Overfull.NativeAssembly.SeparateStars
import Overfull.NativeAssembly.ZeroCase
import Overfull.NativeCore.Coverage

/-!
# A native external palette for every unpaired exceptional configuration

An exceptional set of size at most two is empty, a singleton, or a pair.
For a pair, the original assignment determines whether the internal bundle
must be colored or whether its copies are already joining copies. The
corresponding actual native constructions are assembled here. The input
weights and multiplicities are measured on the union of the old cores.
No final exceptional coloring is assumed.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar
  NativeCore WeightedPalette

/-- Enumerate the actual zero-, one-, and two-vertex exceptional sets,
retaining membership in the original set in each nonempty case. -/
theorem small_exception_cases {V : Type*} (Z : Finset V) (hZ : Z.card ≤ 2) :
    Z = ∅ ∨ (∃ z : Z, Z = {z.val}) ∨
      ∃ x y : Z, x.val ≠ y.val ∧ Z = {x.val,y.val} := by
  by_cases hzero : Z = ∅
  · exact Or.inl hzero
  · have hpos : 0 < Z.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
    by_cases hone : Z.card = 1
    · obtain ⟨z,hz⟩ := card_eq_one.mp hone
      have hzmem : z ∈ Z := by rw [hz]; simp
      exact Or.inr (Or.inl ⟨⟨z,hzmem⟩,hz⟩)
    · have htwo : Z.card = 2 := by omega
      obtain ⟨x,y,hxy,hset⟩ := card_eq_two.mp htwo
      have hx : x ∈ Z := by rw [hset]; simp
      have hy : y ∈ Z := by rw [hset]; simp
      exact Or.inr (Or.inr ⟨⟨x,hx⟩,⟨y,hy⟩,hxy,hset⟩)

/-- Every actual copy between an exceptional pair is an exceptional copy. -/
theorem pairFiberCopies_subset_exceptional {V E : Type*} [Fintype E]
    (H : Multigraph V E) (Z : Finset V) (x y : V) (hx : x ∈ Z) :
    pairFiberCopies H x y ⊆ exceptionalCopies H univ Z := by
  intro e he
  apply mem_exceptionalCopies_of_incident H (mem_univ e) hx
  rw [(mem_pairFiberCopies_iff H x y e).mp he]
  simp

variable {V E J I : Type*} [Fintype V] [Fintype E] [Fintype I]

set_option maxHeartbeats 1600000 in
/-- Construct the full actual external matching palette for every native
unpaired assignment with at most two exceptions. All reserve prescriptions,
original joining classes, and assigned-fiber cuts are retained. Regularity
and saturation then give exact coverage of every exceptional edge copy. -/
theorem exists_native_unpaired_completion
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (q : I → Fin r) (hq : Function.Injective q)
    (f : I → Fin h) (hf : Function.Injective f)
    (P : ReserveExtension C (fun i => R.residualBoundary N T (q i)) f (Z.card+1))
    (hregular : ∀ v, (residualGraph G N T).degree v = h) (herror : h-r ≤ D)
    (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h)
    (hweight : ∀ (z : Z) j, starWeight (residualGraph G N T) z.val
      (U₀ ∪ U₁) (C.classes j) ≤ h/8)
    (hparallel : ∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁,
      ((residualGraph G N T).parallelEdges z v).card ≤ D) :
    let H := residualGraph G N T
    let label := assignedLabel G M U₀ U₁ Z
    ∃ F : Fin h → Finset {e : E // e ∉ removedCopies N T},
      (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = R.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j i, H.cutOn (F j) (labelShore label {i}) =
        H.cutOn (C.classes j) (labelShore label {i})) ∧
      (∀ j, (F j).card ≤ max (3*L) (Z.card+1)+2) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 2*max (3*L) (Z.card+1)+4) ∧
      (∀ j, F j ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z) ∧
      univ.biUnion F = joiningCopies H label ∪ exceptionalCopies H univ Z := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let Ext := joiningCopies H label ∪ exceptionalCopies H univ Z
  let B := fun i => R.residualBoundary N T (q i)
  have htrace (i : I) : B i ∩ joiningCopies H label = C.classes (f i) := by
    dsimp only [B]
    rw [← P.prescribed i]
    exact P.joining (f i)
  have hUsub (z : Z) : (if σ z = 0 then U₀ else U₁) ⊆ U₀ ∪ U₁ := by
    split_ifs
    · exact subset_union_left
    · exact subset_union_right
  have hweight' (z : Z) (j : Fin h) :
      starWeight H z.val (if σ z = 0 then U₀ else U₁) (C.classes j) ≤ h/8 :=
    (starWeight_mono_core H z.val _ _ (hUsub z) (C.classes j)).trans (hweight z j)
  have hRsub : univ.biUnion B ⊆ Ext := by
    intro e he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    exact residualBoundary_subset_joining_exceptional G U₀ U₁ Z hM
      h01 h0Z h1Z r R N T (q i) hi
  have hSsub (z : Z) :
      exceptionCorePool H z.val (if σ z = 0 then U₀ else U₁) ⊆ Ext :=
    (exceptionCorePool_subset_exceptional H z.val _ Z z.property).trans subset_union_right
  have hFsub (F : Fin h → Finset {e : E // e ∉ removedCopies N T})
      (S : Finset {e : E // e ∉ removedCopies N T})
      (hF : univ.biUnion F = S) (hS : S ⊆ Ext) : ∀ j, F j ⊆ Ext := by
    intro j e he
    apply hS
    rw [← hF]
    exact mem_biUnion.mpr ⟨j,mem_univ _,he⟩
  have hex : ∃ F : Fin h → Finset {e : E // e ∉ removedCopies N T},
      (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = B i) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j i, H.cutOn (F j) (labelShore label {i}) =
        H.cutOn (C.classes j) (labelShore label {i})) ∧
      (∀ j, (F j).card ≤ max (3*L) (Z.card+1)+2) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 2*max (3*L) (Z.card+1)+4) ∧
      (∀ j, F j ⊆ Ext) := by
    rcases small_exception_cases Z hZ with hzero | ⟨z,hone⟩ | ⟨x,y,hxy,htwo⟩
    · obtain ⟨hm,hd,hcov,hpres,hz,hcuts,hcard,hsupport⟩ :=
        native_zero_exception_extension G hM U₀ U₁ Z h01 h0Z h1Z hzero
          r R N T C q f P
      refine ⟨P.classes,hm,hd,P.contains_original,hpres,hz,hcuts,?_,?_,?_⟩
      · exact fun j => (hcard j).trans (Nat.le_add_right _ _)
      · exact fun j => (hsupport j).trans (Nat.le_add_right _ _)
      · exact hFsub P.classes _ hcov subset_union_left
    · obtain ⟨F,hm,hd,hcov,hC,hpres,hz,hcuts,hcard,hsupport⟩ :=
        exists_native_single_star_extension G hM U₀ U₁ Z h01 h0Z h1Z hcover
          σ hcode r R N T havoid C z hone hregular herror q hq f hf htrace P
          hD hs (hweight' z)
      refine ⟨F,hm,hd,hC,hpres,hz,hcuts,?_,?_,?_⟩
      · intro j
        exact (hcard j).trans (by omega)
      · intro j
        exact (hsupport j).trans (by omega)
      · exact hFsub F _ hcov (union_subset (union_subset subset_union_left hRsub) (hSsub z))
    · have hpar₀ : ∀ v ∈ (if σ y = 0 then U₀ else U₁),
          (H.parallelEdges x.val v).card ≤ D :=
        fun v hv => hparallel x.val x.property v (hUsub y hv)
      have hpar₁ : ∀ v ∈ (if σ y = 0 then U₀ else U₁),
          (H.parallelEdges y.val v).card ≤ D :=
        fun v hv => hparallel y.val y.property v (hUsub y hv)
      by_cases hsame : label x.val = label y.val
      · obtain ⟨F,hm,hd,hcov,hC,hpres,hz,hcuts,hcard,hsupport⟩ :=
          exists_native_same_label_completion G hM U₀ U₁ Z h01 h0Z h1Z hcover
            σ hcode r R N T havoid C q f hq hf P x y htwo hxy hsame hregular herror
            D le_rfl hD hs (hweight' x) (hweight' y) hpar₀ hpar₁
        have hpair : pairFiberCopies H x.val y.val ⊆ Ext :=
          (pairFiberCopies_subset_exceptional H Z x.val y.val x.property).trans subset_union_right
        exact ⟨F,hm,hd,hC,hpres,hz,hcuts,hcard,hsupport,
          hFsub F _ hcov (union_subset (union_subset
            (union_subset (union_subset subset_union_left hRsub) hpair) (hSsub x)) (hSsub y))⟩
      · obtain ⟨F,hm,hd,hcov,hC,hpres,hz,hcuts,hcard,hsupport⟩ :=
          exists_native_separate_stars_extension G hM U₀ U₁ Z h01 h0Z h1Z hcover
            σ hcode r R N T havoid C x y htwo hsame hregular herror q hq f hf htrace P
            le_rfl hD hs (hweight' x) (hweight' y) hpar₀ hpar₁
        exact ⟨F,hm,hd,hC,hpres,hz,hcuts,hcard,hsupport,
          hFsub F _ hcov (union_subset (union_subset
            (union_subset subset_union_left hRsub) (hSsub x)) (hSsub y))⟩
  obtain ⟨F,hm,hd,hC,hpres,hz,hcuts,hcard,hsupport,hsub⟩ := hex
  refine ⟨F,hm,hd,hC,hpres,hz,hcuts,hcard,hsupport,hsub,?_⟩
  have hjoining : joiningCopies H label ⊆ univ.biUnion F := by
    intro e he
    have hCcover : (∃ j, e ∈ C.classes j) ↔ e ∈ joiningCopies H label := by
      simpa only [mem_biUnion,mem_univ,true_and] using Finset.ext_iff.mp C.cover e
    obtain ⟨j,hej⟩ := hCcover.mpr he
    exact mem_biUnion.mpr ⟨j,mem_univ _,hC j hej⟩
  have heq := external_union_eq_of_saturation H label h F Z hd
    (fun z _ => hregular z) hz hjoining hsub
  ext e
  simpa only [mem_biUnion,mem_univ,true_and] using Finset.ext_iff.mp heq e

end Overfull.NativeAssembly
