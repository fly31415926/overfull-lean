import Overfull.ExceptionalPalette.PairAssigned
import Overfull.ExceptionalPalette.ReserveInsertion
import Overfull.NativeCore.Incidence

/-!
# Paired exceptions with exact native reserve prescriptions

Each original paired reserve boundary contains one surviving internal pair
copy. The copies are distinct across reserve indices. Their prescribed colors
are extended to all actual pair copies, so the full pair completion retains
every selected whole boundary, not merely its joining trace.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E J I K : Type*} [Fintype E]

/-- Select the surviving actual pair copy in each selected native boundary.
The original reserve index is retained, including for parallel copies. -/
theorem exists_native_reserved_pair_injection
    (G : Multigraph V E) {M : Finset E} (U₀ U₁ Z : Finset V)
    (hcode : coarseSignature G M U₀ Z = none)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (q : I → Fin r) (hq : Function.Injective q) :
    ∃ g : I → (residualGraph G N T).internalOn univ Z,
      Function.Injective g ∧ ∀ i, (g i).val ∈ Q.residualBoundary N T (q i) := by
  have hex (i : I) : ∃ e : (residualGraph G N T).internalOn univ Z,
      e.val ∈ Q.residualBoundary N T (q i) := by
    obtain ⟨e,he⟩ := signature_none_uses_internalPool G (Q.parent (q i)) U₀ Z
      ((Q.sameSignature (q i)).trans hcode)
    obtain ⟨heM,heI⟩ := mem_inter.mp he
    have hends := (mem_filter.mp heI).2
    have heB : e ∈ Q.boundary (q i) := by
      apply compressedBoundary_retains_exceptional G (Q.parent (q i)) U₀ U₁ Z
      exact (mem_exceptionalCopies G (Q.parent (q i)) Z e).mpr ⟨heM,Or.inl hends.1⟩
    have hsurvive : e ∉ removedCopies N T :=
      fun hr => disjoint_left.mp (Q.boundary_disjoint_removed N T havoid (q i)) heB hr
    let e' : {e : E // e ∉ removedCopies N T} := ⟨e,hsurvive⟩
    have he' : e' ∈ (residualGraph G N T).internalOn univ Z := by
      apply mem_filter.mpr
      exact ⟨mem_univ _,hends⟩
    exact ⟨⟨e',he'⟩,(Q.mem_residualBoundary N T (q i) e').mpr heB⟩
  choose g hg using hex
  refine ⟨g,?_,hg⟩
  intro i j hij
  by_contra hn
  have heq := congrArg Subtype.val hij
  exact disjoint_left.mp (Q.residualBoundary_disjoint N T (fun hh => hn (hq hh)))
    (hg i) (heq.symm ▸ hg j)

section PairClass

variable [Fintype V] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- A matching boundary containing an internal pair copy is exactly its
joining trace plus that copy, and its joining trace is free at both ends. -/
theorem reserved_pair_class
    (C : JoiningPalette G label h D L p) (k : K) (x y : V)
    (hfiber : labelShore label {k} = {x,y})
    (R : Finset E) (hR : G.IsMatching R) (e : pairFiberCopies G x y) (heR : e.val ∈ R)
    (hsubset : R ⊆ joiningCopies G label ∪ exceptionalCopies G univ {x,y})
    (j : Fin h) (htrace : R ∩ joiningCopies G label = C.classes j) :
    R = C.classes j ∪ {e.val} ∧
      ∀ v ∈ ({x,y} : Finset V), v ∉ G.edgeSupport (C.classes j) := by
  have hCsub : C.classes j ⊆ R := by
    rw [← htrace]
    exact inter_subset_left
  have henot : e.val ∉ joiningCopies G label :=
    fun heJ => disjoint_left.mp (pairFiberCopies_disjoint_joining G label k x y hfiber)
      e.property heJ
  have heIncident (v : V) (hv : v ∈ ({x,y} : Finset V)) : v ∈ G.edge e.val := by
    apply (pairFiberCopies_incident G e.property v).mpr
    simpa only [mem_insert,mem_singleton] using hv
  refine ⟨?_,?_⟩
  · apply subset_antisymm
    · intro a ha
      rcases mem_union.mp (hsubset ha) with haJ | haZ
      · apply mem_union_left
        rw [← htrace]
        exact mem_inter.mpr ⟨ha,haJ⟩
      · have haeq : a = e.val := by
          obtain ⟨_,hv | hv⟩ := (mem_exceptionalCopies G univ {x,y} a).mp haZ
          · exact hR a ha e.val heR (G.firstEnd a)
              ((G.incident_iff a _).mpr (Or.inl rfl)) (heIncident _ hv)
          · exact hR a ha e.val heR (G.secondEnd a)
              ((G.incident_iff a _).mpr (Or.inr rfl)) (heIncident _ hv)
        exact mem_union_right _ (mem_singleton.mpr haeq)
    · intro a ha
      rcases mem_union.mp ha with ha | ha
      · exact hCsub ha
      · exact (mem_singleton.mp ha).symm ▸ heR
  · intro v hv hvc
    obtain ⟨a,ha,hva⟩ := (G.mem_edgeSupport _ v).mp hvc
    have haeq := hR a (hCsub ha) e.val heR v hva (heIncident v hv)
    exact henot (haeq ▸ C.classes_subset_joining j ha)

end PairClass

variable [Fintype V] [Fintype I]

set_option maxHeartbeats 600000 in
/-- Complete the actual paired exception fiber while preserving every selected
native reserve boundary in its exact protected color. -/
theorem exists_native_paired_completion
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = none)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (hp : p 2 = 0) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (q : I → Fin r) (f : I → Fin h) (hq : Function.Injective q) (hf : Function.Injective f)
    (P : ReserveExtension C (fun i => Q.residualBoundary N T (q i)) f (Z.card+1)) :
    ∃ F : PairFiberCompletion C Z,
      ∀ i, F.classes (f i) = Q.residualBoundary N T (q i) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  have hpZ := pairPart_eq_exceptions_of_internal G (hM.isMatching G) Z hZ
    ((coarseSignature_eq_none_iff G M U₀ Z).mp hcode)
  have hfiber : labelShore label {2} = Z := by
    have hh := (assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover).2.2
    simpa only [labelShore,mem_singleton,hpZ.1] using hh
  obtain ⟨x,y,hxy,hxyZ⟩ := card_eq_two.mp hpZ.2
  have hpairfiber : labelShore label {2} = {x,y} := hfiber.trans hxyZ
  obtain ⟨g,hg,hgR⟩ := exists_native_reserved_pair_injection G U₀ U₁ Z hcode
    r Q N T havoid q hq
  have hBcard : Fintype.card (H.internalOn univ Z) = Fintype.card (C.freeColors x) := by
    calc
      _ = (pairFiberCopies H x y).card := by simp only [Fintype.card_coe,pairFiberCopies,hxyZ]
      _ = (C.freeColors x).card := C.pair_freeColors_card 2 x y hpairfiber (hregular x)
      _ = _ := (Fintype.card_coe _).symm
  let u : H.internalOn univ Z ≃ C.freeColors x := Fintype.equivOfCardEq hBcard
  let seed : H.internalOn univ Z → Fin h := Function.extend g f (fun e => (u e).val)
  have hseed (i : I) : seed (g i) = f i := hg.extend_apply f (fun e => (u e).val) i
  let S : Finset (H.internalOn univ Z) := univ.image g
  have hRinfo (i : I) : Q.residualBoundary N T (q i) = C.classes (f i) ∪ {(g i).val} ∧
      ∀ v ∈ Z, v ∉ H.edgeSupport (C.classes (f i)) := by
    have hgPair : (g i).val ∈ pairFiberCopies H x y := by
      change (g i).val ∈ H.internalOn univ {x,y}
      rw [← hxyZ]
      exact (g i).property
    have htrace : Q.residualBoundary N T (q i) ∩ joiningCopies H label = C.classes (f i) := by
      have hh := P.joining (f i)
      rw [P.prescribed i] at hh
      ext e
      simpa only [mem_inter] using Finset.ext_iff.mp hh e
    have hs : Q.residualBoundary N T (q i) ⊆
        joiningCopies H label ∪ exceptionalCopies H univ {x,y} := by
      have hh := NativeCore.residualBoundary_subset_joining_exceptional
        G U₀ U₁ Z hM h01 h0Z h1Z r Q N T (q i)
      intro e he
      rcases mem_union.mp (hh he) with heJ | heZ
      · exact mem_union_left _ heJ
      · apply mem_union_right
        simpa only [hxyZ] using heZ
    have hh := reserved_pair_class C 2 x y hpairfiber (Q.residualBoundary N T (q i))
      (Q.residualBoundary_matching N T (q i)) ⟨(g i).val,hgPair⟩ (hgR i)
      (by
        intro e he
        simpa only [mem_union] using hs he) (f i)
      (by
        ext e
        simpa only [mem_inter] using Finset.ext_iff.mp htrace e)
    refine ⟨?_,fun v hv => hh.2 v (hxyZ ▸ hv)⟩
    ext e
    simpa only [mem_union,mem_singleton] using Finset.ext_iff.mp hh.1 e
  have hfree : ∀ e ∈ S, ∀ v ∈ Z, v ∉ H.edgeSupport (C.classes (seed e)) := by
    intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    rw [hseed]
    exact (hRinfo i).2
  have hinj : Set.InjOn seed S := by
    intro e he e' he' heq
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    obtain ⟨j,_,rfl⟩ := mem_image.mp he'
    rw [hseed,hseed] at heq
    exact congrArg g (hf heq)
  obtain ⟨F,hF⟩ := C.exists_pairFiber_completion 2 Z hpZ.2 hfiber hp
    (fun v _ => hregular v) S seed hfree hinj
  refine ⟨F,?_⟩
  intro i
  have hi : g i ∈ S := mem_image_of_mem g (mem_univ i)
  have hh := F.prescribed_class S seed hF (g i) hi
  rw [hseed] at hh
  ext e
  have hh₁ := Finset.ext_iff.mp hh e
  have hh₂ := Finset.ext_iff.mp (hRinfo i).1 e
  simp only [mem_union,mem_singleton] at hh₁ hh₂
  exact hh₁.trans hh₂.symm

end Overfull.NativeAssembly
