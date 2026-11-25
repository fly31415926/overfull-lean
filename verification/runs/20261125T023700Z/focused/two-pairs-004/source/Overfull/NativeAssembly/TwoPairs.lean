import Overfull.ExceptionalPalette.TwoPairs
import Overfull.NativeAssembly.TwoPairBoundary

/-!
# Preserve actual reserved boundaries while completing two pair fibers

The two actual internal copies of each reserved matching boundary receive
its same protected color. Their seed maps are constructed from injective
copy selections and extended independently against the original palette.
No positivity assumption on the number of colors is required.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E I K : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- Complete both actual pair pools while preserving every selected whole
matching boundary in its protected color. The separate copy injections and
the joining traces suffice; no disjointness assumption on the boundary
family or disjointness between the two seed-color ranges is needed. -/
theorem exists_reserved_two_pair_completion
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
    (hsubset : ∀ i, R i ⊆
      joiningCopies G label ∪ exceptionalCopies G univ (U₀ ∪ U₁))
    (htrace : ∀ i, R i ∩ joiningCopies G label = C.classes (f i)) :
    ∃ B : TwoPairFiberCompletion C U₀ U₁,
      (∀ i, B.first.color (g₀ i) = f i) ∧
      (∀ i, B.second.color (g₁ i) = f i) ∧
      ∀ i, B.classes (f i) = R i := by
  have hdisjoint : Disjoint U₀ U₁ := by
    rw [← hfiber₀, ← hfiber₁]
    apply disjoint_left.mpr
    intro v hv₀ hv₁
    simp only [mem_labelShore, mem_singleton] at hv₀ hv₁
    exact hk (hv₀.symm.trans hv₁)
  have hRinfo (i : I) :
      R i = C.classes (f i) ∪ {(g₀ i).val, (g₁ i).val} ∧
      (∀ v ∈ U₀ ∪ U₁, v ∉ G.edgeSupport (C.classes (f i))) ∧
      (g₀ i).val ≠ (g₁ i).val :=
    reserved_two_pairFiber_class C k₀ k₁ U₀ U₁ hcard₀ hcard₁
      hfiber₀ hfiber₁ hdisjoint (R i) (hR i) (g₀ i) (g₁ i)
      (hmem₀ i) (hmem₁ i) (hsubset i) (f i) (htrace i)
  have hdefault (k : K) (U : Finset V) (hU : U.card = 2)
      (hfiber : labelShore label {k} = U)
      (hregular : ∀ v ∈ U, G.degree v = h) :
      Nonempty (G.internalOn univ U → Fin h) := by
    obtain ⟨x, y, _hxy, hxyU⟩ := card_eq_two.mp hU
    have hpairfiber : labelShore label {k} = {x,y} := hfiber.trans hxyU
    have hxU : x ∈ U := by rw [hxyU]; exact mem_insert_self _ _
    have hcard : Fintype.card (G.internalOn univ U) =
        Fintype.card (C.freeColors x) := by
      calc
        _ = (pairFiberCopies G x y).card := by
          simp only [Fintype.card_coe, pairFiberCopies, hxyU]
        _ = (C.freeColors x).card :=
          C.pair_freeColors_card k x y hpairfiber (hregular x hxU)
        _ = _ := (Fintype.card_coe _).symm
    let u : G.internalOn univ U ≃ C.freeColors x := Fintype.equivOfCardEq hcard
    exact ⟨fun e => (u e).val⟩
  obtain ⟨default₀⟩ := hdefault k₀ U₀ hcard₀ hfiber₀ hregular₀
  obtain ⟨default₁⟩ := hdefault k₁ U₁ hcard₁ hfiber₁ hregular₁
  let seed₀ : G.internalOn univ U₀ → Fin h := Function.extend g₀ f default₀
  let seed₁ : G.internalOn univ U₁ → Fin h := Function.extend g₁ f default₁
  have hseed₀ (i : I) : seed₀ (g₀ i) = f i := hg₀.extend_apply f default₀ i
  have hseed₁ (i : I) : seed₁ (g₁ i) = f i := hg₁.extend_apply f default₁ i
  let S₀ : Finset (G.internalOn univ U₀) := univ.image g₀
  let S₁ : Finset (G.internalOn univ U₁) := univ.image g₁
  have hfree₀ : ∀ e ∈ S₀, ∀ v ∈ U₀,
      v ∉ G.edgeSupport (C.classes (seed₀ e)) := by
    intro e he
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    rw [hseed₀]
    intro v hv
    exact (hRinfo i).2.1 v (mem_union_left _ hv)
  have hfree₁ : ∀ e ∈ S₁, ∀ v ∈ U₁,
      v ∉ G.edgeSupport (C.classes (seed₁ e)) := by
    intro e he
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    rw [hseed₁]
    intro v hv
    exact (hRinfo i).2.1 v (mem_union_right _ hv)
  have hinj₀ : Set.InjOn seed₀ S₀ := by
    intro e he e' he' heq
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    obtain ⟨j, _, rfl⟩ := mem_image.mp he'
    rw [hseed₀, hseed₀] at heq
    exact congrArg g₀ (hf heq)
  have hinj₁ : Set.InjOn seed₁ S₁ := by
    intro e he e' he' heq
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    obtain ⟨j, _, rfl⟩ := mem_image.mp he'
    rw [hseed₁, hseed₁] at heq
    exact congrArg g₁ (hf heq)
  obtain ⟨B, hB₀, hB₁⟩ := C.exists_two_pairFiber_completion k₀ k₁ hk U₀ U₁
    hcard₀ hcard₁ hfiber₀ hfiber₁ hp₀ hp₁ hregular₀ hregular₁
    S₀ S₁ seed₀ seed₁ hfree₀ hfree₁ hinj₀ hinj₁
  have hcolor₀ (i : I) : B.first.color (g₀ i) = f i :=
    (hB₀ (g₀ i) (mem_image_of_mem g₀ (mem_univ i))).trans (hseed₀ i)
  have hcolor₁ (i : I) : B.second.color (g₁ i) = f i :=
    (hB₁ (g₁ i) (mem_image_of_mem g₁ (mem_univ i))).trans (hseed₁ i)
  refine ⟨B, hcolor₀, hcolor₁, ?_⟩
  intro i
  exact (B.class_of_two_copies (g₀ i) (g₁ i) (f i) (hcolor₀ i) (hcolor₁ i)).trans
    (hRinfo i).1.symm

end Overfull.NativeAssembly
