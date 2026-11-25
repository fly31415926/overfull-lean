import Overfull.ResidualPalette.FourReservedPrimary
import Overfull.ResidualPalette.FourTwoOddGrouping

/-!
# Four-label joining palettes with exact protected traces

All-even fibers admit an injectively indexed family of empty protected
classes.  With two odd fibers, selected original direct crossing copies
are forced into singleton primary pieces and remain entire color classes.
The palette and protected colors are constructed from the actual host.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]

/-- Add genuinely empty colors to an even-cut palette, retaining every old
class, every original joining copy, and the original incidence bounds. -/
theorem JoiningPalette.exists_empty_extension {G : Multigraph V E} {label : V → K}
    {m D L : ℕ} (C : JoiningPalette G label m D L (fun _ => 0)) (r : ℕ) :
    ∃ C' : JoiningPalette G label (m+r) D L (fun _ => 0),
      ∃ f : Fin r → Fin (m+r), Function.Injective f ∧
        ∀ i, C'.classes (f i) = ∅ := by
  let B : Fin (m+r) → Finset E := fun j =>
    if hj : j.val < m then C.classes ⟨j.val,hj⟩ else ∅
  let g : Fin m → Fin (m+r) := fun j => ⟨j.val,by omega⟩
  have hBg (j : Fin m) : B (g j) = C.classes j := by
    simp only [B,g,dif_pos j.isLt]
  have hmatching : ∀ j, G.IsMatching (B j) := by
    intro j
    dsimp only [B]
    split_ifs with hj
    · exact C.matching _
    · intro e he
      simp at he
  have hdisjoint : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    dsimp only [B]
    split_ifs with hi hj
    · apply C.disjoint
      intro heq
      exact hij (Fin.ext (congrArg (fun x : Fin m => x.val) heq))
    all_goals simp
  have hcover : univ.biUnion B = joiningCopies G label := by
    rw [← C.cover]
    ext e
    simp only [mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      dsimp only [B] at hj
      split_ifs at hj with hlt
      · exact ⟨⟨j.val,hlt⟩,hj⟩
      · simp at hj
    · rintro ⟨j,hj⟩
      exact ⟨g j,by simpa only [hBg] using hj⟩
  have hparity : ∀ j i, (G.cutOn (B j) (labelShore label {i})).card % 2 = 0 := by
    intro j i
    dsimp only [B]
    split_ifs with hj
    · exact C.cut_parity _ i
    · simp [Multigraph.cutOn]
  have hcard : ∀ j, (B j).card ≤ 3*L := by
    intro j
    dsimp only [B]
    split_ifs with hj
    · exact C.card_le _
    · simp
  have hsupport : ∀ j, (G.edgeSupport (B j)).card ≤ 6*L := by
    intro j
    dsimp only [B]
    split_ifs with hj
    · exact C.support_card_le _
    · simp [Multigraph.edgeSupport]
  have hload : ∀ v, (univ.filter (fun j => v ∈ G.edgeSupport (B j))).card ≤ D := by
    intro v
    have hsub : univ.filter (fun j => v ∈ G.edgeSupport (B j)) ⊆
        (univ.filter (fun j => v ∈ G.edgeSupport (C.classes j))).image g := by
      intro j hj
      have hv := (mem_filter.mp hj).2
      by_cases hlt : j.val < m
      · refine mem_image.mpr ⟨⟨j.val,hlt⟩,?_,rfl⟩
        exact mem_filter.mpr ⟨mem_univ _,by simpa only [B,dif_pos hlt] using hv⟩
      · simp only [B,dif_neg hlt] at hv
        simp [Multigraph.edgeSupport] at hv
    exact (card_le_card hsub).trans ((card_image_le).trans (C.vertex_load_le v))
  let C' : JoiningPalette G label (m+r) D L (fun _ => 0) := {
    classes := B
    matching := hmatching
    disjoint := hdisjoint
    cover := hcover
    cut_parity := hparity
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := hload
  }
  let f : Fin r → Fin (m+r) := fun i => ⟨m+i.val,by omega⟩
  refine ⟨C',f,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    dsimp only [f] at hh
    omega
  · intro i
    change B (f i) = ∅
    simp only [B,f,dif_neg (by omega : ¬ m+i.val < m)]

/-- Group the actual all-even four-label decomposition using the remaining
colors, then construct distinct empty protected classes. -/
theorem FourJoiningDecomposition.exists_palette_with_reserved_empty
    (G : Multigraph V E) (label : V → K) (P : FourJoiningDecomposition G label)
    {h D L r : ℕ} (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hmargin : 8*D+r < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D-r)) :
    ∃ C : JoiningPalette G label h D (2*L) (fun _ => 0),
      ∃ f : Fin r → Fin h, Function.Injective f ∧ ∀ i, C.classes (f i) = ∅ := by
  have hsub : h-r-8*D = h-8*D-r := by omega
  obtain ⟨C⟩ := P.exists_palette G label (h := h-r) hdegree hL (by omega)
    (by simpa only [hsub] using hbudget)
  have ht : h-r+r = h := by omega
  rw [← ht]
  exact C.exists_empty_extension r

/-- Actual distinct selected crossings determine exact singleton protected
classes.  The decomposition, palette, and injective protected-color map are
all constructed; no primary-piece or class-trace hypothesis is assumed. -/
theorem exists_four_protected_singleton_palette
    [Fintype K] (G : Multigraph V E) (label : V → K)
    (a b : K) (hab : a ≠ b) (h D L r : ℕ) (hK : Fintype.card K ≤ 4)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v=i)).card % 2 =
      if i=a ∨ i=b then 1 else 0)
    (q : Fin r → joiningCopies G label) (hq : Function.Injective q)
    (hpair : ∀ i, (joiningQuotient G label).edge (q i) = s(a,b))
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hmargin : 8*D+r < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D-r)) :
    ∃ C : JoiningPalette G label h D (2*L) (fun i => if i=a ∨ i=b then 1 else 0),
      ∃ f : Fin r → Fin h, Function.Injective f ∧ ∀ i, C.classes (f i) = {(q i).val} := by
  let A := univ.image q
  have hAcard : A.card = r := by
    rw [card_image_of_injective _ hq,card_univ,Fintype.card_fin]
  have hA : A.card ≤ h := by rw [hAcard]; omega
  have hD : D ≤ h-A.card := by rw [hAcard]; omega
  have hpairA : ∀ e ∈ A, (joiningQuotient G label).edge e = s(a,b) := by
    intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact hpair i
  have hdeg (v : V) : (joiningGraph G label).degree v ≤ D := by
    rw [joiningGraph_degree_eq]
    exact hdegree v
  obtain ⟨P,hforced⟩ := exists_fourTwoOddJoining_decomposition_with_reserved_primary
    G label a b hab h D hK hregular hno hfibers A hpairA hA hdeg hD
  let S := A.image (fun e => ({e.val} : Finset E))
  have hScard : S.card = r := by
    rw [card_image_of_injective]
    · exact hAcard
    · intro e f hef
      exact Subtype.ext (singleton_inj.mp hef)
  have hSP : S ⊆ P.primary := by
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_image.mp hB
    exact hforced e he
  obtain ⟨C,hprotected⟩ := P.exists_protected_palette G label S hSP hdegree hL
    (by simpa only [hScard] using hmargin)
    (by simpa only [hScard] using hbudget)
  have hex : ∀ i : Fin r, ∃ j, C.classes j = {(q i).val} := by
    intro i
    apply hprotected
    exact mem_image.mpr ⟨q i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,rfl⟩
  choose f hf using hex
  refine ⟨C,f,?_,hf⟩
  intro i j hij
  apply hq
  apply Subtype.ext
  exact singleton_inj.mp ((hf i).symm.trans ((congrArg C.classes hij).trans (hf j)))

end Overfull.NativeReserve
