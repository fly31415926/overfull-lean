import Overfull.NativeWeighted.CoreBounds
import Overfull.NativeAssembly.Unpaired
import Overfull.NativeAssembly.Paired
import Overfull.NativeCore.Parity

/-!
# A complete native external palette from actual residual core data

All exceptional configurations are constructed in the actual surviving
edge-copy type. The entire external set is partitioned into matching
classes with exact native reserve prescriptions. Saturated exceptions and
unchanged assigned cuts supply parity on the original cores. The true core
deficit bounds the load of the whole family, including protected classes.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette
  NativeWeighted NativeAssembly SmallCuts

variable {V E J I : Type*} [Fintype V] [Fintype E] [Fintype I]

/-- Assemble the paired and all unpaired configurations into one native
construction. The whole family covers exactly the joining and exceptional
copies while retaining each selected original reserve boundary. -/
theorem exists_native_external_completion
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (hp : p 2 = 0) (q : I → Fin r) (f : I → Fin h)
    (hq : Function.Injective q) (hf : Function.Injective f)
    (P : ReserveExtension C (fun i => Q.residualBoundary N T (q i)) f (Z.card+1))
    (hregular : ∀ v, (residualGraph G N T).degree v = h) (herror : h-r ≤ D)
    (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h) (hL : 0 < L)
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
      (∀ i, F (f i) = Q.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j i, H.cutOn (F j) (labelShore label {i}) =
        H.cutOn (C.classes j) (labelShore label {i})) ∧
      (∀ j, (F j).card ≤ 3*L+2) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 6*L+4) ∧
      (∀ j, F j ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z) ∧
      univ.biUnion F = joiningCopies H label ∪ exceptionalCopies H univ Z := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  cases hcode : coarseSignature G M U₀ Z with
  | none =>
      obtain ⟨F,hpres⟩ := exists_native_paired_completion G hM U₀ U₁ Z
        h01 h0Z h1Z hcover hZ hcode r Q N T havoid C hp hregular q f hq hf P
      have hsub (j : Fin h) :
          F.classes j ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z := by
        intro e he
        have hmem := Finset.ext_iff.mp F.cover e
        simp only [mem_biUnion,mem_union] at hmem
        rcases hmem.mp ⟨j,mem_univ _,he⟩ with hj | hz
        · exact mem_union_left _ hj
        · apply mem_union_right
          exact (mem_exceptionalCopies H univ Z e).mpr
            ⟨mem_univ _,Or.inl (mem_filter.mp hz).2.1⟩
      refine ⟨F.classes,F.matching,F.disjoint,F.contains_joining,hpres,F.covers,F.cut_eq,
        fun j => (F.card_le j).trans (by omega),
        fun j => (F.support_card_le j).trans (by omega),hsub,?_⟩
      have hjoining : joiningCopies H label ⊆ univ.biUnion F.classes := by
        intro e he
        have hmem := Finset.ext_iff.mp C.cover e
        simp only [mem_biUnion] at hmem
        obtain ⟨j,_,hj⟩ := hmem.mpr he
        exact mem_biUnion.mpr ⟨j,mem_univ _,F.contains_joining j hj⟩
      have hcov := external_union_eq_of_saturation H label h F.classes Z F.disjoint
        (fun z _ => hregular z) F.covers
        (by intro e he; simpa only [mem_biUnion] using hjoining he)
        (by intro j e he; simpa only [mem_union] using hsub j he)
      ext e
      simpa only [mem_biUnion,mem_union] using Finset.ext_iff.mp hcov e
  | some σ =>
      obtain ⟨F,hm,hd,hC,hpres,hz,hcuts,hcard,hsupport,hsub,hcov⟩ :=
        exists_native_unpaired_completion G hM U₀ U₁ Z h01 h0Z h1Z hcover hZ
          σ hcode r Q N T havoid C q hq f hf P hregular herror hD hs hweight hparallel
      have hmax : max (3*L) (Z.card+1) = 3*L := max_eq_left (by omega)
      refine ⟨F,hm,hd,hC,hpres,hz,hcuts,?_,?_,hsub,hcov⟩
      · intro j
        simpa only [hmax] using hcard j
      · intro j
        have hh := hsupport j
        rw [hmax] at hh
        omega

omit [Fintype I] in
/-- Construct the complete bounded external palette directly from actual
native residual core data. All star weights, multiplicities, exceptional
cases, core parities, and whole-family loads are proved internally. -/
theorem exists_native_external_palette_from_core_bounds
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h : ℕ) (a α δ ε : ℝ) (hrh : r ≤ h)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (C₀ : Core (residualGraph G N T) U₀)
    (C₁ : Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ))
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < Fintype.card V)
    (hdensity : α * Fintype.card V / 30 ≤ h)
    (herror : max a ((h : ℝ)-r) ≤ δ * Fintype.card V)
    (hδ : δ ≤ α/3840) (hδε : δ ≤ ε*α/720)
    (hlarge : 20/ε ≤ Fintype.card V) :
    let H := residualGraph G N T
    let label := assignedLabel G M U₀ U₁ Z
    ∃ (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h)
      (F : Fin h → Finset {e : E // e ∉ removedCopies N T}),
      Function.Injective q ∧ Function.Injective f ∧
      (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      (∀ i, F (f i) = Q.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j, Even (U₀ \ H.edgeSupport (F j)).card ∧
        Even (U₁ \ H.edgeSupport (F j)).card) ∧
      univ.biUnion F = joiningCopies H label ∪ exceptionalCopies H univ Z ∧
      (∀ j, Disjoint (F j) (OneCore.coreEdges C₀)) ∧
      (∀ j, Disjoint (F j) (OneCore.coreEdges C₁)) ∧
      (∀ j, ((H.edgeSupport (F j)).card : ℝ) ≤ ε * Fintype.card V) ∧
      (∀ v : U₀, ((univ.filter (fun j => v.val ∈ H.edgeSupport (F j))).card : ℝ) ≤ a) ∧
      (∀ v : U₁, ((univ.filter (fun j => v.val ∈ H.edgeSupport (F j))).card : ℝ) ≤ a) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  obtain ⟨D,L,_hDdef,_hLdef,hL,hDh,herr,_hDreal,hsupport,hparallel,
      C,q,f,hq,hf,hweight,_htrace,P,_hcoverP,_hparityP,_hsizeP⟩ :=
    exists_native_palette_from_core_bounds G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
      r Q N T havoid h a α δ ε hrh hregular hno C₀ C₁ hcore₀ hcore₁
      hα hε hn hdensity herror hδ hδε hlarge
  have hp : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by
    have hh := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z
      h01 h0Z h1Z hcover 2
    simpa only [show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide,or_self,if_false] using hh
  have hhalf : 2*Fintype.card (Fin (r/2)) ≤ h := by
    rw [Fintype.card_fin]
    have hh := Nat.div_mul_le_self r 2
    omega
  obtain ⟨F,hm,hd,_hC,hpres,hz,hcuts,_hcard,hsize,hsub,hcov⟩ :=
    exists_native_external_completion G hM U₀ U₁ Z h01 h0Z h1Z hcover hZ
      r Q N T havoid C hp q f hq hf P hregular herr hDh hhalf hL hweight hparallel
  have heven := old_core_parity_of_joining_cuts G H hM U₀ U₁ Z
    h01 h0Z h1Z hcover C (fun _ => rfl) F hm hz hcuts
  have hlabel₀ : ∀ v ∈ U₀, label v = 0 :=
    fun _ hv => assignedLabel_on_core₀ G M U₀ U₁ Z hv
  have hlabel₁ : ∀ v ∈ U₁, label v = 1 :=
    fun _ hv => assignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hv
  refine ⟨q,f,F,hq,hf,hm,hd,hpres,hz,heven,hcov,?_,?_,?_,?_,?_⟩
  · intro j
    apply disjoint_left.mpr
    intro e he hc
    exact disjoint_left.mp (joining_exceptional_disjoint_core H label U₀ Z C₀ h0Z 0 hlabel₀)
      (by simpa only [mem_union] using hsub j he) hc
  · intro j
    apply disjoint_left.mpr
    intro e he hc
    exact disjoint_left.mp (joining_exceptional_disjoint_core H label U₁ Z C₁ h1Z 1 hlabel₁)
      (by simpa only [mem_union] using hsub j he) hc
  · exact fun j => (Nat.cast_le.mpr (hsize j)).trans hsupport
  · exact external_family_load_le_error H label U₀ Z C₀ h0Z 0 hlabel₀ h a
      hregular hcore₀ F hd (by intro j e he; simpa only [mem_union] using hsub j he)
  · exact external_family_load_le_error H label U₁ Z C₁ h1Z 1 hlabel₁ h a
      hregular hcore₁ F hd (by intro j e he; simpa only [mem_union] using hsub j he)

end Overfull.NativeCore
