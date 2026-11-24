import Overfull.NativeWeighted.NativePalette
import Overfull.NativeCore.Coverage
import Overfull.NativeCore.WeightedBudget

/-!
# Weighted native palettes from the actual old-core deficits

The integer joining bound and both exceptional multiplicity resources are
derived from the same two embedded cores of the actual residual graph.
The capacity is chosen by a natural quotient.  The resulting weighted
palette and prescribed reserve extension therefore have the numerical
bounds needed for actual star insertion and bounded core completion.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette NativeCore

variable {V E J : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- A weight controlling both original cores controls either assigned
core, for any exceptional signature. -/
theorem assigned_core_weight_le_union (H : Multigraph V E) (z : V)
    (U₀ U₁ : Finset V) (i : Fin 2) (B : Finset E) :
    starWeight H z (if i = 0 then U₀ else U₁) B ≤
      starWeight H z (U₀ ∪ U₁) B := by
  split_ifs
  · exact starWeight_mono_core H z U₀ (U₀ ∪ U₁) subset_union_left B
  · exact starWeight_mono_core H z U₁ (U₀ ∪ U₁) subset_union_right B

/-- Construct a quantitatively bounded weighted reserve palette from
the native regular residual and its two actual near-regular old cores.
Neither a star weight bound nor a parallel-copy bound is an input.
The two weighted resources are the actual exceptional vertices. -/
theorem exists_native_palette_from_core_bounds
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
    (C₀ : SmallCuts.Core (residualGraph G N T) U₀)
    (C₁ : SmallCuts.Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ))
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < Fintype.card V)
    (hdensity : α * Fintype.card V / 30 ≤ h)
    (herror : max a ((h : ℝ)-r) ≤ δ * Fintype.card V)
    (hδ : δ ≤ α/3840) (hδε : δ ≤ ε*α/720)
    (hlarge : 20/ε ≤ Fintype.card V) :
    ∃ D L : ℕ,
      D = ⌊max a ((h : ℝ)-r)⌋₊ ∧
      L = (Fintype.card V * D/2)/(h-r/2-32*D)+1 ∧
      0 < L ∧ 128*D ≤ h ∧ h-r ≤ D ∧
      (D : ℝ) ≤ δ * Fintype.card V ∧
      ((6*L+4 : ℕ) : ℝ) ≤ ε * Fintype.card V ∧
      (∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁,
        ((residualGraph G N T).parallelEdges z v).card ≤ D) ∧
      ∃ (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
          h D L (fun i => (univ.filter
            (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2))
        (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h),
        Function.Injective q ∧ Function.Injective f ∧
        (∀ (z : Z) j, starWeight (residualGraph G N T) z.val (U₀ ∪ U₁)
          (C.classes j) ≤ h/8) ∧
        (∀ i, Q.residualBoundary N T (q i) ∩
          joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) =
            C.classes (f i)) ∧
        ∃ P : ReserveExtension C (fun i => Q.residualBoundary N T (q i)) f (Z.card+1),
          (∀ i, Z ⊆ (residualGraph G N T).edgeSupport (P.classes (f i))) ∧
          (∀ i,
            Even (U₀ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card ∧
            Even (U₁ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card) ∧
          (∀ j, ((residualGraph G N T).edgeSupport (P.classes j)).card ≤ 6*L) := by
  let H := residualGraph G N T
  let A := max a ((h : ℝ)-r)
  let D := ⌊A⌋₊
  let n := Fintype.card V
  let L := (n*D/2)/(h-r/2-32*D)+1
  have hsub : (0 : ℝ) ≤ (h : ℝ)-r := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr hrh)
  have hA : 0 ≤ A := hsub.trans (le_max_right _ _)
  have hDreal : (D : ℝ) ≤ δ*n := (Nat.floor_le hA).trans herror
  have hhalf : 2*(r/2) ≤ h := by
    have hh := Nat.div_mul_le_self r 2
    omega
  obtain ⟨hL,hDh,_hmargin,hbudget,hsupport⟩ :=
    uniform_weighted_palette_budget α δ ε n h D (r/2)
      hα hε hn hdensity hDreal hδ hhalf hδε hlarge
  have hh : 0 < h := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp := mul_pos hα hnR
    have hhR : (0 : ℝ) < h := by nlinarith only [hdensity,hp]
    exact_mod_cast hhR
  have herr : h-r ≤ D := by
    apply Nat.le_floor
    rw [Nat.cast_sub hrh]
    exact le_max_right _ _
  have hjoin : ∀ v, (joiningGraph H (assignedLabel G M U₀ U₁ Z)).degree v ≤ D := by
    have hj := (native_residual_joining_degree_bounds G U₀ U₁ Z hM h01 h0Z h1Z
      hcover hZ r Q N T havoid h a hrh hregular C₀ C₁ hcore₀ hcore₁).2.2.2
    exact fun v => Nat.le_floor (hj v)
  have hparallel : ∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁,
      (H.parallelEdges z v).card ≤ D :=
    native_exception_parallel_bounds H U₀ U₁ Z C₀ C₁ h0Z h1Z h r a
      hregular hcore₀ hcore₁
  have hresources : Fintype.card Z ≤ 2 := by simpa only [Fintype.card_coe] using hZ
  obtain ⟨C,q,f,hq,hf,hweight,htrace,P,hcoverP,hparityP⟩ :=
    exists_native_weighted_reserved_palette G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
      r Q N T havoid h D D L hregular hno hjoin
      (fun z : Z => z.val) (fun _ : Z => U₀ ∪ U₁) hresources
      (fun z v hv => hparallel z.val z.property v hv)
      le_rfl hh hDh hrh hL hbudget
  refine ⟨D,L,rfl,rfl,hL,hDh,herr,hDreal,hsupport,hparallel,
    C,q,f,hq,hf,hweight,htrace,P,hcoverP,hparityP,?_⟩
  intro j
  have hmax : max (3*L) (Z.card+1) = 3*L := max_eq_left (by omega)
  have hs := P.support_card_le j
  rw [hmax] at hs
  omega

end Overfull.NativeWeighted
