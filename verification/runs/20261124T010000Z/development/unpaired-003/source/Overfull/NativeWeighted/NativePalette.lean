import Overfull.NativeWeighted.OddNative
import Overfull.NativeWeighted.EvenNative

/-!
# A uniform native weighted reserve palette

Both assigned-core parities produce the same concrete interface: a joining
palette with the actual assigned-fiber parity, at most two bounded star
resources, and `r/2` injectively indexed original reserve boundaries. Their
whole prescribed color classes are constructed with exact joining traces.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette

variable {V E J κ : Type*} [Fintype V] [Fintype E] [Fintype κ]

/-- Construct a native weighted joining palette and the exact half-reserve
extension for either core parity. The reserve indices and colors share
the fixed index type `Fin (r/2)`, and cut parity is stated directly using
the original representative's assigned fibers. -/
theorem exists_native_weighted_reserved_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    (h D b L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (z : κ → V) (U : κ → Finset V) (hresources : Fintype.card κ ≤ 2)
    (hparallel : ∀ i, ∀ v ∈ U i,
      ((residualGraph G N T).parallelEdges (z i) v).card ≤ b)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hrh : r ≤ h) (hL : 0 < L)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - r/2 - 32 * D)) :
    ∃ (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun i => (univ.filter
          (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2))
      (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h),
      Function.Injective q ∧ Function.Injective f ∧
      (∀ i j, starWeight (residualGraph G N T) (z i) (U i) (C.classes j) ≤ h/8) ∧
      (∀ i, R.residualBoundary N T (q i) ∩
        joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f i)) ∧
      ∃ P : ReserveExtension C (fun i => R.residualBoundary N T (q i)) f (Z.card+1),
        (∀ i, Z ⊆ (residualGraph G N T).edgeSupport (P.classes (f i))) ∧
        (∀ i,
          Even (U₀ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card ∧
          Even (U₁ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let p : Fin 3 → ℕ := fun i => (univ.filter (fun v => label v=i)).card % 2
  have hex : ∃ (C : JoiningPalette H label h D L p)
      (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h),
      Function.Injective q ∧ Function.Injective f ∧
      (∀ i j, starWeight H (z i) (U i) (C.classes j) ≤ h/8) ∧
      (∀ i, R.residualBoundary N T (q i) ∩ joiningCopies H label = C.classes (f i)) := by
    have hparity : (corePart G M Z U₀).card % 2 = 0 ∨
        (corePart G M Z U₀).card % 2 = 1 := by omega
    rcases hparity with heven | hodd
    · obtain ⟨C₀,q,f,hq,hf,_hCempty,hweight,htrace,_⟩ :=
        exists_native_even_weighted_reserved_palette G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
          r R heven N T havoid h D b L hregular hno hdegree z U hresources hparallel
          hbD hh hDh hrh hbudget
      have hfibers (i : Fin 3) : p i = 0 := by
        have hpar := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z
          h01 h0Z h1Z hcover i
        rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover, heven] at hpar
        simpa only [ite_self] using hpar
      let C := C₀.congr_parity (fun i => (hfibers i).symm)
      exact ⟨C,q,f,hq,hf,hweight,htrace⟩
    · obtain ⟨A,C₀,q₀,f₀,hA,hq₀,hf₀,_hsource,_hsingle,hweight,htrace,_⟩ :=
        exists_native_odd_weighted_reserved_palette G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
          r R hodd N T havoid h D b L hregular hno hdegree z U hresources hparallel
          hbD hh hDh hrh hL hbudget
      have hfibers (i : Fin 3) : p i = if i=0 ∨ i=1 then 1 else 0 := by
        have hpar := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z
          h01 h0Z h1Z hcover i
        rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover, hodd] at hpar
        exact hpar
      let C := C₀.congr_parity (fun i => (hfibers i).symm)
      let e : Fin (r/2) ≃ A := (A.equivFinOfCardEq hA).symm
      exact ⟨C,q₀ ∘ e,f₀ ∘ e,hq₀.comp e.injective,hf₀.comp e.injective,
        hweight,fun i => htrace (e i)⟩
  obtain ⟨C,q,f,hq,hf,hweight,htrace⟩ := hex
  let B : Fin (r/2) → Finset {e : E // e ∉ removedCopies N T} :=
    fun i => R.residualBoundary N T (q i)
  have hBm : ∀ i, H.IsMatching (B i) :=
    fun i => R.residualBoundary_matching N T (q i)
  have hBd : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    exact R.residualBoundary_disjoint N T (fun heq => hij (hq heq))
  have hBcard (i : Fin (r/2)) : (B i).card ≤ Z.card+1 :=
    R.residualBoundary_card_le N T havoid (q i)
  let P := reserveExtension C B f hf hBm hBd
    (by
      intro i
      ext v
      simpa only [B,mem_inter] using (Finset.ext_iff.mp (htrace i) v)) hBcard
  refine ⟨C,q,f,hq,hf,hweight,htrace,P,?_,?_⟩
  · intro i
    rw [P.prescribed]
    exact R.residualBoundary_covers_exceptional N T havoid (q i)
  · intro i
    rw [P.prescribed]
    exact R.residualBoundary_uncovered_even N T havoid h01 h0Z h1Z hcover (q i)

end Overfull.NativeWeighted
