import Overfull.NativeWeighted.WeightedJoining
import Overfull.ExceptionalPalette.EvenNative

/-!
# Native weighted joining colors with even assigned cores

The native even decomposition is grouped directly in the original `h`
colors. Half the reserve indices receive protected empty joining colors;
their exact surviving boundaries are then inserted. The original joining
classes retain both weighted star budgets and all fiber-cut parities.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette

variable {V E J κ : Type*} [Fintype V] [Fintype E] [Fintype κ]

/-- Construct the even native weighted joining palette and inject the
actual half-reserve into its protected empty colors. The original palette
order is retained in every weight threshold. -/
theorem exists_native_even_weighted_reserved_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (heven : (corePart G M Z U₀).card % 2 = 0)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    (h D b L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (z : κ → V) (U : κ → Finset V) (hresources : Fintype.card κ ≤ 2)
    (hparallel : ∀ i, ∀ v ∈ U i,
      ((residualGraph G N T).parallelEdges (z i) v).card ≤ b)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h) (hrh : r ≤ h)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - r/2 - 32 * D)) :
    ∃ (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun _ => 0))
      (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h),
      Function.Injective q ∧ Function.Injective f ∧
      (∀ i, C.classes (f i) = ∅) ∧
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
  have hfibers : ∀ i, (univ.filter (fun v => label v=i)).card % 2 = 0 := by
    intro i
    have hpar := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z
      h01 h0Z h1Z hcover i
    rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover, heven] at hpar
    simpa only [ite_self] using hpar
  have hsmall : r/2 < h := by omega
  let q : Fin (r/2) → Fin r :=
    fun i => ⟨i.val, lt_of_lt_of_le i.isLt (Nat.div_le_self r 2)⟩
  let f : Fin (r/2) → Fin h := fun i => ⟨i.val, lt_trans i.isLt hsmall⟩
  have hq : Function.Injective q := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin r => k.val) hij)
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin h => k.val) hij)
  let A : Finset (Fin h) := univ.image f
  have hAcard : A.card = r/2 := by
    rw [card_image_of_injective _ hf]
    exact Fintype.card_fin (r/2)
  have hfA (i : Fin (r/2)) : f i ∈ A := mem_image_of_mem f (mem_univ i)
  have hdegreeOn (v : V) : H.degreeOn (joiningCopies H label) v ≤ D := by
    rw [← joiningGraph_degree_eq]
    exact hdegree v
  obtain ⟨P₀⟩ := exists_evenJoining_decomposition H label (by decide)
    hregular hno hfibers
  obtain ⟨C,hweight,hC⟩ := P₀.exists_star_weighted_palette H label A z U
    hresources hdegreeOn hparallel (fun i => (hregular (z i)).le) hbD hh hDh
    (by rw [hAcard]; omega) (by rw [hAcard]; exact hbudget)
  have hCempty (i : Fin (r/2)) : C.classes (f i) = ∅ := hC _ (hfA i)
  have htrace (i : Fin (r/2)) : R.residualBoundary N T (q i) ∩
      joiningCopies H label = C.classes (f i) := by
    rw [hCempty i]
    exact R.residualBoundary_joining_empty hM h01 h0Z h1Z hcover hZ heven N T (q i)
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
  refine ⟨C,q,f,hq,hf,hCempty,hweight,htrace,P,?_,?_⟩
  · intro i
    rw [P.prescribed]
    exact R.residualBoundary_covers_exceptional N T havoid (q i)
  · intro i
    rw [P.prescribed]
    exact R.residualBoundary_uncovered_even N T havoid h01 h0Z h1Z hcover (q i)

end Overfull.NativeWeighted
