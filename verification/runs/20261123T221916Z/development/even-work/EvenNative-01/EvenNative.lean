import Overfull.ExceptionalPalette.EvenColors
import Overfull.ExceptionalPalette.ReserveInsertion

/-!
# Actual native reserve colors for all-even assigned parts

Half the original reserve boundaries are assigned distinct protected empty
joining colors, then inserted as entire surviving boundaries. No selection
or coloring is assumed: the reserve indices and their colors are constructed.
The protected classes cover all exceptions and have even uncovered old cores.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]

/-- In the all-even native case, construct `r/2` empty joining colors and
extend each to a distinct whole original reserve boundary. The final family
retains the original joining-copy coloring and inserts exactly those chosen
internal copies. Other exceptional incidences and core completion remain open. -/
theorem exists_native_even_reserved_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (heven : (corePart G M Z U₀).card % 2 = 0)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h D L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (hL : 0 < L) (hmargin : 6*D+r/2 < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-r/2)) :
    ∃ (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun _ => 0))
      (q : Fin (r/2) → Fin r) (f : Fin (r/2) → Fin h),
      Function.Injective q ∧ Function.Injective f ∧
      (∀ i, C.classes (f i) = ∅) ∧
      ∃ P : ReserveExtension C (fun i => Q.residualBoundary N T (q i)) f (Z.card+1),
        (∀ i, Z ⊆ (residualGraph G N T).edgeSupport (P.classes (f i))) ∧
        (∀ i,
          Even (U₀ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card ∧
          Even (U₁ \ (residualGraph G N T).edgeSupport (P.classes (f i))).card) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  have hfibers : ∀ i, (univ.filter (fun v => label v=i)).card % 2 = 0 := by
    intro i
    have hh := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z h01 h0Z h1Z hcover i
    rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover,heven] at hh
    simpa only [ite_self] using hh
  have hsmall : r/2 < h := by omega
  let q : Fin (r/2) → Fin r :=
    fun i => ⟨i.val,lt_of_lt_of_le i.isLt (Nat.div_le_self r 2)⟩
  let f : Fin (r/2) → Fin h := fun i => ⟨i.val,lt_trans i.isLt hsmall⟩
  have hq : Function.Injective q := by
    intro i j hij
    exact Fin.ext (congrArg Fin.val hij)
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg Fin.val hij)
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
  obtain ⟨C,hC⟩ := P₀.exists_palette_avoiding_colors H label A hdegreeOn hL
    (by rw [hAcard]; exact hmargin) (by rw [hAcard]; exact hbudget)
  have hCempty (i : Fin (r/2)) : C.classes (f i) = ∅ := hC _ (hfA i)
  have htrace (i : Fin (r/2)) : Q.residualBoundary N T (q i) ∩
      joiningCopies H label = C.classes (f i) := by
    rw [hCempty i]
    exact Q.residualBoundary_joining_empty hM h01 h0Z h1Z hcover hZ heven N T (q i)
  let B : Fin (r/2) → Finset {e : E // e ∉ removedCopies N T} :=
    fun i => Q.residualBoundary N T (q i)
  have hBm : ∀ i, H.IsMatching (B i) :=
    fun i => Q.residualBoundary_matching N T (q i)
  have hBd : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    exact Q.residualBoundary_disjoint N T (fun heq => hij (hq heq))
  have hBcard (i : Fin (r/2)) : (B i).card ≤ Z.card+1 :=
    Q.residualBoundary_card_le N T havoid (q i)
  let P := reserveExtension C B f hf hBm hBd
    (by
      intro i
      ext z
      simpa only [B,mem_inter] using (Finset.ext_iff.mp (htrace i) z)) hBcard
  refine ⟨C,q,f,hq,hf,hCempty,P,?_,?_⟩
  · intro i
    rw [P.prescribed]
    exact Q.residualBoundary_covers_exceptional N T havoid (q i)
  · intro i
    rw [P.prescribed]
    exact Q.residualBoundary_uncovered_even N T havoid h01 h0Z h1Z hcover (q i)

end Overfull.NativeReserve
