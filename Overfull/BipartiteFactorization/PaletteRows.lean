import Overfull.BipartiteFactorization.Palettes
import Overfull.BalancedColoring
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual palette rows and inherited exceptional colors

A selected palette determines a set of original edge copies. Properness gives
its exact incidence counts, while balanced original classes give equal side
degree sums. The exceptional base inherits a coloring using exactly the
selected number of labels; each remaining row is the actual palette-to-core
incidence set.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {k : ℕ}

/-- The actual original edge copies whose colors lie in the selected palette. -/
def paletteEdges (c : G.EdgeColoring k) (I : Finset (Fin k)) : Finset E :=
  univ.filter (fun e => c.color e ∈ I)

@[simp] theorem mem_paletteEdges (c : G.EdgeColoring k) (I : Finset (Fin k)) (e : E) :
    e ∈ paletteEdges c I ↔ c.color e ∈ I := by
  simp only [paletteEdges, mem_filter, mem_univ, true_and]

/-- The selected palette copies with both ends outside the core. -/
def paletteBase [Fintype V] (c : G.EdgeColoring k) (U : Finset V) (I : Finset (Fin k)) : Finset E :=
  paletteEdges c I ∩ G.internalEdges Uᶜ

theorem paletteBase_subset [Fintype V] (c : G.EdgeColoring k) (U : Finset V) (I : Finset (Fin k)) :
    paletteBase c U I ⊆ paletteEdges c I := inter_subset_left

/-- Compress a palette while retaining a reversible correspondence with its labels. -/
def paletteEquiv (I : Finset (Fin k)) : I ≃ Fin I.card :=
  Finset.equivFinOfCardEq rfl

/-- Every actual subset of the selected palette inherits its proper coloring
with the exact palette cardinality. -/
def compressedPaletteColoring (c : G.EdgeColoring k) (I : Finset (Fin k))
    (F : Finset E) (hF : F ⊆ paletteEdges c I) :
    (G.restrictEdges F).EdgeColoring I.card where
  color e := paletteEquiv I ⟨c.color e.val, (mem_paletteEdges c I e.val).mp (hF e.property)⟩
  proper := by
    intro e f v hef hev hfv
    apply Subtype.ext
    exact c.proper (congrArg Subtype.val ((paletteEquiv I).injective hef)) hev hfv

/-- Restoring a compressed label recovers the actual original color. -/
@[simp] theorem compressedPaletteColoring_restore
    (c : G.EdgeColoring k) (I : Finset (Fin k))
    (F : Finset E) (hF : F ⊆ paletteEdges c I) (e : F) :
    ((paletteEquiv I).symm ((compressedPaletteColoring c I F hF).color e)).val =
      c.color e.val := by
  change ((paletteEquiv I).symm (paletteEquiv I _)).val = _
  rw [Equiv.symm_apply_apply]

/-- The exceptional base has an actual proper coloring with the selected
palette cardinality. -/
theorem paletteBase_colorable [Fintype V] (c : G.EdgeColoring k) (U : Finset V)
    (I : Finset (Fin k)) :
    Nonempty ((G.restrictEdges (paletteBase c U I)).EdgeColoring I.card) :=
  ⟨compressedPaletteColoring c I _ (paletteBase_subset c U I)⟩

/-- At any vertex, palette degree counts exactly its covered selected colors. -/
theorem palette_degree_eq_coveredColors (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (v : V) :
    (G.restrictEdges (paletteEdges c I)).degree v =
      (I.filter (fun i => c.Covers i v)).card := by
  rw [G.restrictEdges_degree]
  have heq : (paletteEdges c I ∩ G.incidenceEdges v).image c.color =
      I.filter (fun i => c.Covers i v) := by
    ext i
    simp only [mem_image, mem_inter, mem_paletteEdges, G.mem_incidenceEdges,
      mem_filter, Multigraph.EdgeColoring.Covers]
    constructor
    · rintro ⟨e, ⟨heI, hev⟩, rfl⟩
      exact ⟨heI, e, rfl, hev⟩
    · rintro ⟨hi, e, hei, hev⟩
      exact ⟨e, ⟨hei ▸ hi, hev⟩, hei⟩
  rw [← heq]
  symm
  apply card_image_of_injOn
  intro e he f hf hef
  exact c.proper hef ((G.mem_incidenceEdges v e).mp (mem_inter.mp he).2)
    ((G.mem_incidenceEdges v f).mp (mem_inter.mp hf).2)

/-- Every selected label occurs once at a vertex of full original degree. -/
theorem palette_degree_of_degree_eq (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (v : V) (hv : G.degree v = k) :
    (G.restrictEdges (paletteEdges c I)).degree v = I.card := by
  rw [palette_degree_eq_coveredColors]
  congr 1
  exact filter_true_of_mem (fun i _ => c.covers_of_degree_eq v hv i)

/-- The exceptional base and the palette-to-core incidences partition an
exceptional vertex's actual selected incidences. -/
theorem paletteBase_degree_add_core [Fintype V] (c : G.EdgeColoring k)
    (U : Finset V) (I : Finset (Fin k)) (x : V) (hx : x ∉ U) :
    (G.restrictEdges (paletteBase c U I)).degree x +
      (paletteEdges c I ∩ G.edgesTo x U).card =
        (G.restrictEdges (paletteEdges c I)).degree x := by
  have hbase : paletteBase c U I ∩ G.incidenceEdges x =
      paletteEdges c I ∩ G.edgesTo x Uᶜ := by
    ext e
    simp only [paletteBase, mem_inter, G.mem_incidenceEdges, G.mem_edgesTo]
    constructor
    · rintro ⟨⟨heI, heZ⟩, hxe⟩
      exact ⟨heI, hxe,
        ((G.internalEdges_iff_of_edge e x _ (G.edge_eq_otherEnd x e hxe) Uᶜ).mp heZ).2⟩
    · rintro ⟨heI, hxe, heZ⟩
      exact ⟨⟨heI, (G.internalEdges_iff_of_edge e x _
        (G.edge_eq_otherEnd x e hxe) Uᶜ).mpr ⟨mem_compl.mpr hx, heZ⟩⟩, hxe⟩
  rw [G.restrictEdges_degree, hbase]
  have h := (G.restrictEdges (paletteEdges c I)).edgesTo_compl_card_add x U
  simpa only [G.restrictEdges_edgesTo_card] using h

/-- The row demand is exactly the number of actual palette-colored copies
from the exceptional vertex into the core. -/
theorem palette_row_eq [Fintype V] (c : G.EdgeColoring k) (U : Finset V)
    (I : Finset (Fin k)) (x : V) (hx : x ∉ U) (hdegree : G.degree x = k) :
    I.card - (G.restrictEdges (paletteBase c U I)).degree x =
      (paletteEdges c I ∩ G.edgesTo x U).card := by
  have h := paletteBase_degree_add_core c U I x hx
  rw [palette_degree_of_degree_eq c I x hdegree] at h
  omega

/-- Allowed palettes contain no actual core incidence at a low vertex. -/
theorem palette_low_core_empty (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) (I : Finset (Fin k))
    (hI : I ⊆ allowedColors c U L P Q b) (x : V) (hx : x ∈ L) :
    paletteEdges c I ∩ G.edgesTo x U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heI, heU⟩ := mem_inter.mp he
  exact low_core_color_excluded c U L P Q b x hx e heU
    (hI ((mem_paletteEdges c I e).mp heI))

theorem palette_low_row_zero [Fintype V] (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) (I : Finset (Fin k))
    (hI : I ⊆ allowedColors c U L P Q b) (x : V)
    (hxL : x ∈ L) (hx : x ∉ U) (hdegree : G.degree x = k) :
    I.card - (G.restrictEdges (paletteBase c U I)).degree x = 0 := by
  rw [palette_row_eq c U I x hx hdegree,
    palette_low_core_empty c U L P Q b I hI x hxL, card_empty]

variable [Fintype V]

/-- Palette degree sums are the sum of the original selected coverage counts. -/
theorem palette_sum_degrees (c : G.EdgeColoring k) (I : Finset (Fin k))
    (X : Finset V) :
    (∑ v ∈ X, ((G.restrictEdges (paletteEdges c I)).degree v : ℤ)) =
      ∑ i ∈ I, c.coveredCount X i := by
  simp only [Multigraph.EdgeColoring.coveredCount_eq_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [palette_degree_eq_coveredColors]
  simp only [Multigraph.EdgeColoring.coverIndicator, sum_boole]

/-- Balance of the actual selected color classes gives equality of the
actual side-degree sums of their edge-copy restriction. -/
theorem palette_side_degree_eq (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B : Finset V) (hbalanced : ∀ i ∈ I, c.coveredCount A i = c.coveredCount B i) :
    (∑ v ∈ A, (G.restrictEdges (paletteEdges c I)).degree v) =
      ∑ v ∈ B, (G.restrictEdges (paletteEdges c I)).degree v := by
  have h : (∑ v ∈ A, ((G.restrictEdges (paletteEdges c I)).degree v : ℤ)) =
      ∑ v ∈ B, ((G.restrictEdges (paletteEdges c I)).degree v : ℤ) := by
    rw [palette_sum_degrees, palette_sum_degrees]
    exact sum_congr rfl hbalanced
  exact_mod_cast h

end Overfull.BipartiteFactorization
