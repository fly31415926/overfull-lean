import Overfull.BipartiteFactorization.Assembly

/-!
# Palette selection in either correction orientation

The output always uses the original ordered sides and blocks. At most one
correction pool is used, with its actual count given by the corresponding
nonnegative difference of the original palette counts.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- An actual proper coloring together with all balanced localized footprint
properties, for use uniformly across selected families and the residual. -/
structure LocalizedColoring (A B Ablock Bblock : Finset V) (q : ℕ) (a : ℝ) where
  coloring : G.EdgeColoring q
  covers : ∀ i, (A ∪ B)ᶜ ⊆ coloring.coveredVertices i
  balance : ∀ i, (A ∩ coloring.coveredVertices i).card =
    (B ∩ coloring.coveredVertices i).card
  spread : ∀ i j, |((A ∩ coloring.coveredVertices i).card : ℤ) -
    (A ∩ coloring.coveredVertices j).card| ≤ 2
  support : ∀ i, coloring.exteriorFootprint (A ∪ B) i ⊆ Ablock ∪ Bblock
  footprint_bound : ∀ i, ((coloring.exteriorFootprint (A ∪ B) i).card : ℝ) ≤
    2 * Ablock.card * a / q + 4
  footprint_even : ∀ i, Even (coloring.exteriorFootprint (A ∪ B) i).card
  load : ∀ v ∈ A ∪ B,
    (univ.filter (fun i => v ∈ coloring.exteriorFootprint (A ∪ B) i)).card = G.degree v
  load_le : ∀ v ∈ A ∪ B,
    ((univ.filter (fun i => v ∈ coloring.exteriorFootprint (A ∪ B) i)).card : ℝ) ≤ a

/-- A selected palette in the original geometry, allowing either correction
orientation. Both pool counts are exact natural-number differences. -/
structure OrientedPalette {k : ℕ} (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B Ablock Bblock ZA ZB : Finset V) (D : Finset E) where
  copies : Finset E
  avoids : Disjoint copies D
  base : copies ∩ G.internalEdges (A ∪ B)ᶜ = paletteBase c (A ∪ B) I
  rows : ∀ x, x ∉ A ∪ B → (copies ∩ G.edgesTo x (A ∪ B)).card =
    (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card
  exceptional_degree : ∀ x, x ∉ A ∪ B → (G.restrictEdges copies).degree x = I.card
  side_degrees : (∑ v ∈ A, (G.restrictEdges copies).degree v) =
    ∑ v ∈ B, (G.restrictEdges copies).degree v
  support : ∀ v ∈ A ∪ B, v ∉ Ablock ∪ Bblock → (G.restrictEdges copies).degree v = 0
  positive_count : (copies ∩ correctionPool G B ZA).card =
    (paletteEdges c I ∩ correctionPool G B ZA).card -
      (paletteEdges c I ∩ correctionPool G A ZB).card
  negative_count : (copies ∩ correctionPool G A ZB).card =
    (paletteEdges c I ∩ correctionPool G A ZB).card -
      (paletteEdges c I ∩ correctionPool G B ZA).card

/-- Construct selected original copies using whichever correction orientation
has the required finite supplies. The result retains the original side order. -/
theorem exists_oriented_palette {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (A B Ablock Bblock ZA ZB : Finset V)
    (D : Finset E) (ω₁ ω₂ : ℝ)
    (h : PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D ω₁ ω₂ ∨
      PaletteSelectionConditions G c I B A Bblock Ablock ZB ZA D ω₁ ω₂) :
    Nonempty (OrientedPalette G c I A B Ablock Bblock ZA ZB D) := by
  rcases h with h | h
  · obtain ⟨S⟩ := exists_selected_palette G c I A B Ablock Bblock ZA ZB D ω₁ ω₂ h
    refine ⟨{
      copies := S.copies
      avoids := S.avoids
      base := S.base
      rows := S.rows
      exceptional_degree := S.exceptional_degree
      side_degrees := S.side_degrees
      support := S.support
      positive_count := S.positive_count
      negative_count := ?_
    }⟩
    rw [S.negative_empty, Finset.card_empty, Nat.sub_eq_zero_of_le h.orientation]
  · obtain ⟨S⟩ := exists_selected_palette G c I B A Bblock Ablock ZB ZA D ω₁ ω₂ h
    refine ⟨{
      copies := S.copies
      avoids := S.avoids
      base := ?_
      rows := ?_
      exceptional_degree := ?_
      side_degrees := S.side_degrees.symm
      support := ?_
      positive_count := ?_
      negative_count := S.positive_count
    }⟩
    · simpa only [Finset.union_comm B A] using S.base
    · simpa only [Finset.union_comm B A] using S.rows
    · simpa only [Finset.union_comm B A] using S.exceptional_degree
    · simpa only [Finset.union_comm B A, Finset.union_comm Bblock Ablock] using S.support
    · rw [S.negative_empty, Finset.card_empty, Nat.sub_eq_zero_of_le h.orientation]

/-- Color the selected copies in the original side and block geometry.
The inherited exceptional base supplies the inactive coloring; the full
coloring and all balanced localized footprint properties are constructed. -/
theorem OrientedPalette.exists_localized_coloring {k : ℕ}
    {c : G.EdgeColoring k} {I : Finset (Fin k)}
    {A B Ablock Bblock ZA ZB : Finset V} {D : Finset E}
    (S : OrientedPalette G c I A B Ablock Bblock ZA ZB D)
    (a : ℝ) (ha : 0 ≤ a) (hka : 2 * a < I.card)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      paletteEdges c I ∩ G.edgesTo x (A ∪ B) = ∅)
    (hactive : ∀ x ∈ ZA ∪ ZB,
      2 * a < ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hZA : Disjoint ZA (A ∪ B)) (hZB : Disjoint ZB (A ∪ B))
    (hAblock : Ablock ⊆ A) (hBblock : Bblock ⊆ B)
    (hblockcard : Ablock.card = Bblock.card) :
    ∃ d : (G.restrictEdges S.copies).EdgeColoring I.card,
      (∀ i, (A ∪ B)ᶜ ⊆ d.coveredVertices i) ∧
      (∀ i, (A ∩ d.coveredVertices i).card = (B ∩ d.coveredVertices i).card) ∧
      (∀ i j, |((A ∩ d.coveredVertices i).card : ℤ) -
        (A ∩ d.coveredVertices j).card| ≤ 2) ∧
      (∀ i, d.exteriorFootprint (A ∪ B) i ⊆ Ablock ∪ Bblock) ∧
      (∀ i, ((d.exteriorFootprint (A ∪ B) i).card : ℝ) ≤
        2 * Ablock.card * a / I.card + 4) ∧
      (∀ i, Even (d.exteriorFootprint (A ∪ B) i).card) ∧
      (∀ v ∈ A ∪ B,
        (univ.filter (fun i => v ∈ d.exteriorFootprint (A ∪ B) i)).card =
          (G.restrictEdges S.copies).degree v) ∧
      (∀ v ∈ A ∪ B,
        ((univ.filter (fun i => v ∈ d.exteriorFootprint (A ∪ B) i)).card : ℝ) ≤ a) := by
  have hslow (x : V) (hx : x ∉ A ∪ B) (hxZ : x ∉ ZA ∪ ZB) :
      S.copies ∩ G.edgesTo x (A ∪ B) = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [S.rows x hx, hlow x hx hxZ, Finset.card_empty]
  have hinit := color_inactive_from_base G (A ∪ B) (ZA ∪ ZB) S.copies
    (paletteBase c (A ∪ B) I) I.card
    (fun _ he => S.base ▸ he)
    (fun x hx => hslow x (Finset.mem_compl.mp (Finset.mem_sdiff.mp hx).1)
      (Finset.mem_sdiff.mp hx).2)
    (compressedPaletteColoring c I _ (paletteBase_subset c (A ∪ B) I))
  apply exists_balanced_localized_coloring (G.restrictEdges S.copies)
    A B Ablock Bblock (ZA ∪ ZB) I.card a ha hka hAB hcard hZeven
    (fun x hx => S.exceptional_degree x (Finset.mem_compl.mp hx))
    (fun v hv => le_trans (Nat.cast_le.mpr (G.restrictEdges_degree_le _ v)) (hcore v hv))
    S.side_degrees _ hinit hAblock hBblock hblockcard S.support
  intro x hx
  have hxU : x ∉ A ∪ B := by
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact fun hxU => Finset.disjoint_left.mp hZA hxA hxU
    · exact fun hxU => Finset.disjoint_left.mp hZB hxB hxU
  rw [G.restrictEdges_edgesTo_card, S.rows x hxU]
  exact hactive x hx

/-- Package the constructed balanced localized coloring as an actual object
whose footprint properties can be used uniformly for every family member. -/
theorem OrientedPalette.localized_coloring {k : ℕ}
    {c : G.EdgeColoring k} {I : Finset (Fin k)}
    {A B Ablock Bblock ZA ZB : Finset V} {D : Finset E}
    (S : OrientedPalette G c I A B Ablock Bblock ZA ZB D)
    (a : ℝ) (ha : 0 ≤ a) (hka : 2 * a < I.card)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      paletteEdges c I ∩ G.edgesTo x (A ∪ B) = ∅)
    (hactive : ∀ x ∈ ZA ∪ ZB,
      2 * a < ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hZA : Disjoint ZA (A ∪ B)) (hZB : Disjoint ZB (A ∪ B))
    (hAblock : Ablock ⊆ A) (hBblock : Bblock ⊆ B)
    (hblockcard : Ablock.card = Bblock.card) :
    Nonempty (LocalizedColoring (G.restrictEdges S.copies)
      A B Ablock Bblock I.card a) := by
  obtain ⟨d, hcover, hbalance, hspread, hsupport, hbound, heven, hload, hloadle⟩ :=
    S.exists_localized_coloring G a ha hka hAB hcard hZeven hcore hlow hactive
      hZA hZB hAblock hBblock hblockcard
  exact ⟨⟨d, hcover, hbalance, hspread, hsupport, hbound, heven, hload, hloadle⟩⟩

/-- Deleting every original copy incident with a forbidden vertex set makes
all actual color footprints avoid that set. No additional coloring hypothesis
is needed beyond the supplied localized coloring. -/
theorem LocalizedColoring.footprint_avoids
    {A B Ablock Bblock : Finset V} {q : ℕ} {a : ℝ}
    {F D : Finset E}
    (d : LocalizedColoring (G.restrictEdges F) A B Ablock Bblock q a)
    (hFD : Disjoint F D) (W : Finset V)
    (hW : ∀ v ∈ W, G.incidenceEdges v ⊆ D) (i : Fin q) :
    Disjoint (d.coloring.exteriorFootprint (A ∪ B) i) W := by
  apply Finset.disjoint_left.mpr
  intro v hv hvW
  obtain ⟨_, e, _, hve⟩ := (d.coloring.mem_exteriorFootprint (A ∪ B) i v).mp hv
  have heD := hW v hvW ((G.mem_incidenceEdges v e.val).mpr hve)
  exact Finset.disjoint_left.mp hFD e.property heD

end Overfull.BipartiteFactorization
