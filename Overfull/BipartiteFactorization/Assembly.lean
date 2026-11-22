import Overfull.BipartiteFactorization.Coloring
import Overfull.BipartiteFactorization.PaletteRows
import Overfull.BipartiteFactorization.Imbalance
import Overfull.BipartiteFactorization.Selection

/-!
# Assembling a selected palette graph and its localized coloring

The selected graph retains original edge copies. Its initial coloring is
transported from the actual exceptional base, and the fan criterion then
constructs the coloring of every selected copy.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- The inactive residue of a selected graph inherits an actual coloring
from its exceptional base when every inactive vertex has no core copies. -/
theorem color_inactive_from_base (U Zplus : Finset V) (F R0 : Finset E) (k : ℕ)
    (hbase : F ∩ G.internalEdges Uᶜ ⊆ R0)
    (hlow : ∀ x ∈ Uᶜ \ Zplus, F ∩ G.edgesTo x U = ∅)
    (c0 : (G.restrictEdges R0).EdgeColoring k) :
    Nonempty (((G.restrictEdges F).restrictEdges
      (inactiveExterior (G.restrictEdges F) U Zplus)).EdgeColoring k) := by
  classical
  have hmem (e : inactiveExterior (G.restrictEdges F) U Zplus) :
      e.val.val ∈ R0 := by
    have horig : e.val.val ∈ inactiveExterior G U Zplus := by
      apply (mem_inactiveExterior G U Zplus e.val.val).mpr
      have he := (mem_inactiveExterior (G.restrictEdges F) U Zplus e.val).mp e.property
      simpa only [Multigraph.mem_internalEdges, Multigraph.mem_edgesTo] using he
    rw [inactiveExterior_eq] at horig
    rcases Finset.mem_union.mp horig with he | he
    · apply hbase
      exact Finset.mem_inter.mpr ⟨e.val.property, he⟩
    · obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
      have he' : e.val.val ∈ F ∩ G.edgesTo x U := by
        exact Finset.mem_inter.mpr ⟨e.val.property, he⟩
      rw [hlow x hx] at he'
      exact False.elim (Finset.notMem_empty _ he')
  let lift : inactiveExterior (G.restrictEdges F) U Zplus → R0 :=
    fun e => ⟨e.val.val, hmem e⟩
  refine ⟨⟨fun e => c0.color (lift e), ?_⟩⟩
  intro e f v hef hev hfv
  have heq := c0.proper hef hev hfv
  have h : e.val.val = f.val.val := congrArg (fun a : R0 => a.val) heq
  exact Subtype.ext (Subtype.ext h)

/-- An actual selected palette graph, with its exact base and row counts.
The positive correction count records the precise use of that pool. -/
structure SelectedPalette {k : ℕ} (c : G.EdgeColoring k) (I : Finset (Fin k))
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
  negative_empty : copies ∩ correctionPool G A ZB = ∅

/-- Finite conditions on the input palette and unused pools. The inequalities
are supplied before any selected graph or its coloring is constructed. -/
structure PaletteSelectionConditions {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (A B Ablock Bblock ZA ZB : Finset V)
    (D : Finset E) (ω₁ ω₂ : ℝ) : Prop where
  sides : Disjoint A B
  active_left : Disjoint ZA (A ∪ B)
  active_right : Disjoint ZB (A ∪ B)
  active_disjoint : Disjoint ZA ZB
  left_block : Ablock ⊆ A
  right_block : Bblock ⊆ B
  full_degree : ∀ x, x ∉ A ∪ B → G.degree x = k
  balanced : ∀ i ∈ I, c.coveredCount A i = c.coveredCount B i
  low : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
    paletteEdges c I ∩ G.edgesTo x (A ∪ B) = ∅
  base_avoids : Disjoint (paletteBase c (A ∪ B) I) D
  orientation : (paletteEdges c I ∩ correctionPool G A ZB).card ≤
    (paletteEdges c I ∩ correctionPool G B ZA).card
  left_supply : ∀ x ∈ ZA, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
    (G.edgesTo x Ablock \ D).card
  right_supply : ∀ x ∈ ZB, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
    (G.edgesTo x Bblock \ D).card
  weight_nonnegative : 0 ≤ ω₁
  weights_ordered : ω₁ ≤ ω₂
  weight_at_most_one : ω₂ ≤ 1
  score : (((paletteEdges c I ∩ correctionPool G B ZA).card -
      (paletteEdges c I ∩ correctionPool G A ZB).card : ℕ) : ℝ) ≤
    ω₂ * (G.internalEdges Bblock).card +
      (∑ x : ZA, min (ω₁ * (G.edgesTo x.val Bblock).card)
        ((paletteEdges c I ∩ G.edgesTo x.val (A ∪ B)).card : ℝ)) -
      ω₂ * (D ∩ correctionPool G Bblock ZA).card

omit [Fintype V] in
theorem correctionPool_eq_subtype (B Z : Finset V) :
    correctionPool G B Z = G.internalEdges B ∪
      univ.biUnion (fun x : Z => G.edgesTo x.val B) := by
  ext e
  simp only [correctionPool, betweenCopies, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Subtype.exists, exists_prop]

/-- Construct the actual selected graph from palette balance, a surviving
correction score, and unused preferred row supplies. -/
theorem exists_selected_palette {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (A B Ablock Bblock ZA ZB : Finset V)
    (D : Finset E) (ω₁ ω₂ : ℝ)
    (h : PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D ω₁ ω₂) :
    Nonempty (SelectedPalette G c I A B Ablock Bblock ZA ZB D) := by
  let r := fun x => (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card
  let t := (paletteEdges c I ∩ correctionPool G B ZA).card -
    (paletteEdges c I ∩ correctionPool G A ZB).card
  have hBZ : Disjoint Bblock ZA := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxA
    exact Finset.disjoint_left.mp h.active_left hxA
      (Finset.mem_union_right _ (h.right_block hxB))
  have hscore : (t : ℝ) ≤ ω₂ * (G.internalEdges Bblock).card +
      (∑ x : ZA, min (ω₁ * (G.edgesTo x.val Bblock).card) (r x.val : ℝ)) -
      ω₂ * (D ∩ (G.internalEdges Bblock ∪
        univ.biUnion (fun x : ZA => G.edgesTo x.val Bblock))).card := by
    simpa only [t, r, correctionPool_eq_subtype] using h.score
  obtain ⟨C, hC, hCD, hCt, hcap⟩ :=
    exists_graph_correction_subset_after_pool_deletion G Bblock ZA hBZ
      (fun x => r x.val) ω₁ ω₂ h.weight_nonnegative h.weights_ordered
      h.weight_at_most_one D t hscore
  have hC' : C ⊆ G.internalEdges Bblock ∪ ZA.biUnion (fun x => G.edgesTo x Bblock) := by
    change C ⊆ correctionPool G Bblock ZA
    rw [correctionPool_eq_subtype]
    exact hC
  have hzero (x : V) (hx : x ∉ A ∪ B) (hxZ : x ∉ ZA ∪ ZB) : r x = 0 := by
    dsimp only [r]
    rw [h.low x hx hxZ, Finset.card_empty]
  obtain ⟨F, _hbaseF, _hCF, _hFsub, hFD, hdegree, hrows, hsupport, hbase,
      hplus, hminus⟩ := exists_preferred_selected_graph G A B ZA ZB Ablock Bblock
    h.sides h.active_left h.active_right h.active_disjoint h.left_block h.right_block
    (paletteBase c (A ∪ B) I) C D r Finset.inter_subset_right hC' hCD
    (fun x hx => hcap ⟨x, hx⟩) hzero
    (fun x hx => (Nat.sub_le _ _).trans (h.left_supply x hx)) h.right_supply
  have hlow (x : V) (hx : x ∉ A ∪ B) (hxZ : x ∉ ZA ∪ ZB) :
      F ∩ G.edgesTo x (A ∪ B) = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [hrows x hx, hzero x hx hxZ]
  have hdemand : (∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) -
      (∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) = 2 * C.card := by
    have hsource := balanced_correction_imbalance G (paletteEdges c I) A B ZA ZB
      h.sides h.active_left h.active_right h.active_disjoint h.low
      (palette_side_degree_eq c I A B h.balanced)
    have hA : (∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) =
        ∑ x ∈ ZA, ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hrows x (fun hxU => Finset.disjoint_left.mp h.active_left hx hxU)]
    have hB : (∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) =
        ∑ x ∈ ZB, ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hrows x (fun hxU => Finset.disjoint_left.mp h.active_right hx hxU)]
    rw [hA, hB, hsource, hCt]
    dsimp only [t]
    rw [Nat.cast_sub h.orientation]
  have hbalanced := selected_degree_balance G F C A B ZA ZB h.sides
    h.active_left h.active_right h.active_disjoint hlow hplus hminus hdemand
  refine ⟨{
    copies := F
    avoids := ?_
    base := hbase
    rows := hrows
    exceptional_degree := ?_
    side_degrees := hbalanced
    support := hsupport
    positive_count := ?_
    negative_empty := hminus
  }⟩
  · apply Finset.disjoint_left.mpr
    intro e heF heD
    by_cases hebase : e ∈ paletteBase c (A ∪ B) I
    · exact Finset.disjoint_left.mp h.base_avoids hebase heD
    · exact Finset.disjoint_left.mp hFD (Finset.mem_sdiff.mpr ⟨heF, hebase⟩) heD
  · intro x hx
    rw [hdegree x hx]
    exact (paletteBase_degree_add_core c (A ∪ B) I x hx).trans
      (palette_degree_of_degree_eq c I x (h.full_degree x hx))
  · change (F ∩ correctionPool G B ZA).card = t
    rw [show F ∩ correctionPool G B ZA = C from hplus, hCt]

/-- The actual selected palette graph is colorable from its inherited base.
The resulting coloring is balanced and localized; it need not retain the
compressed base labels after the fan and balancing steps. -/
theorem SelectedPalette.exists_localized_coloring {k : ℕ}
    {c : G.EdgeColoring k} {I : Finset (Fin k)}
    {A B Ablock Bblock ZA ZB : Finset V} {D : Finset E}
    (S : SelectedPalette G c I A B Ablock Bblock ZA ZB D)
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

/-- Deterministically construct one palette's selected original copies and
their balanced localized coloring from the finite input conditions. -/
theorem exists_localized_palette {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (A B Ablock Bblock ZA ZB : Finset V)
    (D : Finset E) (ω₁ ω₂ : ℝ)
    (h : PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D ω₁ ω₂)
    (a : ℝ) (ha : 0 ≤ a) (hka : 2 * a < I.card)
    (hcard : A.card = B.card) (hZeven : Even (A ∪ B)ᶜ.card)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hactive : ∀ x ∈ ZA ∪ ZB,
      2 * a < ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hblockcard : Ablock.card = Bblock.card) :
    ∃ S : SelectedPalette G c I A B Ablock Bblock ZA ZB D,
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
  obtain ⟨S⟩ := exists_selected_palette G c I A B Ablock Bblock ZA ZB D ω₁ ω₂ h
  obtain ⟨d, hd⟩ := S.exists_localized_coloring G a ha hka h.sides hcard hZeven
    hcore h.low hactive h.active_left h.active_right h.left_block h.right_block hblockcard
  exact ⟨S, d, hd⟩

end Overfull.BipartiteFactorization
