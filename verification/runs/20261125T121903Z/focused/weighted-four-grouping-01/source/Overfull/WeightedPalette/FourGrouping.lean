import Overfull.WeightedPalette.Grouping
import Overfull.ResidualPalette.FourPaletteGrouping

/-!
# Weighted grouping of four-copy joining pieces

A piece has at most eight occupied vertices, so its actual star-copy weight
is at most `8*b`.  Under `b <= D` and `128*D <= h`, each resource excludes
at most `16*D` overloaded colors.  Eight endpoint conflicts per degree unit
and at most two resources give the protected margin `h - |Q| - 40*D`.

Original copies, matching disjointness, protected seed classes, and the
full-palette star-weight bound `h/8` are retained throughout the construction.
-/

noncomputable section

namespace Overfull.NativeReserve

/-- Four-copy pieces fit under the full-palette weight target. -/
theorem weighted_four_palette_item_bound {b D h : ℕ}
    (hbD : b ≤ D) (hDh : 128*D ≤ h) : 8*b ≤ h/8 := by
  omega

/-- The integer overload threshold accounts for every remainder modulo eight. -/
theorem weighted_four_palette_threshold {b D h : ℕ}
    (hbD : b ≤ D) (hDh : 128*D ≤ h) : h < 16*(h/8-8*b+1) := by
  omega

/-- Endpoint conflicts and two bounded star resources leave a positive gap. -/
theorem weighted_four_palette_protected_margin {s D h : ℕ}
    (hh : 0 < h) (hs : 2*s ≤ h) (hDh : 128*D ≤ h) : s+40*D < h := by
  omega

end Overfull.NativeReserve

namespace Overfull.WeightedPalette

open Finset Classical NativeReserve
open scoped BigOperators

variable {V E I κ : Type*} [Fintype E] [Fintype I] [Fintype κ]

/-- A four-copy piece blocks at most eight bounded parallel neighborhoods. -/
theorem starWeight_le_eight_mul (G : Multigraph V E)
    (z : V) (U : Finset V) (M : Finset E) (b : ℕ)
    (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b)
    (hsize : M.card ≤ 4) : starWeight G z U M ≤ 8*b := by
  apply (starWeight_le_support_mul G z U M b hparallel).trans
  apply Nat.mul_le_mul_right b
  exact (G.edgeSupport_card_le M).trans (Nat.mul_le_mul_left 2 hsize)

/-- Group actual matching pieces while bounding the original star copies
blocked by every whole color class, simultaneously for at most two
specified exceptional vertices and their old-core sets. All local and
total weight bounds are derived from actual multiplicities and incidence.
The given seed certificates are retained, including protected seed unions. -/
theorem exists_star_weighted_matching_grouping_of_four {h D b L : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P : Finset I) (c₀ : I → Fin h) (Q : Finset (Fin h))
    (z : κ → V) (U : κ → Finset V)
    (hresources : Fintype.card κ ≤ 2)
    (hseedProper : ∀ i ∈ P, ∀ j ∈ P, pieceConflict G M i j → c₀ i ≠ c₀ j)
    (hseedCount : ∀ j, (P.filter (fun i => c₀ i = j)).card ≤ L)
    (hseedWeight : ∀ r j,
      paletteWeight P c₀ (fun i => starWeight G (z r) (U r) (M i)) j ≤ h / 8)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 4)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hparallel : ∀ r, ∀ v ∈ U r, (G.parallelEdges (z r) v).card ≤ b)
    (hexception : ∀ r, G.degree (z r) ≤ h)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hQ : 2 * Q.card ≤ h)
    (hbudget : Fintype.card I ≤ L * (h - Q.card - 40 * D)) :
    ∃ c : I → Fin h,
      (∀ i ∈ P, c i = c₀ i) ∧
      (∀ i j, pieceConflict G M i j → c i ≠ c j) ∧
      (∀ i, i ∉ P → c i ∉ Q) ∧
      (∀ j ∈ Q, groupedCopies M c j =
        (P.filter (fun i => c₀ i = j)).biUnion M) ∧
      (∀ j, (univ.filter (fun i => c i = j)).card ≤ L) ∧
      (∀ r j, paletteWeight univ c
        (fun i => starWeight G (z r) (U r) (M i)) j ≤ h / 8) ∧
      (∀ r j, starWeight G (z r) (U r) (groupedCopies M c j) ≤ h / 8) ∧
      (∀ j, G.IsMatching (groupedCopies M c j)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ j, (groupedCopies M c j).card ≤ 4 * L) ∧
      (∀ j, (G.edgeSupport (groupedCopies M c j)).card ≤ 8 * L) ∧
      (∀ v, (univ.filter
        (fun j => v ∈ G.edgeSupport (groupedCopies M c j))).card ≤ D) := by
  let w : κ → I → ℕ := fun r i => starWeight G (z r) (U r) (M i)
  have hsymm : Symmetric (pieceConflict G M) := by
    intro i j hij
    exact ⟨hij.1.symm, fun hd => hij.2 hd.symm⟩
  have hirrefl : Irreflexive (pieceConflict G M) := fun _ hi => hi.1 rfl
  have hitem : ∀ r, ∀ i ∈ (univ : Finset I) \ P, w r i ≤ 8 * b := by
    intro r i _
    exact starWeight_le_eight_mul G (z r) (U r) (M i) b (hparallel r) (hsize i)
  have htotal : ∀ r, ∑ i, w r i ≤ (18 * D) * (h / 8 - 8 * b + 1) := by
    intro r
    have hactual : (∑ i, w r i) ≤ D * h :=
      sum_starWeight_le_mul_degree_bound G (z r) (U r) M S D h
        hdisjoint hsubset (fun v _ => hdegree v) (hexception r)
    calc
      _ ≤ D * h := hactual
      _ ≤ D * (16 * (h / 8 - 8 * b + 1)) :=
        Nat.mul_le_mul_left D (weighted_four_palette_threshold hbD hDh).le
      _ = (18 * D) * (h / 8 - 8 * b + 1) := by ring
  have hresourceBudget : Fintype.card κ * (18 * D) ≤ 2 * (18 * D) :=
    Nat.mul_le_mul_right (18 * D) hresources
  have hforbidden : 8 * D + Q.card + Fintype.card κ * (18 * D) ≤ Q.card + 40 * D := by
    omega
  have hmargin : 8 * D + Q.card + Fintype.card κ * (18 * D) < h :=
    hforbidden.trans_lt (weighted_four_palette_protected_margin hh hQ hDh)
  have hcapacity : Fintype.card I ≤
      L * (h - (8 * D + Q.card + Fintype.card κ * (18 * D))) := by
    apply hbudget.trans
    apply Nat.mul_le_mul_left L
    omega
  obtain ⟨c, hcP, hcproper, hcavoid, hcload, hcweight⟩ :=
    exists_weighted_palette_extension
      (pieceConflict G M) hsymm hirrefl univ P (subset_univ _)
      (B := 8 * D) (K := 18 * D) (L := L) (q := 8 * b) (W := h / 8)
      c₀ Q w hseedProper hseedCount hseedWeight
      (fun i _ => pieceConflict_card_le_of_size G M S D 4 hsize hdisjoint hsubset hdegree i)
      hitem htotal (weighted_four_palette_item_bound hbD hDh) hmargin
      (by simpa only [card_univ] using hcapacity)
  have hproper : ∀ i j, pieceConflict G M i j → c i ≠ c j :=
    fun i j => hcproper i (mem_univ _) j (mem_univ _)
  have havoid : ∀ i, i ∉ P → c i ∉ Q := by
    intro i hi
    exact hcavoid i (mem_sdiff.mpr ⟨mem_univ _, hi⟩)
  refine ⟨c, hcP, hproper, havoid,
    groupedCopies_eq_seed_on_protected_color M P c₀ c Q hcP havoid,
    hcload, hcweight, ?_, groupedCopies_isMatching G M c hM hproper,
    groupedCopies_disjoint M c hdisjoint, groupedCopies_cover M c,
    groupedCopies_card_le_of_size M c hsize hcload,
    groupedCopies_support_card_le_of_size G M c hsize hcload,
    groupedCopies_support_load_le G M c S hdisjoint hsubset hdegree⟩
  intro r j
  exact (starWeight_groupedCopies_le G (z r) (U r) M c j).trans (hcweight r j)

end Overfull.WeightedPalette
