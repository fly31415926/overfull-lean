import Overfull.WeightedPalette.Extension
import Overfull.WeightedPalette.StarWeights

/-!
# Weighted grouping of actual matching pieces

The dynamic palette extension is applied to weights that count actual
star copies blocked at their old-core endpoints. Local multiplicity and
global incidence estimates derive all resource budgets. At most two such
resources cost at most `26D` additional forbidden colors, giving the common
protected margin `h - |Q| - 32D`.

Seed properness, capacity, and resource loads remain explicit hypotheses.
The conclusion groups the original pieces into actual edge-disjoint
matchings and preserves their copy union. It does not assert the later
star completion or construct a joining-cut parity certificate.
-/

noncomputable section

namespace Overfull.WeightedPalette

open Finset Classical NativeReserve
open scoped BigOperators

variable {E I : Type*} [Fintype I]

/-- When only seeds may use a protected color, its whole actual class is
exactly the union of the seeds prescribed that color. -/
theorem groupedCopies_eq_seed_on_protected_color {h : ℕ}
    (M : I → Finset E) (P : Finset I) (c₀ c : I → Fin h)
    (Q : Finset (Fin h))
    (hseed : ∀ i ∈ P, c i = c₀ i)
    (havoid : ∀ i, i ∉ P → c i ∉ Q)
    (j : Fin h) (hj : j ∈ Q) :
    groupedCopies M c j = (P.filter (fun i => c₀ i = j)).biUnion M := by
  ext e
  rw [mem_groupedCopies]
  constructor
  · rintro ⟨i, hi, he⟩
    have hiP : i ∈ P := by
      by_contra hn
      exact havoid i hn (hi.symm ▸ hj)
    exact mem_biUnion.mpr ⟨i,
      mem_filter.mpr ⟨hiP, (hseed i hiP).symm.trans hi⟩, he⟩
  · intro he
    obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
    obtain ⟨hiP, hi⟩ := mem_filter.mp hi
    exact ⟨i, (hseed i hiP).trans hi, he⟩

variable {V κ : Type*} [Fintype E] [Fintype κ]

/-- Group actual matching pieces while bounding the original star copies
blocked by every whole color class, simultaneously for at most two
specified exceptional vertices and their old-core sets. All local and
total weight bounds are derived from actual multiplicities and incidence.
The given seed certificates are retained, including protected seed unions. -/
theorem exists_star_weighted_matching_grouping {h D b L : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P : Finset I) (c₀ : I → Fin h) (Q : Finset (Fin h))
    (z : κ → V) (U : κ → Finset V)
    (hresources : Fintype.card κ ≤ 2)
    (hseedProper : ∀ i ∈ P, ∀ j ∈ P, pieceConflict G M i j → c₀ i ≠ c₀ j)
    (hseedCount : ∀ j, (P.filter (fun i => c₀ i = j)).card ≤ L)
    (hseedWeight : ∀ r j,
      paletteWeight P c₀ (fun i => starWeight G (z r) (U r) (M i)) j ≤ h / 8)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hparallel : ∀ r, ∀ v ∈ U r, (G.parallelEdges (z r) v).card ≤ b)
    (hexception : ∀ r, G.degree (z r) ≤ h)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hQ : 2 * Q.card ≤ h)
    (hbudget : Fintype.card I ≤ L * (h - Q.card - 32 * D)) :
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
      (∀ j, (groupedCopies M c j).card ≤ 3 * L) ∧
      (∀ j, (G.edgeSupport (groupedCopies M c j)).card ≤ 6 * L) ∧
      (∀ v, (univ.filter
        (fun j => v ∈ G.edgeSupport (groupedCopies M c j))).card ≤ D) := by
  let w : κ → I → ℕ := fun r i => starWeight G (z r) (U r) (M i)
  have hsymm : Symmetric (pieceConflict G M) := by
    intro i j hij
    exact ⟨hij.1.symm, fun hd => hij.2 hd.symm⟩
  have hirrefl : Irreflexive (pieceConflict G M) := fun _ hi => hi.1 rfl
  have hitem : ∀ r, ∀ i ∈ (univ : Finset I) \ P, w r i ≤ 6 * b := by
    intro r i _
    exact starWeight_le_six_mul G (z r) (U r) (M i) b (hparallel r) (hsize i)
  have htotal : ∀ r, ∑ i, w r i ≤ (13 * D) * (h / 8 - 6 * b + 1) := by
    intro r
    have hactual : (∑ i, w r i) ≤ D * h :=
      sum_starWeight_le_mul_degree_bound G (z r) (U r) M S D h
        hdisjoint hsubset (fun v _ => hdegree v) (hexception r)
    calc
      _ ≤ D * h := hactual
      _ ≤ D * (13 * (h / 8 - 6 * b + 1)) :=
        Nat.mul_le_mul_left D (weighted_palette_threshold hbD hDh).le
      _ = (13 * D) * (h / 8 - 6 * b + 1) := by ring
  have hresourceBudget : Fintype.card κ * (13 * D) ≤ 2 * (13 * D) :=
    Nat.mul_le_mul_right (13 * D) hresources
  have hforbidden : 6 * D + Q.card + Fintype.card κ * (13 * D) ≤ Q.card + 32 * D := by
    omega
  have hmargin : 6 * D + Q.card + Fintype.card κ * (13 * D) < h :=
    hforbidden.trans_lt (weighted_palette_protected_margin hh hQ hDh)
  have hcapacity : Fintype.card I ≤
      L * (h - (6 * D + Q.card + Fintype.card κ * (13 * D))) := by
    apply hbudget.trans
    apply Nat.mul_le_mul_left L
    omega
  obtain ⟨c, hcP, hcproper, hcavoid, hcload, hcweight⟩ :=
    exists_weighted_palette_extension
      (pieceConflict G M) hsymm hirrefl univ P (subset_univ _)
      (B := 6 * D) (K := 13 * D) (L := L) (q := 6 * b) (W := h / 8)
      c₀ Q w hseedProper hseedCount hseedWeight
      (fun i _ => pieceConflict_card_le G M S D hsize hdisjoint hsubset hdegree i)
      hitem htotal (weighted_palette_item_bound hbD hDh) hmargin
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
    groupedCopies_card_le M c hsize hcload,
    groupedCopies_support_card_le G M c hsize hcload,
    groupedCopies_support_load_le G M c S hdisjoint hsubset hdegree⟩
  intro r j
  exact (starWeight_groupedCopies_le G (z r) (U r) M c j).trans (hcweight r j)

end Overfull.WeightedPalette
