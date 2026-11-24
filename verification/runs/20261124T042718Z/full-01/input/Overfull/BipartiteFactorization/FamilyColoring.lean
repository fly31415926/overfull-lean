import Overfull.BipartiteFactorization.Families
import Overfull.BipartiteFactorization.Remaining

/-!
# Coloring a selected palette family and its exact remainder

Every selected member and the actual residual receive constructed balanced
colorings. The footprint incidence counts then add to the original degree,
so the total load bound is shared by the entire partition.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι]
variable (G : Multigraph V E)

omit [Fintype V] in
/-- Palette exclusion at every low vertex is preserved by taking the
actual union of the selected palettes. -/
theorem palette_family_low {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (U Zplus : Finset V)
    (hlow : ∀ i x, x ∉ U → x ∉ Zplus →
      paletteEdges c (I i) ∩ G.edgesTo x U = ∅)
    (x : V) (hx : x ∉ U) (hxZ : x ∉ Zplus) :
    paletteEdges c (univ.biUnion I) ∩ G.edgesTo x U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heI, hex⟩ := Finset.mem_inter.mp he
  obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp
    ((mem_paletteEdges c (univ.biUnion I) e).mp heI)
  have he' : e ∈ paletteEdges c (I i) ∩ G.edgesTo x U :=
    Finset.mem_inter.mpr ⟨(mem_paletteEdges c (I i) e).mpr hei, hex⟩
  rw [hlow i x hx hxZ] at he'
  exact Finset.notMem_empty _ he'

/-- Across a disjoint family and its exact residual, footprint incidence
counts add to the ambient degree at every core vertex. -/
theorem localized_family_load (F : ι → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (A B : Finset V) (Ablock Bblock : ι → Finset V)
    (q : ι → ℕ) (qRest : ℕ) (a : ℝ)
    (d : ∀ i, LocalizedColoring (G.restrictEdges (F i))
      A B (Ablock i) (Bblock i) (q i) a)
    (dRest : LocalizedColoring (G.restrictEdges (familyCopies F)ᶜ)
      A B A B qRest a)
    (v : V) (hv : v ∈ A ∪ B) :
    (∑ i, (univ.filter
      (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) +
      (univ.filter (fun j => v ∈ dRest.coloring.exteriorFootprint (A ∪ B) j)).card =
        G.degree v := by
  have hsum : (∑ i, (univ.filter
      (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) =
      ∑ i, (G.restrictEdges (F i)).degree v :=
    Finset.sum_congr rfl (fun i _ => (d i).load v hv)
  rw [hsum, dRest.load v hv, ← familyCopies_degree G F hdisj v, Nat.add_comm]
  exact OneCore.complement_degree_add G (familyCopies F) v

/-- Construct all selected colorings and the coloring of their actual
complement. The residual coloring comes from the unused original palette
on its inactive residue, and the final load bound applies to all colors
from both parts together. -/
theorem exists_family_and_remaining_colorings {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (A B ZA ZB : Finset V)
    (Ablock Bblock : ι → Finset V) (D : Finset E)
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (hpalettes : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (a : ℝ) (ha : 0 ≤ a)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card)
    (hZA : Disjoint ZA (A ∪ B)) (hZB : Disjoint ZB (A ∪ B))
    (hfull : ∀ x, x ∉ A ∪ B → G.degree x = k)
    (hfullBalanced : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hka : ∀ i, 2 * a < (I i).card)
    (hlow : ∀ i x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      paletteEdges c (I i) ∩ G.edgesTo x (A ∪ B) = ∅)
    (hactive : ∀ i x, x ∈ ZA ∪ ZB →
      2 * a < ((paletteEdges c (I i) ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hAblock : ∀ i, Ablock i ⊆ A) (hBblock : ∀ i, Bblock i ⊆ B)
    (hblockcard : ∀ i, (Ablock i).card = (Bblock i).card)
    (hrest : 2 * a < (k - (univ.biUnion I).card : ℕ))
    (hrestActive : ∀ x ∈ ZA ∪ ZB,
      2 * a < ((G.edgesTo x (A ∪ B)).card : ℝ) - (univ.biUnion I).card) :
    ∃ d : ∀ i, LocalizedColoring (G.restrictEdges (S i).copies)
        A B (Ablock i) (Bblock i) (I i).card a,
      ∃ dRest : LocalizedColoring
          (G.restrictEdges (familyCopies (fun i => (S i).copies))ᶜ)
          A B A B (k - (univ.biUnion I).card) a,
        (∀ v ∈ A ∪ B,
          (∑ i, (univ.filter
            (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) +
            (univ.filter
              (fun j => v ∈ dRest.coloring.exteriorFootprint (A ∪ B) j)).card =
                G.degree v) ∧
        (∀ v ∈ A ∪ B,
          (((∑ i, (univ.filter
            (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) +
            (univ.filter
              (fun j => v ∈ dRest.coloring.exteriorFootprint (A ∪ B) j)).card : ℕ) : ℝ) ≤ a) := by
  have hex (i : ι) : Nonempty (LocalizedColoring (G.restrictEdges (S i).copies)
      A B (Ablock i) (Bblock i) (I i).card a) :=
    (S i).localized_coloring G a ha (hka i) hAB hcard hZeven hcore
      (hlow i) (hactive i) hZA hZB (hAblock i) (hBblock i) (hblockcard i)
  let d := fun i => Classical.choice (hex i)
  have hlowUnion := palette_family_low G c I (A ∪ B) (ZA ∪ ZB) hlow
  obtain ⟨d₀, hcover, hbalance, hspread, hsupport, hbound, heven, hload, hloadle⟩ :=
    exists_balanced_remaining_coloring G c A B (ZA ∪ ZB)
      (familyCopies (fun i => (S i).copies)) (univ.biUnion I) a ha hrest hAB hcard
      hZeven (Finset.disjoint_union_left.mpr ⟨hZA, hZB⟩) hfull
      (fun x hx => OrientedPalette.family_exceptional_degree_palette_union G S
        hdisj hpalettes x hx)
      (OrientedPalette.family_base G S) hlowUnion hcore hfullBalanced
      (OrientedPalette.family_side_degrees G S hdisj) hrestActive
  let dRest : LocalizedColoring
      (G.restrictEdges (familyCopies (fun i => (S i).copies))ᶜ)
      A B A B (k - (univ.biUnion I).card) a :=
    ⟨d₀, hcover, hbalance, hspread, hsupport, hbound, heven, hload, hloadle⟩
  have htotal (v : V) (hv : v ∈ A ∪ B) :=
    localized_family_load G (fun i => (S i).copies) hdisj A B Ablock Bblock
      (fun i => (I i).card) (k - (univ.biUnion I).card) a d dRest v hv
  refine ⟨d, dRest, htotal, ?_⟩
  intro v hv
  rw [htotal v hv]
  exact hcore v hv

end Overfull.BipartiteFactorization
