import Overfull.ResidualPalette.PaletteGrouping

/-!
# Endpoint-compatible grouping with arbitrary bounded piece size

Pieces with at most `s` original copies have at most `2*s*D` conflicting
indices under a vertex incidence bound `D`. The greedy construction retains
all prescribed primary seeds and every original copy. Its class-size and
support bounds are `s*L` and `2*s*L`; for four-copy pieces these are `4*L`
and `8*L`, with conflict allowance `8*D`.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {V E I : Type*} [Fintype I]

theorem pieceConflict_card_le_of_size (G : Multigraph V E) (M : I → Finset E)
    (S : Finset E) (D s : ℕ) (hsize : ∀ i, (M i).card ≤ s)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D) (i : I) :
    (univ.filter (pieceConflict G M i)).card ≤ 2*s*D := by
  have hsub : univ.filter (pieceConflict G M i) ⊆
      univ.filter (fun j => ¬ Disjoint (G.edgeSupport (M i)) (G.edgeSupport (M j))) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2.2⟩
  exact (card_le_card hsub).trans
    ((CircuitPatterns.support_conflicts_card_le (G.edgeSupport (M i))
      (fun j => G.edgeSupport (M j)) D (fun v _ =>
        (G.family_support_load_le_degreeOn M S hdisjoint hsubset v).trans (hdegree v))).trans
          (Nat.mul_le_mul_right D ((G.edgeSupport_card_le _).trans (Nat.mul_le_mul_left 2 (hsize i)))))

theorem groupedCopies_card_le_of_size {h L s : ℕ} (M : I → Finset E) (c : I → Fin h)
    (hsize : ∀ i, (M i).card ≤ s)
    (hload : ∀ i, (univ.filter (fun j => c j = i)).card ≤ L) (i : Fin h) :
    (groupedCopies M c i).card ≤ s*L := by
  calc
    _ ≤ ∑ j ∈ univ.filter (fun j => c j = i), (M j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ univ.filter (fun j => c j = i), s := sum_le_sum (fun j _ => hsize j)
    _ = s*(univ.filter (fun j => c j = i)).card := by simp [Nat.mul_comm]
    _ ≤ s*L := Nat.mul_le_mul_left s (hload i)

theorem groupedCopies_support_card_le_of_size {h L s : ℕ} (G : Multigraph V E)
    (M : I → Finset E) (c : I → Fin h) (hsize : ∀ i, (M i).card ≤ s)
    (hload : ∀ i, (univ.filter (fun j => c j = i)).card ≤ L) (i : Fin h) :
    (G.edgeSupport (groupedCopies M c i)).card ≤ 2*s*L := by
  have hh := (G.edgeSupport_card_le _).trans
    (Nat.mul_le_mul_left 2 (groupedCopies_card_le_of_size M c hsize hload i))
  simpa only [← Nat.mul_assoc] using hh

theorem exists_bounded_matching_grouping_of_size {h D L s : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P : Finset I) (c₀ : I → Fin h)
    (hprimary : Set.InjOn c₀ P)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ s)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hL : 0 < L) (hDh : 2*s*D < h) (hbudget : Fintype.card I ≤ L*(h-2*s*D)) :
    ∃ c : I → Fin h,
      (∀ i ∈ P, c i = c₀ i) ∧
      (∀ i, (univ.filter (fun j => c j = i)).card ≤ L) ∧
      (∀ i, G.IsMatching (groupedCopies M c i)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ i, (groupedCopies M c i).card ≤ s*L) ∧
      (∀ i, (G.edgeSupport (groupedCopies M c i)).card ≤ 2*s*L) := by
  have hsymm : Symmetric (pieceConflict G M) := by
    intro i j hij
    exact ⟨hij.1.symm, fun hh => hij.2 hh.symm⟩
  have hirrefl : Irreflexive (pieceConflict G M) := fun _ hh => hh.1 rfl
  have hp : ∀ i ∈ P, ∀ j ∈ P, pieceConflict G M i j → c₀ i ≠ c₀ j := by
    intro i hi j hj hij hc
    exact hij.1 (hprimary hi hj hc)
  have hl : ∀ i, (P.filter (fun j => c₀ j = i)).card ≤ L := by
    intro i
    have hh : (P.filter (fun j => c₀ j = i)).card ≤ 1 := by
      apply card_le_one.mpr
      intro j hj k hk
      exact hprimary (mem_filter.mp hj).1 (mem_filter.mp hk).1
        ((mem_filter.mp hj).2.trans (mem_filter.mp hk).2.symm)
    omega
  obtain ⟨c, hcP, hcproper, hcload⟩ := exists_bounded_palette_extension
    (pieceConflict G M) hsymm hirrefl univ P (subset_univ _) c₀ hp hl
    (fun i _ => pieceConflict_card_le_of_size G M S D s hsize hdisjoint hsubset hdegree i)
    hDh (by simpa only [card_univ] using hbudget)
  refine ⟨c, hcP, hcload, ?_, groupedCopies_disjoint M c hdisjoint,
    groupedCopies_cover M c, groupedCopies_card_le_of_size M c hsize hcload,
    groupedCopies_support_card_le_of_size G M c hsize hcload⟩
  exact groupedCopies_isMatching G M c hM (fun i j => hcproper i (mem_univ _) j (mem_univ _))

theorem palette_capacity_of_incidence_budget_of_size [Fintype V]
    {h D L s : ℕ} (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-2*s*D)) :
    Fintype.card I ≤ L*(h-2*s*D) := by
  have hh := twice_piece_count_le_order_mul_degree G M S D hne hdisjoint hsubset hdegree
  nlinarith

end Overfull.NativeReserve
