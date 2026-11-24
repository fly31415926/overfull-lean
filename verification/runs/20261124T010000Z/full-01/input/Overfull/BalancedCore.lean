import Overfull.PairedCut.Sides
import Overfull.RandomReserveDegrees
import Mathlib.Data.Real.Sqrt

/-!
# Extracting a balanced core from a bipartite partition outcome

The exceptional opposite-degree vertices are defined from the original
graph. They are removed, and the two remaining sides are trimmed to the
smaller order. The resulting graph is the actual induced crossing graph.
The robust-partition proposition supplying the input outcome is not assumed
to have been proved in this file.
-/

namespace Overfull.BalancedCore

open Finset Classical SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def badVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℝ) (A B : Finset V) : Finset V :=
  (A.filter (fun v => ((G.neighborFinset v ∩ B).card : ℝ) <
    G.maxDegree - 2 * r * Fintype.card V)) ∪
  (B.filter (fun v => ((G.neighborFinset v ∩ A).card : ℝ) <
    G.maxDegree - 2 * r * Fintype.card V))

omit [Fintype V] [DecidableEq V] in
theorem crossing_bipartite (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B) :
    (PairedCut.cutSidesGraph G A B).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  refine ⟨?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro v ⟨a,rfl⟩ ⟨b,h⟩
    cases h
  · intro x y hxy
    rcases x with a | b <;> rcases y with a' | b'
    · simp [PairedCut.cutSidesGraph,PairedCut.crossingGraph,a.property,a'.property] at hxy
    · exact Or.inl ⟨⟨a,rfl⟩,⟨b',rfl⟩⟩
    · exact Or.inr ⟨⟨b,rfl⟩,⟨a',rfl⟩⟩
    · have hb : b.val ∉ A := fun h => Finset.disjoint_left.mp hd h b.property
      have hb' : b'.val ∉ A := fun h => Finset.disjoint_left.mp hd h b'.property
      simp [PairedCut.cutSidesGraph,PairedCut.crossingGraph,hb,hb'] at hxy

theorem crossing_left_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B) (a : A) :
    (PairedCut.cutSidesGraph G A B).degree (.inl a) =
      (G.neighborFinset a.val ∩ B).card := by
  let H := PairedCut.cutSidesGraph G A B
  have heq : (rightNeighbors H a).image Subtype.val = G.neighborFinset a.val ∩ B := by
    ext v
    constructor
    · intro hv
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      have hadj : G.Adj a.val b.val := by
        simpa [rightNeighbors,H,PairedCut.cutSidesGraph_cross_adj G A B hd] using hb
      exact Finset.mem_inter.mpr ⟨by simpa using hadj,b.property⟩
    · intro hv
      obtain ⟨hvG,hvB⟩ := Finset.mem_inter.mp hv
      let b : B := ⟨v,hvB⟩
      refine Finset.mem_image.mpr ⟨b,?_,rfl⟩
      have hadj : G.Adj a.val b.val := by simpa [b] using hvG
      simpa [rightNeighbors,H,PairedCut.cutSidesGraph_cross_adj G A B hd] using hadj
  have hdeg : (rightNeighbors H a).card = H.degree (.inl a) :=
    RandomReserve.crossingDegree_eq_degree H (crossing_bipartite G A B hd) (.inl a)
  rw [← hdeg,← heq,Finset.card_image_of_injective _ Subtype.val_injective]

theorem crossing_right_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B) (b : B) :
    (PairedCut.cutSidesGraph G A B).degree (.inr b) =
      (G.neighborFinset b.val ∩ A).card := by
  let H := PairedCut.cutSidesGraph G A B
  have heq : (leftNeighbors H b).image Subtype.val = G.neighborFinset b.val ∩ A := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      have hadj : G.Adj b.val a.val := by
        simpa [leftNeighbors,H,PairedCut.cutSidesGraph_cross_adj G A B hd,G.adj_comm] using ha
      exact Finset.mem_inter.mpr ⟨by simpa using hadj,a.property⟩
    · intro hv
      obtain ⟨hvG,hvA⟩ := Finset.mem_inter.mp hv
      let a : A := ⟨v,hvA⟩
      refine Finset.mem_image.mpr ⟨a,?_,rfl⟩
      have hadj : G.Adj a.val b.val := by simpa [a,G.adj_comm] using hvG
      simpa [leftNeighbors,H,PairedCut.cutSidesGraph_cross_adj G A B hd] using hadj
  have hdeg : (leftNeighbors H b).card = H.degree (.inr b) :=
    RandomReserve.crossingDegree_eq_degree H (crossing_bipartite G A B hd) (.inr b)
  rw [← hdeg,← heq,Finset.card_image_of_injective _ Subtype.val_injective]

omit [Fintype V] in
theorem inter_card_loss (S A B : Finset V) :
    (S ∩ A).card ≤ (S ∩ B).card + (A \ B).card := by
  have hsub : S ∩ A ⊆ (S ∩ B) ∪ (A \ B) := by
    intro v hv
    obtain ⟨hvS,hvA⟩ := Finset.mem_inter.mp hv
    by_cases hvB : v ∈ B
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hvS,hvB⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvA,hvB⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Construct the retained sides from an actual bipartite outcome. -/
theorem extract (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hrsmall : r ≤ 1 / 18) (A₁ B₁ : Finset V)
    (hdisjoint : Disjoint A₁ B₁)
    (hmissing : (((A₁ ∪ B₁)ᶜ).card : ℝ) ≤ r * Fintype.card V)
    (hbalance : |(A₁.card : ℝ) - B₁.card| ≤ r * Fintype.card V)
    (hbad : ((badVertices G r A₁ B₁).card : ℝ) ≤ 2 * r * Fintype.card V) :
    ∃ A B : Finset V, A ⊆ A₁ ∧ B ⊆ B₁ ∧ Disjoint A B ∧ A.card = B.card ∧
      (Fintype.card V : ℝ) / 3 ≤ A.card ∧
      (Fintype.card V : ℝ) - 2 * A.card ≤ 6 * r * Fintype.card V ∧
      ∀ v : A ⊕ B,
        (G.maxDegree : ℝ) - 8 * r * Fintype.card V ≤
          ((PairedCut.cutSidesGraph G A B).degree v : ℝ) ∧
        (PairedCut.cutSidesGraph G A B).degree v ≤ G.maxDegree := by
  let X := badVertices G r A₁ B₁
  let A₀ := A₁ \ X
  let B₀ := B₁ \ X
  let m := min A₀.card B₀.card
  obtain ⟨A,hAA₀,hAcard⟩ := Finset.exists_subset_card_eq (min_le_left A₀.card B₀.card)
  obtain ⟨B,hBB₀,hBcard⟩ := Finset.exists_subset_card_eq (min_le_right A₀.card B₀.card)
  have hA : A ⊆ A₁ := hAA₀.trans Finset.sdiff_subset
  have hB : B ⊆ B₁ := hBB₀.trans Finset.sdiff_subset
  have hAB : Disjoint A B := hdisjoint.mono hA hB
  have hAc : A.card = m := hAcard
  have hBc : B.card = m := hBcard
  have hA₁ : (A₁.card : ℝ) ≤ A₀.card + (X.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : A₁.card ≤ (A₁ \ X).card + X.card)
  have hB₁ : (B₁.card : ℝ) ≤ B₀.card + (X.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : B₁.card ≤ (B₁ \ X).card + X.card)
  have hparts : (A₁.card : ℝ) + B₁.card ≤ 2 * m + 2 * (X.card : ℝ) + r * Fintype.card V := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hbalance
    rcases le_total A₀.card B₀.card with h | h
    · have hm : m = A₀.card := min_eq_left h
      rw [hm]
      linarith only [hA₁,hhi,hlo]
    · have hm : m = B₀.card := min_eq_right h
      rw [hm]
      linarith only [hB₁,hhi,hlo]
  have hcover : (A₁.card : ℝ) + B₁.card + ((A₁ ∪ B₁)ᶜ).card = Fintype.card V := by
    have h := Finset.card_add_card_compl (A₁ ∪ B₁)
    rw [Finset.card_union_of_disjoint hdisjoint] at h
    exact_mod_cast h
  have hloss : (Fintype.card V : ℝ) - 2 * m ≤ 6 * r * Fintype.card V := by
    change (X.card : ℝ) ≤ 2 * r * Fintype.card V at hbad
    linarith only [hparts,hcover,hmissing,hbad]
  have hm : (Fintype.card V : ℝ) / 3 ≤ m := by
    have hmul := mul_le_mul_of_nonneg_right hrsmall (Nat.cast_nonneg (Fintype.card V))
    linarith only [hloss,hmul]
  have hcompl : (((A ∪ B)ᶜ).card : ℝ) ≤ 6 * r * Fintype.card V := by
    have h := Finset.card_add_card_compl (A ∪ B)
    rw [Finset.card_union_of_disjoint hAB,hAc,hBc] at h
    have h' : (m : ℝ) + m + ((A ∪ B)ᶜ).card = Fintype.card V := by exact_mod_cast h
    linarith only [h',hloss]
  have hAloss : ((A₁ \ A).card : ℝ) ≤ 6 * r * Fintype.card V := by
    apply le_trans _ hcompl
    exact_mod_cast Finset.card_le_card (show A₁ \ A ⊆ (A ∪ B)ᶜ by
      intro v hv
      apply Finset.mem_compl.mpr
      intro hu
      rcases Finset.mem_union.mp hu with hvA | hvB
      · exact (Finset.mem_sdiff.mp hv).2 hvA
      · exact Finset.disjoint_left.mp hdisjoint (Finset.mem_sdiff.mp hv).1 (hB hvB))
  have hBloss : ((B₁ \ B).card : ℝ) ≤ 6 * r * Fintype.card V := by
    apply le_trans _ hcompl
    exact_mod_cast Finset.card_le_card (show B₁ \ B ⊆ (A ∪ B)ᶜ by
      intro v hv
      apply Finset.mem_compl.mpr
      intro hu
      rcases Finset.mem_union.mp hu with hvA | hvB
      · exact Finset.disjoint_left.mp hdisjoint (hA hvA) (Finset.mem_sdiff.mp hv).1
      · exact (Finset.mem_sdiff.mp hv).2 hvB)
  refine ⟨A,B,hA,hB,hAB,hAc.trans hBc.symm,?_,?_,?_⟩
  · simpa only [hAc] using hm
  · simpa only [hAc] using hloss
  · intro v
    rcases v with a | b
    · rw [crossing_left_degree G A B hAB]
      have ha := Finset.mem_sdiff.mp (hAA₀ a.property)
      have hgood : (G.maxDegree : ℝ) - 2 * r * Fintype.card V ≤
          (G.neighborFinset a.val ∩ B₁).card := by
        apply le_of_not_gt
        intro hlow
        exact ha.2 (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha.1,hlow⟩)))
      have hdelete : ((G.neighborFinset a.val ∩ B₁).card : ℝ) ≤
          (G.neighborFinset a.val ∩ B).card + ((B₁ \ B).card : ℝ) := by
        exact_mod_cast inter_card_loss (G.neighborFinset a.val) B₁ B
      refine ⟨by linarith only [hgood,hdelete,hBloss],?_⟩
      exact (Finset.card_le_card Finset.inter_subset_left).trans (G.degree_le_maxDegree a.val)
    · rw [crossing_right_degree G A B hAB]
      have hb := Finset.mem_sdiff.mp (hBB₀ b.property)
      have hgood : (G.maxDegree : ℝ) - 2 * r * Fintype.card V ≤
          (G.neighborFinset b.val ∩ A₁).card := by
        apply le_of_not_gt
        intro hlow
        exact hb.2 (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hb.1,hlow⟩)))
      have hdelete : ((G.neighborFinset b.val ∩ A₁).card : ℝ) ≤
          (G.neighborFinset b.val ∩ A).card + ((A₁ \ A).card : ℝ) := by
        exact_mod_cast inter_card_loss (G.neighborFinset b.val) A₁ A
      refine ⟨by linarith only [hgood,hdelete,hAloss],?_⟩
      exact (Finset.card_le_card Finset.inter_subset_left).trans (G.degree_le_maxDegree b.val)

/-- Lemma 2.25 from precisely the bipartite-outcome properties of
Proposition 2.24. That proposition supplies the bad-vertex bound appearing
here; the retained sets and their degree bounds are constructed above. -/
theorem balanced_core_of_bipartite_outcome (G : SimpleGraph V) [DecidableRel G.Adj]
    (ρ ζ : ℝ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 324)
    (hζ : 0 ≤ ζ) (hζρ : ζ ≤ ρ / 4) (A₁ B₁ Z : Finset V)
    (hdisjoint : Disjoint A₁ B₁) (hcover : A₁ ∪ B₁ = Zᶜ)
    (hZ : (Z.card : ℝ) ≤ ζ ^ 2 * Fintype.card V)
    (hbalance : |(A₁.card : ℝ) - B₁.card| ≤ ρ * Fintype.card V)
    (hbad : ((badVertices G (Real.sqrt ρ) A₁ B₁).card : ℝ) ≤
      2 * Real.sqrt ρ * Fintype.card V) :
    ∃ A B : Finset V, A ⊆ A₁ ∧ B ⊆ B₁ ∧ Disjoint A B ∧ A.card = B.card ∧
      (Fintype.card V : ℝ) / 3 ≤ A.card ∧
      (Fintype.card V : ℝ) - 2 * A.card ≤ 6 * Real.sqrt ρ * Fintype.card V ∧
      ∀ v : A ⊕ B,
        (G.maxDegree : ℝ) - 8 * Real.sqrt ρ * Fintype.card V ≤
          ((PairedCut.cutSidesGraph G A B).degree v : ℝ) ∧
        (PairedCut.cutSidesGraph G A B).degree v ≤ G.maxDegree := by
  have hr : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ
  have hrsmall : Real.sqrt ρ ≤ 1 / 18 := by nlinarith only [hr,hr2,hρsmall]
  have hρr : ρ ≤ Real.sqrt ρ := by nlinarith only [hr,hr2,hrsmall]
  have hζr : ζ ≤ Real.sqrt ρ := by linarith only [hζρ,hρ,hρr]
  have hζ2r : ζ ^ 2 ≤ Real.sqrt ρ := by
    have hζ1 : ζ ≤ 1 := by linarith only [hζr,hrsmall]
    have hζ2 : ζ ^ 2 ≤ ζ := by nlinarith only [hζ,hζ1]
    exact hζ2.trans hζr
  apply extract G (Real.sqrt ρ) hrsmall A₁ B₁ hdisjoint
  · have heq : (A₁ ∪ B₁)ᶜ = Z := by rw [hcover,compl_compl]
    rw [heq]
    exact hZ.trans (mul_le_mul_of_nonneg_right hζ2r (Nat.cast_nonneg _))
  · exact hbalance.trans (mul_le_mul_of_nonneg_right hρr (Nat.cast_nonneg _))
  · exact hbad

end Overfull.BalancedCore
