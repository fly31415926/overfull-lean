import Overfull.CircuitPatterns.Pairing

/-!
# Hall choice with different conflict bounds on the two sides

The two exceptional stars have different row and column obstruction bounds.
This module proves the finite relation statement at the non-strict threshold
`a + b ≤ m`, including empty types. Its numerical specialization uses the
original palette size `h`; it does not assert the actual-copy balance needed
to instantiate the relation with the remaining exceptional stars.
-/

noncomputable section

namespace Overfull.CircuitPatterns

open Finset Classical

variable {I J : Type*}

/-- A balanced finite relation admits a bijective choice when the sum of the
row and column forbidden-partner bounds is at most the common order. -/
theorem exists_equiv_of_asymmetric_conflicts [Fintype I] [Fintype J]
    (R : I → J → Prop) (a b : ℕ)
    (hcard : Fintype.card I = Fintype.card J)
    (hleft : ∀ i, (univ.filter (fun j => ¬ R i j)).card ≤ a)
    (hright : ∀ j, (univ.filter (fun i => ¬ R i j)).card ≤ b)
    (hsize : a + b ≤ Fintype.card I) :
    ∃ f : I ≃ J, ∀ i, R i (f i) := by
  let T : I → Finset J := fun i => univ.filter (R i)
  have hT (i : I) : Fintype.card J ≤ (T i).card + a := by
    have hpartition := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset J)) (R i)
    have hbound := hleft i
    simp only [card_univ] at hpartition
    dsimp only [T]
    omega
  have hHall : ∀ S : Finset I, S.card ≤ (S.biUnion T).card := by
    intro S
    by_cases hS : S.Nonempty
    · by_cases hsmall : S.card ≤ b
      · obtain ⟨i, hi⟩ := hS
        have hsubset := card_le_card (subset_biUnion_of_mem T hi)
        have hdegree := hT i
        omega
      · have hfull : S.biUnion T = univ := by
          apply eq_univ_iff_forall.mpr
          intro j
          by_contra hj
          have hsub : S ⊆ univ.filter (fun i => ¬ R i j) := by
            intro i hi
            refine mem_filter.mpr ⟨mem_univ _, ?_⟩
            intro hij
            exact hj (mem_biUnion.mpr ⟨i, hi,
              mem_filter.mpr ⟨mem_univ _, hij⟩⟩)
          exact hsmall ((card_le_card hsub).trans (hright j))
        rw [hfull, card_univ, ← hcard]
        exact card_le_univ S
    · simp [not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨f, hinj, hmem⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' T).mp hHall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  exact ⟨Equiv.ofBijective f hbij, fun i => (mem_filter.mp (hmem i)).2⟩

/-- The original-palette regime supplies the asymmetric Hall margin for a
remaining star palette of size at least `h - s - D`. -/
theorem star_hall_margin (h D b s : ℕ)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hs : 2 * s ≤ h) :
    (D + b) + (h / 8 + b) ≤ h - s - D := by
  omega

/-- An abstract remaining-star relation has a bijective choice once its exact
balanced finite sets and the two actual conflict bounds have been supplied. -/
theorem exists_star_equiv_of_conflict_bounds [Fintype I] [Fintype J]
    (R : I → J → Prop) (h D b s : ℕ)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hs : 2 * s ≤ h)
    (hcard : Fintype.card I = Fintype.card J)
    (hlower : h - s - D ≤ Fintype.card I)
    (hleft : ∀ i, (univ.filter (fun j => ¬ R i j)).card ≤ D + b)
    (hright : ∀ j, (univ.filter (fun i => ¬ R i j)).card ≤ h / 8 + b) :
    ∃ f : I ≃ J, ∀ i, R i (f i) := by
  exact exists_equiv_of_asymmetric_conflicts R (D + b) (h / 8 + b)
    hcard hleft hright ((star_hall_margin h D b s hb hD hs).trans hlower)

end Overfull.CircuitPatterns
