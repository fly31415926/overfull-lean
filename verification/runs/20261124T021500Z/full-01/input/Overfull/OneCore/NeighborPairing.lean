import Overfull.MatchingPairing
import Mathlib.Data.Fintype.Sum

/-!
# Pairing a prescribed neighbor set before choosing a balanced cut

In an even finite population, all but at most one member of a prescribed
set can be paired inside that set. Every cut meeting each pair therefore
contains at least half of the prescribed set, rounded down. Applying this
to both shores gives the deterministic neighbor supply needed at an apex.
-/

noncomputable section

namespace Overfull.OneCore.NeighborPairing

open Finset Classical

variable {W : Type*} [Fintype W]

/-- Construct an actual pairing and `|S|/2` distinct pairs contained in `S`. -/
theorem exists_pairing_with_internal_pairs (heven : Even (Fintype.card W)) (S : Finset W) :
    ∃ e : Fin (Fintype.card W / 2) × Bool ≃ W,
      ∃ ι : Fin (S.card / 2) ↪ Fin (Fintype.card W / 2),
        ∀ i b, e (ι i, b) ∈ S := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq
    (show 2 * (S.card / 2) ≤ S.card by omega)
  let k := S.card / 2
  let C := {w : W // w ∉ T}
  let r := Fintype.card C / 2
  have hsum : T.card + Fintype.card C = Fintype.card W := by
    have h := Fintype.card_congr (Equiv.sumCompl (fun w : W => w ∈ T))
    simpa only [Fintype.card_sum, Fintype.card_coe] using h
  have hT : Fintype.card (Fin k × Bool) = Fintype.card T := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_coe]
    dsimp [k]
    omega
  have hC : Fintype.card (Fin r × Bool) = Fintype.card C := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    dsimp [r]
    obtain ⟨a, ha⟩ := heven
    omega
  let eT : Fin k × Bool ≃ T := Fintype.equivOfCardEq hT
  let eC : Fin r × Bool ≃ C := Fintype.equivOfCardEq hC
  let K := Fin k ⊕ Fin r
  let e₀ : K × Bool ≃ W :=
    (Equiv.sumProdDistrib (Fin k) (Fin r) Bool).trans
      ((Equiv.sumCongr eT eC).trans (Equiv.sumCompl (fun w : W => w ∈ T)))
  have hleft (i : Fin k) (b : Bool) : e₀ (Sum.inl i, b) ∈ S := by
    change (eT (i, b)).val ∈ S
    exact hTS (eT (i, b)).property
  have hK : Fintype.card K = Fintype.card W / 2 := by
    have h := Fintype.card_congr e₀
    simp only [Fintype.card_prod, Fintype.card_bool] at h
    omega
  let eI : Fin (Fintype.card W / 2) ≃ K := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using hK.symm)
  let e : Fin (Fintype.card W / 2) × Bool ≃ W :=
    (Equiv.prodCongr eI (Equiv.refl Bool)).trans e₀
  let ι : Fin k ↪ Fin (Fintype.card W / 2) :=
    ⟨fun i => eI.symm (Sum.inl i), fun i j h => Sum.inl.inj (eI.symm.injective h)⟩
  refine ⟨e, ι, ?_⟩
  intro i b
  change e₀ (eI (eI.symm (Sum.inl i)), b) ∈ S
  rw [eI.apply_symm_apply]
  exact hleft i b

/-- Every shore meeting every prescribed pair receives the required number
of vertices of `S`. No probabilistic or graph assumption is needed. -/
theorem exists_pairing_meeting_bound (heven : Even (Fintype.card W)) (S : Finset W) :
    ∃ e : Fin (Fintype.card W / 2) × Bool ≃ W,
      ∀ A : Finset W, (∀ i, ∃ b, e (i, b) ∈ A) → S.card / 2 ≤ (S ∩ A).card := by
  classical
  obtain ⟨e, ι, hι⟩ := exists_pairing_with_internal_pairs heven S
  refine ⟨e, ?_⟩
  intro A hA
  choose b hb using (fun i : Fin (S.card / 2) => hA (ι i))
  let f : Fin (S.card / 2) → (S ∩ A : Finset W) := fun i =>
    ⟨e (ι i, b i), Finset.mem_inter.mpr ⟨hι i (b i), hb i⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := e.injective (congrArg Subtype.val hij)
    exact ι.injective (congrArg Prod.fst h)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-- A cut splitting every pair has almost half of the prescribed neighbor
set on both shores. The conclusion includes the original integer form. -/
theorem exists_balancing_pairing (heven : Even (Fintype.card W)) (S : Finset W) :
    ∃ e : Fin (Fintype.card W / 2) × Bool ≃ W,
      ∀ A B : Finset W,
        (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
          (e (i, false) ∈ B ∧ e (i, true) ∈ A)) →
        S.card / 2 ≤ (S ∩ A).card ∧ S.card / 2 ≤ (S ∩ B).card ∧
          S.card ≤ 2 * (S ∩ A).card + 1 ∧ S.card ≤ 2 * (S ∩ B).card + 1 := by
  obtain ⟨e, he⟩ := exists_pairing_meeting_bound heven S
  refine ⟨e, ?_⟩
  intro A B hsplit
  have hA := he A (fun i => by
    rcases hsplit i with h | h
    · exact ⟨false, h.1⟩
    · exact ⟨true, h.2⟩)
  have hB := he B (fun i => by
    rcases hsplit i with h | h
    · exact ⟨true, h.2⟩
    · exact ⟨false, h.1⟩)
  exact ⟨hA, hB, by omega, by omega⟩

end Overfull.OneCore.NeighborPairing
