import Overfull.BoundedExterior.ReserveLabels
import Overfull.BoundedExterior.ExteriorClasses
import Mathlib.Data.Finset.Powerset

/-!
# Choosing a common exterior split and its reserved labels

Each label with a balanced core footprint admits a balanced exterior split.
The exterior has bounded size, so pigeonholing these actual splits leaves a
linear set of labels crossing one common cut.  The first group of labels is
then chosen in the complement of this reserve.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}

/-- A reserve of original color labels crossing one balanced exterior split. -/
structure OriginalReserve (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (A : Finset U) {h : ℕ} (labels : Fin h ↪ Fin k) (s : ℕ) where
  J : Finset (Fin k)
  reserved_card : J.card = reserveCount k s
  avoid : ∀ i ∈ J, i ∉ Set.range labels
  ZA : Finset V
  ZB : Finset V
  disjoint : Disjoint ZA ZB
  cover : ZA ∪ ZB = Uᶜ
  balance : ZA.card = ZB.card
  crossing : ∀ i ∈ J, ∀ e ∈ exteriorClass U c i,
    e ∈ G.cutEdges (A.map (Function.Embedding.subtype (fun v => v ∈ U)) ∪ ZA)

/-- Pigeonhole balanced footprints into one balanced exterior split and choose
the first labels only after retaining its reserve. -/
theorem exists_originalReserve (C : Core G U)
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (A B : Finset U) (s h : ℕ) (hregular : ∀ v, G.degree v = k)
    (hZcard : Uᶜ.card ≤ s) (hlarge : 2 * reserveDenominator s ≤ k)
    (hAB : Disjoint A B) (hcover : A ∪ B = univ)
    (hmany : k ≤ 2 ^ (s + 1) *
      (univ.filter (fun i : Fin k =>
        (coreFootprintSubtype G U (exteriorClass U c i) ∩ A).card =
        (coreFootprintSubtype G U (exteriorClass U c i) ∩ B).card)).card)
    (hupper : (h : ℝ) ≤ 3 * k / 5) :
    ∃ labels : Fin h ↪ Fin k, Nonempty (OriginalReserve C c A labels s) := by
  let good : Finset (Fin k) := univ.filter (fun i =>
    (coreFootprintSubtype G U (exteriorClass U c i) ∩ A).card =
    (coreFootprintSubtype G U (exteriorClass U c i) ∩ B).card)
  have hsplit : ∀ i : good, ∃ ZA ZB : Finset V,
      Disjoint ZA ZB ∧ ZA ∪ ZB = Uᶜ ∧ ZA.card = ZB.card ∧
        ∀ e ∈ exteriorClass U c i.val,
          e ∈ G.cutEdges (A.map (Function.Embedding.subtype (fun v => v ∈ U)) ∪ ZA) := by
    intro i
    exact coreComplement_exteriorClass_split C c A B hregular hAB hcover i.val
      (mem_filter.mp i.property).2
  choose ZA ZB hs using hsplit
  have hmap : ∀ i ∈ (univ : Finset good), ZA i ∈ Uᶜ.powerset := by
    intro i _
    apply mem_powerset.mpr
    intro z hz
    rw [← (hs i).2.1]
    exact mem_union_left _ hz
  have hcount : Uᶜ.powerset.card * reserveCount k s ≤ (univ : Finset good).card := by
    rw [card_powerset, card_univ, Fintype.card_coe]
    have hpow : (2 : ℕ) ^ Uᶜ.card ≤ 2 ^ s :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hZcard
    apply (Nat.mul_le_mul_right (reserveCount k s) hpow).trans
    apply le_of_mul_le_mul_left (a := 2 ^ (s + 1)) ?_ (by positivity)
    calc
      2 ^ (s + 1) * (2 ^ s * reserveCount k s) =
          reserveCount k s * (2 ^ (s + 1) * 2 ^ s) := by ring
      _ ≤ reserveCount k s * (8 * (2 ^ (s + 1) * 2 ^ s)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = reserveCount k s * reserveDenominator s := by rw [reserveDenominator_factor]
      _ ≤ k := reserveCount_mul_le k s
      _ ≤ 2 ^ (s + 1) * good.card := hmany
  obtain ⟨Z, _hZ, hZmany⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmap
      (show Uᶜ.powerset.Nonempty from ⟨∅, by simp⟩) hcount
  obtain ⟨K, hKsub, hKcard⟩ := exists_subset_card_eq hZmany
  have hKpos : 0 < K.card := by
    rw [hKcard]
    exact reserveCount_pos_of_large k s hlarge
  obtain ⟨j, hj⟩ := card_pos.mp hKpos
  have hjZ : ZA j = Z := (mem_filter.mp (hKsub hj)).2
  let J : Finset (Fin k) := K.map (Function.Embedding.subtype (fun i => i ∈ good))
  have hJcard : J.card = reserveCount k s := by
    simp only [J, card_map, hKcard]
  obtain ⟨labels, havoid⟩ := exists_labels_avoiding_reserve J hJcard hupper
  refine ⟨labels, ⟨{
    J := J
    reserved_card := hJcard
    avoid := havoid
    ZA := ZA j
    ZB := ZB j
    disjoint := (hs j).1
    cover := (hs j).2.1
    balance := (hs j).2.2.1
    crossing := ?_
  }⟩⟩
  intro i hi e he
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
  have haZ : ZA a = Z := (mem_filter.mp (hKsub ha)).2
  have hsame : ZA a = ZA j := haZ.trans hjZ.symm
  simpa only [hsame] using (hs a).2.2.2 e he

end Overfull.BoundedExterior
