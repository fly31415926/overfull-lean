import Overfull.Multigraph
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

namespace Overfull.Compression

open Finset
open scoped BigOperators

/-- The six unordered pairs of distinct labels among four labels. -/
abbrev LabelPair := {P : Finset (Fin 4) // P.card = 2}

def pairDegree (P : Finset LabelPair) (i : Fin 4) : ℕ :=
  (P.filter (fun e => i ∈ e.val)).card

/-- Every nonempty edge subgraph has a leaf, the finite forest criterion. -/
def LeafForest (P : Finset LabelPair) : Prop :=
  ∀ Q : Finset LabelPair, Q ⊆ P → Q.Nonempty → ∃ i : Fin 4, pairDegree Q i = 1

instance (P : Finset LabelPair) : Decidable (LeafForest P) := by
  unfold LeafForest
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite assertion is checked by Lean's kernel over the six actual
unordered pairs. No external computation or native decision axiom is used. -/
theorem four_label_parity_forest :
    ∀ P : Finset LabelPair, ∃ Q : Finset LabelPair,
      Q ⊆ P ∧ Q.card ≤ 3 ∧
      (∀ i : Fin 4, pairDegree Q i % 2 = pairDegree P i % 2) ∧ LeafForest Q := by
  decide

open Classical

variable {α : Type*} [DecidableEq α]

def copyDegree (E : Finset α) (label : α → LabelPair) (i : Fin 4) : ℕ :=
  (E.filter (fun e => i ∈ (label e).val)).card

def oddPairs (E : Finset α) (label : α → LabelPair) : Finset LabelPair :=
  univ.filter (fun p => (E.filter (fun e => label e = p)).card % 2 = 1)

omit [DecidableEq α] in
theorem oddPairs_degree_parity (E : Finset α) (label : α → LabelPair) (i : Fin 4) :
    pairDegree (oddPairs E label) i % 2 = copyDegree E label i % 2 := by
  let A : Finset LabelPair := univ.filter (fun p => i ∈ p.val)
  have hfiber : copyDegree E label i =
      ∑ p ∈ A, (E.filter (fun e => label e = p)).card := by
    symm
    simpa [A, copyDegree] using Finset.sum_card_fiberwise_eq_card_filter E A label
  have hp : pairDegree (oddPairs E label) i =
      ∑ p ∈ A, (E.filter (fun e => label e = p)).card % 2 := by
    have hset : (oddPairs E label).filter (fun p => i ∈ p.val) =
        A.filter (fun p => (E.filter (fun e => label e = p)).card % 2 = 1) := by
      ext p
      simp [oddPairs, A, and_comm]
    rw [pairDegree, hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    have hmod := Nat.mod_lt (E.filter (fun e => label e = p)).card (by norm_num : 0 < 2)
    split_ifs <;> omega
  rw [hp, hfiber]
  exact (Finset.sum_nat_mod A 2 (fun p => (E.filter (fun e => label e = p)).card)).symm

/-- Actual edge copies can be selected, not merely their projected labels.
The selected projection is injective and satisfies the forest criterion. -/
theorem exists_parity_subset (E : Finset α) (label : α → LabelPair) :
    ∃ T : Finset α, T ⊆ E ∧ T.card ≤ 3 ∧
      (∀ i : Fin 4, copyDegree T label i % 2 = copyDegree E label i % 2) ∧
      Set.InjOn label T ∧ LeafForest (T.image label) := by
  obtain ⟨Q, hQP, hQcard, hQparity, hQforest⟩ := four_label_parity_forest (oddPairs E label)
  have hrep (p : Q) : ∃ e, e ∈ E ∧ label e = p.val := by
    have hp : (E.filter (fun e => label e = p.val)).card % 2 = 1 :=
      (Finset.mem_filter.mp (hQP p.property)).2
    have hpos : 0 < (E.filter (fun e => label e = p.val)).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  choose pick hpickE hpicklabel using hrep
  have hpick : Function.Injective pick := by
    intro p q hpq
    apply Subtype.ext
    rw [← hpicklabel p, ← hpicklabel q, hpq]
  let T := (univ : Finset Q).image pick
  have hTE : T ⊆ E := by
    intro e he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact hpickE p
  have hTcard : T.card ≤ 3 := by
    calc
      _ ≤ (univ : Finset Q).card := Finset.card_image_le
      _ = Q.card := by simp
      _ ≤ 3 := hQcard
  have hTlabel : T.image label = Q := by
    ext p
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, ⟨q, rfl⟩, he⟩
      rw [hpicklabel q] at he
      exact he ▸ q.property
    · intro hp
      exact ⟨pick ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, hpicklabel ⟨p, hp⟩⟩
  have hdegree (i : Fin 4) : copyDegree T label i = pairDegree Q i := by
    simp only [copyDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
    change (∑ e ∈ (univ : Finset Q).image pick, if i ∈ (label e).val then 1 else 0) = _
    rw [Finset.sum_image (fun p _ q _ h => hpick h)]
    simp only [hpicklabel]
    rw [Finset.univ_eq_attach]
    change (∑ x ∈ Q.attach, (fun p : LabelPair => if i ∈ p.val then (1 : ℕ) else 0) x.val) = _
    rw [@Finset.sum_attach LabelPair ℕ _ Q (fun p : LabelPair => if i ∈ p.val then 1 else 0)]
    simp only [pairDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine ⟨T, hTE, hTcard, ?_, ?_, ?_⟩
  · intro i
    rw [hdegree i, hQparity i, oddPairs_degree_parity]
  · intro e he f hf hef
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hf
    have hpq : p = q := Subtype.ext (by simpa only [hpicklabel] using hef)
    exact congrArg pick hpq
  · rw [hTlabel]
    exact hQforest

end Overfull.Compression
