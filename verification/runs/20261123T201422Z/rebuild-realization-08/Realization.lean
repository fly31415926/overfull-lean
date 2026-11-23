import Overfull.CircuitPatterns.Realization
import Overfull.AssignedParts.BoundaryCompression

/-!
# Realizing boundary slots with original multigraph copies

The special endpoints are prescribed, while the remaining endpoints are
chosen greedily. Injectivity here is injectivity of the original copy type.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {V E I R : Type*} (G : Multigraph V E)

def specialEnds (Z : Finset V) (e : E) : Finset V := (G.edge e).toFinset ∩ Z

def coreEnds (Z : Finset V) (e : E) : Finset V := (G.edge e).toFinset \ Z

@[simp] theorem mem_specialEnds (Z : Finset V) (e : E) (v : V) :
    v ∈ specialEnds G Z e ↔ v ∈ G.edge e ∧ v ∈ Z := by
  simp [specialEnds]

@[simp] theorem mem_coreEnds (Z : Finset V) (e : E) (v : V) :
    v ∈ coreEnds G Z e ↔ v ∈ G.edge e ∧ v ∉ Z := by
  simp [coreEnds]

theorem coreEnds_card_le_two (Z : Finset V) (e : E) :
    (coreEnds G Z e).card ≤ 2 := by
  calc
    _ ≤ (G.edge e).toFinset.card := card_le_card sdiff_subset
    _ = 2 := Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)

variable [Fintype I]

def chosenRound (round : I → R) (pick : I → E) (r : R) : Finset E :=
  (univ.filter (fun i => round i = r)).image pick

theorem mem_chosenRound (round : I → R) (pick : I → E) (r : R) (e : E) :
    e ∈ chosenRound round pick r ↔ ∃ i, round i = r ∧ pick i = e := by
  simp [chosenRound]

theorem chosenRound_pairwiseDisjoint (round : I → R) (pick : I → E)
    (hinj : Function.Injective pick) :
    Pairwise (fun r s => Disjoint (chosenRound round pick r) (chosenRound round pick s)) := by
  intro r s hrs
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨i, hi, hie⟩ := (mem_chosenRound round pick r e).mp he
  obtain ⟨j, hj, hje⟩ := (mem_chosenRound round pick s e).mp hf
  have hij := hinj (hie.trans hje.symm)
  exact hrs (hi.symm.trans (hij ▸ hj))

theorem chosenRound_isMatching (Z : Finset V) (round : I → R) (pick : I → E)
    (hspecial : ∀ i j, i ≠ j → round i = round j →
      Disjoint (specialEnds G Z (pick i)) (specialEnds G Z (pick j)))
    (hcore : ∀ i j, i ≠ j → round i = round j →
      Disjoint (coreEnds G Z (pick i)) (coreEnds G Z (pick j))) (r : R) :
    G.IsMatching (chosenRound round pick r) := by
  intro e he f hf v hev hfv
  obtain ⟨i, hi, rfl⟩ := (mem_chosenRound round pick r e).mp he
  obtain ⟨j, hj, rfl⟩ := (mem_chosenRound round pick r f).mp hf
  by_cases hij : i = j
  · exact congrArg pick hij
  · by_cases hv : v ∈ Z
    · exact (disjoint_left.mp (hspecial i j hij (hi.trans hj.symm))
        ((mem_specialEnds G Z _ _).mpr ⟨hev, hv⟩)
        ((mem_specialEnds G Z _ _).mpr ⟨hfv, hv⟩)).elim
    · exact (disjoint_left.mp (hcore i j hij (hi.trans hj.symm))
        ((mem_coreEnds G Z _ _).mpr ⟨hev, hv⟩)
        ((mem_coreEnds G Z _ _).mpr ⟨hfv, hv⟩)).elim

end Overfull.NativeReserve
