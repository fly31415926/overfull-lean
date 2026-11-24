import Overfull.CompatibleCircuits.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Checked finite certificates for small compatible-circuit kernels

The five templates have four parallel copies, a doubled triangle, and the
four-label opposite multiplicities (3,1,0), (2,2,0), and (2,1,1).
There are 9 + 27 + 81 + 81 + 81 = 279 relevant local class assignments.

The 71 distinct circuit masks are checked once.  Each proposed decomposition
then records four circuit indices (the index 20 denotes an empty part).
All certificate theorems below are checked by Lean's kernel using `decide`.
No native evaluation is used as a proof.
-/

namespace Overfull.CompatibleCircuits.SmallKernel

open Finset

set_option Elab.async false

/-- Explicit first endpoints for eight indexed actual copies. -/
def first : Fin 5 → Fin 8 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 2, 2, 2, 0, 1], ![0, 0, 2, 2, 0, 0, 1, 1], ![0, 0, 2, 2, 0, 1, 0, 1]]

/-- Explicit second endpoints; copies beyond the template size are unused. -/
def second : Fin 5 → Fin 8 → Fin 4 :=
  ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 2, 2, 2, 2, 1, 1], ![1, 1, 1, 3, 3, 3, 2, 3], ![1, 1, 3, 3, 2, 2, 3, 3], ![1, 1, 3, 3, 2, 3, 3, 2]]

/-- Number of active actual copies. -/
def copyCount : Fin 5 → ℕ := ![4, 6, 8, 8, 8]

/-- Rank of an active incident copy among the four copies at its vertex. -/
def incidenceRank : Fin 5 → Fin 4 → Fin 8 → ℕ :=
  ![![![0, 1, 2, 3, 0, 0, 0, 0], ![0, 1, 2, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 2, 3, 0, 0, 0, 0], ![0, 1, 0, 0, 2, 3, 0, 0], ![0, 0, 0, 1, 2, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 2, 0, 0, 0, 3, 0], ![0, 1, 2, 0, 0, 0, 0, 3], ![0, 0, 0, 0, 1, 2, 3, 0], ![0, 0, 0, 0, 1, 2, 0, 3]], ![![0, 1, 0, 0, 2, 3, 0, 0], ![0, 1, 0, 0, 0, 0, 2, 3], ![0, 0, 0, 1, 2, 3, 0, 0], ![0, 0, 0, 1, 0, 0, 2, 3]], ![![0, 1, 0, 0, 2, 0, 3, 0], ![0, 1, 0, 0, 0, 2, 0, 3], ![0, 0, 0, 1, 2, 0, 0, 3], ![0, 0, 0, 1, 0, 2, 3, 0]]]

/-- Edge masks of all circuits of a template. -/
def circuitMasks : Fin 5 → Array ℕ :=
  ![#[3, 5, 6, 9, 10, 12], #[3, 12, 21, 22, 25, 26, 37, 38, 41, 42, 48], #[3, 5, 6, 24, 40, 48, 201, 202, 204, 209, 210, 212, 225, 226, 228], #[3, 12, 48, 85, 86, 89, 90, 101, 102, 105, 106, 149, 150, 153, 154, 165, 166, 169, 170, 192], #[3, 12, 53, 54, 57, 58, 84, 88, 97, 98, 145, 146, 164, 168, 197, 198, 201, 202, 240]]

/-- Four base-four digits.  At an incident vertex the digit records the unique
local pair partition that forbids the circuit; digit three means no incidence. -/
def deniedCodes : Fin 5 → Array ℕ :=
  ![#[240, 245, 250, 250, 245, 240], #[240, 204, 213, 218, 230, 233, 233, 230, 218, 213, 195], #[240, 245, 250, 15, 95, 175, 170, 165, 160, 90, 85, 80, 10, 5, 0], #[240, 15, 204, 85, 90, 165, 170, 102, 105, 150, 153, 153, 150, 105, 102, 170, 165, 90, 85, 51], #[240, 15, 85, 90, 165, 170, 156, 108, 54, 57, 201, 198, 99, 147, 170, 165, 90, 85, 0]]

/-- Four explicit circuit indices for every relevant class assignment. -/
def witnessRows : Fin 5 → Array (Array ℕ) :=
  ![#[#[1, 4, 20, 20], #[3, 2, 20, 20], #[1, 4, 20, 20], #[3, 2, 20, 20], #[0, 5, 20, 20], #[0, 5, 20, 20], #[1, 4, 20, 20], #[0, 5, 20, 20], #[0, 5, 20, 20]], #[#[2, 9, 20, 20], #[4, 7, 20, 20], #[2, 9, 20, 20], #[6, 5, 20, 20], #[8, 3, 20, 20], #[6, 5, 20, 20], #[2, 9, 20, 20], #[4, 7, 20, 20], #[2, 9, 20, 20], #[4, 7, 20, 20], #[4, 7, 20, 20], #[6, 5, 20, 20], #[6, 5, 20, 20], #[0, 1, 10, 20], #[0, 1, 10, 20], #[4, 7, 20, 20], #[0, 1, 10, 20], #[0, 1, 10, 20], #[2, 9, 20, 20], #[8, 3, 20, 20], #[2, 9, 20, 20], #[8, 3, 20, 20], #[0, 1, 10, 20], #[0, 1, 10, 20], #[2, 9, 20, 20], #[0, 1, 10, 20], #[0, 1, 10, 20]], #[#[1, 7, 5, 20], #[6, 2, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20], #[1, 10, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[1, 7, 5, 20], #[6, 2, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 7, 5, 20], #[0, 8, 5, 20], #[0, 8, 5, 20], #[1, 13, 3, 20], #[12, 2, 3, 20], #[1, 13, 3, 20], #[12, 2, 3, 20], #[0, 14, 3, 20], #[0, 14, 3, 20], #[1, 13, 3, 20], #[0, 14, 3, 20], #[0, 14, 3, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20], #[1, 10, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20], #[1, 13, 3, 20], #[12, 2, 3, 20], #[1, 13, 3, 20], #[12, 2, 3, 20], #[0, 14, 3, 20], #[0, 14, 3, 20], #[1, 13, 3, 20], #[0, 14, 3, 20], #[0, 14, 3, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[1, 10, 4, 20], #[9, 2, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20], #[1, 10, 4, 20], #[0, 11, 4, 20], #[0, 11, 4, 20]], #[#[3, 18, 20, 20], #[7, 14, 20, 20], #[3, 18, 20, 20], #[11, 10, 20, 20], #[15, 6, 20, 20], #[11, 10, 20, 20], #[3, 18, 20, 20], #[7, 14, 20, 20], #[3, 18, 20, 20], #[5, 16, 20, 20], #[7, 14, 20, 20], #[5, 16, 20, 20], #[13, 8, 20, 20], #[15, 6, 20, 20], #[13, 8, 20, 20], #[5, 16, 20, 20], #[7, 14, 20, 20], #[5, 16, 20, 20], #[3, 18, 20, 20], #[9, 12, 20, 20], #[3, 18, 20, 20], #[11, 10, 20, 20], #[17, 4, 20, 20], #[11, 10, 20, 20], #[3, 18, 20, 20], #[9, 12, 20, 20], #[3, 18, 20, 20], #[5, 16, 20, 20], #[9, 12, 20, 20], #[5, 16, 20, 20], #[11, 10, 20, 20], #[15, 6, 20, 20], #[11, 10, 20, 20], #[5, 16, 20, 20], #[9, 12, 20, 20], #[5, 16, 20, 20], #[5, 16, 20, 20], #[15, 6, 20, 20], #[5, 16, 20, 20], #[15, 6, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[5, 16, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[9, 12, 20, 20], #[9, 12, 20, 20], #[11, 10, 20, 20], #[11, 10, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[9, 12, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[3, 18, 20, 20], #[7, 14, 20, 20], #[3, 18, 20, 20], #[13, 8, 20, 20], #[17, 4, 20, 20], #[13, 8, 20, 20], #[3, 18, 20, 20], #[7, 14, 20, 20], #[3, 18, 20, 20], #[7, 14, 20, 20], #[7, 14, 20, 20], #[13, 8, 20, 20], #[13, 8, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[7, 14, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[3, 18, 20, 20], #[17, 4, 20, 20], #[3, 18, 20, 20], #[17, 4, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19], #[3, 18, 20, 20], #[0, 1, 2, 19], #[0, 1, 2, 19]], #[#[2, 17, 20, 20], #[14, 5, 20, 20], #[2, 17, 20, 20], #[14, 5, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[2, 17, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[4, 15, 20, 20], #[14, 5, 20, 20], #[4, 15, 20, 20], #[14, 5, 20, 20], #[0, 12, 7, 20], #[0, 12, 7, 20], #[4, 15, 20, 20], #[0, 12, 7, 20], #[0, 12, 7, 20], #[2, 17, 20, 20], #[16, 3, 20, 20], #[2, 17, 20, 20], #[16, 3, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[2, 17, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[4, 15, 20, 20], #[14, 5, 20, 20], #[4, 15, 20, 20], #[14, 5, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[4, 15, 20, 20], #[0, 6, 13, 20], #[0, 6, 13, 20], #[4, 15, 20, 20], #[8, 11, 1, 20], #[4, 15, 20, 20], #[10, 9, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[4, 15, 20, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[8, 11, 1, 20], #[8, 11, 1, 20], #[10, 9, 1, 20], #[10, 9, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[8, 11, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[2, 17, 20, 20], #[16, 3, 20, 20], #[2, 17, 20, 20], #[16, 3, 20, 20], #[0, 12, 7, 20], #[0, 12, 7, 20], #[2, 17, 20, 20], #[0, 12, 7, 20], #[0, 12, 7, 20], #[8, 11, 1, 20], #[8, 11, 1, 20], #[10, 9, 1, 20], #[10, 9, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[8, 11, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[2, 17, 20, 20], #[8, 11, 1, 20], #[2, 17, 20, 20], #[10, 9, 1, 20], #[0, 1, 18, 20], #[0, 1, 18, 20], #[2, 17, 20, 20], #[0, 1, 18, 20], #[0, 1, 18, 20]]]

/-- The selected actual copies of a canonical template. -/
def copies (kind : Fin 5) : Finset (Fin 8) :=
  univ.filter (fun e => e.val < copyCount kind)

/-- Computable incidence from the explicit endpoints. -/
def incident (kind : Fin 5) (v : Fin 4) (e : Fin 8) : Prop :=
  v = first kind e ∨ v = second kind e

instance (kind : Fin 5) (v : Fin 4) (e : Fin 8) :
    Decidable (incident kind v e) := by
  unfold incident
  infer_instance

/-- The three partitions of four ports into two pairs. -/
def pairClass (choice : Fin 3) (rank : ℕ) : Bool :=
  if choice = 0 then decide (rank < 2)
  else if choice = 1 then decide (rank % 2 = 0)
  else decide (rank = 0 ∨ rank = 3)

/-- Two forbidden incidence classes at each active vertex. -/
def classOf (kind : Fin 5) (choice : Fin 4 → Fin 3)
    (v : Fin 4) (e : Fin 8) : Bool :=
  pairClass (choice v) (incidenceRank kind v e)

/-- One candidate circuit as an actual finite set of copies. -/
def catalogPart (kind : Fin 5) (index : Fin 21) : Finset (Fin 8) :=
  univ.filter (fun e => Nat.testBit ((circuitMasks kind).getD index.val 0) e.val = true)

/-- The forbidden local choice for this circuit, or three at an unused vertex. -/
def deniedChoice (kind : Fin 5) (index : Fin 21) (v : Fin 4) : ℕ :=
  (deniedCodes kind).getD index.val 255 / 4 ^ v.val % 4

private def witnessIndex (kind : Fin 5) (choice : Fin 4 → Fin 3) : ℕ :=
  (choice 0).val + 3 * (choice 1).val +
    (if kind = 0 then 0 else 9 * (choice 2).val) +
    (if kind.val ≤ 1 then 0 else 27 * (choice 3).val)

/-- The indexed candidate circuit chosen in one slot of the certificate. -/
def witnessCircuit (kind : Fin 5) (choice : Fin 4 → Fin 3) (i : Fin 4) : Fin 21 :=
  ⟨((witnessRows kind).getD (witnessIndex kind choice) #[]).getD i.val 20 % 21,
    Nat.mod_lt _ (by decide)⟩

/-- One of the four candidate parts; empty slots will be discarded. -/
def witnessPart (kind : Fin 5) (choice : Fin 4 → Fin 3) (i : Fin 4) : Finset (Fin 8) :=
  catalogPart kind (witnessCircuit kind choice i)

/-- Computable incident vertex support. -/
def codeSupport (kind : Fin 5) (C : Finset (Fin 8)) : Finset (Fin 4) :=
  univ.filter (fun v => ∃ e ∈ C, incident kind v e)

/-- Computable degree within selected copies. -/
def codeDegree (kind : Fin 5) (C : Finset (Fin 8)) (v : Fin 4) : ℕ :=
  (C.filter (incident kind v)).card

/-- Computable cut using explicit endpoints. -/
def codeCut (kind : Fin 5) (C : Finset (Fin 8)) (X : Finset (Fin 4)) :
    Finset (Fin 8) :=
  C.filter (fun e => (first kind e ∈ X) ≠ (second kind e ∈ X))

/-- Computable version of the connected 2-regular condition. -/
def CodeCircuit (kind : Fin 5) (C : Finset (Fin 8)) : Prop :=
  C.Nonempty ∧
  (∀ v ∈ codeSupport kind C, codeDegree kind C v = 2) ∧
  ∀ X : Finset (Fin 4), X ⊆ codeSupport kind C → X.Nonempty →
    X ≠ codeSupport kind C → (codeCut kind C X).Nonempty

instance (kind : Fin 5) (C : Finset (Fin 8)) : Decidable (CodeCircuit kind C) := by
  unfold CodeCircuit
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Every nonempty catalogue entry is a genuine circuit according to the
computable endpoint checker. -/
theorem catalog_circuit : ∀ (kind : Fin 5) (index : Fin 21),
    (catalogPart kind index).Nonempty → CodeCircuit kind (catalogPart kind index) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Choosing any of the other two local pair partitions uses each local
incidence class at most once in this circuit. -/
theorem catalog_class_bound : ∀ (kind : Fin 5) (index : Fin 21)
    (v : Fin 4) (q : Fin 3), q.val ≠ deniedChoice kind index v →
    ∀ b : Bool, ((catalogPart kind index).filter (fun e =>
      incident kind v e ∧ pairClass q (incidenceRank kind v e) = b)).card ≤ 1 := by
  decide +kernel

private def WitnessValid (kind : Fin 5) (choice : Fin 4 → Fin 3) : Prop :=
    (univ.biUnion (witnessPart kind choice) = copies kind) ∧
    (∀ i j, i ≠ j → Disjoint (witnessPart kind choice i) (witnessPart kind choice j)) ∧
    (∀ i v, (choice v).val ≠ deniedChoice kind (witnessCircuit kind choice i) v)

private instance (kind : Fin 5) (choice : Fin 4 → Fin 3) :
    Decidable (WitnessValid kind choice) := by
  unfold WitnessValid
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem witness_valid_vector : ∀ (kind : Fin 5) (c₀ c₁ c₂ c₃ : Fin 3),
    WitnessValid kind ![c₀, c₁, c₂, c₃] := by
  intro kind c₀ c₁ c₂ c₃
  fin_cases kind <;> fin_cases c₀ <;> fin_cases c₁ <;>
    fin_cases c₂ <;> fin_cases c₃ <;> decide +kernel

/-- All 279 stored witnesses cover exactly the active copies, are disjoint,
and avoid the forbidden local pair choice at every vertex. -/
theorem witness_valid (kind : Fin 5) (choice : Fin 4 → Fin 3) :
    (univ.biUnion (witnessPart kind choice) = copies kind) ∧
    (∀ i j, i ≠ j → Disjoint (witnessPart kind choice i) (witnessPart kind choice j)) ∧
    (∀ i v, (choice v).val ≠ deniedChoice kind (witnessCircuit kind choice i) v) := by
  have h := witness_valid_vector kind (choice 0) (choice 1) (choice 2) (choice 3)
  have heq : ![choice 0, choice 1, choice 2, choice 3] = choice := by
    funext i
    fin_cases i <;> rfl
  simpa only [WitnessValid, heq] using h

/-- Every indexed edge has two different endpoint labels. -/
theorem endpoints_ne : ∀ (kind : Fin 5) (e : Fin 8),
    first kind e ≠ second kind e := by decide

end Overfull.CompatibleCircuits.SmallKernel

