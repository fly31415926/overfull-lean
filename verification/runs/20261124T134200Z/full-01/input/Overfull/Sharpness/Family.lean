import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
The actual simple graph constructed in Proposition 7.1 of the manuscript.

The vertices `(i,a)` are the four clique copies, with `a = 0` denoting `u_i`
and `a = 1` denoting `v_i`; the five additional vertices are the right summand.
The clique indices here run from zero to three, so clique `i` is attached to
the additional vertex `i + 1`. All degree results below hold for every
`Δ ≥ 3`, without requiring the parity needed for the coloring obstruction.

This file does not assert the class-2 or odd-set conclusions of Proposition 7.1.
-/

namespace Overfull.Sharpness.Family

open scoped BigOperators

abbrev Vertex (Δ : ℕ) := (Fin 4 × Fin Δ) ⊕ Fin 5

def Adjacent (Δ : ℕ) : Vertex Δ → Vertex Δ → Prop
  | .inl (i, a), .inl (j, b) =>
      (i = j ∧ a ≠ b) ∨
      (i.val + 1 = j.val ∧ a.val = 1 ∧ b.val = 0) ∨
      (j.val + 1 = i.val ∧ b.val = 1 ∧ a.val = 0)
  | .inl (i, a), .inr w => 2 ≤ a.val ∧ w.val = i.val + 1
  | .inr w, .inl (i, a) => 2 ≤ a.val ∧ w.val = i.val + 1
  | .inr w, .inr z => z.val = (w.val + 2) % 5 ∨ w.val = (z.val + 2) % 5

theorem adjacent_symmetric (Δ : ℕ) : Symmetric (Adjacent Δ) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      rcases x with ⟨i, a⟩
      rcases y with ⟨j, b⟩
      rcases h with h | h | h
      · exact Or.inl ⟨h.1.symm, h.2.symm⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    | inr y => exact h
  | inr x =>
    cases y with
    | inl y => exact h
    | inr y => exact h.symm

theorem adjacent_irreflexive (Δ : ℕ) : Irreflexive (Adjacent Δ) := by
  intro x h
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    rcases h with h | h | h
    · exact h.2 rfl
    · omega
    · omega
  | inr w =>
    have hw := w.isLt
    change w.val = (w.val + 2) % 5 ∨ w.val = (w.val + 2) % 5 at h
    omega

def graph (Δ : ℕ) : SimpleGraph (Vertex Δ) where
  Adj := Adjacent Δ
  symm := adjacent_symmetric Δ
  loopless := adjacent_irreflexive Δ

instance (Δ : ℕ) : DecidableRel (graph Δ).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [graph, Adjacent] <;> infer_instance

@[simp] theorem vertex_count (Δ : ℕ) : Fintype.card (Vertex Δ) = 4 * Δ + 5 := by
  simp [Vertex, Fintype.card_sum, Fintype.card_prod]

def u {Δ : ℕ} (hΔ : 3 ≤ Δ) : Fin Δ := ⟨0, by omega⟩
def v {Δ : ℕ} (hΔ : 3 ≤ Δ) : Fin Δ := ⟨1, by omega⟩

@[simp] theorem u_val {Δ : ℕ} (hΔ : 3 ≤ Δ) : (u hΔ).val = 0 := rfl
@[simp] theorem v_val {Δ : ℕ} (hΔ : 3 ≤ Δ) : (v hΔ).val = 1 := rfl

def spoke (i : Fin 4) : Fin 5 := ⟨i.val + 1, by omega⟩

def cliqueNeighbors {Δ : ℕ} (i : Fin 4) (a : Fin Δ) : Finset (Vertex Δ) :=
  (Finset.univ.erase a).image (fun b => Sum.inl (i, b))

@[simp] theorem mem_cliqueNeighbors {Δ : ℕ} (i j : Fin 4) (a b : Fin Δ) :
    Sum.inl (j, b) ∈ cliqueNeighbors i a ↔ i = j ∧ a ≠ b := by
  simp [cliqueNeighbors, and_comm, eq_comm]

@[simp] theorem inr_not_mem_cliqueNeighbors {Δ : ℕ} (i : Fin 4) (a : Fin Δ)
    (w : Fin 5) : Sum.inr w ∉ cliqueNeighbors i a := by
  simp [cliqueNeighbors]

theorem cliqueNeighbors_card {Δ : ℕ} (i : Fin 4) (a : Fin Δ) :
    (cliqueNeighbors i a).card = Δ - 1 := by
  have hi : Function.Injective (fun b : Fin Δ => (Sum.inl (i, b) : Vertex Δ)) := by
    intro b c h
    simpa using h
  simp [cliqueNeighbors, Finset.card_image_of_injective _ hi]

theorem degree_other_clique_vertex {Δ : ℕ} (i : Fin 4) (a : Fin Δ)
    (ha : 2 ≤ a.val) : (graph Δ).degree (Sum.inl (i, a)) = Δ := by
  have hN : (graph Δ).neighborFinset (Sum.inl (i, a)) =
      insert (Sum.inr (spoke i)) (cliqueNeighbors i a) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      simp only [SimpleGraph.mem_neighborFinset, graph, Adjacent,
        Finset.mem_insert,
        mem_cliqueNeighbors, Sum.inl_ne_inr, false_or]
      have ha0 : a.val ≠ 0 := by omega
      have ha1 : a.val ≠ 1 := by omega
      simp [ha0, ha1]
    | inr w =>
      simp [graph, Adjacent, ha, spoke, Fin.ext_iff]
  rw [SimpleGraph.degree, hN, Finset.card_insert_of_notMem]
  · rw [cliqueNeighbors_card]
    have := a.isLt
    omega
  · exact inr_not_mem_cliqueNeighbors i a (spoke i)

theorem degree_first_u {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    (graph Δ).degree (Sum.inl (0, u hΔ)) = Δ - 1 := by
  have hN : (graph Δ).neighborFinset (Sum.inl (0, u hΔ)) =
      cliqueNeighbors 0 (u hΔ) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      simp [graph, Adjacent, u, mem_cliqueNeighbors]
    | inr w => simp [graph, Adjacent, u]
  rw [SimpleGraph.degree, hN, cliqueNeighbors_card]

theorem degree_last_v {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    (graph Δ).degree (Sum.inl (3, v hΔ)) = Δ - 1 := by
  have hN : (graph Δ).neighborFinset (Sum.inl (3, v hΔ)) =
      cliqueNeighbors 3 (v hΔ) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      have hj : j.val ≠ 4 := by omega
      simp [graph, Adjacent, v, hj, eq_comm]
    | inr w => simp [graph, Adjacent, v]
  rw [SimpleGraph.degree, hN, cliqueNeighbors_card]

def predecessor (i : Fin 4) (hi : 0 < i.val) : Fin 4 :=
  ⟨i.val - 1, by omega⟩

def successor (i : Fin 4) (hi : i.val < 3) : Fin 4 :=
  ⟨i.val + 1, by omega⟩

theorem degree_u {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) (hi : 0 < i.val) :
    (graph Δ).degree (Sum.inl (i, u hΔ)) = Δ := by
  let x : Vertex Δ := Sum.inl (predecessor i hi, v hΔ)
  have hx : x ∉ cliqueNeighbors i (u hΔ) := by
    intro hx
    have heq := ((mem_cliqueNeighbors i (predecessor i hi) (u hΔ) (v hΔ)).mp hx).1
    have := congrArg Fin.val heq
    dsimp [predecessor] at this
    omega
  have hN : (graph Δ).neighborFinset (Sum.inl (i, u hΔ)) =
      insert x (cliqueNeighbors i (u hΔ)) := by
    ext y
    cases y with
    | inl y =>
      rcases y with ⟨j, b⟩
      simp [graph, Adjacent, x, u, v, predecessor, Fin.ext_iff]
      omega
    | inr w => simp [graph, Adjacent, x, u]
  rw [SimpleGraph.degree, hN, Finset.card_insert_of_notMem hx, cliqueNeighbors_card]
  omega

theorem degree_v {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) (hi : i.val < 3) :
    (graph Δ).degree (Sum.inl (i, v hΔ)) = Δ := by
  let x : Vertex Δ := Sum.inl (successor i hi, u hΔ)
  have hx : x ∉ cliqueNeighbors i (v hΔ) := by
    intro hx
    have heq := ((mem_cliqueNeighbors i (successor i hi) (v hΔ) (u hΔ)).mp hx).1
    have := congrArg Fin.val heq
    dsimp [successor] at this
    omega
  have hN : (graph Δ).neighborFinset (Sum.inl (i, v hΔ)) =
      insert x (cliqueNeighbors i (v hΔ)) := by
    ext y
    cases y with
    | inl y =>
      rcases y with ⟨j, b⟩
      simp [graph, Adjacent, x, u, v, successor, Fin.ext_iff]
      omega
    | inr w => simp [graph, Adjacent, x, v]
  rw [SimpleGraph.degree, hN, Finset.card_insert_of_notMem hx, cliqueNeighbors_card]
  omega

def innerNeighbors {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) : Finset (Vertex Δ) :=
  ((Finset.univ.erase (u hΔ)).erase (v hΔ)).image (fun a => Sum.inl (i, a))

@[simp] theorem mem_innerNeighbors {Δ : ℕ} (hΔ : 3 ≤ Δ) (i j : Fin 4)
    (a : Fin Δ) : Sum.inl (j, a) ∈ innerNeighbors hΔ i ↔ i = j ∧ 2 ≤ a.val := by
  simp only [innerNeighbors, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hba⟩
    rcases Prod.mk.inj (Sum.inl.inj hba) with ⟨hij, hba'⟩
    subst b
    have h1 : a ≠ v hΔ := (Finset.mem_erase.mp hb).1
    have h0 : a ≠ u hΔ :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
    have h0' : a.val ≠ 0 := fun heq => h0 (Fin.ext heq)
    have h1' : a.val ≠ 1 := fun heq => h1 (Fin.ext heq)
    exact ⟨hij, by omega⟩
  · rintro ⟨rfl, ha⟩
    refine ⟨a, ?_, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hav
      have := congrArg Fin.val hav
      simp only [v_val] at this
      omega
    · intro hau
      have := congrArg Fin.val hau
      simp only [u_val] at this
      omega

@[simp] theorem inr_not_mem_innerNeighbors {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4)
    (w : Fin 5) : Sum.inr w ∉ innerNeighbors hΔ i := by
  simp [innerNeighbors]

theorem innerNeighbors_card {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) :
    (innerNeighbors hΔ i).card = Δ - 2 := by
  have hi : Function.Injective (fun a : Fin Δ => (Sum.inl (i, a) : Vertex Δ)) := by
    intro a b h
    simpa using h
  have hv : v hΔ ∈ Finset.univ.erase (u hΔ) := by
    simp [Finset.mem_erase, u, v, Fin.ext_iff]
  rw [innerNeighbors, Finset.card_image_of_injective _ hi,
    Finset.card_erase_of_mem hv, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

def nextCycle (w : Fin 5) : Fin 5 := ⟨(w.val + 2) % 5, by omega⟩
def prevCycle (w : Fin 5) : Fin 5 := ⟨(w.val + 3) % 5, by omega⟩

theorem degree_w_zero (Δ : ℕ) : (graph Δ).degree (Sum.inr 0) = 2 := by
  have hN : (graph Δ).neighborFinset (Sum.inr 0) =
      {Sum.inr 2, Sum.inr 3} := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨i, a⟩
      simp [graph, Adjacent]
    | inr w => fin_cases w <;> simp [graph, Adjacent]
  rw [SimpleGraph.degree, hN]
  simp [Fin.ext_iff]

theorem degree_spoke {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) :
    (graph Δ).degree (Sum.inr (spoke i)) = Δ := by
  let x : Vertex Δ := Sum.inr (nextCycle (spoke i))
  let y : Vertex Δ := Sum.inr (prevCycle (spoke i))
  have hxy : x ≠ y := by
    fin_cases i <;> simp [x, y, nextCycle, prevCycle, spoke, Fin.ext_iff]
  have hy : y ∉ innerNeighbors hΔ i := inr_not_mem_innerNeighbors hΔ i _
  have hx : x ∉ insert y (innerNeighbors hΔ i) := by
    simp [hxy, x, inr_not_mem_innerNeighbors]
  have hN : (graph Δ).neighborFinset (Sum.inr (spoke i)) =
      insert x (insert y (innerNeighbors hΔ i)) := by
    ext z
    cases z with
    | inl z =>
      rcases z with ⟨j, a⟩
      simp [graph, Adjacent, x, y, spoke, Fin.ext_iff, and_comm]
    | inr w =>
      fin_cases i <;> fin_cases w <;>
        simp [graph, Adjacent, x, y, spoke, nextCycle, prevCycle]
  rw [SimpleGraph.degree, hN, Finset.card_insert_of_notMem hx,
    Finset.card_insert_of_notMem hy, innerNeighbors_card]
  omega

theorem degree_clique_vertex {Δ : ℕ} (hΔ : 3 ≤ Δ) (i : Fin 4) (a : Fin Δ) :
    (graph Δ).degree (Sum.inl (i, a)) =
      if (i.val = 0 ∧ a.val = 0) ∨ (i.val = 3 ∧ a.val = 1) then Δ - 1 else Δ := by
  by_cases ha0 : a.val = 0
  · have ha : a = u hΔ := Fin.ext ha0
    subst a
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst i
      simpa using degree_first_u hΔ
    · have hi : 0 < i.val := by omega
      simpa [hi0] using degree_u hΔ i hi
  · by_cases ha1 : a.val = 1
    · have ha : a = v hΔ := Fin.ext ha1
      subst a
      by_cases hi3 : i.val = 3
      · have hi : i = 3 := Fin.ext hi3
        subst i
        simpa using degree_last_v hΔ
      · have hi : i.val < 3 := by omega
        simpa [hi3] using degree_v hΔ i hi
    · have ha : 2 ≤ a.val := by omega
      simpa [ha0, ha1] using degree_other_clique_vertex i a ha

theorem degree_additional_vertex {Δ : ℕ} (hΔ : 3 ≤ Δ) (w : Fin 5) :
    (graph Δ).degree (Sum.inr w) = if w.val = 0 then 2 else Δ := by
  by_cases hw : w.val = 0
  · have heq : w = 0 := Fin.ext hw
    subst w
    simpa using degree_w_zero Δ
  · let i : Fin 4 := ⟨w.val - 1, by have := w.isLt; omega⟩
    have heq : w = spoke i := by
      apply Fin.ext
      dsimp [spoke, i]
      omega
    rw [if_neg hw, heq]
    exact degree_spoke hΔ i

theorem maximum_degree {Δ : ℕ} (hΔ : 3 ≤ Δ) : (graph Δ).maxDegree = Δ := by
  apply Nat.le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro x
    cases x with
    | inl x =>
      rcases x with ⟨i, a⟩
      rw [degree_clique_vertex hΔ]
      split_ifs <;> omega
    | inr w =>
      rw [degree_additional_vertex hΔ]
      split_ifs <;> omega
  · let a : Fin Δ := ⟨2, by omega⟩
    have hd : (graph Δ).degree (Sum.inl (0, a)) = Δ :=
      degree_other_clique_vertex 0 a (by simp [a])
    calc
      Δ = (graph Δ).degree (Sum.inl (0, a)) := hd.symm
      _ ≤ (graph Δ).maxDegree := SimpleGraph.degree_le_maxDegree _ _

theorem additional_vertices_reachable (Δ : ℕ) (w : Fin 5) :
    (graph Δ).Reachable (Sum.inr 0) (Sum.inr w) := by
  have h02 : (graph Δ).Adj (Sum.inr 0) (Sum.inr 2) := by simp [graph, Adjacent]
  have h24 : (graph Δ).Adj (Sum.inr 2) (Sum.inr 4) := by simp [graph, Adjacent]
  have h03 : (graph Δ).Adj (Sum.inr 0) (Sum.inr 3) := by simp [graph, Adjacent]
  have h31 : (graph Δ).Adj (Sum.inr 3) (Sum.inr 1) := by simp [graph, Adjacent]
  fin_cases w
  · exact SimpleGraph.Reachable.rfl
  · exact h03.reachable.trans h31.reachable
  · exact h02.reachable
  · exact h03.reachable
  · exact h02.reachable.trans h24.reachable

theorem clique_vertex_reaches_spoke {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (i : Fin 4) (a : Fin Δ) :
    (graph Δ).Reachable (Sum.inl (i, a)) (Sum.inr (spoke i)) := by
  by_cases ha : 2 ≤ a.val
  · apply SimpleGraph.Adj.reachable
    exact ⟨ha, rfl⟩
  · let b : Fin Δ := ⟨2, by omega⟩
    have hab : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      dsimp [b] at this
      omega
    have h1 : (graph Δ).Adj (Sum.inl (i, a)) (Sum.inl (i, b)) :=
      Or.inl ⟨rfl, hab⟩
    have h2 : (graph Δ).Adj (Sum.inl (i, b)) (Sum.inr (spoke i)) := by
      exact ⟨by simp [b], rfl⟩
    exact h1.reachable.trans h2.reachable

theorem connected {Δ : ℕ} (hΔ : 3 ≤ Δ) : (graph Δ).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨Sum.inr 0, ?_⟩
  intro x
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    exact (additional_vertices_reachable Δ (spoke i)).trans
      (clique_vertex_reaches_spoke hΔ i a).symm
  | inr w => exact additional_vertices_reachable Δ w

theorem degree_deficiency_identity {Δ : ℕ} (hΔ : 3 ≤ Δ) (x : Vertex Δ) :
    (graph Δ).degree x +
      (if x = Sum.inl (0, u hΔ) then 1 else 0) +
      (if x = Sum.inl (3, v hΔ) then 1 else 0) +
      (if x = Sum.inr 0 then Δ - 2 else 0) = Δ := by
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    rw [degree_clique_vertex hΔ]
    simp only [Sum.inl.injEq, Prod.mk.injEq, Sum.inl_ne_inr,
      if_false, add_zero, Fin.ext_iff, u_val, v_val]
    split_ifs <;> omega
  | inr w =>
    rw [degree_additional_vertex hΔ]
    simp only [Sum.inr_ne_inl, Sum.inr.injEq, if_false, add_zero, Fin.ext_iff]
    split_ifs <;> omega

theorem degree_sum {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    ∑ x : Vertex Δ, (graph Δ).degree x = 4 * Δ * (Δ + 1) := by
  have hs :
      (∑ x : Vertex Δ, ((graph Δ).degree x +
        (if x = Sum.inl (0, u hΔ) then 1 else 0) +
        (if x = Sum.inl (3, v hΔ) then 1 else 0) +
        (if x = Sum.inr 0 then Δ - 2 else 0))) =
        ∑ _ : Vertex Δ, Δ := by
    apply Finset.sum_congr rfl
    intro x _
    exact degree_deficiency_identity hΔ x
  simp [Finset.sum_add_distrib] at hs
  have hsub : Δ - 2 + 2 = Δ := by omega
  rw [Fintype.sum_sum_type]
  nlinarith [hs, hsub]

theorem edge_count {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    (graph Δ).edgeFinset.card = 2 * Δ * (Δ + 1) := by
  have hs := (graph Δ).sum_degrees_eq_twice_card_edges
  rw [degree_sum hΔ] at hs
  nlinarith [hs]

end Overfull.Sharpness.Family
