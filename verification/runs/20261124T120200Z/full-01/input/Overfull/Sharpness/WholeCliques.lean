import Overfull.Sharpness.Family
import Overfull.Sharpness.Encoding
import Overfull.CutCounting
import Mathlib.Tactic

/-!
Counting induced edges when the vertex set contains every clique wholly or
not at all in the graph of Proposition 7.1.
-/

namespace Overfull.Sharpness.WholeCliques

open Family
open scoped BigOperators

def index {Δ : ℕ} : Vertex Δ → ℕ
  | .inl (i, _) => i.val + 1
  | .inr w => w.val + 5

def subset (Δ m : ℕ) : Finset (Vertex Δ) :=
  Finset.univ.filter (fun x => m.testBit (index x))

@[simp] theorem mem_subset_clique (Δ m : ℕ) (i : Fin 4) (a : Fin Δ) :
    Sum.inl (i, a) ∈ subset Δ m ↔ m.testBit (i.val + 1) = true := by
  simp [subset, index]

@[simp] theorem mem_subset_additional (Δ m : ℕ) (w : Fin 5) :
    Sum.inr w ∈ subset Δ m ↔ m.testBit (w.val + 5) = true := by
  simp [subset, index]

def cliqueCount (m : ℕ) : ℕ := bit m 1 + bit m 2 + bit m 3 + bit m 4
def additionalCount (m : ℕ) : ℕ :=
  bit m 5 + bit m 6 + bit m 7 + bit m 8 + bit m 9

theorem bit_zero_or_one (m j : ℕ) : bit m j = 0 ∨ bit m j = 1 := by
  unfold bit
  split <;> simp_all

theorem subset_card (Δ m : ℕ) :
    (subset Δ m).card = Δ * cliqueCount m + additionalCount m := by
  rw [Finset.card_eq_sum_ones]
  simp only [subset, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [index]
  change (∑ i : Fin 4, ∑ _a : Fin Δ, bit m (i.val + 1)) +
    (∑ w : Fin 5, bit m (w.val + 5)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  simp only [bit, cliqueCount, additionalCount]
  norm_cast
  ring

theorem sum_three_values {Δ : ℕ} (hΔ : 3 ≤ Δ) (A B C : ℕ) :
    (∑ a : Fin Δ, if a.val = 0 then A else if a.val = 1 then B else C) =
      A + B + (Δ - 2) * C := by
  let f : Fin Δ → ℕ := fun a => if a.val = 0 then A else if a.val = 1 then B else C
  let S : Finset (Fin Δ) := (Finset.univ.erase (u hΔ)).erase (v hΔ)
  have hv : v hΔ ∈ Finset.univ.erase (u hΔ) := by
    simp [Finset.mem_erase, u, v, Fin.ext_iff]
  have hcard : S.card = Δ - 2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hrest : ∑ a ∈ S, f a = (Δ - 2) * C := by
    calc
      ∑ a ∈ S, f a = ∑ _a ∈ S, C := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha1 : a ≠ v hΔ := (Finset.mem_erase.mp ha).1
        have ha0 : a ≠ u hΔ :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        have h0 : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
        have h1 : a.val ≠ 1 := fun h => ha1 (Fin.ext h)
        simp [f, h0, h1]
      _ = (Δ - 2) * C := by simp [hcard]
  have hs0 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (u hΔ))
  have hs1 := Finset.sum_erase_add (Finset.univ.erase (u hΔ)) f hv
  have hf0 : f (u hΔ) = A := by simp [f]
  have hf1 : f (v hΔ) = B := by simp [f]
  change (∑ a : Fin Δ, f a) = _
  change (∑ a ∈ S, f a) + f (v hΔ) = _ at hs1
  rw [hrest, hf1] at hs1
  rw [hf0] at hs0
  omega

theorem clique_neighbors_inter_card {Δ : ℕ} (m : ℕ) (i : Fin 4) (a : Fin Δ) :
    (cliqueNeighbors i a ∩ subset Δ m).card = (Δ - 1) * bit m (i.val + 1) := by
  have heq : cliqueNeighbors i a ∩ subset Δ m =
      if m.testBit (i.val + 1) then cliqueNeighbors i a else ∅ := by
    split_ifs with hm <;> ext x
    all_goals
      cases x with
      | inl x =>
        rcases x with ⟨j, b⟩
        by_cases hij : i = j
        · subst j
          simp [hm]
        · simp [hij]
      | inr w => simp
  rw [heq]
  by_cases h : m.testBit (i.val + 1) = true
  · simp [h, bit, cliqueNeighbors_card]
  · have hf : m.testBit (i.val + 1) = false := by simpa using h
    simp [hf, bit]

theorem inner_neighbors_inter_card {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) :
    (innerNeighbors hΔ i ∩ subset Δ m).card = (Δ - 2) * bit m (i.val + 1) := by
  have heq : innerNeighbors hΔ i ∩ subset Δ m =
      if m.testBit (i.val + 1) then innerNeighbors hΔ i else ∅ := by
    split_ifs with hm <;> ext x
    all_goals
      cases x with
      | inl x =>
        rcases x with ⟨j, b⟩
        by_cases hij : i = j
        · subst j
          simp [hm]
        · simp [hij]
      | inr w => simp
  rw [heq]
  by_cases h : m.testBit (i.val + 1) = true
  · simp [h, bit, innerNeighbors_card]
  · have hf : m.testBit (i.val + 1) = false := by simpa using h
    simp [hf, bit]

theorem card_insert_inter {α : Type*} [DecidableEq α] (x : α) (S X : Finset α)
    (hx : x ∉ S) :
    (insert x S ∩ X).card = (S ∩ X).card + if x ∈ X then 1 else 0 := by
  by_cases h : x ∈ X
  · rw [Finset.insert_inter_of_mem h, Finset.card_insert_of_notMem]
    · simp [h]
    · intro hin
      exact hx (Finset.mem_inter.mp hin).1
  · rw [Finset.insert_inter_of_notMem h]
    simp [h]

def localCount (Δ m : ℕ) (x : Vertex Δ) : ℕ :=
  ((graph Δ).neighborFinset x ∩ subset Δ m).card

theorem localCount_other {Δ : ℕ} (m : ℕ) (i : Fin 4) (a : Fin Δ)
    (ha : 2 ≤ a.val) :
    localCount Δ m (Sum.inl (i, a)) =
      (Δ - 1) * bit m (i.val + 1) + bit m (i.val + 6) := by
  have hN : (graph Δ).neighborFinset (Sum.inl (i, a)) =
      insert (Sum.inr (spoke i)) (cliqueNeighbors i a) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      simp only [SimpleGraph.mem_neighborFinset, graph, Adjacent,
        Finset.mem_insert, mem_cliqueNeighbors, Sum.inl_ne_inr, false_or]
      have ha0 : a.val ≠ 0 := by omega
      have ha1 : a.val ≠ 1 := by omega
      simp [ha0, ha1]
    | inr w => simp [graph, Adjacent, ha, spoke, Fin.ext_iff]
  unfold localCount
  rw [hN, card_insert_inter _ _ _ (inr_not_mem_cliqueNeighbors i a _),
    clique_neighbors_inter_card]
  simp [bit, spoke, Nat.add_assoc]

theorem localCount_first_u {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) :
    localCount Δ m (Sum.inl (0, u hΔ)) = (Δ - 1) * bit m 1 := by
  have hN : (graph Δ).neighborFinset (Sum.inl (0, u hΔ)) =
      cliqueNeighbors 0 (u hΔ) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      simp [graph, Adjacent, u, mem_cliqueNeighbors]
    | inr w => simp [graph, Adjacent, u]
  exact (congrArg (fun S => (S ∩ subset Δ m).card) hN).trans
    (clique_neighbors_inter_card m 0 (u hΔ))

theorem localCount_last_v {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) :
    localCount Δ m (Sum.inl (3, v hΔ)) = (Δ - 1) * bit m 4 := by
  have hN : (graph Δ).neighborFinset (Sum.inl (3, v hΔ)) =
      cliqueNeighbors 3 (v hΔ) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, b⟩
      have hj : j.val ≠ 4 := by omega
      simp [graph, Adjacent, v, hj, eq_comm]
    | inr w => simp [graph, Adjacent, v]
  exact (congrArg (fun S => (S ∩ subset Δ m).card) hN).trans
    (clique_neighbors_inter_card m 3 (v hΔ))

theorem localCount_u {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) (hi : 0 < i.val) :
    localCount Δ m (Sum.inl (i, u hΔ)) =
      (Δ - 1) * bit m (i.val + 1) + bit m i.val := by
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
  unfold localCount
  rw [hN, card_insert_inter _ _ _ hx, clique_neighbors_inter_card]
  have hi' : i.val - 1 + 1 = i.val := by omega
  simp [x, predecessor, hi', bit]

theorem localCount_v {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) (hi : i.val < 3) :
    localCount Δ m (Sum.inl (i, v hΔ)) =
      (Δ - 1) * bit m (i.val + 1) + bit m (i.val + 2) := by
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
  unfold localCount
  rw [hN, card_insert_inter _ _ _ hx, clique_neighbors_inter_card]
  simp [x, successor, bit, Nat.add_assoc]

theorem localCount_clique {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) (a : Fin Δ) :
    localCount Δ m (Sum.inl (i, a)) = (Δ - 1) * bit m (i.val + 1) +
      if a.val = 0 then (if i.val = 0 then 0 else bit m i.val)
      else if a.val = 1 then (if i.val = 3 then 0 else bit m (i.val + 2))
      else bit m (i.val + 6) := by
  by_cases ha0 : a.val = 0
  · have ha : a = u hΔ := Fin.ext ha0
    subst a
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst i
      simpa using localCount_first_u hΔ m
    · have hi : 0 < i.val := by omega
      simpa [hi0] using localCount_u hΔ m i hi
  · by_cases ha1 : a.val = 1
    · have ha : a = v hΔ := Fin.ext ha1
      subst a
      by_cases hi3 : i.val = 3
      · have hi : i = 3 := Fin.ext hi3
        subst i
        simpa using localCount_last_v hΔ m
      · have hi : i.val < 3 := by omega
        simpa [hi3] using localCount_v hΔ m i hi
    · have ha : 2 ≤ a.val := by omega
      simpa [ha0, ha1] using localCount_other m i a ha

theorem localCount_w_zero {Δ : ℕ} (m : ℕ) :
    localCount Δ m (Sum.inr 0) = bit m 7 + bit m 8 := by
  have hN : (graph Δ).neighborFinset (Sum.inr 0) =
      {Sum.inr 2, Sum.inr 3} := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨i, a⟩
      simp [graph, Adjacent]
    | inr w => fin_cases w <;> simp [graph, Adjacent]
  unfold localCount
  rw [hN, card_insert_inter _ _ _ (by simp [Fin.ext_iff])]
  by_cases h3 : m.testBit 8 = true
  · have hmem : (Sum.inr 3 : Vertex Δ) ∈ subset Δ m := by simpa using h3
    rw [Finset.singleton_inter_of_mem hmem]
    simp [bit, h3, Nat.add_comm]
  · have hmem : (Sum.inr 3 : Vertex Δ) ∉ subset Δ m := by simpa using h3
    rw [Finset.singleton_inter_of_notMem hmem]
    simp [bit, h3]

theorem localCount_spoke {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) :
    localCount Δ m (Sum.inr (spoke i)) =
      (Δ - 2) * bit m (i.val + 1) +
      bit m (((i.val + 1 + 2) % 5) + 5) +
      bit m (((i.val + 1 + 3) % 5) + 5) := by
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
  unfold localCount
  rw [hN, card_insert_inter _ _ _ hx, card_insert_inter _ _ _ hy,
    inner_neighbors_inter_card]
  simp [x, y, nextCycle, prevCycle, spoke, bit, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem localCount_additional {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (hm : bit m 0 = 0)
    (w : Fin 5) :
    localCount Δ m (Sum.inr w) =
      bit m (((w.val + 2) % 5) + 5) + bit m (((w.val + 3) % 5) + 5) +
      (Δ - 2) * bit m w.val := by
  by_cases hw : w.val = 0
  · have heq : w = 0 := Fin.ext hw
    subst w
    simpa [hm] using localCount_w_zero (Δ := Δ) m
  · let i : Fin 4 := ⟨w.val - 1, by have := w.isLt; omega⟩
    have heq : w = spoke i := by
      apply Fin.ext
      dsimp [spoke, i]
      omega
    rw [heq]
    have h := localCount_spoke hΔ m i
    change localCount Δ m (Sum.inr (spoke i)) = _
    change localCount Δ m (Sum.inr (spoke i)) =
      (Δ - 2) * bit m (i.val + 1) +
      bit m (((i.val + 1 + 2) % 5) + 5) +
      bit m (((i.val + 1 + 3) % 5) + 5) at h
    change localCount Δ m (Sum.inr (spoke i)) =
      bit m (((i.val + 1 + 2) % 5) + 5) +
      bit m (((i.val + 1 + 3) % 5) + 5) + (Δ - 2) * bit m (i.val + 1)
    omega

theorem bit_mul_self (m j : ℕ) : bit m j * bit m j = bit m j := by
  rcases bit_zero_or_one m j with h | h <;> simp [h]

theorem bit_sq (m j : ℕ) : bit m j ^ 2 = bit m j := by
  simpa only [pow_two] using bit_mul_self m j

theorem bit_mul (m j a : ℕ) : (if m.testBit j then a else 0) = bit m j * a := by
  unfold bit
  split <;> simp

theorem sum_localCount_clique {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (i : Fin 4) :
    (∑ a : Fin Δ, localCount Δ m (Sum.inl (i, a))) =
      Δ * (Δ - 1) * bit m (i.val + 1) +
      (if i.val = 0 then 0 else bit m i.val) +
      (if i.val = 3 then 0 else bit m (i.val + 2)) +
      (Δ - 2) * bit m (i.val + 6) := by
  simp_rw [localCount_clique hΔ]
  rw [Finset.sum_add_distrib, sum_three_values hΔ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  ring

def outerProducts (m : ℕ) : ℕ :=
  bit m 0 * bit m 1 + bit m 1 * bit m 2 + bit m 2 * bit m 3 +
  bit m 3 * bit m 4 + bit m 4 * bit m 0

def innerProducts (m : ℕ) : ℕ :=
  bit m 5 * bit m 7 + bit m 6 * bit m 8 + bit m 7 * bit m 9 +
  bit m 8 * bit m 5 + bit m 9 * bit m 6

def spokeProducts (m : ℕ) : ℕ :=
  bit m 0 * bit m 5 + bit m 1 * bit m 6 + bit m 2 * bit m 7 +
  bit m 3 * bit m 8 + bit m 4 * bit m 9

theorem internal_edge_count {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) (hm : bit m 0 = 0) :
    2 * (internalEdges (graph Δ) (subset Δ m)).card =
      Δ * (Δ - 1) * cliqueCount m +
      2 * (outerProducts m + innerProducts m + (Δ - 2) * spokeProducts m) := by
  classical
  rw [internal_degree_sum]
  simp only [subset, Finset.sum_filter]
  change (∑ x : Vertex Δ, if m.testBit (index x) then localCount Δ m x else 0) = _
  simp_rw [bit_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [index]
  simp_rw [← Finset.mul_sum, sum_localCount_clique hΔ,
    localCount_additional hΔ m hm]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, if_pos, if_neg,
    Nat.zero_ne_add_one] 
  unfold cliqueCount outerProducts innerProducts spokeProducts
  rw [hm]
  ring_nf
  simp only [bit_sq]
  ring

theorem bit_edge_identity (m i j : ℕ) :
    2 * (bit m i * bit m j) + crosses m i j = bit m i + bit m j := by
  rcases bit_zero_or_one m i with hi | hi <;>
    rcases bit_zero_or_one m j with hj | hj <;>
    simp [crosses, hi, hj]

theorem nonspoke_incidence_identity (m : ℕ) :
    2 * (outerProducts m + innerProducts m) + nonspokeCut m = 2 * vertexCount m := by
  have h01 := bit_edge_identity m 0 1
  have h12 := bit_edge_identity m 1 2
  have h23 := bit_edge_identity m 2 3
  have h34 := bit_edge_identity m 3 4
  have h40 := bit_edge_identity m 4 0
  have h57 := bit_edge_identity m 5 7
  have h68 := bit_edge_identity m 6 8
  have h79 := bit_edge_identity m 7 9
  have h85 := bit_edge_identity m 8 5
  have h96 := bit_edge_identity m 9 6
  unfold outerProducts innerProducts nonspokeCut vertexCount count5
  omega

theorem spoke_incidence_identity (m : ℕ) :
    2 * spokeProducts m + spokeCut m = vertexCount m := by
  have h05 := bit_edge_identity m 0 5
  have h16 := bit_edge_identity m 1 6
  have h27 := bit_edge_identity m 2 7
  have h38 := bit_edge_identity m 3 8
  have h49 := bit_edge_identity m 4 9
  unfold spokeProducts spokeCut vertexCount count5
  omega

theorem weighted_incidence_identity {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ) :
    2 * (outerProducts m + innerProducts m + (Δ - 2) * spokeProducts m) +
      (petersenCut m + (Δ - 3) * spokeCut m) = Δ * vertexCount m := by
  have hn := nonspoke_incidence_identity m
  have hs := spoke_incidence_identity m
  have hΔ2 : Δ - 2 + 2 = Δ := by omega
  have hΔ3 : Δ - 3 + 1 = Δ - 2 := by omega
  unfold petersenCut
  nlinarith

theorem vertexCount_eq (m : ℕ) (hm : bit m 0 = 0) :
    vertexCount m = cliqueCount m + additionalCount m := by
  simp only [vertexCount, count5, cliqueCount, additionalCount, hm]
  omega

theorem internal_edges_add_weighted_cut {Δ : ℕ} (hΔ : 3 ≤ Δ) (m : ℕ)
    (hm : bit m 0 = 0) :
    2 * (internalEdges (graph Δ) (subset Δ m)).card +
      (petersenCut m + (Δ - 3) * spokeCut m) = Δ * (subset Δ m).card := by
  rw [internal_edge_count hΔ m hm]
  have hw := weighted_incidence_identity hΔ m
  rw [vertexCount_eq m hm] at hw
  rw [subset_card]
  have hΔ1 : Δ - 1 + 1 = Δ := by omega
  calc
    _ = Δ * (Δ - 1) * cliqueCount m +
        (2 * (outerProducts m + innerProducts m + (Δ - 2) * spokeProducts m) +
          (petersenCut m + (Δ - 3) * spokeCut m)) := by ring
    _ = Δ * (Δ - 1) * cliqueCount m + Δ * (cliqueCount m + additionalCount m) := by
      rw [hw]
    _ = Δ * ((Δ - 1 + 1) * cliqueCount m + additionalCount m) := by ring
    _ = _ := by rw [hΔ1]

theorem degree_bound {Δ : ℕ} (hΔ : 3 ≤ Δ) (x : Vertex Δ) :
    (graph Δ).degree x ≤ Δ := by
  simpa only [maximum_degree hΔ] using SimpleGraph.degree_le_maxDegree (graph Δ) x

theorem subset_parity {Δ : ℕ} (hodd : Δ % 2 = 1) (m : ℕ) (hm : bit m 0 = 0) :
    (subset Δ m).card % 2 = vertexCount m % 2 := by
  rw [subset_card, vertexCount_eq m hm]
  simp [Nat.add_mod, Nat.mul_mod, hodd]

theorem subset_not_overfull {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (m : Fin 1024) (hm : bit m.val 0 = 0) :
    ¬ IsOverfull (graph Δ) Δ (subset Δ m.val) := by
  by_cases hcard : (subset Δ m.val).card % 2 = 1
  · have hoddm : vertexCount m.val % 2 = 1 := by
      rwa [subset_parity hodd m.val hm] at hcard
    have hcut := weighted_odd_cut Δ hΔ m hoddm
    have hid := internal_edges_add_weighted_cut hΔ m.val hm
    have hc : (subset Δ m.val).card = 2 * ((subset Δ m.val).card / 2) + 1 := by
      omega
    rw [hc, Nat.mul_add, Nat.mul_one] at hid
    unfold IsOverfull
    nlinarith only [hid, hcut]
  · exact not_overfull_of_even_card (graph Δ) (subset Δ m.val) Δ
      (degree_bound hΔ) (by omega)

def pairMask (a b : Fin 32) : Fin 1024 := ⟨32 * b.val + a.val, by omega⟩

theorem pairMask_low (a b : Fin 32) (j : Fin 5) :
    bit (pairMask a b).val j.val = bit a.val j.val := by
  unfold bit pairMask
  have hb : a.val < 2 ^ 5 := a.isLt
  have h := Nat.testBit_two_pow_mul_add b.val hb j.val
  change (if (2 ^ 5 * b.val + a.val).testBit j.val then 1 else 0) = _
  rw [h, if_pos j.isLt]

theorem pairMask_high (a b : Fin 32) (j : Fin 5) :
    bit (pairMask a b).val (j.val + 5) = bit b.val j.val := by
  unfold bit pairMask
  have hb : a.val < 2 ^ 5 := a.isLt
  have h := Nat.testBit_two_pow_mul_add b.val hb (j.val + 5)
  change (if (2 ^ 5 * b.val + a.val).testBit (j.val + 5) then 1 else 0) = _
  have hge : ¬ j.val + 5 < 5 := by omega
  simp only [h, if_neg hge, Nat.add_sub_cancel]

def outerSelection {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ)) : Fin 5 → Bool :=
  ![false, decide (Sum.inl (0, u hΔ) ∈ X), decide (Sum.inl (1, u hΔ) ∈ X),
    decide (Sum.inl (2, u hΔ) ∈ X), decide (Sum.inl (3, u hΔ) ∈ X)]

def setMask {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ)) : Fin 1024 :=
  pairMask (maskOf (outerSelection hΔ X)) (maskOf (fun w => decide (Sum.inr w ∈ X)))

theorem setMask_zero {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ)) :
    bit (setMask hΔ X).val 0 = 0 := by
  change bit (pairMask _ _).val (0 : Fin 5).val = _
  rw [pairMask_low, bit_maskOf]
  rfl

theorem setMask_clique {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ)) (i : Fin 4) :
    bit (setMask hΔ X).val (i.val + 1) =
      if Sum.inl (i, u hΔ) ∈ X then 1 else 0 := by
  change bit (pairMask _ _).val (spoke i).val = _
  rw [pairMask_low, bit_maskOf]
  fin_cases i <;> simp [outerSelection, spoke, boolValue]

theorem setMask_additional {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ)) (w : Fin 5) :
    bit (setMask hΔ X).val (w.val + 5) = if Sum.inr w ∈ X then 1 else 0 := by
  change bit (pairMask _ _).val (w.val + 5) = _
  rw [pairMask_high, bit_maskOf]
  simp [boolValue]

theorem bit_eq_one_iff (m j : ℕ) : bit m j = 1 ↔ m.testBit j = true := by
  simp [bit]

theorem eq_subset_setMask {Δ : ℕ} (hΔ : 3 ≤ Δ) (X : Finset (Vertex Δ))
    (hwhole : ∀ (i : Fin 4) (a : Fin Δ),
      Sum.inl (i, a) ∈ X ↔ Sum.inl (i, u hΔ) ∈ X) :
    X = subset Δ (setMask hΔ X).val := by
  ext x
  cases x with
  | inl p =>
    rcases p with ⟨i, a⟩
    rw [mem_subset_clique, ← bit_eq_one_iff, setMask_clique]
    simpa using hwhole i a
  | inr w =>
    rw [mem_subset_additional, ← bit_eq_one_iff, setMask_additional]
    simp

theorem whole_cliques_not_overfull {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (X : Finset (Vertex Δ))
    (hwhole : ∀ (i : Fin 4) (a : Fin Δ),
      Sum.inl (i, a) ∈ X ↔ Sum.inl (i, u hΔ) ∈ X) :
    ¬ IsOverfull (graph Δ) Δ X := by
  have h := subset_not_overfull hΔ hodd (setMask hΔ X) (setMask_zero hΔ X)
  rwa [← eq_subset_setMask hΔ X hwhole] at h

end Overfull.Sharpness.WholeCliques
