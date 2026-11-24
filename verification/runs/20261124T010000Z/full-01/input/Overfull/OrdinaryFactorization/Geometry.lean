import Overfull.BipartitePackingAccounting

/-!
# The actual internal graph outside a reserve

All graphs retain the original vertex type. The internal leftover consists
exactly of host edges within the two sides and outside the actual reserve.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical

variable {V : Type*}

/-- Host edges whose endpoints lie on the same side of `A` and its complement. -/
def insideGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ ((v ∈ A) ↔ (w ∈ A))
  symm := by intro v w h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := by intro v h; exact G.loopless v h.1

@[simp] theorem insideGraph_adj (G : SimpleGraph V) (A : Finset V) (v w : V) :
    (insideGraph G A).Adj v w ↔ G.Adj v w ∧ ((v ∈ A) ↔ (w ∈ A)) := Iff.rfl

instance insideGraph_decidable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : DecidableRel (insideGraph G A).Adj := by
  intro v w
  change Decidable (G.Adj v w ∧ ((v ∈ A) ↔ (w ∈ A)))
  infer_instance

theorem insideGraph_le (G : SimpleGraph V) (A : Finset V) : insideGraph G A ≤ G :=
  fun _ _ h => h.1

theorem insideGraph_mono (A : Finset V) {G R : SimpleGraph V} (hRG : R ≤ G) :
    insideGraph R A ≤ insideGraph G A := fun _ _ h => ⟨hRG h.1, h.2⟩

/-- The exact internal edges that remain after removing the reserve. -/
def internalLeftover (G R : SimpleGraph V) (A : Finset V) : SimpleGraph V :=
  insideGraph G A \ insideGraph R A

@[simp] theorem internalLeftover_adj (G R : SimpleGraph V) (A : Finset V) (v w : V) :
    (internalLeftover G R A).Adj v w ↔
      G.Adj v w ∧ ¬ R.Adj v w ∧ ((v ∈ A) ↔ (w ∈ A)) := by
  simp only [internalLeftover, SimpleGraph.sdiff_adj, insideGraph_adj]
  tauto

theorem internalLeftover_le (G R : SimpleGraph V) (A : Finset V) :
    internalLeftover G R A ≤ G := fun _ _ h => (internalLeftover_adj _ _ _ _ _).mp h |>.1

theorem internalLeftover_disjoint (G R : SimpleGraph V) (A : Finset V) :
    Disjoint (internalLeftover G R A) R := by
  apply disjoint_iff_inf_le.mpr
  intro v w h
  exact ((internalLeftover_adj G R A v w).mp h.1).2.1 h.2

variable [Fintype V] [DecidableEq V]

/-- Internal neighbors are precisely the neighbors in the vertex's own side. -/
theorem insideGraph_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ) (v : V) :
    (insideGraph G A).neighborFinset v =
      if v ∈ A then G.neighborFinset v ∩ A else G.neighborFinset v ∩ B := by
  have hB (w : V) : w ∈ B ↔ w ∉ A := by
    constructor
    · intro hwB hwA
      exact Finset.disjoint_left.mp hAB hwA hwB
    · intro hwA
      have hw : w ∈ A ∪ B := by rw [hcover]; simp
      exact (Finset.mem_union.mp hw).resolve_left hwA
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    ext w
    simp [hv]
  · rw [if_neg hv]
    ext w
    simp [hv, hB]

theorem insideGraph_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ) (v : V) :
    (insideGraph G A).degree v =
      if v ∈ A then (G.neighborFinset v ∩ A).card else (G.neighborFinset v ∩ B).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    insideGraph_neighbors G A B hAB hcover v]
  split_ifs <;> rfl

/-- Exact degree subtraction for the actual internal leftover. -/
theorem internalLeftover_degree_add (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (hRG : R ≤ G)
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ) (v : V) :
    (internalLeftover G R A).degree v +
        (R.neighborFinset v ∩ (if v ∈ A then A else B)).card =
      (G.neighborFinset v ∩ (if v ∈ A then A else B)).card := by
  have hneighbors : (internalLeftover G R A).neighborFinset v =
      (insideGraph G A).neighborFinset v \ (insideGraph R A).neighborFinset v := by
    ext w
    simp only [internalLeftover, SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj, Finset.mem_sdiff]
  have hsubset (S : Finset V) : R.neighborFinset v ∩ S ⊆ G.neighborFinset v ∩ S := by
    intro w hw
    obtain ⟨hR, hS⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨by
      rw [SimpleGraph.mem_neighborFinset] at hR ⊢
      exact hRG hR, hS⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors,
    insideGraph_neighbors G A B hAB hcover v,
    insideGraph_neighbors R A B hAB hcover v]
  split_ifs
  · exact Finset.card_sdiff_add_card_eq_card (hsubset A)
  · exact Finset.card_sdiff_add_card_eq_card (hsubset B)

/-- Errors in the original and reserve side degrees add when their actual
internal edge sets are subtracted. The two sides may have arbitrary targets. -/
theorem internalLeftover_degree_error (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (hRG : R ≤ G)
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ)
    (v : V) (x y ε η : ℝ)
    (hG : |((G.neighborFinset v ∩ A).card : ℝ) - x| ≤ ε ∧
      |((G.neighborFinset v ∩ B).card : ℝ) - x| ≤ ε)
    (hR : |((R.neighborFinset v ∩ A).card : ℝ) - y| ≤ η ∧
      |((R.neighborFinset v ∩ B).card : ℝ) - y| ≤ η) :
    |((internalLeftover G R A).degree v : ℝ) - (x - y)| ≤ ε + η := by
  let S := if v ∈ A then A else B
  have hdegree : ((internalLeftover G R A).degree v : ℝ) +
      (R.neighborFinset v ∩ S).card = (G.neighborFinset v ∩ S).card := by
    exact_mod_cast internalLeftover_degree_add G R hRG A B hAB hcover v
  have hG' : |((G.neighborFinset v ∩ S).card : ℝ) - x| ≤ ε := by
    dsimp only [S]
    split_ifs
    · exact hG.1
    · exact hG.2
  have hR' : |((R.neighborFinset v ∩ S).card : ℝ) - y| ≤ η := by
    dsimp only [S]
    split_ifs
    · exact hR.1
    · exact hR.2
  calc
    _ = |(((G.neighborFinset v ∩ S).card : ℝ) - x) -
        (((R.neighborFinset v ∩ S).card : ℝ) - y)| := by congr 1; linarith
    _ ≤ |((G.neighborFinset v ∩ S).card : ℝ) - x| +
        |((R.neighborFinset v ∩ S).card : ℝ) - y| := abs_sub _ _
    _ ≤ ε + η := add_le_add hG' hR'

end Overfull.OrdinaryFactorization
