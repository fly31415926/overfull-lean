import Overfull.Dense.LinkPacking.Packing
import Overfull.Dense.LinkPacking.Tripartite

/-!
# Uniform tripartite link packing

The order threshold is chosen using only the fixed real parameters. Every
balanced omitted-part link then receives an actual matching covering exactly
its vertices, and the selected matchings are pairwise edge-disjoint. The
displayed assumptions concern only the tripartite graph and its link family.
-/

noncomputable section

universe uA uB uW

namespace Overfull.Dense.LinkPacking

open Finset Classical
open Overfull.DenseLinkPacking.TripartiteGeometry

/-- The full uniform tripartite link-packing conclusion of Lemma 5.12.
The threshold precedes the graph order, host graph, and entire link family.
The minimum-degree assumption is on each actual induced graph. -/
theorem exists_tripartite_link_packing (b lam : ℝ) (hb : 1 ≤ b)
    (hlam : 0 < lam) (_hlam_one : lam ≤ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (A : Type uA) (B : Type uB) (W : Type uW)
        [Fintype A] [Fintype B] [Fintype W],
      ∀ (G : TripartiteGraph A B W),
      Fintype.card A = n → Fintype.card B = n → Fintype.card W = n →
      ∀ (q : ℕ) (Y : ℕ → Finset (A ⊕ B ⊕ W))
        (s : ℕ → ℕ) (omitted : ℕ → Fin 3),
      (q : ℝ) ≤ 3 * b * n →
      (∀ i < q, ∀ j, (Y i ∩ part j).card =
        if j = omitted i then 0 else s i) →
      (∀ i < q, (s i : ℝ) / 2 + 81 * b * lam ^ (3 / 2 : ℝ) * n ≤
        ((G.toSimpleGraph.induce (↑(Y i) : Set (A ⊕ B ⊕ W))).minDegree : ℝ)) →
      (∀ i < q, ∀ j < q, i ≠ j →
        ((Y i ∩ Y j).card : ℝ) ≤ 6 * lam ^ 2 * n) →
      (∀ v, (((range q).filter (fun i => v ∈ Y i)).card : ℝ) ≤
        2 * b * lam * n) →
      ∃ M : Fin q → G.toSimpleGraph.Subgraph,
        (∀ i, (M i).IsMatching) ∧
        (∀ i, (M i).verts = (↑(Y i.val) : Set (A ⊕ B ⊕ W))) ∧
        Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  obtain ⟨n₀, hn₀⟩ := Parameters.exists_threshold b lam hb hlam
  refine ⟨n₀, ?_⟩
  intro n hn A B W _ _ _ G hA hB hW q Y s omitted hq hcounts hdegree hoverlap hincidence
  obtain ⟨_, hL, hbudget⟩ := hn₀ n hn
  let X : ℕ → Finset (A ⊕ B ⊕ W) := fun i => localLeft (Y i) (omitted i)
  let Z : ℕ → Finset (A ⊕ B ⊕ W) := fun i => localRight (Y i) (omitted i)
  let hdata (i : ℕ) (hi : i < q) : LocalSides G (Y i) (s i) :=
    localSides G (Y i) (omitted i) (s i) (hcounts i hi)
  have hcover (i : ℕ) (hi : i < q) : X i ∪ Z i = Y i :=
    (hdata i hi).union_eq
  have hcardX (i : ℕ) (hi : i < q) : (X i).card = s i :=
    (hdata i hi).left_card
  have hcardZ (i : ℕ) (hi : i < q) : (Z i).card = s i :=
    (hdata i hi).right_card
  have hV : (Fintype.card (A ⊕ B ⊕ W) : ℝ) ≤ 3 * n := by
    exact_mod_cast (le_of_eq (card_vertices n hA hB hW))
  have hAB : ∀ i < q, Disjoint (X i) (Z i) := by
    intro i _
    exact local_disjoint (Y i) (omitted i)
  have hbalance : ∀ i < q, (X i).card = (Z i).card := by
    intro i hi
    rw [hcardX i hi, hcardZ i hi]
  have hleft : ∀ i < q, ∀ v ∈ X i,
      ((X i).card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.toSimpleGraph.neighborFinset v ∩ Z i).card := by
    intro i hi v hv
    have hmin : ((G.toSimpleGraph.induce
        (↑(Y i) : Set (A ⊕ B ⊕ W))).minDegree : ℝ) ≤
        (G.toSimpleGraph.neighborFinset v ∩ Z i).card := by
      exact_mod_cast (hdata i hi).minDegree_le_left v hv
    rw [hcardX i hi, Parameters.load_eq_rpow lam n hlam.le]
    calc
      (s i : ℝ) / 2 + 81 * b * (lam ^ (3 / 2 : ℝ) * n) =
          (s i : ℝ) / 2 + 81 * b * lam ^ (3 / 2 : ℝ) * n := by ring
      _ ≤ _ := (hdegree i hi).trans hmin
  have hright : ∀ i < q, ∀ v ∈ Z i,
      ((X i).card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.toSimpleGraph.neighborFinset v ∩ X i).card := by
    intro i hi v hv
    have hmin : ((G.toSimpleGraph.induce
        (↑(Y i) : Set (A ⊕ B ⊕ W))).minDegree : ℝ) ≤
        (G.toSimpleGraph.neighborFinset v ∩ X i).card := by
      exact_mod_cast (hdata i hi).minDegree_le_right v hv
    rw [hcardX i hi, Parameters.load_eq_rpow lam n hlam.le]
    calc
      (s i : ℝ) / 2 + 81 * b * (lam ^ (3 / 2 : ℝ) * n) =
          (s i : ℝ) / 2 + 81 * b * lam ^ (3 / 2 : ℝ) * n := by ring
      _ ≤ _ := (hdegree i hi).trans hmin
  have hoverlap' : ∀ i < q, ∀ j < q, i ≠ j →
      (((X i ∪ Z i) ∩ (X j ∪ Z j)).card : ℝ) ≤ 6 * lam ^ 2 * n := by
    intro i hi j hj hij
    rw [hcover i hi, hcover j hj]
    exact hoverlap i hi j hj hij
  have hincidence' : ∀ v,
      (((range q).filter (fun i => v ∈ X i ∪ Z i)).card : ℝ) ≤
        2 * b * lam * n := by
    intro v
    have hfilter : (range q).filter (fun i => v ∈ X i ∪ Z i) =
        (range q).filter (fun i => v ∈ Y i) := by
      apply Finset.filter_congr
      intro i hi
      rw [hcover i (mem_range.mp hi)]
    rw [hfilter]
    exact hincidence v
  obtain ⟨M, hmatching, hverts, hdisjoint⟩ :=
    exists_packing_of_budget G.toSimpleGraph X Z b lam n q hb hlam hL hV hq
      hAB hbalance
      (by
        intro i hi v hv
        convert hleft i hi v hv using 1
        congr 2
        ext w
        simp only [Finset.mem_inter])
      (by
        intro i hi v hv
        convert hright i hi v hv using 1
        congr 2
        ext w
        simp only [Finset.mem_inter])
      (by
        intro i hi j hj hij
        convert hoverlap' i hi j hj hij using 1
        congr 2
        ext w
        simp only [Finset.mem_inter, Finset.mem_union])
      (by
        intro v
        convert hincidence' v using 1
        congr 2
        ext i
        simp only [Finset.mem_filter, Finset.mem_union])
      hbudget
  refine ⟨M, hmatching, ?_, hdisjoint⟩
  intro i
  rw [hverts i]
  simpa only [Finset.coe_union] using
    congrArg (fun S : Finset (A ⊕ B ⊕ W) => (↑S : Set (A ⊕ B ⊕ W)))
      (hcover i.val i.isLt)

end Overfull.Dense.LinkPacking
