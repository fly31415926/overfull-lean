import Overfull.Dense.LinkPacking.History
import Overfull.Dense.LinkPacking.LocalProbability

/-!
# Actual local used-edge loads along the finite history

The predictable hit count is exactly the degree of the union of chosen
matching edges into a monitored link. A bound on every final load therefore
bounds the loads at all earlier stages and makes each stage's candidate
family feasible.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking

open Finset Classical SimpleGraph BipartitePackingAccounting

variable {V : Type*} [Fintype V]

/-- The number of actual used neighbors inside a monitored finite link. -/
def localLoad (U : SimpleGraph V) (Y : Finset V) (v : V) : ℕ :=
  (U.neighborFinset v ∩ Y).card

@[simp] theorem localLoad_bot (Y : Finset V) (v : V) :
    localLoad (⊥ : SimpleGraph V) Y v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hbot : (⊥ : SimpleGraph V).Adj v w := by
    simpa using (Finset.mem_inter.mp hw).1
  exact hbot

/-- Adding edges cannot decrease the actual local load. -/
theorem localLoad_mono (U W : SimpleGraph V) (hUW : U ≤ W)
    (Y : Finset V) (v : V) : localLoad U Y v ≤ localLoad W Y v := by
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hU, hY⟩ := Finset.mem_inter.mp hw
  exact Finset.mem_inter.mpr ⟨by
    have hUadj : U.Adj v w := by simpa using hU
    simpa using hUW hUadj, hY⟩

/-- Edge-disjoint graphs contribute additively to every actual local load. -/
theorem localLoad_sup (U W : SimpleGraph V) (hdisj : Disjoint U W)
    (Y : Finset V) (v : V) :
    localLoad (U ⊔ W) Y v = localLoad U Y v + localLoad W Y v := by
  have hsets : Disjoint (U.neighborFinset v ∩ Y) (W.neighborFinset v ∩ Y) := by
    apply Finset.disjoint_left.mpr
    intro w hU hW
    have hUadj : U.Adj v w := by simpa using (Finset.mem_inter.mp hU).1
    have hWadj : W.Adj v w := by simpa using (Finset.mem_inter.mp hW).1
    exact hdisj.le_bot ⟨hUadj, hWadj⟩
  unfold localLoad
  calc
    _ = ((U.neighborFinset v ∩ Y) ∪ (W.neighborFinset v ∩ Y)).card := by
      congr 1
      ext w
      simp only [Finset.mem_inter, Finset.mem_union, SimpleGraph.mem_neighborFinset,
        SimpleGraph.sup_adj]
      tauto
    _ = _ := Finset.card_union_of_disjoint hsets

/-- A matching contributes exactly the indicator of using an edge from the
fixed vertex into the monitored link. -/
theorem localLoad_matching_indicator (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (Y : Finset V) (v : V) :
    localLoad M.spanningCoe Y v = if ∃ w ∈ Y, M.Adj v w then 1 else 0 := by
  have hle : localLoad M.spanningCoe Y v ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans
      (matching_degree_le_one G M hM v)
  by_cases hh : ∃ w ∈ Y, M.Adj v w
  · rw [if_pos hh]
    obtain ⟨w, hw, hadj⟩ := hh
    have hpos : 0 < localLoad M.spanningCoe Y v := by
      apply Finset.card_pos.mpr
      exact ⟨w, Finset.mem_inter.mpr ⟨by simpa using hadj, hw⟩⟩
    omega
  · rw [if_neg hh]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hh ⟨w, (Finset.mem_inter.mp hw).2,
      by simpa using (Finset.mem_inter.mp hw).1⟩

omit [Fintype V] in
@[simp] theorem history_castSucc (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (q : ℕ) (ω : Fin (q + 1) → Fin t) (i : Fin q) :
    history G t Y (q + 1) ω i.castSucc = history G t Y q (Fin.init ω) i := by
  simp only [history, Fin.snoc_castSucc]

omit [Fintype V] in
@[simp] theorem history_last (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (q : ℕ) (ω : Fin (q + 1) → Fin t) :
    history G t Y (q + 1) ω (Fin.last q) =
      candidates G t (Y q) (used G (history G t Y q (Fin.init ω))) (ω (Fin.last q)) := by
  simp only [history, Fin.snoc_last]

omit [Fintype V] in
@[simp] theorem used_history_zero (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (ω : Fin 0 → Fin t) :
    used G (history G t Y 0 ω) = ⊥ := by
  exact BipartitePackingHistory.edgeUnion_zero G _

omit [Fintype V] in
/-- Appending a round adds exactly its chosen candidate to the used graph. -/
theorem used_history_succ (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (q : ℕ) (ω : Fin (q + 1) → Fin t) :
    used G (history G t Y (q + 1) ω) =
      used G (history G t Y q (Fin.init ω)) ⊔
        (candidates G t (Y q) (used G (history G t Y q (Fin.init ω)))
          (ω (Fin.last q))).spanningCoe := by
  exact BipartitePackingHistory.edgeUnion_snoc G
    (history G t Y q (Fin.init ω))
    (candidates G t (Y q) (used G (history G t Y q (Fin.init ω))) (ω (Fin.last q)))

omit [Fintype V] in
theorem used_history_init_le (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (q : ℕ) (ω : Fin (q + 1) → Fin t) :
    used G (history G t Y q (Fin.init ω)) ≤ used G (history G t Y (q + 1) ω) := by
  rw [used_history_succ]
  exact le_sup_left

/-- The actual predictable hit count equals the actual final used-edge
degree into the monitored link. No probability hypothesis is involved. -/
theorem hits_count_eq_localLoad (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (i : ℕ) (v : V) (q : ℕ) (ω : Fin q → Fin t) :
    PredictableBernoulli.count (hitsProcess G t Y i v) q ω =
      localLoad (used G (history G t Y q ω)) (Y i) v := by
  induction q with
  | zero => simp only [PredictableBernoulli.count_zero, used_history_zero, localLoad_bot]
  | succ q ih =>
    rw [PredictableBernoulli.count, ih, used_history_succ,
      localLoad_sup _ _ (candidates_avoid G t (Y q)
        (used G (history G t Y q (Fin.init ω))) (ω (Fin.last q))).symm,
      localLoad_matching_indicator _ _ (candidates_matching G t (Y q)
        (used G (history G t Y q (Fin.init ω))) (ω (Fin.last q)))]
    simp only [hitsProcess, decide_eq_true_eq]

/-- Final local load bounds force every actual history entry to cover its
prescribed link. Feasibility is used only for the actual preceding used
graph, whose local loads are bounded by those of the final used graph. -/
theorem history_covers_of_localLoad (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (L : ℝ) (q : ℕ) (ω : Fin q → Fin t)
    (hfeasible : ∀ s < q, ∀ U : SimpleGraph V,
      (∀ v, (localLoad U (Y s) v : ℝ) ≤ L) →
        ∃ K, CandidateOK G t (Y s) U K)
    (hload : ∀ s < q, ∀ v,
      (localLoad (used G (history G t Y q ω)) (Y s) v : ℝ) ≤ L) :
    ∀ i : Fin q, (history G t Y q ω i).verts = (↑(Y i.val) : Set V) := by
  induction q with
  | zero => intro i; exact Fin.elim0 i
  | succ q ih =>
    have hmono (s : ℕ) (v : V) :
        (localLoad (used G (history G t Y q (Fin.init ω))) (Y s) v : ℝ) ≤
          localLoad (used G (history G t Y (q + 1) ω)) (Y s) v := by
      exact_mod_cast localLoad_mono _ _ (used_history_init_le G t Y q ω) (Y s) v
    have hprevload : ∀ s < q, ∀ v,
        (localLoad (used G (history G t Y q (Fin.init ω))) (Y s) v : ℝ) ≤ L := by
      intro s hs v
      exact (hmono s v).trans (hload s (Nat.lt_succ_of_lt hs) v)
    have hprevcovers := ih (Fin.init ω)
      (fun s hs U hU => hfeasible s (Nat.lt_succ_of_lt hs) U hU) hprevload
    have hlastload : ∀ v,
        (localLoad (used G (history G t Y q (Fin.init ω))) (Y q) v : ℝ) ≤ L := by
      intro v
      exact (hmono q v).trans (hload q (Nat.lt_succ_self q) v)
    have hlastfeasible := hfeasible q (Nat.lt_succ_self q)
      (used G (history G t Y q (Fin.init ω))) hlastload
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [history_last]
      exact ((candidates_spec G t (Y q)
        (used G (history G t Y q (Fin.init ω))) hlastfeasible).1
          (ω (Fin.last q))).2.1
    | cast i => simpa only [history_castSucc, Fin.coe_castSucc] using hprevcovers i

end Overfull.Dense.LinkPacking
