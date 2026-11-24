import Overfull.Dense.BalanceRepair.Model

/-!
# Actual subgraphs selected by directed arcs

Selecting or deleting cyclically oriented arcs gives actual tripartite
subgraphs. Their simple-graph degrees are the sums of the incoming and
outgoing arc counts, and zero imbalance is exactly local balance.
-/

namespace Overfull.Dense.BalanceRepair

open Finset Classical
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem arcOut_sdiff_add (E F : Finset (V × V)) (hF : F ⊆ E) (v : V) :
    arcOut (E \ F) v + arcOut F v = arcOut E v := by
  exact Finset.sum_sdiff hF

theorem arcIn_sdiff_add (E F : Finset (V × V)) (hF : F ⊆ E) (v : V) :
    arcIn (E \ F) v + arcIn F v = arcIn E v := by
  exact Finset.sum_sdiff hF

theorem arcBalance_sdiff (E F : Finset (V × V)) (hF : F ⊆ E) (v : V) :
    arcBalance (E \ F) v = arcBalance E v - arcBalance F v := by
  have ho := arcOut_sdiff_add E F hF v
  have hi := arcIn_sdiff_add E F hF v
  unfold arcBalance
  omega

variable {A B W : Type*}

def selectArcs (G : TripartiteGraph A B W)
    (F : Finset (Vertex A B W × Vertex A B W)) : TripartiteGraph A B W where
  ab a b := G.ab a b ∧ (.inl a, .inr (.inl b)) ∈ F
  aw a w := G.aw a w ∧ (.inr (.inr w), .inl a) ∈ F
  bw b w := G.bw b w ∧ (.inr (.inl b), .inr (.inr w)) ∈ F

def eraseArcs (G : TripartiteGraph A B W)
    (F : Finset (Vertex A B W × Vertex A B W)) : TripartiteGraph A B W where
  ab a b := G.ab a b ∧ (.inl a, .inr (.inl b)) ∉ F
  aw a w := G.aw a w ∧ (.inr (.inr w), .inl a) ∉ F
  bw b w := G.bw b w ∧ (.inr (.inl b), .inr (.inr w)) ∉ F

theorem selectArcs_le (G : TripartiteGraph A B W) (F) :
    (selectArcs G F).toSimpleGraph ≤ G.toSimpleGraph := by
  rintro (a | b | w) (a' | b' | w') h <;>
    simp only [TripartiteGraph.toSimpleGraph, selectArcs] at h ⊢ <;> tauto

theorem eraseArcs_eq_sdiff (G : TripartiteGraph A B W) (F) :
    (eraseArcs G F).toSimpleGraph = G.toSimpleGraph \ (selectArcs G F).toSimpleGraph := by
  ext (a | b | w) (a' | b' | w') <;>
    simp [TripartiteGraph.toSimpleGraph, eraseArcs, selectArcs] <;> tauto

theorem arc_not_reverse (G : TripartiteGraph A B W) (u v : Vertex A B W)
    (h : arc G u v) : ¬ arc G v u := by
  rcases u with a | b | w <;> rcases v with a' | b' | w' <;> simp_all [arc]

theorem adjacent_iff_arc (G : TripartiteGraph A B W) (u v : Vertex A B W) :
    G.toSimpleGraph.Adj u v ↔ arc G u v ∨ arc G v u := by
  rcases u with a | b | w <;> rcases v with a' | b' | w' <;>
    simp [arc, TripartiteGraph.toSimpleGraph]

variable [Fintype A] [Fintype B] [Fintype W]
variable [DecidableEq A] [DecidableEq B] [DecidableEq W]

theorem arcSet_selectArcs (G : TripartiteGraph A B W) (F) :
    arcSet (selectArcs G F) = arcSet G ∩ F := by
  ext ⟨u,v⟩
  rcases u with a | b | w <;> rcases v with a' | b' | w' <;>
    simp [arcSet, arc, selectArcs]

theorem arcSet_selectArcs_of_subset (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) : arcSet (selectArcs G F) = F := by
  rw [arcSet_selectArcs, Finset.inter_eq_right.mpr hF]

theorem arcSet_eraseArcs (G : TripartiteGraph A B W) (F) :
    arcSet (eraseArcs G F) = arcSet G \ F := by
  ext ⟨u,v⟩
  rcases u with a | b | w <;> rcases v with a' | b' | w' <;>
    simp [arcSet, arc, eraseArcs]

theorem arcOut_arcSet (G : TripartiteGraph A B W) (v : Vertex A B W) :
    arcOut (arcSet G) v = (univ.filter (fun w => arc G v w)).card := by
  rw [arcOut_eq_card]
  apply Finset.card_bij (fun e _ => e.2)
  · intro e he
    obtain ⟨heG, hev⟩ := Finset.mem_filter.mp he
    have hh : arc G e.1 e.2 := (mem_arcSet G e.1 e.2).mp heG
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hev] using hh
  · intro e he f hf heq
    have hev := (Finset.mem_filter.mp he).2
    have hfv := (Finset.mem_filter.mp hf).2
    exact Prod.ext (hev.trans hfv.symm) heq
  · intro w hw
    refine ⟨(v,w), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨(mem_arcSet G v w).mpr (Finset.mem_filter.mp hw).2, rfl⟩

theorem arcIn_arcSet (G : TripartiteGraph A B W) (v : Vertex A B W) :
    arcIn (arcSet G) v = (univ.filter (fun w => arc G w v)).card := by
  rw [arcIn_eq_card]
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    obtain ⟨heG, hev⟩ := Finset.mem_filter.mp he
    have hh : arc G e.1 e.2 := (mem_arcSet G e.1 e.2).mp heG
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hev] using hh
  · intro e he f hf heq
    have hev := (Finset.mem_filter.mp he).2
    have hfv := (Finset.mem_filter.mp hf).2
    exact Prod.ext heq (hev.trans hfv.symm)
  · intro w hw
    refine ⟨(w,v), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨(mem_arcSet G w v).mpr (Finset.mem_filter.mp hw).2, rfl⟩

theorem degree_eq_arc_counts (G : TripartiteGraph A B W) (v : Vertex A B W) :
    G.toSimpleGraph.degree v = arcOut (arcSet G) v + arcIn (arcSet G) v := by
  rw [arcOut_arcSet, arcIn_arcSet]
  have hneigh : G.toSimpleGraph.neighborFinset v =
      univ.filter (fun w => arc G v w) ∪ univ.filter (fun w => arc G w v) := by
    ext w
    simp [adjacent_iff_arc]
  have hd : Disjoint (univ.filter (fun w => arc G v w))
      (univ.filter (fun w => arc G w v)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact arc_not_reverse G v w (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hw').2
  change (G.toSimpleGraph.neighborFinset v).card = _
  rw [hneigh, Finset.card_union_of_disjoint hd]

@[simp] theorem arcOut_A (G : TripartiteGraph A B W) (a : A) :
    arcOut (arcSet G) (.inl a) = (G.neighborsB a).card := by
  rw [arcOut_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.neighborsB]
  simp

@[simp] theorem arcIn_A (G : TripartiteGraph A B W) (a : A) :
    arcIn (arcSet G) (.inl a) = (G.neighborsWA a).card := by
  rw [arcIn_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.neighborsWA]
  simp

@[simp] theorem arcOut_B (G : TripartiteGraph A B W) (b : B) :
    arcOut (arcSet G) (.inr (.inl b)) = (G.neighborsWB b).card := by
  rw [arcOut_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.neighborsWB]
  simp

@[simp] theorem arcIn_B (G : TripartiteGraph A B W) (b : B) :
    arcIn (arcSet G) (.inr (.inl b)) = (G.neighborsA b).card := by
  rw [arcIn_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.neighborsA]
  simp

@[simp] theorem arcOut_W (G : TripartiteGraph A B W) (w : W) :
    arcOut (arcSet G) (.inr (.inr w)) = (G.linkA w).card := by
  rw [arcOut_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.linkA]
  simp

@[simp] theorem arcIn_W (G : TripartiteGraph A B W) (w : W) :
    arcIn (arcSet G) (.inr (.inr w)) = (G.linkB w).card := by
  rw [arcIn_arcSet]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    arc, TripartiteGraph.linkB]
  simp

theorem locallyBalanced_iff (G : TripartiteGraph A B W) :
    G.IsLocallyBalanced ↔ ∀ v, arcBalance (arcSet G) v = 0 := by
  simp only [TripartiteGraph.IsLocallyBalanced, Sum.forall, arcBalance,
    arcOut_A, arcIn_A, arcOut_B, arcIn_B, arcOut_W, arcIn_W, sub_eq_zero,
    Nat.cast_inj]
  constructor <;> rintro ⟨hA, hB, hW⟩ <;> exact ⟨hA, fun b => (hB b).symm, hW⟩

theorem selectArcs_degree (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (v : Vertex A B W) :
    (selectArcs G F).toSimpleGraph.degree v = arcOut F v + arcIn F v := by
  rw [degree_eq_arc_counts, arcSet_selectArcs_of_subset G F hF]

theorem erase_arcOut_add (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (v : Vertex A B W) :
    arcOut (arcSet (eraseArcs G F)) v + arcOut F v = arcOut (arcSet G) v := by
  rw [arcSet_eraseArcs]
  exact arcOut_sdiff_add _ _ hF v

theorem erase_arcIn_add (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (v : Vertex A B W) :
    arcIn (arcSet (eraseArcs G F)) v + arcIn F v = arcIn (arcSet G) v := by
  rw [arcSet_eraseArcs]
  exact arcIn_sdiff_add _ _ hF v

theorem erase_arcOut_le (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (v : Vertex A B W) (D : ℝ)
    (hD : (arcOut F v : ℝ) + arcIn F v ≤ D) :
    (arcOut (arcSet G) v : ℝ) ≤ arcOut (arcSet (eraseArcs G F)) v + D := by
  have heq : (arcOut (arcSet (eraseArcs G F)) v : ℝ) + arcOut F v =
      arcOut (arcSet G) v := by exact_mod_cast erase_arcOut_add G F hF v
  have hi : (0 : ℝ) ≤ arcIn F v := Nat.cast_nonneg _
  linarith only [heq, hD, hi]

theorem erase_arcIn_le (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (v : Vertex A B W) (D : ℝ)
    (hD : (arcOut F v : ℝ) + arcIn F v ≤ D) :
    (arcIn (arcSet G) v : ℝ) ≤ arcIn (arcSet (eraseArcs G F)) v + D := by
  have heq : (arcIn (arcSet (eraseArcs G F)) v : ℝ) + arcIn F v =
      arcIn (arcSet G) v := by exact_mod_cast erase_arcIn_add G F hF v
  have ho : (0 : ℝ) ≤ arcOut F v := Nat.cast_nonneg _
  linarith only [heq, hD, ho]

/-- All routing margins follow from the original graph's densities and
the actual degree of the deleted arc set. -/
theorem routingConditions_after_deletion (G : TripartiteGraph A B W) (F)
    (hF : F ⊆ arcSet G) (n : ℕ) (η c₀ D k : ℝ)
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hW : (n : ℝ) / 2 ≤ Fintype.card W)
    (hq : 0 ≤ c₀ * n + D)
    (hpart : c₀ * n + D + k + 2 < n)
    (hWmargin : 2 * (c₀ * n + D) + k + 2 < (n : ℝ) / 2)
    (hmargin : c₀ * n + D + k + 2 < (1 / 2 + η) * n - D)
    (hdegreeA : ∀ a, (1 / 2 + η) * n ≤ ((G.neighborsB a).card : ℝ))
    (hdegreeB : ∀ b, (1 / 2 + η) * n ≤ ((G.neighborsA b).card : ℝ))
    (hmissingA : ∀ a, (Fintype.card W : ℝ) - (G.neighborsWA a).card ≤ c₀ * n)
    (hmissingB : ∀ b, (Fintype.card W : ℝ) - (G.neighborsWB b).card ≤ c₀ * n)
    (hmissingWA : ∀ w, (Fintype.card A : ℝ) - (G.linkA w).card ≤ c₀ * n)
    (hmissingWB : ∀ w, (Fintype.card B : ℝ) - (G.linkB w).card ≤ c₀ * n)
    (hdeleted : ∀ v, (arcOut F v : ℝ) + arcIn F v ≤ D) :
    RoutingConditions (eraseArcs G F) (c₀ * n + D) k := by
  have hOut (v) := erase_arcOut_le G F hF v D (hdeleted v)
  have hIn (v) := erase_arcIn_le G F hF v D (hdeleted v)
  refine ⟨hq, ?_, ?_, hWmargin.trans_le hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hA] using hpart
  · simpa only [hB] using hpart
  · intro a
    have hh := hOut (.inl a)
    simp only [arcOut_A] at hh
    linarith only [hh, hdegreeA a, hmargin]
  · intro b
    have hh := hIn (.inr (.inl b))
    simp only [arcIn_B] at hh
    linarith only [hh, hdegreeB b, hmargin]
  · intro a
    have hh := hIn (.inl a)
    simp only [arcIn_A] at hh
    linarith only [hh, hmissingA a]
  · intro b
    have hh := hOut (.inr (.inl b))
    simp only [arcOut_B] at hh
    linarith only [hh, hmissingB b]
  · intro w
    have hh := hOut (.inr (.inr w))
    simp only [arcOut_W] at hh
    linarith only [hh, hmissingWA w]
  · intro w
    have hh := hIn (.inr (.inr w))
    simp only [arcIn_W] at hh
    linarith only [hh, hmissingWB w]

end Overfull.Dense.BalanceRepair
