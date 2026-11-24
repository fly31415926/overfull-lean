import Overfull.BipartiteMatching
import Overfull.External.FiniteCirculation

/-!
# Bounded signed flows in dense bipartite graphs

The entries of each flow are real weights on actual crossing edges of a
finite simple graph. Nonedges have weight zero. The circulation theorem is
proved in `Overfull.External.FiniteCirculation`; no flow-existence assumption
is used in the graph theorems below.
-/

namespace Overfull

open Finset

namespace BoundedFlow

private def networkTail {V E : Type*} (tail : E → V) : E ⊕ V → Option V
  | .inl e => some (tail e)
  | .inr _ => none

private def networkHead {V E : Type*} (head : E → V) : E ⊕ V → Option V
  | .inl e => some (head e)
  | .inr v => some v

private def networkLower {V E : Type*} (capacity : E → ℝ) (demand : V → ℝ) :
    E ⊕ V → ℝ
  | .inl e => -capacity e
  | .inr v => demand v

private def networkUpper {V E : Type*} (capacity : E → ℝ) (demand : V → ℝ) :
    E ⊕ V → ℝ
  | .inl e => capacity e
  | .inr v => demand v

/-- A finite directed network with symmetric real capacities and prescribed
net outflow. The hypothesis is precisely the necessary cut inequality. -/
theorem exists_of_cut {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (tail head : E → V) (capacity : E → ℝ)
    (demand : V → ℝ) (hcapacity : ∀ e, 0 ≤ capacity e)
    (htotal : ∑ v, demand v = 0)
    (hcut : ∀ S : Finset V, ∑ v ∈ S, demand v ≤
      ∑ e, if (head e ∈ S) ≠ (tail e ∈ S) then capacity e else 0) :
    ∃ flow : E → ℝ, (∀ e, |flow e| ≤ capacity e) ∧
      ∀ v, (∑ e, if tail e = v then flow e else 0) -
        (∑ e, if head e = v then flow e else 0) = demand v := by
  classical
  have hlu : ∀ e : E ⊕ V,
      networkLower capacity demand e ≤ networkUpper capacity demand e := by
    intro e
    cases e with
    | inl e => exact neg_le_self (hcapacity e)
    | inr v => exact le_rfl
  have hnetwork : ∀ J : Finset (Option V),
      ∑ e ∈ univ.filter (fun e =>
        networkHead head e ∈ J ∧ networkTail tail e ∉ J),
          networkLower capacity demand e ≤
      ∑ e ∈ univ.filter (fun e =>
        networkTail tail e ∈ J ∧ networkHead head e ∉ J),
          networkUpper capacity demand e := by
    intro J
    let S : Finset V := univ.filter (fun v => some v ∈ J)
    have hmem (v : V) : v ∈ S ↔ some v ∈ J := by simp [S]
    have hcore :
        (∑ e, if some (head e) ∈ J ∧ some (tail e) ∉ J
          then -capacity e else 0) -
        (∑ e, if some (tail e) ∈ J ∧ some (head e) ∉ J
          then capacity e else 0) =
        -(∑ e, if (head e ∈ S) ≠ (tail e ∈ S) then capacity e else 0) := by
      rw [← sum_sub_distrib, ← sum_neg_distrib]
      apply sum_congr rfl
      intro e _
      simp only [hmem]
      by_cases hh : some (head e) ∈ J <;>
        by_cases ht : some (tail e) ∈ J <;> simp [hh, ht]
    have hdummy :
        (∑ v, if some v ∈ J ∧ none ∉ J then demand v else 0) -
        (∑ v, if none ∈ J ∧ some v ∉ J then demand v else 0) =
        ∑ v ∈ S, demand v := by
      by_cases hroot : none ∈ J
      · have hsplit := Finset.sum_add_sum_compl S demand
        have hcomp : (∑ v, if some v ∉ J then demand v else 0) =
            ∑ v ∈ Sᶜ, demand v := by
          rw [← sum_filter]
          congr 1
          ext v
          simp [S]
        simp only [hroot, not_true_eq_false, and_false, if_false, sum_const_zero,
          true_and, zero_sub]
        rw [hcomp]
        linarith
      · simp only [hroot, not_false_eq_true, and_true, false_and, if_false,
          sum_const_zero, sub_zero]
        exact (Finset.sum_filter _ _).symm
    rw [sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [networkHead, networkTail, networkLower, networkUpper]
    have hc := hcut S
    linarith
  obtain ⟨g, hg, hconserve⟩ := Lovasz.hoffman_circulation
    (networkTail tail) (networkHead head)
    (networkLower capacity demand) (networkUpper capacity demand) hlu hnetwork
  refine ⟨fun e => g (.inl e), ?_, ?_⟩
  · intro e
    exact abs_le.mpr (hg (.inl e))
  · intro v
    have hv := hconserve (some v)
    rw [sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type] at hv
    simp only [networkHead, networkTail, Option.some.injEq, reduceCtorEq, if_false,
      sum_const_zero, add_zero] at hv
    have hfixed : g (.inr v) = demand v := le_antisymm (hg (.inr v)).2 (hg (.inr v)).1
    simp only [sum_ite_eq', mem_univ, if_true] at hv
    rw [hfixed] at hv
    linarith

end BoundedFlow


variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- The indicator of a crossing edge, with values in the real numbers. -/
noncomputable def bipartiteEdgeIndicator (a : A) (b : B) : ℝ :=
  if G.Adj (.inl a) (.inr b) then 1 else 0

/-- The number of actual edges between the indicated vertex subsets. -/
noncomputable def bipartiteEdgeCount (X : Finset A) (Y : Finset B) : ℝ :=
  ∑ a ∈ X, ∑ b ∈ Y, bipartiteEdgeIndicator G a b

/-- The number of actual crossing edges of the vertex cut `X ∪ Y`. -/
noncomputable def bipartiteCutSize (X : Finset A) (Y : Finset B) : ℝ :=
  bipartiteEdgeCount G X Yᶜ + bipartiteEdgeCount G Xᶜ Y

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem bipartite_edge_indicator_nonneg (a : A) (b : B) :
    0 ≤ bipartiteEdgeIndicator G a b := by
  unfold bipartiteEdgeIndicator
  split_ifs <;> norm_num

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem bipartite_edge_count_nonneg (X : Finset A) (Y : Finset B) :
    0 ≤ bipartiteEdgeCount G X Y :=
  sum_nonneg fun a _ => sum_nonneg fun b _ => bipartite_edge_indicator_nonneg G a b

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem bipartite_edge_count_le (X : Finset A) (Y : Finset B) :
    bipartiteEdgeCount G X Y ≤ (X.card : ℝ) * Y.card := by
  calc
    bipartiteEdgeCount G X Y ≤ ∑ _a ∈ X, ∑ _b ∈ Y, (1 : ℝ) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      unfold bipartiteEdgeIndicator
      split_ifs <;> norm_num
    _ = _ := by simp

omit [Fintype A] [DecidableEq A] in
theorem bipartite_edge_count_add_compl_right (X : Finset A) (Y : Finset B) :
    bipartiteEdgeCount G X Y + bipartiteEdgeCount G X Yᶜ =
      bipartiteEdgeCount G X univ := by
  unfold bipartiteEdgeCount
  rw [← sum_add_distrib]
  exact sum_congr rfl fun a _ => Finset.sum_add_sum_compl Y _

omit [Fintype B] [DecidableEq B] in
theorem bipartite_edge_count_add_compl_left (X : Finset A) (Y : Finset B) :
    bipartiteEdgeCount G X Y + bipartiteEdgeCount G Xᶜ Y =
      bipartiteEdgeCount G univ Y := by
  exact Finset.sum_add_sum_compl X _

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
theorem bipartite_edge_count_univ_right (X : Finset A) :
    bipartiteEdgeCount G X univ = ∑ a ∈ X, ((rightNeighbors G a).card : ℝ) := by
  apply sum_congr rfl
  intro a _
  simp [bipartiteEdgeIndicator, rightNeighbors]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem bipartite_edge_count_univ_left (Y : Finset B) :
    bipartiteEdgeCount G univ Y = ∑ b ∈ Y, ((leftNeighbors G b).card : ℝ) := by
  unfold bipartiteEdgeCount
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  simp [bipartiteEdgeIndicator, leftNeighbors]

theorem bipartite_cut_degree_identity (X : Finset A) (Y : Finset B) :
    bipartiteCutSize G X Y + 2 * bipartiteEdgeCount G X Y =
      (∑ a ∈ X, ((rightNeighbors G a).card : ℝ)) +
      ∑ b ∈ Y, ((leftNeighbors G b).card : ℝ) := by
  have hx := bipartite_edge_count_add_compl_right G X Y
  have hy := bipartite_edge_count_add_compl_left G X Y
  rw [bipartite_edge_count_univ_right] at hx
  rw [bipartite_edge_count_univ_left] at hy
  unfold bipartiteCutSize
  linarith

theorem bipartite_cut_compl (X : Finset A) (Y : Finset B) :
    bipartiteCutSize G Xᶜ Yᶜ = bipartiteCutSize G X Y := by
  simp [bipartiteCutSize, add_comm]

theorem bipartite_cut_nonneg (X : Finset A) (Y : Finset B) :
    0 ≤ bipartiteCutSize G X Y :=
  add_nonneg (bipartite_edge_count_nonneg G X Yᶜ)
    (bipartite_edge_count_nonneg G Xᶜ Y)

theorem bipartite_cut_sum (X : Finset A) (Y : Finset B) :
    bipartiteCutSize G X Y =
      ∑ a, ∑ b, if (a ∈ X) ≠ (b ∈ Y) then bipartiteEdgeIndicator G a b else 0 := by
  have hedges (U : Finset A) (W : Finset B) :
      bipartiteEdgeCount G U W =
        ∑ a, ∑ b, if a ∈ U ∧ b ∈ W then bipartiteEdgeIndicator G a b else 0 := by
    unfold bipartiteEdgeCount
    simp_rw [ite_and, sum_ite_irrel]
    simp
  rw [bipartiteCutSize, hedges, hedges, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  by_cases ha : a ∈ X <;> by_cases hb : b ∈ Y <;> simp [ha, hb]

/-- The graph form of the finite signed-flow criterion. The cut and the
support of the resulting weights are computed from actual edges of `G`. -/
theorem bipartite_signed_flow_of_cut (M : ℝ) (hM : 0 ≤ M)
    (r : A → ℝ) (s : B → ℝ) (htotal : ∑ a, r a = ∑ b, s b)
    (hcut : ∀ X : Finset A, ∀ Y : Finset B,
      (∑ a ∈ X, r a) - (∑ b ∈ Y, s b) ≤ M * bipartiteCutSize G X Y) :
    ∃ z : A → B → ℝ,
      (∀ a b, ¬ G.Adj (.inl a) (.inr b) → z a b = 0) ∧
      (∀ a, ∑ b, z a b = r a) ∧
      (∀ b, ∑ a, z a b = s b) ∧
      ∀ a b, |z a b| ≤ M := by
  classical
  let capacity : A × B → ℝ := fun e => M * bipartiteEdgeIndicator G e.1 e.2
  let demand : A ⊕ B → ℝ := Sum.elim r (fun b => -s b)
  have hcapacity : ∀ e, 0 ≤ capacity e := fun e =>
    mul_nonneg hM (bipartite_edge_indicator_nonneg G e.1 e.2)
  have hsum : ∑ v, demand v = 0 := by
    simp only [demand, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_neg_distrib]
    linarith
  have hc : ∀ S : Finset (A ⊕ B), ∑ v ∈ S, demand v ≤
      ∑ e : A × B, if (Sum.inr e.2 ∈ S) ≠ (Sum.inl e.1 ∈ S)
        then capacity e else 0 := by
    intro S
    let X : Finset A := univ.filter (fun a => Sum.inl a ∈ S)
    let Y : Finset B := univ.filter (fun b => Sum.inr b ∈ S)
    have hd : ∑ v ∈ S, demand v = (∑ a ∈ X, r a) - ∑ b ∈ Y, s b := by
      calc
        _ = ∑ v, if v ∈ S then demand v else 0 := by simp
        _ = _ := by
          rw [Fintype.sum_sum_type]
          simp only [demand, X, Y, sum_filter, Sum.elim_inl, Sum.elim_inr,
            sub_eq_add_neg, ← sum_neg_distrib]
          congr 1
          apply sum_congr rfl
          intro b _
          split_ifs <;> simp only [neg_zero]
    have he :
        (∑ e : A × B, if (Sum.inr e.2 ∈ S) ≠ (Sum.inl e.1 ∈ S)
          then capacity e else 0) = M * bipartiteCutSize G X Y := by
      rw [bipartite_cut_sum, Fintype.sum_prod_type, mul_sum]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      simp only [X, Y, mem_filter, mem_univ, true_and, capacity]
      by_cases ha : Sum.inl a ∈ S <;> by_cases hb : Sum.inr b ∈ S <;> simp [ha, hb]
    rw [hd, he]
    exact hcut X Y
  obtain ⟨z, hz, hrow⟩ := BoundedFlow.exists_of_cut
    (fun e : A × B => Sum.inl e.1) (fun e => Sum.inr e.2)
    capacity demand hcapacity hsum hc
  refine ⟨fun a b => z (a, b), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h := hz (a, b)
    simp only [capacity, bipartiteEdgeIndicator, hab, if_false, mul_zero] at h
    exact abs_nonpos_iff.mp h
  · intro a
    have h := hrow (Sum.inl a)
    simp only [Fintype.sum_prod_type, Sum.inl.injEq, Sum.inr_ne_inl, if_false,
      sum_const_zero, sub_zero, demand, Sum.elim_inl] at h
    rw [sum_comm] at h
    simpa only [sum_ite_eq', mem_univ, if_true] using h
  · intro b
    have h := hrow (Sum.inr b)
    simp only [Fintype.sum_prod_type, Sum.inl_ne_inr, if_false, sum_const_zero,
      Sum.inr.injEq, sum_ite_eq', mem_univ, if_true, zero_sub,
      demand, Sum.elim_inr, neg_inj] at h
    exact h
  · intro a b
    refine (hz (a, b)).trans ?_
    dsimp [capacity, bipartiteEdgeIndicator]
    split_ifs
    · simp
    · simpa using hM

end Overfull

namespace Overfull

open Finset

/-- A uniform bound on each demand bounds the total demand of every pair
of vertex subsets. -/
theorem bipartite_demand_abs_le {A B : Type*}
    (r : A → ℝ) (s : B → ℝ) (α β : ℝ)
    (hr : ∀ a, |r a| ≤ α) (hs : ∀ b, |s b| ≤ β)
    (X : Finset A) (Y : Finset B) :
    |(∑ a ∈ X, r a) - ∑ b ∈ Y, s b| ≤ α * X.card + β * Y.card := by
  calc
    _ ≤ |∑ a ∈ X, r a| + |∑ b ∈ Y, s b| := abs_sub _ _
    _ ≤ (∑ a ∈ X, |r a|) + ∑ b ∈ Y, |s b| :=
      add_le_add (Finset.abs_sum_le_sum_abs r X) (Finset.abs_sum_le_sum_abs s Y)
    _ ≤ (∑ _a ∈ X, α) + ∑ _b ∈ Y, β :=
      add_le_add (sum_le_sum fun a _ => hr a) (sum_le_sum fun b _ => hs b)
    _ = _ := by simp [mul_comm]

theorem bipartite_demand_compl {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → ℝ) (s : B → ℝ) (htotal : ∑ a, r a = ∑ b, s b)
    (X : Finset A) (Y : Finset B) :
    (∑ a ∈ Xᶜ, r a) - ∑ b ∈ Yᶜ, s b =
      -((∑ a ∈ X, r a) - ∑ b ∈ Y, s b) := by
  have hx := Finset.sum_add_sum_compl X r
  have hy := Finset.sum_add_sum_compl Y s
  linarith

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- A set containing at most half the vertices has at least `lam` times its
order crossing edges under the balanced minimum-degree hypothesis. -/
theorem balanced_bipartite_cut_lower (lam : ℝ)
    (hleft : ∀ a, (Fintype.card A : ℝ) / 2 + lam ≤ (rightNeighbors G a).card)
    (hright : ∀ b, (Fintype.card A : ℝ) / 2 + lam ≤ (leftNeighbors G b).card)
    (X : Finset A) (Y : Finset B)
    (hsize : (X.card : ℝ) + Y.card ≤ Fintype.card A) :
    lam * ((X.card : ℝ) + Y.card) ≤ bipartiteCutSize G X Y := by
  have hx : ((Fintype.card A : ℝ) / 2 + lam) * X.card ≤
      ∑ a ∈ X, ((rightNeighbors G a).card : ℝ) := by
    calc
      _ = ∑ _a ∈ X, ((Fintype.card A : ℝ) / 2 + lam) := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun a _ => hleft a
  have hy : ((Fintype.card A : ℝ) / 2 + lam) * Y.card ≤
      ∑ b ∈ Y, ((leftNeighbors G b).card : ℝ) := by
    calc
      _ = ∑ _b ∈ Y, ((Fintype.card A : ℝ) / 2 + lam) := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun b _ => hright b
  have hdegree := bipartite_cut_degree_identity G X Y
  have hinside := bipartite_edge_count_le G X Y
  have hsquare := sq_nonneg ((X.card : ℝ) - Y.card)
  have hproduct := mul_le_mul_of_nonneg_left hsize
    (add_nonneg (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card))
  nlinarith

/-- Lemma 5.6 of the manuscript (signed flow). Both vertex classes may be
empty. The real weights have the prescribed sums and vanish on nonedges. -/
theorem dense_signed_flow (lam d : ℝ) (hlam : 0 < lam)
    (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, (Fintype.card A : ℝ) / 2 + lam ≤ (rightNeighbors G a).card)
    (hright : ∀ b, (Fintype.card A : ℝ) / 2 + lam ≤ (leftNeighbors G b).card)
    (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, |r a| ≤ d) (hs : ∀ b, |s b| ≤ d)
    (htotal : ∑ a, r a = ∑ b, s b) :
    ∃ z : A → B → ℝ,
      (∀ a b, ¬ G.Adj (.inl a) (.inr b) → z a b = 0) ∧
      (∀ a, ∑ b, z a b = r a) ∧
      (∀ b, ∑ a, z a b = s b) ∧
      ∀ a b, |z a b| ≤ d / lam := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · letI := hA
    haveI : IsEmpty B := Fintype.card_eq_zero_iff.mp
      (hbalance.symm.trans (Fintype.card_eq_zero))
    exact ⟨fun _ _ => 0, by simp⟩
  · obtain ⟨a⟩ := hA
    have hd : 0 ≤ d := (abs_nonneg (r a)).trans (hr a)
    have hM : 0 ≤ d / lam := div_nonneg hd hlam.le
    apply bipartite_signed_flow_of_cut G (d / lam) hM r s htotal
    intro X Y
    have hsmall (U : Finset A) (W : Finset B)
        (hsize : (U.card : ℝ) + W.card ≤ Fintype.card A) :
        |(∑ a ∈ U, r a) - ∑ b ∈ W, s b| ≤
          (d / lam) * bipartiteCutSize G U W := by
      have hc := balanced_bipartite_cut_lower G lam hleft hright U W hsize
      have hh := mul_le_mul_of_nonneg_left hc hM
      have hcancel : (d / lam) * (lam * ((U.card : ℝ) + W.card)) =
          d * ((U.card : ℝ) + W.card) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hlam.ne']
      calc
        _ ≤ d * U.card + d * W.card := bipartite_demand_abs_le r s d d hr hs U W
        _ = d * ((U.card : ℝ) + W.card) := by ring
        _ ≤ _ := by rwa [hcancel] at hh
    apply (le_abs_self _).trans
    by_cases hsize : (X.card : ℝ) + Y.card ≤ Fintype.card A
    · exact hsmall X Y hsize
    · have hx : (Xᶜ.card : ℝ) + X.card = Fintype.card A := by
        exact_mod_cast Finset.card_compl_add_card X
      have hy : (Yᶜ.card : ℝ) + Y.card = Fintype.card A := by
        rw [hbalance]
        exact_mod_cast Finset.card_compl_add_card Y
      have hcomp : (Xᶜ.card : ℝ) + Yᶜ.card ≤ Fintype.card A := by linarith
      have hh := hsmall Xᶜ Yᶜ hcomp
      rw [bipartite_demand_compl r s htotal, abs_neg, bipartite_cut_compl] at hh
      exact hh

end Overfull



