import Overfull.BipartiteFactorization.Capacity
import Overfull.BipartiteFactorization.Preferred

/-!
# Actual correction-pool imbalance

All counts are of original edge copies. The signed identity applies to
any retained set of copies with no core incidences at inactive vertices.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- Copies with one end in each of the indicated vertex sets. -/
def betweenCopies (X Y : Finset V) : Finset E :=
  X.biUnion (fun x => G.edgesTo x Y)

/-- Wrong-side exceptional copies together with internal side copies. -/
def correctionPool (B ZA : Finset V) : Finset E :=
  G.internalEdges B ∪ betweenCopies G ZA B

theorem mem_betweenCopies (X Y : Finset V) (e : E) :
    e ∈ betweenCopies G X Y ↔
      (G.firstEnd e ∈ X ∧ G.secondEnd e ∈ Y) ∨
        (G.secondEnd e ∈ X ∧ G.firstEnd e ∈ Y) := by
  simp only [betweenCopies, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨hxe, hy⟩ := (G.mem_edgesTo x Y e).mp he
    rcases (G.incident_iff e x).mp hxe with h | h
    · subst x
      exact Or.inl ⟨hx, (G.otherEnd_eq_of_edge e _ _ (G.edge_eq e).symm) ▸ hy⟩
    · subst x
      exact Or.inr ⟨hx,
        (G.otherEnd_eq_of_edge e _ _ ((G.edge_eq e).symm.trans Sym2.eq_swap)) ▸ hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · refine ⟨G.firstEnd e, hx, (G.mem_edgesTo _ _ _).mpr ⟨?_, ?_⟩⟩
      · rw [← G.edge_eq e]; simp
      · rw [G.otherEnd_eq_of_edge e _ _ (G.edge_eq e).symm]
        exact hy
    · refine ⟨G.secondEnd e, hy, (G.mem_edgesTo _ _ _).mpr ⟨?_, ?_⟩⟩
      · rw [← G.edge_eq e]; simp
      · rw [G.otherEnd_eq_of_edge e _ _ ((G.edge_eq e).symm.trans Sym2.eq_swap)]
        exact hx

theorem betweenCopies_inter_card (F : Finset E) (X Y : Finset V)
    (hXY : Disjoint X Y) :
    (F ∩ betweenCopies G X Y).card = ∑ x ∈ X, (F ∩ G.edgesTo x Y).card := by
  have heq : F ∩ betweenCopies G X Y = X.biUnion (fun x => F ∩ G.edgesTo x Y) := by
    ext e
    simp only [betweenCopies, Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [heq]
  apply Finset.card_biUnion
  intro x hx y hy hxy
  have hd := (correction_pools_disjoint G Y X hXY.symm).2
    ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h))
  exact hd.mono Finset.inter_subset_right Finset.inter_subset_right

/-- The endpoint contribution of one copy to a side degree sum. -/
def sideIncidence (X : Finset V) (e : E) : ℤ :=
  (if G.firstEnd e ∈ X then 1 else 0) +
    (if G.secondEnd e ∈ X then 1 else 0)

theorem restricted_degree_sum (F : Finset E) (X : Finset V) :
    (∑ v ∈ X, ((G.restrictEdges F).degree v : ℤ)) =
      ∑ e ∈ F, sideIncidence G X e := by
  have hsum : (∑ v ∈ X, (F ∩ G.incidenceEdges v).card) =
      ∑ e ∈ F, (X.filter (fun v => v ∈ G.edge e)).card := by
    have hf (v : V) : F ∩ G.incidenceEdges v = F.filter (fun e => v ∈ G.edge e) := by
      ext e
      simp
    simp only [hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hcount (e : E) :
      ((X.filter (fun v => v ∈ G.edge e)).card : ℤ) = sideIncidence G X e := by
    have hfilter : X.filter (fun v => v ∈ G.edge e) =
        (if G.firstEnd e ∈ X then {G.firstEnd e} else ∅) ∪
          (if G.secondEnd e ∈ X then {G.secondEnd e} else ∅) := by
      ext v
      by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
        simp [h₁, h₂, G.incident_iff] <;> aesop
    rw [hfilter]
    have hne := G.endpoints_distinct e
    by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
      simp [sideIncidence, h₁, h₂, hne.symm]
  simp_rw [Multigraph.restrictEdges_degree]
  rw [← Nat.cast_sum, hsum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun e _ => hcount e)

/-- A retained core-exceptional copy has an active exceptional endpoint
when all inactive core rows are empty. -/
theorem retained_copy_active_ends (F : Finset E) (U Z : Finset V)
    (hlow : ∀ x, x ∉ U → x ∉ Z → F ∩ G.edgesTo x U = ∅)
    (e : E) (he : e ∈ F) :
    (G.firstEnd e ∈ U → G.secondEnd e ∈ U ∨ G.secondEnd e ∈ Z) ∧
      (G.secondEnd e ∈ U → G.firstEnd e ∈ U ∨ G.firstEnd e ∈ Z) := by
  have hactive (x y : V) (heq : G.edge e = s(x,y)) (hy : y ∈ U) :
      x ∈ U ∨ x ∈ Z := by
    by_contra hn
    have hxU : x ∉ U := fun hx => hn (Or.inl hx)
    have hxZ : x ∉ Z := fun hx => hn (Or.inr hx)
    have hmem : e ∈ F ∩ G.edgesTo x U := by
      refine Finset.mem_inter.mpr ⟨he, (G.mem_edgesTo _ _ _).mpr ⟨?_, ?_⟩⟩
      · simp [heq]
      · rw [G.otherEnd_eq_of_edge e x y heq]
        exact hy
    rw [hlow x hxU hxZ] at hmem
    exact Finset.notMem_empty _ hmem
  exact ⟨hactive _ _ ((G.edge_eq e).symm.trans Sym2.eq_swap),
    hactive _ _ (G.edge_eq e).symm⟩

theorem correction_identity_at_copy (A B ZA ZB : Finset V)
    (hAB : Disjoint A B) (hZA : Disjoint ZA (A ∪ B))
    (hZB : Disjoint ZB (A ∪ B)) (hZZ : Disjoint ZA ZB)
    (e : E)
    (hactive :
      (G.firstEnd e ∈ A ∪ B → G.secondEnd e ∈ A ∪ B ∨ G.secondEnd e ∈ ZA ∪ ZB) ∧
      (G.secondEnd e ∈ A ∪ B → G.firstEnd e ∈ A ∪ B ∨ G.firstEnd e ∈ ZA ∪ ZB)) :
    sideIncidence G A e - sideIncidence G B e =
      (if e ∈ betweenCopies G ZA (A ∪ B) then (1 : ℤ) else 0) -
      (if e ∈ betweenCopies G ZB (A ∪ B) then (1 : ℤ) else 0) -
      2 * ((if e ∈ correctionPool G B ZA then (1 : ℤ) else 0) -
        (if e ∈ correctionPool G A ZB then (1 : ℤ) else 0)) := by
  have hdis (x : V) :
      ¬ (x ∈ A ∧ x ∈ B) ∧
      ¬ (x ∈ ZA ∧ (x ∈ A ∨ x ∈ B)) ∧
      ¬ (x ∈ ZB ∧ (x ∈ A ∨ x ∈ B)) ∧ ¬ (x ∈ ZA ∧ x ∈ ZB) := by
    refine ⟨fun h => Finset.disjoint_left.mp hAB h.1 h.2,
      fun h => Finset.disjoint_left.mp hZA h.1 (Finset.mem_union.mpr h.2),
      fun h => Finset.disjoint_left.mp hZB h.1 (Finset.mem_union.mpr h.2),
      fun h => Finset.disjoint_left.mp hZZ h.1 h.2⟩
  have hcases (x : V) :
      (x ∈ A ∧ x ∉ B ∧ x ∉ ZA ∧ x ∉ ZB) ∨
      (x ∉ A ∧ x ∈ B ∧ x ∉ ZA ∧ x ∉ ZB) ∨
      (x ∉ A ∧ x ∉ B ∧ x ∈ ZA ∧ x ∉ ZB) ∨
      (x ∉ A ∧ x ∉ B ∧ x ∉ ZA ∧ x ∈ ZB) ∨
      (x ∉ A ∧ x ∉ B ∧ x ∉ ZA ∧ x ∉ ZB) := by
    obtain ⟨hab, hza, hzb, hzz⟩ := hdis x
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, fun hb => hab ⟨ha, hb⟩,
        fun hz => hza ⟨hz, Or.inl ha⟩, fun hz => hzb ⟨hz, Or.inl ha⟩⟩
    apply Or.inr
    by_cases hb : x ∈ B
    · exact Or.inl ⟨ha, hb, fun hz => hza ⟨hz, Or.inr hb⟩,
        fun hz => hzb ⟨hz, Or.inr hb⟩⟩
    apply Or.inr
    by_cases hza' : x ∈ ZA
    · exact Or.inl ⟨ha, hb, hza', fun hz => hzz ⟨hza', hz⟩⟩
    apply Or.inr
    by_cases hzb' : x ∈ ZB
    · exact Or.inl ⟨ha, hb, hza', hzb'⟩
    · exact Or.inr ⟨ha, hb, hza', hzb'⟩
  have hx := hcases (G.firstEnd e)
  have hy := hcases (G.secondEnd e)
  clear hcases hdis hAB hZA hZB hZZ
  simp only [sideIncidence, correctionPool, Finset.mem_union,
    Multigraph.mem_internalEdges, mem_betweenCopies] at hactive ⊢
  rcases hx with hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy | hy <;> simp_all

/-- Exact signed degree accounting for actual copies, including all
parallel copies in the two correction pools. -/
theorem correction_imbalance_identity (F : Finset E) (A B ZA ZB : Finset V)
    (hAB : Disjoint A B) (hZA : Disjoint ZA (A ∪ B))
    (hZB : Disjoint ZB (A ∪ B)) (hZZ : Disjoint ZA ZB)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      F ∩ G.edgesTo x (A ∪ B) = ∅) :
    (∑ v ∈ A, ((G.restrictEdges F).degree v : ℤ)) -
        (∑ v ∈ B, ((G.restrictEdges F).degree v : ℤ)) =
      (∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) -
        (∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) -
      2 * (((F ∩ correctionPool G B ZA).card : ℤ) -
        (F ∩ correctionPool G A ZB).card) := by
  have hcount (S : Finset E) :
      (∑ e ∈ F, if e ∈ S then (1 : ℤ) else 0) = (F ∩ S).card := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.filter_mem_eq_inter]
  have hZAcount : ((F ∩ betweenCopies G ZA (A ∪ B)).card : ℤ) =
      ∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ) := by
    exact_mod_cast betweenCopies_inter_card G F ZA (A ∪ B) hZA
  have hZBcount : ((F ∩ betweenCopies G ZB (A ∪ B)).card : ℤ) =
      ∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ) := by
    exact_mod_cast betweenCopies_inter_card G F ZB (A ∪ B) hZB
  rw [restricted_degree_sum, restricted_degree_sum]
  have hsum := Finset.sum_congr (s₁ := F) rfl (fun e he =>
    correction_identity_at_copy G A B ZA ZB hAB hZA hZB hZZ e
      (retained_copy_active_ends G F (A ∪ B) (ZA ∪ ZB) hlow e he))
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount, hZAcount, hZBcount]
    using hsum

/-- The manuscript imbalance identity follows from the actual equality
of the two side-degree sums of the palette graph. -/
theorem balanced_correction_imbalance (F : Finset E) (A B ZA ZB : Finset V)
    (hAB : Disjoint A B) (hZA : Disjoint ZA (A ∪ B))
    (hZB : Disjoint ZB (A ∪ B)) (hZZ : Disjoint ZA ZB)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      F ∩ G.edgesTo x (A ∪ B) = ∅)
    (hdegree : (∑ v ∈ A, (G.restrictEdges F).degree v) =
      ∑ v ∈ B, (G.restrictEdges F).degree v) :
    (∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) -
        (∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) =
      2 * (((F ∩ correctionPool G B ZA).card : ℤ) -
        (F ∩ correctionPool G A ZB).card) := by
  have h := correction_imbalance_identity G F A B ZA ZB hAB hZA hZB hZZ hlow
  have hd : (∑ v ∈ A, ((G.restrictEdges F).degree v : ℤ)) =
      ∑ v ∈ B, ((G.restrictEdges F).degree v : ℤ) := by exact_mod_cast hdegree
  rw [hd, sub_self] at h
  omega

/-- Filling the same actual exceptional rows with exactly the required
number of positive correction copies makes the selected side sums equal. -/
theorem selected_degree_balance (F C : Finset E) (A B ZA ZB : Finset V)
    (hAB : Disjoint A B) (hZA : Disjoint ZA (A ∪ B))
    (hZB : Disjoint ZB (A ∪ B)) (hZZ : Disjoint ZA ZB)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
      F ∩ G.edgesTo x (A ∪ B) = ∅)
    (hplus : F ∩ correctionPool G B ZA = C)
    (hminus : F ∩ correctionPool G A ZB = ∅)
    (hdemand : (∑ x ∈ ZA, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) -
      (∑ x ∈ ZB, ((F ∩ G.edgesTo x (A ∪ B)).card : ℤ)) = 2 * C.card) :
    (∑ v ∈ A, (G.restrictEdges F).degree v) =
      ∑ v ∈ B, (G.restrictEdges F).degree v := by
  have h := correction_imbalance_identity G F A B ZA ZB hAB hZA hZB hZZ hlow
  rw [hplus, hminus, Finset.card_empty, Nat.cast_zero, sub_zero, hdemand, sub_self] at h
  have hd : (∑ v ∈ A, ((G.restrictEdges F).degree v : ℤ)) =
      ∑ v ∈ B, ((G.restrictEdges F).degree v : ℤ) := sub_eq_zero.mp h
  exact_mod_cast hd

end Overfull.BipartiteFactorization
