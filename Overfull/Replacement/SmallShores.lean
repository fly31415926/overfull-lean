import Overfull.Replacement.Graph

/-!
# Comparing the only possible shores of an overfull set

A robust replacement rules out cuts having at least two core vertices on
both sides. On the four remaining shores, the new regular core has no
more edges than the old core.
-/

namespace Overfull.Replacement

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem internal_count_mono {G H : SimpleGraph V} (hGH : G ≤ H) (X : Finset V) :
    (internalEdges G X).card ≤ (internalEdges H X).card := by
  rw [internal_count_eq, internal_count_eq]
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_inter.mpr ⟨SimpleGraph.edgeFinset_mono hGH
    (Finset.mem_inter.mp he).1, (Finset.mem_inter.mp he).2⟩

theorem internal_count_small (G : SimpleGraph V) (S : Finset V) (hS : S.card ≤ 1) :
    (internalEdges G S).card = 0 := by
  rw [internal_count_eq, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨v,w⟩ := e
  simp only [Finset.mem_inter, Finset.mk_mem_sym2_iff] at he
  obtain ⟨hvw, hv, hw⟩ := he
  have hvw' : G.Adj v w := SimpleGraph.mem_edgeFinset.mp hvw
  have heq : v = w := (Finset.card_le_one.mp hS) v hv w hw
  exact hvw'.ne heq

theorem internal_compl_singleton (G : SimpleGraph V) (v : V) :
    (internalEdges G ({v} : Finset V)ᶜ).card + G.degree v = G.edgeFinset.card := by
  rw [internal_count_eq, ← SimpleGraph.card_incidenceFinset_eq_degree]
  have heq : G.edgeFinset ∩ ({v} : Finset V)ᶜ.sym2 =
      G.edgeFinset \ G.incidenceFinset v := by
    ext e
    obtain ⟨x,y⟩ := e
    simp only [Finset.mem_inter, Finset.mk_mem_sym2_iff, Finset.mem_compl,
      Finset.mem_singleton, Finset.mem_sdiff, SimpleGraph.mem_incidenceFinset,
      SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    tauto
  rw [heq]
  exact Finset.card_sdiff_add_card_eq_card (G.incidenceFinset_subset v)

theorem regular_small_shore_comparison (H R : SimpleGraph V) (m r k : ℕ)
    (horder : Fintype.card V = 2*m)
    (hR : ∀ v, R.degree v = r)
    (hHlower : ∀ v, r+1 ≤ H.degree v)
    (hHupper : ∀ v, H.degree v ≤ k)
    (hk : k ≤ m+r) (S : Finset V)
    (hsmall : S.card ≤ 1 ∨ Sᶜ.card ≤ 1) :
    (internalEdges R S).card ≤ (internalEdges H S).card := by
  have hRsum : (∑ v, R.degree v) = (2*m)*r := by simp [hR, horder]
  have hRtotal : R.edgeFinset.card = m*r := by
    have hh := R.sum_degrees_eq_twice_card_edges
    rw [hRsum] at hh
    nlinarith only [hh]
  have hHsum : (2*m)*(r+1) ≤ ∑ v, H.degree v := by
    calc
      _ = ∑ _v : V, (r+1) := by simp [horder]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hHlower v)
  have hHtotal : m*(r+1) ≤ H.edgeFinset.card := by
    rw [H.sum_degrees_eq_twice_card_edges] at hHsum
    nlinarith only [hHsum]
  rcases hsmall with hsmall | hsmall
  · rw [internal_count_small R S hsmall]
    exact Nat.zero_le _
  · by_cases hzero : Sᶜ.card = 0
    · have hempty : Sᶜ = ∅ := Finset.card_eq_zero.mp hzero
      have hS : S = univ := by
        apply Finset.ext
        intro v
        have hv : v ∉ Sᶜ := by rw [hempty]; simp
        simpa only [Finset.mem_univ, iff_true, Finset.mem_compl, not_not] using hv
      rw [hS, internalEdges_univ_card, internalEdges_univ_card, hRtotal]
      exact (Nat.mul_le_mul_left m (Nat.le_succ r)).trans hHtotal
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show Sᶜ.card = 1 by omega)
      have hS : S = ({v} : Finset V)ᶜ := by
        have hh := congrArg (fun T : Finset V => Tᶜ) hv
        simpa only [compl_compl] using hh
      rw [hS]
      have hRc := internal_compl_singleton R v
      have hHc := internal_compl_singleton H v
      rw [hR v, hRtotal] at hRc
      have hvupper := hHupper v
      nlinarith only [hRc,hHc,hHtotal,hvupper,hk]

theorem no_overfull_of_core_cuts (G : SimpleGraph V) (U : Finset V)
    (H R : SimpleGraph U) (k : ℕ) (hH : H ≤ G.induce (U : Set V))
    (hdegree : ∀ v, (graph G U H R).degree v ≤ k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (hcuts : ∀ S : Finset U, 2 ≤ S.card → 2 ≤ Sᶜ.card →
      k < (Multigraph.ofSimpleGraph (core G U H R)).cutSize S)
    (hsmall : ∀ S : Finset U, S.card ≤ 1 ∨ Sᶜ.card ≤ 1 →
      (internalEdges (core G U H R) S).card ≤ (internalEdges H S).card) :
    ∀ X : Finset V, ¬ IsOverfull (graph G U H R) k X := by
  intro X hX
  have hodd : X.card % 2 = 1 := by
    by_contra hh
    exact not_overfull_of_even_card (graph G U H R) X k hdegree (by omega) hX
  have hfail := (overfull_iff_odd_deficiency (graph G U H R) X k hdegree hodd).mp hX
  have hcut : (Multigraph.ofSimpleGraph (graph G U H R)).cutSize X < k := by
    rw [SmallCuts.simple_cut_boundary]
    omega
  let S := SmallCuts.shore U X
  have hshore : S.card ≤ 1 ∨ Sᶜ.card ≤ 1 := by
    by_contra hh
    have hlo : 2 ≤ S.card := by omega
    have hhi : 2 ≤ Sᶜ.card := by omega
    have hcore := hcuts S hlo hhi
    have hamb := cut_core_le (graph G U H R) U (core G U H R)
      (core_lift_le G U H R) X
    change (Multigraph.ofSimpleGraph (core G U H R)).cutSize S ≤ _ at hamb
    omega
  have hcompare := hsmall S hshore
  have hid := graph_internal_count_identity G U H R hH X
  have hle : (internalEdges (graph G U H R) X).card ≤ (internalEdges G X).card := by
    change (internalEdges (core G U H R) (SmallCuts.shore U X)).card ≤
      (internalEdges H (SmallCuts.shore U X)).card at hcompare
    omega
  exact hno X (lt_of_lt_of_le hX hle)

end Overfull.Replacement
