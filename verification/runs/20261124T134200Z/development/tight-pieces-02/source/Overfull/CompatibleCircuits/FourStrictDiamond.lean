import Overfull.CompatibleCircuits.FourStrictComplete

/-!
# Diamond support forces a short compatible circuit

At the two support-degree-two vertices, strict singleton bounds force
equal opposite bundles.  A monochromatic blocker of each triangle then
contradicts the local half-degree inequalities at the two remaining
vertices.  All five positive bundles retain their original copies.
-/

namespace Overfull.Multigraph

open Finset Classical Overfull.CompatibleCircuits

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- The missing diagonal leaves exactly two bundles at each of its ends. -/
theorem fourLabel_diamond_incidence (C : Finset E)
    (h23 : Q.edgeBundleOn C 2 3 = ∅) :
    C.filter (fun e => (2 : Fin 4) ∈ Q.edge e) =
      Q.edgeBundleOn C 2 0 ∪ Q.edgeBundleOn C 2 1 ∧
    C.filter (fun e => (3 : Fin 4) ∈ Q.edge e) =
      Q.edgeBundleOn C 3 0 ∪ Q.edgeBundleOn C 3 1 := by
  have hnot (e : E) : e ∈ C → Q.edge e ≠ s((2 : Fin 4), 3) := by
    intro heC hends
    have he := (Q.mem_edgeBundleOn C 2 3 e).mpr ⟨heC, hends⟩
    rw [h23] at he
    exact notMem_empty e he
  constructor <;> ext e
  all_goals
    simp only [mem_filter, mem_union, mem_edgeBundleOn]
    have hloop := Q.endpoints_distinct e
    have hn := hnot e
    rw [← Q.edge_eq e] at hn ⊢
    generalize hx : Q.firstEnd e = x at *
    generalize hy : Q.secondEnd e = y at *
    fin_cases x <;> fin_cases y <;> simp_all

/-- The canonical diamond, with absent bundle `2--3`, always contains an
actual compatible pair or triangle in the strict nonlocal branch. -/
theorem exists_short_compatible_circuit_of_four_diamond_support
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C)
    (h01 : (Q.edgeBundleOn C 0 1).Nonempty)
    (h02 : (Q.edgeBundleOn C 0 2).Nonempty)
    (h03 : (Q.edgeBundleOn C 0 3).Nonempty)
    (h12 : (Q.edgeBundleOn C 1 2).Nonempty)
    (h13 : (Q.edgeBundleOn C 1 3).Nonempty)
    (h23 : Q.edgeBundleOn C 2 3 = ∅) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧ Q.Compatible classOf D ∧ D.card ≤ 3 := by
  by_contra hnone
  have hpair : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2 := by
    rintro ⟨D, hDC, hcir, hcomp, hcard⟩
    exact hnone ⟨D, hDC, hcir, hcomp, by omega⟩
  obtain ⟨hi2, hi3⟩ := Q.fourLabel_diamond_incidence C h23
  have h2 := Q.two_neighbor_bundle_structure classOf C hadmissible hpair
    (v := 2) (u := 0) (w := 1) (by decide) (by decide) (by decide)
    (by simpa only [Q.edgeBundleOn_swap C 2 0] using h02)
    (by simpa only [Q.edgeBundleOn_swap C 2 1] using h12)
    (by convert hi2 using 1 <;> ext e <;> simp)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
  have h3 := Q.two_neighbor_bundle_structure classOf C hadmissible hpair
    (v := 3) (u := 0) (w := 1) (by decide) (by decide) (by decide)
    (by simpa only [Q.edgeBundleOn_swap C 3 0] using h03)
    (by simpa only [Q.edgeBundleOn_swap C 3 1] using h13)
    (by convert hi3 using 1 <;> ext e <;> simp)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
  have heq2 := h2.1
  have heq3 := h3.1
  simp only [Q.edgeBundleOn_swap C 2 0, Q.edgeBundleOn_swap C 2 1] at heq2
  simp only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 1] at heq3
  let a := (Q.edgeBundleOn C 0 1).card
  let b := (Q.edgeBundleOn C 0 2).card
  let c := (Q.edgeBundleOn C 0 3).card
  let d := (Q.edgeBundleOn C 1 2).card
  let e := (Q.edgeBundleOn C 1 3).card
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Q.fourLabel_degree_bundle_counts C
  simp only [h23, card_empty, add_zero] at hd2 hd3
  have ha : 0 < a := card_pos.mpr h01
  have hb : 0 < b := card_pos.mpr h02
  have hc : 0 < c := card_pos.mpr h03
  have h012 : a + b ≤ c ∨ a + d ≤ e := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 0) (v := 1) (w := 2) (by decide) (by decide) (by decide)
      h01 h02 h12 with h | h | h
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 0) (u := 1) (w := 2) (by decide) (by decide) h
      rw [hd0] at hbnd
      exact Or.inl (by omega)
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 1) (u := 0) (w := 2) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 1 0] using h)
      simp only [Q.edgeBundleOn_swap C 1 0, hd1] at hbnd
      exact Or.inr (by omega)
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 2) (u := 0) (w := 1) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 2 0, Q.edgeBundleOn_swap C 2 1] using h)
      simp only [Q.edgeBundleOn_swap C 2 0, Q.edgeBundleOn_swap C 2 1, hd2] at hbnd
      omega
  have h013 : a + c ≤ b ∨ a + e ≤ d := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 0) (v := 1) (w := 3) (by decide) (by decide) (by decide)
      h01 h03 h13 with h | h | h
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 0) (u := 1) (w := 3) (by decide) (by decide) h
      rw [hd0] at hbnd
      exact Or.inl (by omega)
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 1) (u := 0) (w := 3) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 1 0] using h)
      simp only [Q.edgeBundleOn_swap C 1 0, hd1] at hbnd
      exact Or.inr (by omega)
    · have hbnd := Q.common_corner_local_bound classOf hadmissible
        (v := 3) (u := 0) (w := 1) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 1] using h)
      simp only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 1, hd3] at hbnd
      omega
  omega

end Overfull.Multigraph
