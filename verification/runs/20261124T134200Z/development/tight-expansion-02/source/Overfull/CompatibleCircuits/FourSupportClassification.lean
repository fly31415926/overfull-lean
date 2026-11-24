import Overfull.CompatibleCircuits.FourStrictCycle

/-!
# Four-label simple support classification

The underlying simple support of a graph with four active labels and no
support leaf is a square, a diamond, or the complete graph. The finite
classification is checked in Lean's kernel; its graph application retains
the selected actual copies and proves that strict nonlocal bounds and the
absence of a compatible parallel pair supply the required support degrees.
-/

namespace Overfull.CompatibleCircuits.FourSupport

open Finset

def complete : Finset (Sym2 (Fin 4)) :=
  {s(0,1), s(0,2), s(0,3), s(1,2), s(1,3), s(2,3)}

def square : Finset (Sym2 (Fin 4)) := univ.image UniformCycle.pairs

def diamond : Finset (Sym2 (Fin 4)) := complete.erase s(2,3)

def squarePermutation : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.refl _, Equiv.swap 2 3, Equiv.swap 1 2]

def diamondPermutation : Fin 6 → Equiv.Perm (Fin 4) :=
  ![(Equiv.swap 0 2).trans (Equiv.swap 1 3), Equiv.swap 0 3,
    Equiv.swap 0 2, Equiv.swap 1 3, Equiv.swap 1 2, Equiv.refl _]

def renamed (S : Finset (Sym2 (Fin 4))) (σ : Equiv.Perm (Fin 4)) :
    Finset (Sym2 (Fin 4)) := S.image (Sym2.map σ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaustion over the ten unordered label pairs, excluding all loops.
No external computation or native decision axiom is used. -/
theorem classify_min_degree_two : ∀ S : Finset (Sym2 (Fin 4)),
    (∀ p ∈ S, ¬ p.IsDiag) →
    (∀ v : Fin 4, 2 ≤ (S.filter (fun p => v ∈ p)).card) →
    (∃ i : Fin 3, S = renamed square (squarePermutation i)) ∨
    (∃ i : Fin 6, S = renamed diamond (diamondPermutation i)) ∨
    S = complete := by
  decide

end Overfull.CompatibleCircuits.FourSupport

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits UniformCycle FourSupport

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- Strict nonlocal singleton cuts force every label to have positive
degree whenever there is at least one selected copy. -/
theorem StrictNonlocalOn.four_degree_pos
    {classOf : Fin 4 → E → K} {C : Finset E}
    (hstrict : Q.StrictNonlocalOn classOf C) (hC : C.Nonempty) (v : Fin 4) :
    0 < Q.degreeOn C v := by
  obtain ⟨e, _⟩ := hC
  have h := hstrict.singleton_bound Q (by decide) (next_ne v).symm (classOf (next v) e)
  omega

/-- No support leaf can remain under the same hypotheses, because all
incident copies at such a vertex belong to one nonempty endpoint bundle. -/
theorem StrictNonlocalOn.four_support_degree_ge_two
    {classOf : Fin 4 → E → K} {C : Finset E}
    (hstrict : Q.StrictNonlocalOn classOf C) (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2) (v : Fin 4) :
    2 ≤ ((C.image Q.edge).filter (fun p => v ∈ p)).card := by
  have hpos := hstrict.four_degree_pos Q hC v
  obtain ⟨e, he⟩ := card_pos.mp hpos
  obtain ⟨heC, hve⟩ := mem_filter.mp he
  have hedge_mem : Q.edge e ∈ (C.image Q.edge).filter (fun p => v ∈ p) :=
    mem_filter.mpr ⟨mem_image.mpr ⟨e, heC, rfl⟩, hve⟩
  have hsupportpos : 0 < ((C.image Q.edge).filter (fun p => v ∈ p)).card :=
    card_pos.mpr ⟨Q.edge e, hedge_mem⟩
  by_contra hbound
  have hone : ((C.image Q.edge).filter (fun p => v ∈ p)).card = 1 := by omega
  have honly (f : E) (hf : f ∈ C) (hvf : v ∈ Q.edge f) : Q.edge f = Q.edge e :=
    card_le_one.mp (by omega) (mem_filter.mpr ⟨mem_image.mpr ⟨f, hf, rfl⟩, hvf⟩)
      hedge_mem
  obtain ⟨u, hvu, hu⟩ : ∃ u, v ≠ u ∧ Q.edge e = s(v,u) := by
    rcases (Q.incident_iff e v).mp hve with hv | hv
    · exact ⟨Q.secondEnd e, by simpa only [hv] using Q.endpoints_distinct e,
        by rw [hv, Q.edge_eq]⟩
    · exact ⟨Q.firstEnd e, by simpa only [hv] using (Q.endpoints_distinct e).symm,
        by rw [hv, Sym2.eq_swap, Q.edge_eq]⟩
  have hB : (Q.edgeBundleOn C v u).Nonempty :=
    ⟨e, (Q.mem_edgeBundleOn C v u e).mpr ⟨heC, hu⟩⟩
  have hinc : C.filter (fun f => v ∈ Q.edge f) = Q.edgeBundleOn C v u := by
    ext f
    simp only [mem_filter, mem_edgeBundleOn]
    constructor
    · rintro ⟨hf, hvf⟩
      exact ⟨hf, (honly f hf hvf).trans hu⟩
    · rintro ⟨hf, hfends⟩
      exact ⟨hf, by simp [hfends]⟩
  exact Q.no_single_bundle_incidence_of_no_compatible_pair classOf C hadmissible hnone
    hvu hB (by
      convert hinc using 1
      ext f
      simp)

/-- Every strict nonlocal input without a compatible parallel pair has
one of the three exact simple support shapes, with relabelings provided. -/
theorem StrictNonlocalOn.four_support_classification
    {classOf : Fin 4 → E → K} {C : Finset E}
    (hstrict : Q.StrictNonlocalOn classOf C) (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2) :
    (∃ i : Fin 3, C.image Q.edge = renamed square (squarePermutation i)) ∨
    (∃ i : Fin 6, C.image Q.edge = renamed diamond (diamondPermutation i)) ∨
    C.image Q.edge = complete := by
  apply classify_min_degree_two
  · intro p hp
    obtain ⟨e, _, rfl⟩ := mem_image.mp hp
    exact Q.loopless e
  · exact hstrict.four_support_degree_ge_two Q hC hadmissible hnone

end Overfull.Multigraph
