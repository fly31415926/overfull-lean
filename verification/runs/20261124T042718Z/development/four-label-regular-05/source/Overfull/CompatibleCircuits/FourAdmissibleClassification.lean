import Overfull.CompatibleCircuits.FourAdmissibleTemplates
import Overfull.CompatibleCircuits.VertexRelabeling

/-! Deriving the canonical four-regular template from actual bundle counts. -/

namespace Overfull.CompatibleCircuits.FourRegular

open Finset Classical

def pairs : Fin 6 → Sym2 (Fin 4) :=
  ![s(0,1),s(0,2),s(0,3),s(1,2),s(1,3),s(2,3)]

def countVector (a b c : ℕ) : Fin 6 → ℕ := ![a,b,c,c,b,a]

def permutation : Fin 6 → Equiv.Perm (Fin 4) :=
  ![Equiv.refl _,Equiv.swap 1 2,Equiv.swap 1 3,Equiv.swap 2 3,
    (Equiv.swap 1 2).trans (Equiv.swap 2 3),
    (Equiv.swap 1 3).trans (Equiv.swap 2 3)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_template_counts : ∀ (a b c : Fin 5), a.val+b.val+c.val=4 →
    ∃ (t : Fin 4) (r : Fin 6), ∀ i : Fin 6,
      (univ.filter (fun e : Fin 8 =>
        Sym2.map (permutation r) ((graph t).edge e) = pairs i)).card =
          countVector a.val b.val c.val i := by
  decide +kernel

variable {E : Type*} (Q : Multigraph (Fin 4) E)

noncomputable def bundle (C : Finset E) (i : Fin 6) : Finset E :=
  C.filter (fun e => Q.edge e = pairs i)

theorem degree_bundle_sum (C : Finset E) (v : Fin 4) :
    Q.degreeOn C v = ∑ i : Fin 6, if v ∈ pairs i then (bundle Q C i).card else 0 := by
  have hlocal : ∀ (x y v : Fin 4), x ≠ y →
      (if v ∈ s(x,y) then 1 else 0 : ℕ) =
        ∑ i : Fin 6, if v ∈ pairs i ∧ s(x,y) = pairs i then 1 else 0 := by decide
  calc
    Q.degreeOn C v = ∑ e ∈ C, if v ∈ Q.edge e then 1 else 0 := by
      simp only [Multigraph.degreeOn,card_eq_sum_ones,sum_filter]
      apply sum_congr rfl
      intro e _
      split_ifs <;> rfl
    _ = ∑ e ∈ C, ∑ i : Fin 6,
        if v ∈ pairs i ∧ Q.edge e = pairs i then 1 else 0 := by
      apply sum_congr rfl
      intro e _
      rw [← Q.edge_eq e]
      exact hlocal _ _ _ (Q.endpoints_distinct e)
    _ = ∑ i : Fin 6, ∑ e ∈ C,
        if v ∈ pairs i ∧ Q.edge e = pairs i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      by_cases hi : v ∈ pairs i
      · simp only [hi,true_and,ite_true,bundle,card_eq_sum_ones,sum_filter]
      · simp only [hi,false_and,ite_false,sum_const_zero]

theorem regular_bundle_counts (C : Finset E)
    (hregular : ∀ v, Q.degreeOn C v = 4) :
    (bundle Q C 0).card+(bundle Q C 1).card+(bundle Q C 2).card=4 ∧
    ∀ i : Fin 6, (bundle Q C i).card = countVector
      (bundle Q C 0).card (bundle Q C 1).card (bundle Q C 2).card i := by
  have h0 := degree_bundle_sum Q C 0
  have h1 := degree_bundle_sum Q C 1
  have h2 := degree_bundle_sum Q C 2
  have h3 := degree_bundle_sum Q C 3
  norm_num [hregular,Fin.sum_univ_succ,pairs,Sym2.mem_iff,Fin.ext_iff,Fin.succ]
    at h0 h1 h2 h3
  refine ⟨by omega,?_⟩
  intro i
  fin_cases i <;> norm_num [countVector] <;> omega

/-- Original counts force a template and a relabeling; these are conclusions. -/
theorem exists_template_counts (C : Finset E)
    (hregular : ∀ v, Q.degreeOn C v = 4) :
    ∃ (t : Fin 4) (r : Fin 6), ∀ i : Fin 6,
      (univ.filter (fun e : Fin 8 =>
        Sym2.map (permutation r) ((graph t).edge e) = pairs i)).card =
          (bundle Q C i).card := by
  obtain ⟨hsum,hcounts⟩ := regular_bundle_counts Q C hregular
  let a : Fin 5 := ⟨(bundle Q C 0).card,by omega⟩
  let b : Fin 5 := ⟨(bundle Q C 1).card,by omega⟩
  let c : Fin 5 := ⟨(bundle Q C 2).card,by omega⟩
  obtain ⟨t,r,htr⟩ := finite_template_counts a b c hsum
  exact ⟨t,r,fun i => (htr i).trans (hcounts i).symm⟩

theorem filter_card_subtype (C : Finset E) (f : E → Sym2 (Fin 4)) (p : Sym2 (Fin 4)) :
    Fintype.card {e : C // f e.val = p} = (C.filter (fun e => f e=p)).card := by
  let φ : {e : C // f e.val=p} ≃ {e : E // e ∈ C.filter (fun e => f e=p)} := {
    toFun := fun e => ⟨e.val.val,mem_filter.mpr ⟨e.val.property,e.property⟩⟩
    invFun := fun e => ⟨⟨e.val,(mem_filter.mp e.property).1⟩,(mem_filter.mp e.property).2⟩
    left_inv := by intro e; rfl
    right_inv := by intro e; rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr φ

/-- The template labels and actual-copy bijection are constructed from regularity. -/
theorem exists_template_copy_equiv (C : Finset E)
    (hregular : ∀ v, Q.degreeOn C v = 4) :
    ∃ (t : Fin 4) (r : Fin 6) (φ : Fin 8 ≃ C),
      ∀ e, Q.edge (φ e).val = Sym2.map (permutation r) ((graph t).edge e) := by
  obtain ⟨t,r,hcounts⟩ := exists_template_counts Q C hregular
  let A := (graph t).renameVertices (permutation r)
  have heq (p : Sym2 (Fin 4)) :
      (univ.filter (fun e : Fin 8 => A.edge e=p)).card =
        (C.filter (fun e => Q.edge e=p)).card := by
    have hcases : ∀ p : Sym2 (Fin 4), p.IsDiag ∨ ∃ i, pairs i=p := by decide
    rcases hcases p with hdiag | ⟨i,rfl⟩
    · have hleft : univ.filter (fun e : Fin 8 => A.edge e=p) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        exact A.loopless e (by simpa only [(mem_filter.mp he).2] using hdiag)
      have hright : C.filter (fun e => Q.edge e=p) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        exact Q.loopless e (by simpa only [(mem_filter.mp he).2] using hdiag)
      rw [hleft,hright]
      simp only [card_empty]
    · exact hcounts i
  let fibres (p : Sym2 (Fin 4)) :
      {e : Fin 8 // A.edge e=p} ≃ {e : C // Q.edge e.val=p} :=
    Fintype.equivOfCardEq (by
      rw [filter_card_subtype C Q.edge p]
      simpa only [Fintype.card_subtype] using heq p)
  let φ : Fin 8 ≃ C := Equiv.ofFiberEquiv fibres
  refine ⟨t,r,φ,?_⟩
  intro e
  exact Equiv.ofFiberEquiv_map fibres e

end Overfull.CompatibleCircuits.FourRegular
