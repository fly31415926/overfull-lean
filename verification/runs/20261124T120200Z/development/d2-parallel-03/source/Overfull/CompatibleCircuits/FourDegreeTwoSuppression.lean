import Overfull.CompatibleCircuits.FourDegreeTwoParallel

/-!
# Suppression of a two-copy path

The copy `e` of `a-v` becomes a copy of `a-b`; the copy `f` of `v-b`
is removed from the selected set.  The new incidence at `b` inherits the
class of `f`.  All other original copies and incidence classes are retained.
Two placements of `v` in a tested shore prove the exact admissibility
transfer, including the class at the changed endpoint.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

def suppressionGraph (a b : V) (e : E) (hab : a ≠ b) : Multigraph V E where
  edge g := if g = e then s(a,b) else G.edge g
  loopless g := by
    by_cases h : g = e
    · simp only [h,if_pos,Sym2.isDiag_iff_proj_eq]
      exact hab
    · simpa only [h,if_false] using G.loopless g

def suppressionClass (classOf : V → E → K) (b : V) (e f : E) : V → E → K :=
  fun x g => if g = e ∧ x = b then classOf b f else classOf x g

@[simp] theorem suppressionGraph_edge_self (a b : V) (e : E) (hab : a ≠ b) :
    (G.suppressionGraph a b e hab).edge e = s(a,b) := by
  simp [suppressionGraph]

theorem suppressionGraph_edge_of_ne (a b : V) (e : E) (hab : a ≠ b)
    {g : E} (hge : g ≠ e) :
    (G.suppressionGraph a b e hab).edge g = G.edge g := by
  simp [suppressionGraph,hge]

@[simp] theorem suppressionClass_at_changed (classOf : V → E → K)
    (b : V) (e f : E) : suppressionClass classOf b e f b e = classOf b f := by
  simp [suppressionClass]

theorem suppressionClass_of_copy_ne (classOf : V → E → K) (b : V) (e f : E)
    (x : V) {g : E} (hge : g ≠ e) :
    suppressionClass classOf b e f x g = classOf x g := by
  simp [suppressionClass,hge]

theorem suppressionClass_of_vertex_ne (classOf : V → E → K) (b : V) (e f : E)
    {x : V} (hxb : x ≠ b) (g : E) :
    suppressionClass classOf b e f x g = classOf x g := by
  simp [suppressionClass,hxb]

theorem suppressionGraph_mem_cut_of_copy_ne
    (a b : V) (e : E) (hab : a ≠ b) {g : E} (hge : g ≠ e)
    (C : Finset E) (X : Finset V) :
    g ∈ (G.suppressionGraph a b e hab).cutOn C X ↔ g ∈ G.cutOn C X := by
  have h := G.suppressionGraph_edge_of_ne a b e hab hge
  unfold cutOn firstEnd secondEnd
  simp only [mem_filter,h]

theorem suppressionGraph_cutOn
    (C : Finset E) (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (X : Finset V) :
    (G.suppressionGraph a b e hab).cutOn (C.erase f) X =
      G.cutOn C (moveShore b v X) := by
  ext g
  by_cases hge : g = e
  · subst g
    rw [(G.suppressionGraph a b e hab).mem_cutOn_of_edge_eq
      (G.suppressionGraph_edge_self a b e hab),G.mem_cutOn_of_edge_eq he]
    simp only [mem_erase,hef,not_false_eq_true,true_and,
      mem_moveShore_of_ne b v X hav,mem_moveShore_self]
  by_cases hgf : g = f
  · subst g
    rw [G.suppressionGraph_mem_cut_of_copy_ne a b e hab hef.symm,
      G.mem_cutOn_of_edge_eq hf,G.mem_cutOn_of_edge_eq hf]
    simp only [mem_erase,ne_self_iff_false,false_and,mem_moveShore_self,
      mem_moveShore_of_ne b v X hbv]
    simp
  by_cases hgC : g ∈ C
  · have hv : v ∉ G.edge g := by
      intro hvg
      rcases hstar g hgC hvg with h | h
      · exact hge h
      · exact hgf h
    rw [G.suppressionGraph_mem_cut_of_copy_ne a b e hab hge,
      G.cutOn_moveShore_of_not_incident b v X C hv]
    simp only [mem_cutOn,mem_erase,hgf,not_false_eq_true,true_and]
  · simp only [mem_cutOn,mem_erase,hgC,and_false,false_and]

theorem suppressionGraph_swap_cutOn
    (C : Finset E) (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (X : Finset V) :
    ((G.suppressionGraph a b e hab).cutOn (C.erase f) X).map
        (Equiv.swap e f).toEmbedding = G.cutOn C (moveShore a v X) := by
  ext g
  simp only [mem_map_equiv,Equiv.symm_swap]
  by_cases hge : g = e
  · subst g
    rw [Equiv.swap_apply_left,G.mem_cutOn_of_edge_eq he]
    simp only [mem_cutOn,mem_erase,ne_self_iff_false,false_and,
      mem_moveShore_of_ne a v X hav,mem_moveShore_self]
    simp
  by_cases hgf : g = f
  · subst g
    rw [Equiv.swap_apply_right,
      (G.suppressionGraph a b e hab).mem_cutOn_of_edge_eq
        (G.suppressionGraph_edge_self a b e hab),G.mem_cutOn_of_edge_eq hf]
    simp only [mem_erase,hef,not_false_eq_true,heC,hfC,true_and,
      mem_moveShore_self,mem_moveShore_of_ne a v X hbv]
  rw [Equiv.swap_apply_of_ne_of_ne hge hgf]
  by_cases hgC : g ∈ C
  · have hv : v ∉ G.edge g := by
      intro hvg
      rcases hstar g hgC hvg with h | h
      · exact hge h
      · exact hgf h
    rw [G.suppressionGraph_mem_cut_of_copy_ne a b e hab hge,
      G.cutOn_moveShore_of_not_incident a v X C hv]
    simp only [mem_cutOn,mem_erase,hgf,not_false_eq_true,true_and]
  · simp only [mem_cutOn,mem_erase,hgC,and_false,false_and]

theorem suppressionGraph_classCutOn_of_ne
    (classOf : V → E → K) (C : Finset E)
    (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (x : V) (hxv : x ≠ v) (hxb : x ≠ b) (k : K) (X : Finset V) :
    (G.suppressionGraph a b e hab).classCutOn
        (suppressionClass classOf b e f) (C.erase f) x k X =
      G.classCutOn classOf C x k (moveShore b v X) := by
  unfold classCutOn
  rw [G.suppressionGraph_cutOn C a v b hav hbv hab e f hef he hf hstar]
  ext g
  simp only [mem_filter,suppressionClass_of_vertex_ne classOf b e f hxb]
  by_cases hge : g = e
  · subst g
    rw [G.suppressionGraph_edge_self,he]
    simp only [Sym2.mem_iff,hxv,hxb,or_false]
  · rw [G.suppressionGraph_edge_of_ne a b e hab hge]

theorem suppressionGraph_swap_classCutOn
    (classOf : V → E → K) (C : Finset E)
    (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (k : K) (X : Finset V) :
    ((G.suppressionGraph a b e hab).classCutOn
        (suppressionClass classOf b e f) (C.erase f) b k X).map
        (Equiv.swap e f).toEmbedding =
      G.classCutOn classOf C b k (moveShore a v X) := by
  ext g
  simp only [mem_map_equiv,Equiv.symm_swap,classCutOn,mem_filter]
  by_cases hge : g = e
  · subst g
    rw [Equiv.swap_apply_left,G.mem_cutOn_of_edge_eq he]
    simp only [mem_cutOn,mem_erase,ne_self_iff_false,false_and,
      mem_moveShore_of_ne a v X hav,mem_moveShore_self]
    simp
  by_cases hgf : g = f
  · subst g
    rw [Equiv.swap_apply_right,
      (G.suppressionGraph a b e hab).mem_cutOn_of_edge_eq
        (G.suppressionGraph_edge_self a b e hab),G.mem_cutOn_of_edge_eq hf]
    simp only [mem_erase,hef,not_false_eq_true,heC,hfC,true_and,
      mem_moveShore_self,mem_moveShore_of_ne a v X hbv,
      G.suppressionGraph_edge_self,hf,Sym2.mem_iff,or_true,
      suppressionClass_at_changed]
  rw [Equiv.swap_apply_of_ne_of_ne hge hgf,
    G.suppressionGraph_edge_of_ne a b e hab hge,
    suppressionClass_of_copy_ne classOf b e f b hge]
  by_cases hgC : g ∈ C
  · have hv : v ∉ G.edge g := by
      intro hvg
      rcases hstar g hgC hvg with h | h
      · exact hge h
      · exact hgf h
    rw [G.suppressionGraph_mem_cut_of_copy_ne a b e hab hge,
      G.cutOn_moveShore_of_not_incident a v X C hv]
    simp only [mem_cutOn,mem_erase,hgf,not_false_eq_true,true_and]
  · simp only [mem_cutOn,mem_erase,hgC,and_false,false_and]

theorem suppressionGraph_degreeOn_zero
    (C : Finset E) (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E)
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f) :
    (G.suppressionGraph a b e hab).degreeOn (C.erase f) v = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro g hg
  obtain ⟨hgC,hvg⟩ := mem_filter.mp hg
  by_cases hge : g = e
  · subst g
    rw [G.suppressionGraph_edge_self,Sym2.mem_iff] at hvg
    exact hvg.elim (fun h => hav h.symm) (fun h => hbv h.symm)
  · rw [G.suppressionGraph_edge_of_ne a b e hab hge] at hvg
    rcases hstar g (mem_erase.mp hgC).2 hvg with h | h
    · exact hge h
    · exact (mem_erase.mp hgC).1 h

theorem suppressionGraph_degreeOn_of_ne
    (C : Finset E) (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (x : V) (hxv : x ≠ v) :
    (G.suppressionGraph a b e hab).degreeOn (C.erase f) x = G.degreeOn C x := by
  rw [← (G.suppressionGraph a b e hab).cutOn_singleton_card,
    ← G.cutOn_singleton_card]
  by_cases hxb : x = b
  · subst x
    have hh := congrArg Finset.card
      (G.suppressionGraph_swap_cutOn C a v b hav hbv hab e f hef heC hfC he hf hstar {b})
    simpa [moveShore,hab,hbv] using hh
  · rw [G.suppressionGraph_cutOn C a v b hav hbv hab e f hef he hf hstar]
    have hshore : moveShore b v {x} = {x} := by simp [moveShore,Ne.symm hxb,Ne.symm hxv]
    rw [hshore]

theorem suppressionGraph_admissibleOn
    (classOf : V → E → K) (C : Finset E)
    (a v b : V) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : G.edge e = s(a,v)) (hf : G.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ G.edge g → g = e ∨ g = f)
    (hadmissible : G.AdmissibleOn classOf C) :
    (G.suppressionGraph a b e hab).AdmissibleOn
      (suppressionClass classOf b e f) (C.erase f) := by
  intro x k X
  by_cases hxv : x = v
  · subst x
    have hz := G.suppressionGraph_degreeOn_zero C a v b hav hbv hab e f hstar
    have hsub : (G.suppressionGraph a b e hab).classCutOn
        (suppressionClass classOf b e f) (C.erase f) v k X ⊆
        (C.erase f).filter (fun g => v ∈ (G.suppressionGraph a b e hab).edge g) := by
      intro g hg
      obtain ⟨hg,hvg,_⟩ := mem_filter.mp hg
      exact mem_filter.mpr ⟨(mem_cutOn _ _ _ _).mp hg |>.1,hvg⟩
    have hc := card_le_card hsub
    change _ ≤ (G.suppressionGraph a b e hab).degreeOn (C.erase f) v at hc
    rw [hz] at hc
    omega
  by_cases hxb : x = b
  · subst x
    have hc := congrArg Finset.card
      (G.suppressionGraph_swap_classCutOn classOf C a v b hav hbv hab
        e f hef heC hfC he hf hstar k X)
    have hd := congrArg Finset.card
      (G.suppressionGraph_swap_cutOn C a v b hav hbv hab e f hef heC hfC he hf hstar X)
    simp only [card_map] at hc hd
    rw [hc,hd]
    exact hadmissible b k (moveShore a v X)
  · rw [G.suppressionGraph_classCutOn_of_ne classOf C a v b hav hbv hab
      e f hef he hf hstar x hxv hxb k X,
      G.suppressionGraph_cutOn C a v b hav hbv hab e f hef he hf hstar]
    exact hadmissible x k (moveShore b v X)

end Overfull.Multigraph
