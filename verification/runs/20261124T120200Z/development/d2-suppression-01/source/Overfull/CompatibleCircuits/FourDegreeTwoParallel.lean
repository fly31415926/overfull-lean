import Overfull.CompatibleCircuits.FourDegreeTwoSupport

/-! Degree-two parallel copies can be removed safely and restored exactly. -/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

theorem mem_cutOn_of_edge_eq {e : E} {u v : V} (hedge : G.edge e = s(u,v))
    (C : Finset E) (X : Finset V) :
    e ∈ G.cutOn C X ↔ e ∈ C ∧ ((u ∈ X) ≠ (v ∈ X)) := by
  have h := (G.edge_eq e).trans hedge
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp only [mem_cutOn,ha,hb]
  · simp only [mem_cutOn,ha,hb,ne_eq,eq_iff_iff]
    tauto

/-- Move just `v` to the side of `u`. -/
def moveShore (u v : V) (X : Finset V) : Finset V :=
  if u ∈ X then insert v X else X.erase v

theorem mem_moveShore_of_ne (u v : V) (X : Finset V) {w : V} (hw : w ≠ v) :
    w ∈ moveShore u v X ↔ w ∈ X := by
  by_cases hu : u ∈ X <;> simp [moveShore,hu,hw]

theorem mem_moveShore_self (u v : V) (X : Finset V) :
    v ∈ moveShore u v X ↔ u ∈ X := by
  by_cases hu : u ∈ X <;> simp [moveShore,hu]

theorem cutOn_moveShore_of_not_incident (u v : V) (X : Finset V)
    (C : Finset E) {e : E} (hv : v ∉ G.edge e) :
    e ∈ G.cutOn C (moveShore u v X) ↔ e ∈ G.cutOn C X := by
  have hfirst : G.firstEnd e ≠ v := by
    intro h
    apply hv
    rw [G.incident_iff]
    exact Or.inl h
  have hsecond : G.secondEnd e ≠ v := by
    intro h
    apply hv
    rw [G.incident_iff]
    exact Or.inr h
  simp only [mem_cutOn,mem_moveShore_of_ne u v X hfirst,
    mem_moveShore_of_ne u v X hsecond]

/-- Deleting the complete two-copy parallel star preserves all class-cut bounds. -/
theorem admissibleOn_delete_degree_two_parallel
    (classOf : V → E → K) (C : Finset E) (u v : V) (huv : u ≠ v)
    (e f : E) (he : G.edge e = s(u,v)) (hf : G.edge f = s(u,v))
    (hstar : ∀ a ∈ C, v ∈ G.edge a → a = e ∨ a = f)
    (hadmissible : G.AdmissibleOn classOf C) :
    G.AdmissibleOn classOf (C \ {e,f}) := by
  intro w k X
  have hcut : G.cutOn (C \ {e,f}) X = G.cutOn C (moveShore u v X) := by
    ext a
    by_cases hae : a = e
    · subst a
      rw [G.mem_cutOn_of_edge_eq he, G.mem_cutOn_of_edge_eq he]
      simp only [mem_sdiff,mem_insert,mem_singleton,true_or,not_true_eq_false,and_false,
        false_and,mem_moveShore_of_ne u v X huv,mem_moveShore_self,ne_self_iff_false]
    by_cases haf : a = f
    · subst a
      rw [G.mem_cutOn_of_edge_eq hf, G.mem_cutOn_of_edge_eq hf]
      simp only [mem_sdiff,mem_insert,mem_singleton,or_true,not_true_eq_false,and_false,
        false_and,mem_moveShore_of_ne u v X huv,mem_moveShore_self,ne_self_iff_false]
    by_cases haC : a ∈ C
    · have hv : v ∉ G.edge a := by
        intro hva
        rcases hstar a haC hva with h | h
        · exact hae h
        · exact haf h
      rw [G.cutOn_moveShore_of_not_incident u v X C hv]
      simp only [mem_cutOn,mem_sdiff,mem_insert,mem_singleton,hae,haf,false_or,
        not_false_eq_true,and_true]
    · simp only [mem_cutOn,mem_sdiff,haC,false_and]
  have hclass : G.classCutOn classOf (C \ {e,f}) w k X =
      G.classCutOn classOf C w k (moveShore u v X) := by
    simp only [classCutOn,hcut]
  rw [hcut,hclass]
  exact hadmissible w k (moveShore u v X)

theorem compatible_degree_two_parallel
    (classOf : V → E → K) (C : Finset E) (v : V)
    (hdegree : G.degreeOn C v = 2)
    (hadmissible : G.AdmissibleOn classOf C)
    (e f : E) (heC : e ∈ C) (hfC : f ∈ C) (hef : e ≠ f)
    (he : v ∈ G.edge e) (hparallel : G.edge e = G.edge f) :
    G.Compatible classOf {e,f} := by
  intro w a ha hwa b hb hwb hclass
  by_contra hab
  have hboth : {a,b} ⊆ G.classCutOn classOf C w (classOf w a) {v} := by
    intro g hg
    have hgf : g = a ∨ g = b := by simpa only [mem_insert,mem_singleton] using hg
    have hgC : g ∈ C := by
      have : g ∈ ({e,f} : Finset E) := hgf.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      rcases mem_insert.mp this with rfl | h
      · exact heC
      · exact mem_singleton.mp h ▸ hfC
    have hgv : v ∈ G.edge g := by
      have : g ∈ ({e,f} : Finset E) := hgf.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      rcases mem_insert.mp this with rfl | h
      · exact he
      · rw [mem_singleton.mp h,← hparallel]
        exact he
    apply mem_filter.mpr
    refine ⟨?_,?_,?_⟩
    · rw [G.cutOn_singleton]
      exact mem_filter.mpr ⟨hgC,hgv⟩
    · exact hgf.elim (fun h => h ▸ hwa) (fun h => h ▸ hwb)
    · rcases hgf with rfl | rfl
      · rfl
      · exact hclass.symm
  have hcard : 2 ≤ (G.classCutOn classOf C w (classOf w a) {v}).card := by
    have := card_le_card hboth
    simpa [hab] using this
  have hh := hadmissible w (classOf w a) {v}
  rw [G.cutOn_singleton_card,hdegree] at hh
  omega

/-- The original degree-two parallel pair, followed by an exact three-label partition. -/
theorem exists_compatibleCircuitPartition_of_four_label_degree_two_parallel
    (Q : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (v : Fin 4) (hdegree : Q.degreeOn C v = 2)
    (e f : E) (heC : e ∈ C) (hfC : f ∈ C) (hef : e ≠ f)
    (hev : v ∈ Q.edge e) (hparallel : Q.edge e = Q.edge f) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let D : Finset E := {e,f}
  have hD : D ⊆ C := by simp [D,heC,hfC]
  have hDcircuit : Q.IsCircuit D := Q.isCircuit_parallel_pair hef hparallel
  have hDcomp := Q.compatible_degree_two_parallel classOf C v hdegree
    hadmissible e f heC hfC hef hev hparallel
  have hstar : C.filter (fun a => v ∈ Q.edge a) = D := by
    apply eq_of_subset_of_card_le
    · intro a ha
      have hsub : D ⊆ C.filter (fun a => v ∈ Q.edge a) := by
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact mem_filter.mpr ⟨heC,hev⟩
        · have ha := mem_singleton.mp ha
          subst a
          exact mem_filter.mpr ⟨hfC,hparallel ▸ hev⟩
      have heq : D = C.filter (fun a => v ∈ Q.edge a) :=
        eq_of_subset_of_card_le hsub (by simpa [D,hef] using hdegree.le)
      exact heq.symm ▸ ha
    · simpa [D,hef,degreeOn] using hdegree.ge
  obtain ⟨u, huv, he⟩ : ∃ u, u ≠ v ∧ Q.edge e = s(u,v) := by
    rcases (Q.incident_iff e v).mp hev with h | h
    · exact ⟨Q.secondEnd e, by simpa [← h] using (Q.endpoints_distinct e).symm,
        (Q.edge_eq e).symm.trans (by rw [h,Sym2.eq_swap])⟩
    · exact ⟨Q.firstEnd e, by simpa [← h] using Q.endpoints_distinct e,
        (Q.edge_eq e).symm.trans (by rw [h])⟩
  have hsafe := Q.admissibleOn_delete_degree_two_parallel classOf C u v huv
    e f he (hparallel.symm.trans he) (fun a ha hva => by
      have hm : a ∈ D := by rw [← hstar]; exact mem_filter.mpr ⟨ha,hva⟩
      simpa [D] using hm) hadmissible
  have hzero : Q.degreeOn (C \ D) v = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨haC,haD⟩ := mem_sdiff.mp (mem_filter.mp ha).1
    apply haD
    rw [← hstar]
    exact mem_filter.mpr ⟨haC,(mem_filter.mp ha).2⟩
  obtain ⟨P⟩ := Q.exists_compatibleCircuitPartition_of_four_label_degree_zero classOf
    (C \ D) hsafe (Q.even_degreeOn_sdiff hD heven hDcircuit.even_degreeOn) v hzero
  exact ⟨P.insertCircuit Q hD hDcircuit hDcomp⟩

end Overfull.Multigraph
