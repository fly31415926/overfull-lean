import Overfull.CompatibleCircuits.FourDegreeTwoLift

/-!
# The four-label compatible-circuit theorem with a small-degree label

An unused label invokes the full three-label theorem. A degree-two label
is either removed with its parallel two-circuit or suppressed along its
two-edge path. The suppression preserves all half-cut inequalities, and
the final partition restores exactly the original actual copies.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

theorem exists_other_endpoint {e : E} {v : V} (hv : v ∈ G.edge e) :
    ∃ u, u ≠ v ∧ G.edge e = s(u,v) := by
  rcases (G.incident_iff e v).mp hv with h | h
  · refine ⟨G.secondEnd e,?_,?_⟩
    · simpa only [← h] using (G.endpoints_distinct e).symm
    · rw [← G.edge_eq e,h,Sym2.eq_swap]
  · refine ⟨G.firstEnd e,?_,?_⟩
    · simpa only [← h] using G.endpoints_distinct e
    · rw [← G.edge_eq e,h]

theorem distinct_classes_at_degree_two
    (classOf : V → E → K) (C : Finset E) (v : V)
    (hdegree : G.degreeOn C v = 2)
    (hadmissible : G.AdmissibleOn classOf C)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) :
    classOf v e ≠ classOf v f := by
  intro heq
  have hsub : {e,f} ⊆ C.filter (fun g => v ∈ G.edge g ∧ classOf v g = classOf v e) := by
    intro g hg
    rcases mem_insert.mp hg with rfl | hg
    · exact mem_filter.mpr ⟨heC,hev,rfl⟩
    · have hg := mem_singleton.mp hg
      subst g
      exact mem_filter.mpr ⟨hfC,hfv,heq.symm⟩
  have hcard := card_le_card hsub
  have hh := hadmissible.local_class_bound G v (classOf v e)
  rw [hdegree] at hh
  have hpair : ({e,f} : Finset E).card = 2 := by simp [hef]
  rw [hpair] at hcard
  omega

variable (Q : Multigraph (Fin 4) E)

/-- Suppress a degree-two path, solve the three-label graph, and restore every copy. -/
theorem exists_compatibleCircuitPartition_of_four_label_degree_two_path
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (a v b : Fin 4) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hdegree : Q.degreeOn C v = 2)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : Q.edge e = s(a,v)) (hf : Q.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ Q.edge g → g = e ∨ g = f) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let H := Q.suppressionGraph a b e hab
  let f' := suppressionClass classOf b e f
  have hzero := Q.suppressionGraph_degreeOn_zero C a v b hav hbv hab e f hstar
  have hadm := Q.suppressionGraph_admissibleOn classOf C a v b hav hbv hab
    e f hef heC hfC he hf hstar hadmissible
  have heven' (x : Fin 4) : Even (H.degreeOn (C.erase f) x) := by
    by_cases hxv : x = v
    · subst x
      rw [hzero]
      exact ⟨0,rfl⟩
    · rw [Q.suppressionGraph_degreeOn_of_ne C a v b hav hbv hab e f
        hef heC hfC he hf hstar x hxv]
      exact heven x
  obtain ⟨P⟩ := H.exists_compatibleCircuitPartition_of_four_label_degree_zero
    f' (C.erase f) hadm heven' v hzero
  have hclasses := Q.distinct_classes_at_degree_two classOf C v hdegree
    hadmissible e f hef heC hfC (by simp [he]) (by simp [hf])
  exact Q.exists_compatibleCircuitPartition_of_degree_two_suppressed classOf C
    a v b hav hbv hab e f hef heC hfC he hf hstar hclasses P

/-- Complete existence whenever one of the four labels has degree two. -/
theorem exists_compatibleCircuitPartition_of_four_label_degree_two
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (v : Fin 4) (hdegree : Q.degreeOn C v = 2) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  obtain ⟨e,f,hef,hpair⟩ := card_eq_two.mp hdegree
  have heinc : e ∈ C.filter (fun g => v ∈ Q.edge g) := by rw [hpair]; simp
  have hfinc : f ∈ C.filter (fun g => v ∈ Q.edge g) := by rw [hpair]; simp
  obtain ⟨heC,hev⟩ := mem_filter.mp heinc
  obtain ⟨hfC,hfv⟩ := mem_filter.mp hfinc
  have hstar : ∀ g ∈ C, v ∈ Q.edge g → g = e ∨ g = f := by
    intro g hg hvg
    have hm : g ∈ C.filter (fun g => v ∈ Q.edge g) := mem_filter.mpr ⟨hg,hvg⟩
    rw [hpair] at hm
    simpa only [mem_insert,mem_singleton] using hm
  by_cases hparallel : Q.edge e = Q.edge f
  · exact Q.exists_compatibleCircuitPartition_of_four_label_degree_two_parallel
      classOf C hadmissible heven v hdegree e f heC hfC hef hev hparallel
  obtain ⟨a,hav,he⟩ := Q.exists_other_endpoint hev
  obtain ⟨b,hbv,hf'⟩ := Q.exists_other_endpoint hfv
  have hf : Q.edge f = s(v,b) := hf'.trans Sym2.eq_swap
  have hab : a ≠ b := by
    intro hab
    apply hparallel
    rw [he,hf',hab]
  exact Q.exists_compatibleCircuitPartition_of_four_label_degree_two_path
    classOf C hadmissible heven a v b hav hbv hab hdegree e f hef heC hfC he hf hstar

/-- Original admissibility and Eulerian parity suffice if any label has degree at most two. -/
theorem exists_compatibleCircuitPartition_of_four_label_small_degree
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hsmall : ∃ v, Q.degreeOn C v ≤ 2) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  obtain ⟨v,hv⟩ := hsmall
  have hparity := Nat.even_iff.mp (heven v)
  have hcase : Q.degreeOn C v = 0 ∨ Q.degreeOn C v = 2 := by omega
  rcases hcase with hzero | htwo
  · exact Q.exists_compatibleCircuitPartition_of_four_label_degree_zero
      classOf C hadmissible heven v hzero
  · exact Q.exists_compatibleCircuitPartition_of_four_label_degree_two
      classOf C hadmissible heven v htwo

end Overfull.Multigraph
