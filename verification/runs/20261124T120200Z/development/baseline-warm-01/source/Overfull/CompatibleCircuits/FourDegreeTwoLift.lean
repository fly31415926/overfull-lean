import Overfull.CompatibleCircuits.FourDegreeTwoSuppression
import Overfull.CompatibleCircuits.FourDegreeTwoReassembly

/-!
# Restoring the original two-edge path

Only the part using the suppressed copy is expanded. Its entire expanded
copy set is compatible and has even degrees; ordinary circuit decomposition
therefore supplies genuine compatible circuits. All other original parts
are transported without changing a copy.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

theorem compatible_degree_two_expansion
    (classOf : Fin 4 → E → K) (C D : Finset E)
    (a v b : Fin 4) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f)
    (he : Q.edge e = s(a,v)) (hf : Q.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ Q.edge g → g = e ∨ g = f)
    (hclassv : classOf v e ≠ classOf v f)
    (hDC : D ⊆ C.erase f) (heD : e ∈ D) (hfC : f ∈ C)
    (hcomp : (Q.suppressionGraph a b e hab).Compatible
      (suppressionClass classOf b e f) D) :
    Q.Compatible classOf (insert f D) := by
  let H := Q.suppressionGraph a b e hab
  let collapse : E → E := fun g => if g = f then e else g
  have hTC : insert f D ⊆ C := by
    intro g hg
    rcases mem_insert.mp hg with rfl | hg
    · exact hfC
    · exact (mem_erase.mp (hDC hg)).2
  have hmem (g : E) (hg : g ∈ insert f D) : collapse g ∈ D := by
    by_cases hgf : g = f
    · simpa [collapse,hgf] using heD
    · have hgD : g ∈ D := (mem_insert.mp hg).resolve_left hgf
      simpa [collapse,hgf] using hgD
  have htransfer (x : Fin 4) (hxv : x ≠ v) (g : E)
      (hg : g ∈ insert f D) (hxg : x ∈ Q.edge g) :
      x ∈ H.edge (collapse g) ∧
        suppressionClass classOf b e f x (collapse g) = classOf x g := by
    by_cases hgf : g = f
    · subst g
      have hxb : x = b := by simpa only [hf,Sym2.mem_iff,hxv,false_or] using hxg
      subst x
      simp [H,collapse,suppressionGraph,suppressionClass]
    by_cases hge : g = e
    · subst g
      have hxa : x = a := by
        have := hxg
        rw [he,Sym2.mem_iff] at this
        exact this.resolve_right hxv
      subst x
      simp [H,collapse,hef,suppressionGraph,suppressionClass,hab]
    · simp only [collapse,if_neg hgf]
      rw [show H.edge g = Q.edge g by exact Q.suppressionGraph_edge_of_ne a b e hab hge]
      exact ⟨hxg,suppressionClass_of_copy_ne classOf b e f x hge⟩
  intro x g hg hxg h hh hxh hclasses
  by_cases hxv : x = v
  · subst x
    rcases hstar g (hTC hg) hxg with rfl | rfl <;>
      rcases hstar h (hTC hh) hxh with rfl | rfl
    · rfl
    · exact (hclassv hclasses).elim
    · exact (hclassv hclasses.symm).elim
    · rfl
  have hgtransfer := htransfer x hxv g hg hxg
  have hhtransfer := htransfer x hxv h hh hxh
  have hcollapsed : collapse g = collapse h := by
    apply hcomp x (collapse g) (hmem g hg) hgtransfer.1
      (collapse h) (hmem h hh) hhtransfer.1
    rw [hgtransfer.2,hhtransfer.2]
    exact hclasses
  by_cases hgf : g = f
  · subst g
    by_cases hhf : h = f
    · exact hhf.symm
    have heh : e = h := by simpa [collapse,hhf] using hcollapsed
    subst h
    have hxb : x = b := by simpa only [hf,Sym2.mem_iff,hxv,false_or] using hxg
    have hxa : x = a := by
      rw [he,Sym2.mem_iff] at hxh
      exact hxh.resolve_right hxv
    exact (hab (hxa.symm.trans hxb)).elim
  by_cases hhf : h = f
  · subst h
    have hge : g = e := by simpa [collapse,hgf] using hcollapsed
    subst g
    have hxb : x = b := by simpa only [hf,Sym2.mem_iff,hxv,false_or] using hxh
    have hxa : x = a := by
      rw [he,Sym2.mem_iff] at hxg
      exact hxg.resolve_right hxv
    exact (hab (hxa.symm.trans hxb)).elim
  · simpa only [collapse,if_neg hgf,if_neg hhf] using hcollapsed

theorem even_degrees_degree_two_expansion
    (C D : Finset E) (a v b : Fin 4)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f)
    (he : Q.edge e = s(a,v)) (hf : Q.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ Q.edge g → g = e ∨ g = f)
    (hDC : D ⊆ C.erase f) (heD : e ∈ D) (hfC : f ∈ C)
    (heven : ∀ x, Even ((Q.suppressionGraph a b e hab).degreeOn D x)) :
    ∀ x, Even (Q.degreeOn (insert f D) x) := by
  have hfD : f ∉ D := fun h => (mem_erase.mp (hDC h)).1 rfl
  have hTC : insert f D ⊆ C := by
    intro g hg
    rcases mem_insert.mp hg with rfl | hg
    · exact hfC
    · exact (mem_erase.mp (hDC hg)).2
  have hstarT : ∀ g ∈ insert f D, v ∈ Q.edge g → g = e ∨ g = f :=
    fun g hg hv => hstar g (hTC hg) hv
  have herase : (insert f D).erase f = D := by simp [hfD]
  intro x
  by_cases hxv : x = v
  · subst x
    have hfilter : (insert f D).filter (fun g => v ∈ Q.edge g) = {e,f} := by
      ext g
      constructor
      · intro hg
        exact mem_insert.mpr ((hstarT g (mem_filter.mp hg).1 (mem_filter.mp hg).2).imp
          id (fun h => mem_singleton.mpr h))
      · intro hg
        rcases mem_insert.mp hg with rfl | hg
        · exact mem_filter.mpr ⟨mem_insert_of_mem heD,by simp [he]⟩
        · have hg := mem_singleton.mp hg
          subst g
          exact mem_filter.mpr ⟨mem_insert_self _ _,by simp [hf]⟩
    have hdeg : Q.degreeOn (insert f D) v = 2 := by
      unfold degreeOn
      rw [hfilter]
      simp [hef]
    rw [hdeg]
    decide
  · have hdeg := Q.suppressionGraph_degreeOn_of_ne (insert f D)
      a v b hav hbv hab e f hef (mem_insert_of_mem heD) (mem_insert_self _ _)
      he hf hstarT x hxv
    rw [herase] at hdeg
    rw [← hdeg]
    exact heven x

/-- Restore the original copies from an already constructed suppressed partition. -/
theorem exists_compatibleCircuitPartition_of_degree_two_suppressed
    (classOf : Fin 4 → E → K) (C : Finset E)
    (a v b : Fin 4) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (e f : E) (hef : e ≠ f) (heC : e ∈ C) (hfC : f ∈ C)
    (he : Q.edge e = s(a,v)) (hf : Q.edge f = s(v,b))
    (hstar : ∀ g ∈ C, v ∈ Q.edge g → g = e ∨ g = f)
    (hclassv : classOf v e ≠ classOf v f)
    (P : (Q.suppressionGraph a b e hab).CompatibleCircuitPartition
      (suppressionClass classOf b e f) (C.erase f)) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let H := Q.suppressionGraph a b e hab
  have heS : e ∈ C.erase f := mem_erase.mpr ⟨hef,heC⟩
  rw [← P.cover] at heS
  obtain ⟨D,hD,heD⟩ := mem_biUnion.mp heS
  have hDC := P.part_subset H hD
  have hfD : f ∉ D := fun h => (mem_erase.mp (hDC h)).1 rfl
  have hcomp := Q.compatible_degree_two_expansion classOf C D a v b hav hbv hab
    e f hef he hf hstar hclassv hDC heD hfC (P.compatible D hD)
  have heven := Q.even_degrees_degree_two_expansion C D a v b hav hbv hab
    e f hef he hf hstar hDC heD hfC (P.circuit D hD).even_degreeOn
  obtain ⟨R⟩ := Q.exists_compatibleCircuitPartition_of_compatible classOf
    (insert f D) hcomp heven
  let S := P.eraseCircuit H hD
  have hedge (g : E) (hg : g ∈ C.erase f \ D) : H.edge g = Q.edge g := by
    apply Q.suppressionGraph_edge_of_ne a b e hab
    intro hge
    exact (mem_sdiff.mp hg).2 (hge.symm ▸ heD)
  have hclasses (x : Fin 4) (g : E) (hg : g ∈ C.erase f \ D) :
      suppressionClass classOf b e f x g = classOf x g := by
    apply suppressionClass_of_copy_ne classOf b e f x
    intro hge
    exact (mem_sdiff.mp hg).2 (hge.symm ▸ heD)
  let S' := S.congrOn H Q hedge hclasses
  have hdisjoint : Disjoint (insert f D) (C.erase f \ D) := by
    apply disjoint_left.mpr
    intro g hg hgs
    rcases mem_insert.mp hg with rfl | hg
    · exact (mem_erase.mp (mem_sdiff.mp hgs).1).1 rfl
    · exact (mem_sdiff.mp hgs).2 hg
  have hcover : insert f D ∪ (C.erase f \ D) = C := by
    ext g
    simp only [mem_union,mem_insert,mem_sdiff,mem_erase]
    have hsub : g ∈ D → g ∈ C := fun hg => (mem_erase.mp (hDC hg)).2
    constructor
    · rintro (hgf | hg) | ⟨⟨hgf,hgC⟩,hgD⟩
      · exact hgf.symm ▸ hfC
      · exact hsub hg
      · exact hgC
    · intro hgC
      by_cases hgf : g = f
      · exact Or.inl (Or.inl hgf)
      by_cases hgD : g ∈ D
      · exact Or.inl (Or.inr hgD)
      · exact Or.inr ⟨⟨hgf,hgC⟩,hgD⟩
  exact ⟨hcover ▸ R.union Q S' hdisjoint⟩

end Overfull.Multigraph
