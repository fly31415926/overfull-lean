import Overfull.OneCore.Complement

/-!
# Retaining the moved vertex's original simple neighbors

Moving one vertex out of a core retains every one of its original simple
neighbors as a distinct surviving core vertex. The original embedded edge
copy gives an injection from any subset of those neighbors into the actual
host incidences toward that subset.
-/

noncomputable section

namespace Overfull.OneCore

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {U : Finset V}

/-- Original simple neighbors, indexed by the core after moving `y` out. -/
def movedNeighbors (C : Core G U) (y : U) : Finset ↥(U \ {y.val}) :=
  univ.filter (fun v => C.graph.Adj y
    (ForeignRefinement.survivingInclusion U {y.val} v))

omit [Fintype E] in
@[simp] theorem mem_movedNeighbors (C : Core G U) (y : U)
    (v : ↥(U \ {y.val})) :
    v ∈ movedNeighbors C y ↔
      C.graph.Adj y (ForeignRefinement.survivingInclusion U {y.val} v) := by
  simp only [movedNeighbors, mem_filter, mem_univ, true_and]

omit [Fintype E] in
/-- No original simple neighbor disappears when its own source is moved. -/
theorem movedNeighbors_card (C : Core G U) (y : U) :
    (movedNeighbors C y).card = C.graph.degree y := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply card_bij (fun v _ => ForeignRefinement.survivingInclusion U {y.val} v)
  · intro v hv
    exact (C.graph.mem_neighborFinset y _).mpr ((mem_movedNeighbors C y v).mp hv)
  · intro v _ w _ hvw
    exact Subtype.ext (congrArg (fun z : U => z.val) hvw)
  · intro v hv
    have hne : v.val ≠ y.val := by
      intro h
      have hsub : v = y := Subtype.ext h
      exact ((C.graph.mem_neighborFinset y v).mp hv).ne hsub.symm
    let w : ↥(U \ {y.val}) := ⟨v.val, mem_sdiff.mpr
      ⟨v.property, by simpa only [mem_singleton] using hne⟩⟩
    refine ⟨w, ?_, ?_⟩
    · exact (mem_movedNeighbors C y w).mpr ((C.graph.mem_neighborFinset y v).mp hv)
    · exact Subtype.ext rfl

/-- Each original simple neighbor in a shore supplies a different actual
host copy incident with the moved vertex and that shore. -/
theorem movedNeighbors_shore_le (C : Core G U) (y : U)
    (A : Finset ↥(U \ {y.val})) :
    (movedNeighbors C y ∩ A).card ≤
      (G.edgesTo y.val (A.map (Function.Embedding.subtype
        (fun v => v ∈ U \ {y.val})))).card := by
  let f : ↥(movedNeighbors C y ∩ A) →
      ↥(G.edgesTo y.val (A.map (Function.Embedding.subtype
        (fun v => v ∈ U \ {y.val})))) := fun v => by
    let w : U := ForeignRefinement.survivingInclusion U {y.val} v.val
    have hadj : C.graph.Adj y w :=
      (mem_movedNeighbors C y v.val).mp (mem_inter.mp v.property).1
    let e : C.graph.edgeSet := ⟨s(y, w), hadj⟩
    have hedge : G.edge (C.edgeMap e) = s(y.val, v.val.val) := by
      rw [C.map_edge]
      rfl
    refine ⟨C.edgeMap e, (G.mem_edgesTo _ _ _).mpr ⟨?_, ?_⟩⟩
    · rw [hedge]
      simp only [Sym2.mem_iff, true_or]
    · rw [G.otherEnd_eq_of_edge _ _ _ hedge]
      exact mem_map.mpr ⟨v.val, (mem_inter.mp v.property).2, rfl⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    have hedge : s(y, ForeignRefinement.survivingInclusion U {y.val} v.val) =
        s(y, ForeignRefinement.survivingInclusion U {y.val} w.val) := by
      have hcopies := congrArg Subtype.val hvw
      have hcore := C.edgeMap.injective hcopies
      exact congrArg Subtype.val hcore
    have hneighbor : ForeignRefinement.survivingInclusion U {y.val} v.val =
        ForeignRefinement.survivingInclusion U {y.val} w.val := by
      rcases Sym2.eq_iff.mp hedge with ⟨_, h⟩ | ⟨h₁, h₂⟩
      · exact h
      · exact h₂.trans h₁
    exact Subtype.ext (Subtype.ext (congrArg (fun z : U => z.val) hneighbor))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end Overfull.OneCore
