import Overfull.Basic

/-!
# Finite loopless multigraphs

The edge type distinguishes parallel copies. Each edge has an actual unordered
pair of distinct endpoints; all degrees and cuts count edge copies.
-/

namespace Overfull

structure Multigraph (V E : Type*) where
  edge : E → Sym2 V
  loopless : ∀ e, ¬ (edge e).IsDiag

namespace Multigraph

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

noncomputable def firstEnd (e : E) : V := (G.edge e).out.1
noncomputable def secondEnd (e : E) : V := (G.edge e).out.2

theorem edge_eq (e : E) : s(G.firstEnd e, G.secondEnd e) = G.edge e :=
  (G.edge e).out_eq

theorem endpoints_distinct (e : E) : G.firstEnd e ≠ G.secondEnd e := by
  intro h
  have hdiag : (G.edge e).IsDiag := by rw [← G.edge_eq e, h]; simp
  exact G.loopless e hdiag

theorem incident_iff (e : E) (v : V) :
    v ∈ G.edge e ↔ G.firstEnd e = v ∨ G.secondEnd e = v := by
  rw [← G.edge_eq e, Sym2.mem_iff]
  exact or_congr eq_comm eq_comm

variable [Fintype E]

noncomputable def incidenceEdges (v : V) : Finset E :=
  univ.filter (fun e => v ∈ G.edge e)

noncomputable def degree (v : V) : ℕ := (G.incidenceEdges v).card

noncomputable def internalEdges (X : Finset V) : Finset E :=
  univ.filter (fun e => (G.edge e).toFinset ⊆ X)

noncomputable def cutEdges (X : Finset V) : Finset E :=
  univ.filter (fun e => (G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X))

noncomputable def cutSize (X : Finset V) : ℕ := (G.cutEdges X).card

@[simp] theorem mem_incidenceEdges (v : V) (e : E) :
    e ∈ G.incidenceEdges v ↔ v ∈ G.edge e := by simp [incidenceEdges]

@[simp] theorem mem_internalEdges (X : Finset V) (e : E) :
    e ∈ G.internalEdges X ↔ G.firstEnd e ∈ X ∧ G.secondEnd e ∈ X := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← G.edge_eq e]
  simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]

@[simp] theorem mem_cutEdges (X : Finset V) (e : E) :
    e ∈ G.cutEdges X ↔ (G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X) := by
  simp [cutEdges]

theorem mem_cutEdges_iff (X : Finset V) (e : E) :
    e ∈ G.cutEdges X ↔
      ∃ v w, G.edge e = s(v,w) ∧ v ∈ X ∧ w ∉ X := by
  rw [mem_cutEdges]
  constructor
  · intro h
    by_cases h₁ : G.firstEnd e ∈ X
    · exact ⟨G.firstEnd e, G.secondEnd e, (G.edge_eq e).symm, h₁, by tauto⟩
    · exact ⟨G.secondEnd e, G.firstEnd e,
        (G.edge_eq e).symm.trans Sym2.eq_swap, by tauto, h₁⟩
  · rintro ⟨v,w,h,hv,hw⟩
    have he := (G.edge_eq e).trans h
    rcases Sym2.eq_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp_all

variable [Fintype V] [DecidableEq V]

theorem cutEdges_compl (X : Finset V) : G.cutEdges Xᶜ = G.cutEdges X := by
  ext e
  simp only [mem_cutEdges, Finset.mem_compl, ne_eq, eq_iff_iff]
  tauto

theorem cutSize_compl (X : Finset V) : G.cutSize Xᶜ = G.cutSize X := by
  simp only [cutSize, cutEdges_compl]

omit [Fintype V] [DecidableEq V] in
/-- Degree counting includes every parallel edge copy separately. -/
theorem degree_sum_on (X : Finset V) :
    (∑ v ∈ X, G.degree v) = 2 * (G.internalEdges X).card + G.cutSize X := by
  have hsum : (∑ v ∈ X, G.degree v) =
      ∑ e : E, (X.filter (fun v => v ∈ G.edge e)).card := by
    simp only [degree, incidenceEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hcount (e : E) :
      (X.filter (fun v => v ∈ G.edge e)).card =
        2 * (if e ∈ G.internalEdges X then 1 else 0) +
          (if e ∈ G.cutEdges X then 1 else 0) := by
    have hfilter : X.filter (fun v => v ∈ G.edge e) =
        (if G.firstEnd e ∈ X then {G.firstEnd e} else ∅) ∪
          (if G.secondEnd e ∈ X then {G.secondEnd e} else ∅) := by
      ext v
      by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
        simp [h₁, h₂, G.incident_iff] <;> aesop
    rw [hfilter]
    have hne := G.endpoints_distinct e
    by_cases h₁ : G.firstEnd e ∈ X <;> by_cases h₂ : G.secondEnd e ∈ X <;>
      simp [h₁, h₂, hne.symm]
  rw [hsum]
  simp_rw [hcount]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, cutSize, Nat.cast_id]

/-- A finite simple graph is a multigraph with one copy of each unordered edge. -/
def ofSimpleGraph {W : Type*} (G : SimpleGraph W) : Multigraph W G.edgeSet where
  edge e := e.val
  loopless e := G.not_isDiag_of_mem_edgeSet e.property

@[simp] theorem ofSimpleGraph_degree {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (v : W) :
    (ofSimpleGraph G).degree v = G.degree v := by
  have himage : ((ofSimpleGraph G).incidenceEdges v).image Subtype.val =
      G.incidenceFinset v := by
    ext e
    simp only [Finset.mem_image, mem_incidenceEdges, ofSimpleGraph,
      SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, hv, rfl⟩
  rw [degree, ← Finset.card_image_of_injective _ Subtype.val_injective,
    himage, G.card_incidenceFinset_eq_degree]

@[simp] theorem ofSimpleGraph_internalEdges {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (X : Finset W) :
    (ofSimpleGraph G).internalEdges X = Overfull.internalEdges G X := by
  ext e
  simp [internalEdges, Overfull.internalEdges, ofSimpleGraph]

end Multigraph

end Overfull
