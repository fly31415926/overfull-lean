import Overfull.SparseColoring

/-!
# Extending a prescribed restriction across a bounded-degree core

Start from a proper coloring on a set of actual edge copies. If every
uncolored copy is internal to a vertex set of degree at most `a`, then a
palette larger than `2 * a` extends the coloring. All prescribed labels
are retained, and no degree bound is needed at exterior vertices.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical

variable {V E : Type*} [Fintype E] (G : Multigraph V E) {k : ℕ}

/-- Regard the supplied restriction coloring as a proper partial host coloring. -/
def restrictionPartialColoring (S : Finset E) (cS : (G.restrictEdges S).EdgeColoring k) :
    G.PartialEdgeColoring k where
  color e := if he : e ∈ S then some (cS.color ⟨e, he⟩) else none
  proper := by
    intro e f v i he hf hev hfv
    by_cases heS : e ∈ S
    · by_cases hfS : f ∈ S
      · have he' : cS.color ⟨e, heS⟩ = i := by
          simpa only [dif_pos heS, Option.some.injEq] using he
        have hf' : cS.color ⟨f, hfS⟩ = i := by
          simpa only [dif_pos hfS, Option.some.injEq] using hf
        exact congrArg Subtype.val (cS.proper (he'.trans hf'.symm) hev hfv)
      · simp only [dif_neg hfS, reduceCtorEq] at hf
    · simp only [dif_neg heS, reduceCtorEq] at he

omit [Fintype E] in
@[simp] theorem restrictionPartialColoring_color (S : Finset E)
    (cS : (G.restrictEdges S).EdgeColoring k) (e : S) :
    (restrictionPartialColoring G S cS).color e.val = some (cS.color e) := by
  simp only [restrictionPartialColoring, dif_pos e.property]

omit [Fintype E] in
@[simp] theorem restrictionPartialColoring_eq_none (S : Finset E)
    (cS : (G.restrictEdges S).EdgeColoring k) (e : E) :
    (restrictionPartialColoring G S cS).color e = none ↔ e ∉ S := by
  by_cases he : e ∈ S <;> simp [restrictionPartialColoring, he]

/-- Complete a prescribed actual restriction when every remaining copy lies
inside the bounded-degree core. The conclusion preserves every supplied color. -/
theorem extend_restriction_coloring (U : Finset V) (S : Finset E)
    (cS : (G.restrictEdges S).EdgeColoring k) (a : ℝ)
    (huncolored : Sᶜ ⊆ G.internalEdges U)
    (hdegree : ∀ v ∈ U, (G.degree v : ℝ) ≤ a) (hslack : 2 * a < k) :
    ∃ c : G.EdgeColoring k, ∀ e : S, c.color e.val = cS.color e := by
  let p := restrictionPartialColoring G S cS
  have hbound : ∀ e, p.color e = none → (G.conflictingEdges e).card < k := by
    intro e he
    have heS : e ∉ S := (restrictionPartialColoring_eq_none G S cS e).mp he
    have hends := (G.mem_internalEdges U e).mp (huncolored (mem_compl.mpr heS))
    have hconf : ((G.conflictingEdges e).card : ℝ) + 2 ≤
        G.degree (G.firstEnd e) + G.degree (G.secondEnd e) := by
      exact_mod_cast G.conflictingEdges_card_add_two_le e
    have hlt : ((G.conflictingEdges e).card : ℝ) < k := by
      linarith [hdegree (G.firstEnd e) hends.1, hdegree (G.secondEnd e) hends.2]
    exact_mod_cast hlt
  obtain ⟨c, hc⟩ := p.exists_edgeColoring_extending hbound
  refine ⟨c, ?_⟩
  intro e
  exact hc e.val (cS.color e) (restrictionPartialColoring_color G S cS e)

/-- Endpoint form of the same extension criterion. -/
theorem extend_restriction_coloring_of_endpoints (U : Finset V) (S : Finset E)
    (cS : (G.restrictEdges S).EdgeColoring k) (a : ℝ)
    (huncolored : ∀ e, e ∉ S → G.firstEnd e ∈ U ∧ G.secondEnd e ∈ U)
    (hdegree : ∀ v ∈ U, (G.degree v : ℝ) ≤ a) (hslack : 2 * a < k) :
    ∃ c : G.EdgeColoring k, ∀ e : S, c.color e.val = cS.color e := by
  apply extend_restriction_coloring G U S cS a _ hdegree hslack
  intro e he
  exact (G.mem_internalEdges U e).mpr (huncolored e (mem_compl.mp he))

end Overfull.OrdinaryFactorization
