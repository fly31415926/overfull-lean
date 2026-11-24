import Overfull.Konig

/-!
# Overfull sets obstruct multigraph edge colorings

The color classes are matchings of actual edge copies. Counting their internal
edges gives the overfull obstruction with parallel multiplicities retained.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Every matching has at most half as many internal edges as vertices. -/
theorem IsMatching.internal_edges_card_le {M : Finset E} (hM : G.IsMatching M)
    (X : Finset V) : (G.internalEdges X ∩ M).card ≤ X.card / 2 := by
  have hz : matchingIndicator M ∈ MatchingPolytope.integral G.firstEnd G.secondEnd := by
    rw [G.integral_eq_matchingIndicators]
    exact ⟨M, hM, rfl⟩
  have hhand := Lovasz.BMatch.handshake G.firstEnd G.secondEnd univ
    (fun e _ => G.endpoints_distinct e) X (matchingIndicator M)
  have hinside : (∑ e ∈ Lovasz.BMatch.inside G.firstEnd G.secondEnd univ X,
      matchingIndicator M e) = ((G.internalEdges X ∩ M).card : ℝ) := by
    simp only [matchingIndicator, Finset.sum_boole]
    congr 2
    ext e
    simp [Lovasz.BMatch.inside]
  have hcut : 0 ≤ ∑ e ∈ Lovasz.BMatch.cut G.firstEnd G.secondEnd univ X,
      matchingIndicator M e := by
    apply Finset.sum_nonneg
    intro e _
    by_cases he : e ∈ M <;> simp [matchingIndicator, he]
  have hdeg : (∑ v ∈ X,
      Lovasz.BMatch.dsum G.firstEnd G.secondEnd univ (matchingIndicator M) v) ≤
      (X.card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hz.2 v)
      _ = _ := by simp
  have hboundR : (2 : ℝ) * (G.internalEdges X ∩ M).card ≤ X.card := by linarith
  have hbound : 2 * (G.internalEdges X ∩ M).card ≤ X.card := by exact_mod_cast hboundR
  omega

namespace EdgeColoring

variable {G} {k : ℕ} (c : G.EdgeColoring k)

noncomputable def colorClass (i : Fin k) : Finset E := univ.filter (fun e => c.color e = i)

omit [Fintype V] in
theorem colorClass_isMatching (i : Fin k) : G.IsMatching (c.colorClass i) := by
  intro e he f hf v hev hfv
  exact c.proper ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hev hfv

theorem colorClass_internal_card_le (i : Fin k) (X : Finset V) :
    ((G.internalEdges X).filter (fun e => c.color e = i)).card ≤ X.card / 2 := by
  have h := (c.colorClass_isMatching i).internal_edges_card_le G X
  simpa [colorClass, Finset.inter_filter] using h

include c in
theorem internalEdges_card_le (X : Finset V) :
    (G.internalEdges X).card ≤ k * (X.card / 2) := by
  calc
    _ = ∑ i : Fin k, ((G.internalEdges X).filter (fun e => c.color e = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ (c.color e))
    _ ≤ ∑ _i : Fin k, X.card / 2 :=
      Finset.sum_le_sum (fun i _ => c.colorClass_internal_card_le i X)
    _ = _ := by simp

include c in
theorem not_overfull (X : Finset V) : ¬ G.IsOverfull k X :=
  not_lt_of_ge (c.internalEdges_card_le X)

end EdgeColoring

theorem overfull_not_edgeColorable {k : ℕ} {X : Finset V} (hX : G.IsOverfull k X) :
    ¬ Nonempty (G.EdgeColoring k) := by
  rintro ⟨c⟩
  exact c.not_overfull X hX

end Overfull.Multigraph
