import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Edge colorings and the overfull obstruction

An edge is an unordered pair in mathlib's `SimpleGraph.edgeSet`.
An edge coloring assigns a color to each edge, with distinct colors on
distinct edges sharing a vertex. No coloring or matching theorem is
assumed in this file.
-/

namespace Overfull

open Finset

variable {V : Type*}

/-- A proper edge coloring of a simple graph with `k` available colors. -/
structure EdgeColoring (G : SimpleGraph V) (k : ℕ) where
  color : G.edgeSet → Fin k
  proper : ∀ {e f : G.edgeSet} {v : V},
    v ∈ e.val → v ∈ f.val → color e = color f → e = f

/-- The actual edges of `G` whose two endpoints belong to `X`. -/
noncomputable def internalEdges [Fintype V] (G : SimpleGraph V)
    (X : Finset V) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => e.val.toFinset ⊆ X)

/-- Overfullness uses the usual matching bound, including for even sets. -/
noncomputable def IsOverfull [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (X : Finset V) : Prop :=
  k * (X.card / 2) < (internalEdges G X).card

variable [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- Incident edges must have distinct colors, so the degree is at most `k`. -/
theorem EdgeColoring.degree_le [DecidableRel G.Adj] (c : EdgeColoring G k)
    (v : V) : G.degree v ≤ k := by
  classical
  let f : G.neighborSet v → Fin k := fun u => c.color ⟨s(v, u.val), u.property⟩
  have hf : Function.Injective f := by
    intro u w h
    have he : (⟨s(v, u.val), u.property⟩ : G.edgeSet) =
        ⟨s(v, w.val), w.property⟩ :=
      c.proper (v := v) (by simp) (by simp) h
    apply Subtype.ext
    have hval := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hval with ⟨_, huw⟩ | ⟨hvw, huv⟩
    · exact huw
    · exact huv.trans hvw
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] using hcard

/-- Any proper edge coloring uses at least the graph's maximum degree. -/
theorem EdgeColoring.maxDegree_le [DecidableRel G.Adj] (c : EdgeColoring G k) :
    G.maxDegree ≤ k :=
  G.maxDegree_le_of_forall_degree_le k (fun v => c.degree_le v)

/-- A color class has at most `floor (|X|/2)` edges inside any vertex set. -/
theorem EdgeColoring.colorClass_card_le (c : EdgeColoring G k)
    (X : Finset V) (i : Fin k) :
    ((internalEdges G X).filter (fun e => c.color e = i)).card ≤ X.card / 2 := by
  classical
  let S := (internalEdges G X).filter (fun e => c.color e = i)
  have htwo (e : G.edgeSet) : e.val.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeSet e.property)
  have hdisj : S.toSet.PairwiseDisjoint (fun e => e.val.toFinset) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    apply hne
    exact c.proper (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf)
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have hsub : S.biUnion (fun e => e.val.toFinset) ⊆ X := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have heX := (Finset.mem_filter.mp he).1
    have hend : e.val.toFinset ⊆ X := (Finset.mem_filter.mp heX).2
    exact hend hve
  have hcard : 2 * S.card ≤ X.card := by
    calc
      2 * S.card = ∑ e ∈ S, e.val.toFinset.card := by simp [htwo, Nat.mul_comm]
      _ = (S.biUnion (fun e => e.val.toFinset)).card := (Finset.card_biUnion hdisj).symm
      _ ≤ X.card := Finset.card_le_card hsub
  change S.card ≤ X.card / 2
  omega

/-- Counting color classes proves the overfull obstruction for every vertex set. -/
theorem EdgeColoring.internalEdges_card_le (c : EdgeColoring G k)
    (X : Finset V) :
    (internalEdges G X).card ≤ k * (X.card / 2) := by
  classical
  have hcount : (internalEdges G X).card =
      ∑ i : Fin k, ((internalEdges G X).filter (fun e => c.color e = i)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hcount]
  calc
    ∑ i : Fin k, ((internalEdges G X).filter (fun e => c.color e = i)).card
        ≤ ∑ _i : Fin k, X.card / 2 :=
      Finset.sum_le_sum (fun i _ => c.colorClass_card_le X i)
    _ = k * (X.card / 2) := by simp

/-- A properly edge-colored graph has no overfull vertex set. -/
theorem EdgeColoring.not_overfull (c : EdgeColoring G k) (X : Finset V) :
    ¬ IsOverfull G k X :=
  Nat.not_lt.mpr (c.internalEdges_card_le X)

/-- A graph with an overfull set admits no proper edge coloring with `k` colors. -/
theorem overfull_not_edgeColorable (X : Finset V) (hX : IsOverfull G k X) :
    ¬ Nonempty (EdgeColoring G k) := by
  rintro ⟨c⟩
  exact c.not_overfull X hX

end Overfull
