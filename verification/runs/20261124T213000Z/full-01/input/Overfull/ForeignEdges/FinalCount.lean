import Overfull.ForeignEdges.Assignment
import Overfull.SafePrescription.Boundary

/-!
# Counting every exceptional incidence outside its assigned core

Each relevant edge has exactly one exceptional endpoint.  Same-cluster
unmarked foreign edges account for one part; the actual fixed boundary
accounts for all marked or intercluster edges.  The counting theorem keeps
these as actual host-edge finsets.
-/

namespace Overfull.ForeignAssignment

open Finset Classical SimpleGraph FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I C : Type*} [Fintype V]

/-- All exceptional-to-core edges outside the assigned core, with no
same-cluster restriction. -/
noncomputable def allForeignEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (a : V → I) : Finset G.edgeSet :=
  foreignEdges G U Z (fun _ => ()) (fun _ => ()) a

/-- The two endpoints of every counted edge have different exceptional
membership.  This is what makes an edge count also an incidence count. -/
theorem allForeignEdges_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (a : V → I)
    (hUZ : ∀ i, Disjoint (U i) Z) (e : G.edgeSet) (he : e ∈ allForeignEdges G U Z a) :
    (firstEnd e ∈ Z) ≠ (secondEnd e ∈ Z) := by
  have he' : e.val ∈ (foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).edgeSet :=
    (mem_foreignEdges G U Z (fun _ => ()) (fun _ => ()) a e).mp he
  rw [← edge_eq e] at he'
  change (foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).Adj (firstEnd e) (secondEnd e) at he'
  rcases he'.2 with ⟨hu,i,hv,_⟩ | ⟨hv,i,hu,_⟩
  · exact fun h => disjoint_left.mp (hUZ i) hv (h ▸ hu)
  · exact fun h => disjoint_left.mp (hUZ i) hu (h ▸ hv)

omit [Fintype V] in
/-- A finset of actual cut edges contributes exactly one incidence at the
vertices on a specified shore. -/
theorem cut_edge_incidence_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) (Z : Finset V)
    (hcross : ∀ e ∈ A, (firstEnd e ∈ Z) ≠ (secondEnd e ∈ Z)) :
    (∑ v ∈ Z, (A.filter (fun e => v ∈ e.val)).card) = A.card := by
  have hone (e : G.edgeSet) (he : e ∈ A) :
      (Z.filter (fun v => v ∈ e.val)).card = 1 := by
    have hc := hcross e he
    by_cases hu : firstEnd e ∈ Z
    · have hv : secondEnd e ∉ Z := fun hv => hc (propext (iff_of_true hu hv))
      have hset : Z.filter (fun v => v ∈ e.val) = {firstEnd e} := by
        ext v
        rw [mem_filter,← edge_eq e,Sym2.mem_iff,mem_singleton]
        constructor
        · rintro ⟨hvZ,hvU | hvV⟩
          · exact hvU
          · exact False.elim (hv (hvV ▸ hvZ))
        · intro h
          subst v
          exact ⟨hu,Or.inl rfl⟩
      rw [hset,card_singleton]
    · have hv : secondEnd e ∈ Z := by
        by_contra hn
        exact hc (propext (iff_of_false hu hn))
      have hset : Z.filter (fun v => v ∈ e.val) = {secondEnd e} := by
        ext v
        rw [mem_filter,← edge_eq e,Sym2.mem_iff,mem_singleton]
        constructor
        · rintro ⟨hvZ,hvU | hvV⟩
          · exact False.elim (hu (hvU ▸ hvZ))
          · exact hvV
        · intro h
          subst v
          exact ⟨hv,Or.inr rfl⟩
      rw [hset,card_singleton]
  calc
    _ = ∑ v ∈ Z, ∑ e ∈ A, if v ∈ e.val then 1 else 0 := by
      simp only [card_eq_sum_ones,sum_filter]
    _ = ∑ e ∈ A, ∑ v ∈ Z, if v ∈ e.val then 1 else 0 := sum_comm
    _ = ∑ e ∈ A, (Z.filter (fun v => v ∈ e.val)).card := by
      simp only [card_eq_sum_ones,sum_filter]
    _ = ∑ _e ∈ A, 1 := sum_congr rfl hone
    _ = A.card := by simp

/-- No factor of two is lost: the total exceptional incidence is the
cardinality of the actual edge finset. -/
theorem allForeignEdges_incidence_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (a : V → I)
    (hUZ : ∀ i, Disjoint (U i) Z) :
    (∑ v ∈ Z, ((allForeignEdges G U Z a).filter (fun e => v ∈ e.val)).card) =
      (allForeignEdges G U Z a).card :=
  cut_edge_incidence_sum G _ Z (allForeignEdges_cross G U Z a hUZ)

/-- At an exceptional vertex the counted incidences are exactly its
neighbours in cores other than its assigned core. -/
theorem allForeignEdges_incidence_eq_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (a : V → I)
    (hUZ : ∀ i, Disjoint (U i) Z) (v : V) (hv : v ∈ Z) :
    ((allForeignEdges G U Z a).filter (fun e => v ∈ e.val)).card =
      ((G.neighborFinset v).filter (fun w => ∃ i, w ∈ U i ∧ i ≠ a v)).card := by
  change ((foreignEdges G U Z (fun _ => ()) (fun _ => ()) a).filter _).card = _
  rw [foreignEdges_incidence,← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  constructor
  · intro hw
    have hw' := ((foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).mem_neighborFinset v w).mp hw
    apply mem_filter.mpr
    refine ⟨(G.mem_neighborFinset v w).mpr hw'.1,?_⟩
    rcases hw'.2 with ⟨_,i,hi,_,hia⟩ | ⟨_,i,hi,_⟩
    · exact ⟨i,hi,hia⟩
    · exact False.elim (disjoint_left.mp (hUZ i) hi hv)
  · intro hw
    obtain ⟨hG,i,hi,hia⟩ := mem_filter.mp hw
    apply ((foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).mem_neighborFinset v w).mpr
    exact ⟨(G.mem_neighborFinset v w).mp hG,Or.inl ⟨hv,i,hi,rfl,hia⟩⟩

/-- Every unassigned edge is either an unmarked same-cluster foreign edge
or an edge in the actual marked/intercluster boundary. -/
theorem allForeignEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z Z₀ : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hcolor : ∀ i v, v ∈ U i → c v = p i) :
    allForeignEdges G U Z a ⊆
      foreignEdges G U (Z \ Z₀) c p a ∪ SafePrescription.boundaryEdges G c Z₀ := by
  intro e he
  by_cases hb : e ∈ SafePrescription.boundaryEdges G c Z₀
  · exact mem_union_right _ hb
  · have hn := (SafePrescription.mem_boundaryEdges G c Z₀ e).not.mp hb
    push_neg at hn
    have he' : e.val ∈ (foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).edgeSet :=
      (mem_foreignEdges G U Z (fun _ => ()) (fun _ => ()) a e).mp he
    rw [← edge_eq e] at he'
    change (foreignGraph G U Z (fun _ => ()) (fun _ => ()) a).Adj (firstEnd e) (secondEnd e) at he'
    apply mem_union_left
    apply (mem_foreignEdges G U (Z \ Z₀) c p a e).mpr
    rw [← edge_eq e]
    change (foreignGraph G U (Z \ Z₀) c p a).Adj (firstEnd e) (secondEnd e)
    refine ⟨he'.1,?_⟩
    rcases he'.2 with ⟨hu,i,hv,_,hia⟩ | ⟨hv,i,hu,_,hia⟩
    · exact Or.inl ⟨mem_sdiff.mpr ⟨hu,hn.1⟩,i,hv,(hcolor i _ hv).symm.trans hn.2.2.symm,hia⟩
    · exact Or.inr ⟨mem_sdiff.mpr ⟨hv,hn.2.1⟩,i,hu,(hcolor i _ hu).symm.trans hn.2.2,hia⟩

/-- Actual total exceptional incidence is bounded by the remaining
same-cluster foreign edges, the actual intercluster edges, and the degree
sum at marked vertices. -/
theorem allForeignEdges_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z Z₀ : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (h : ℕ) (hregular : ∀ v, G.degree v = h) :
    (allForeignEdges G U Z a).card ≤
      (foreignEdges G U (Z \ Z₀) c p a).card +
        (SafePrescription.clusterCrossingEdges G c Z₀).card + Z₀.card*h := by
  have hsub := card_le_card (allForeignEdges_subset G U Z Z₀ c p a hcolor)
  have hsum := card_union_le (foreignEdges G U (Z \ Z₀) c p a)
    (SafePrescription.boundaryEdges G c Z₀)
  have hb := SafePrescription.boundaryEdges_card_le G c Z₀ h hregular
  omega

theorem allForeignEdges_incidence_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z Z₀ : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (h : ℕ) (hregular : ∀ v, G.degree v = h) :
    (∑ v ∈ Z, ((allForeignEdges G U Z a).filter (fun e => v ∈ e.val)).card) ≤
      (foreignEdges G U (Z \ Z₀) c p a).card +
        (SafePrescription.clusterCrossingEdges G c Z₀).card + Z₀.card*h := by
  rw [allForeignEdges_incidence_sum G U Z a hUZ]
  exact allForeignEdges_card_le G U Z Z₀ c p a hcolor h hregular

/-- The final bound from a completed last phase, using its fresh
assignment.  The actual edge and incidence bounds are retained throughout. -/
theorem final_foreign_incidence_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z Z₀ : Finset V) (c : V → C) (p : I → C) (a : V → I)
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (h k₀ c₁ t₀ : ℕ) (hregular : ∀ v, G.degree v = h)
    (hforeign : (foreignEdges G U (Z \ Z₀) c p a).card ≤ c₁*k₀)
    (hcross : (SafePrescription.clusterCrossingEdges G c Z₀).card ≤ 6*k₀)
    (hmarked : Z₀.card ≤ t₀) (hh : h ≤ k₀) (hreserve : k₀ ≤ 256*h) :
    (∑ v ∈ Z, ((G.neighborFinset v).filter
      (fun w => ∃ i, w ∈ U i ∧ i ≠ a v)).card) ≤ 256*(c₁+6+t₀)*h := by
  have hinc := allForeignEdges_incidence_le G U Z Z₀ c p a hUZ hcolor h hregular
  have hmarked' : Z₀.card*h ≤ t₀*k₀ := Nat.mul_le_mul hmarked hh
  have hsum : (∑ v ∈ Z, ((allForeignEdges G U Z a).filter (fun e => v ∈ e.val)).card) ≤
      (c₁+6+t₀)*k₀ := by nlinarith
  have heq : (∑ v ∈ Z, ((allForeignEdges G U Z a).filter (fun e => v ∈ e.val)).card) =
      ∑ v ∈ Z, ((G.neighborFinset v).filter
        (fun w => ∃ i, w ∈ U i ∧ i ≠ a v)).card := by
    apply sum_congr rfl
    exact fun v hv => allForeignEdges_incidence_eq_neighbors G U Z a hUZ v hv
  rw [heq] at hsum
  calc
    _ ≤ (c₁+6+t₀)*k₀ := hsum
    _ ≤ (c₁+6+t₀)*(256*h) := Nat.mul_le_mul_left _ hreserve
    _ = 256*(c₁+6+t₀)*h := by ring

end Overfull.ForeignAssignment
