import Overfull.Dense.TripartiteGraph
import Overfull.Dense.TriangleDecomposition

namespace Overfull.Dense.BalanceRepair

open Finset Classical
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable def arcOut (E : Finset (V × V)) (v : V) : ℕ :=
  ∑ e ∈ E, if e.1 = v then 1 else 0

noncomputable def arcIn (E : Finset (V × V)) (v : V) : ℕ :=
  ∑ e ∈ E, if e.2 = v then 1 else 0

noncomputable def arcBalance (E : Finset (V × V)) (v : V) : ℤ :=
  (arcOut E v : ℤ) - arcIn E v

theorem arcOut_eq_card (E : Finset (V × V)) (v : V) :
    arcOut E v = (E.filter (fun e => e.1 = v)).card := by
  simp [arcOut]

theorem arcIn_eq_card (E : Finset (V × V)) (v : V) :
    arcIn E v = (E.filter (fun e => e.2 = v)).card := by
  simp [arcIn]

theorem sum_arcOut [Fintype V] (E : Finset (V × V)) :
    (∑ v : V, arcOut E v) = E.card := by
  simp only [arcOut]
  rw [Finset.sum_comm]
  simp

theorem sum_arcIn [Fintype V] (E : Finset (V × V)) :
    (∑ v : V, arcIn E v) = E.card := by
  simp only [arcIn]
  rw [Finset.sum_comm]
  simp

theorem sum_arcBalance [Fintype V] (E : Finset (V × V)) :
    (∑ v : V, arcBalance E v) = 0 := by
  simp only [arcBalance, Finset.sum_sub_distrib, ← Nat.cast_sum,
    sum_arcOut, sum_arcIn, sub_self]

/-- The actual arcs of a short directed path, with its exact incidences.
The count interface records the source, target, and internal vertices. -/
structure RoutingPath (E : Finset (V × V)) (u v : V) where
  distinct : u ≠ v
  arcs : Finset (V × V)
  internal : Finset V
  subset : arcs ⊆ E
  short : arcs.card ≤ 4
  source_not_internal : u ∉ internal
  target_not_internal : v ∉ internal
  out_count : ∀ x, arcOut arcs x = (if x = u then 1 else 0) +
    (if x ∈ internal then 1 else 0)
  in_count : ∀ x, arcIn arcs x = (if x = v then 1 else 0) +
    (if x ∈ internal then 1 else 0)

theorem routingPath_two (E : Finset (V × V)) (u x v : V) (F : Finset V)
    (hux : u ≠ x) (huv : u ≠ v) (hxv : x ≠ v)
    (huxE : (u,x) ∈ E) (hxvE : (x,v) ∈ E) (hxF : x ∉ F) :
    ∃ P : RoutingPath E u v, Disjoint P.internal F := by
  have hedges : (u,x) ≠ (x,v) := fun h => hux (congrArg Prod.fst h)
  refine ⟨{
    distinct := huv
    arcs := {(u,x), (x,v)}
    internal := {x}
    subset := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨huxE,hxvE⟩
    short := by simp [hedges]
    source_not_internal := by simpa using hux
    target_not_internal := by simpa using hxv.symm
    out_count := ?_
    in_count := ?_ }, ?_⟩
  · intro z
    by_cases hzU : z = u <;> by_cases hzX : z = x <;>
      simp_all [arcOut, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · intro z
    by_cases hzV : z = v <;> by_cases hzX : z = x <;>
      simp_all [arcIn, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · simpa using hxF

theorem routingPath_three (E : Finset (V × V)) (u x y v : V) (F : Finset V)
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (huxE : (u,x) ∈ E) (hxyE : (x,y) ∈ E) (hyvE : (y,v) ∈ E)
    (hxF : x ∉ F) (hyF : y ∉ F) :
    ∃ P : RoutingPath E u v, Disjoint P.internal F := by
  have h₁ : (u,x) ≠ (x,y) := fun h => hux (congrArg Prod.fst h)
  have h₂ : (u,x) ≠ (y,v) := fun h => huy (congrArg Prod.fst h)
  have h₃ : (x,y) ≠ (y,v) := fun h => hxy (congrArg Prod.fst h)
  refine ⟨{
    distinct := huv
    arcs := {(u,x), (x,y), (y,v)}
    internal := {x,y}
    subset := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨huxE,hxyE,hyvE⟩
    short := by simp [h₁,h₂,h₃]
    source_not_internal := by simp [hux,huy]
    target_not_internal := by simp [hxv.symm,hyv.symm]
    out_count := ?_
    in_count := ?_ }, ?_⟩
  · intro z
    by_cases hzU : z = u <;> by_cases hzX : z = x <;> by_cases hzY : z = y <;>
      simp_all [arcOut, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · intro z
    by_cases hzV : z = v <;> by_cases hzX : z = x <;> by_cases hzY : z = y <;>
      simp_all [arcIn, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · simp [hxF,hyF]

theorem routingPath_four (E : Finset (V × V)) (u x y z v : V) (F : Finset V)
    (hux : u ≠ x) (huy : u ≠ y) (huz : u ≠ z) (huv : u ≠ v)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxv : x ≠ v)
    (hyz : y ≠ z) (hyv : y ≠ v) (hzv : z ≠ v)
    (huxE : (u,x) ∈ E) (hxyE : (x,y) ∈ E) (hyzE : (y,z) ∈ E) (hzvE : (z,v) ∈ E)
    (hxF : x ∉ F) (hyF : y ∉ F) (hzF : z ∉ F) :
    ∃ P : RoutingPath E u v, Disjoint P.internal F := by
  have h₁ : (u,x) ≠ (x,y) := fun h => hux (congrArg Prod.fst h)
  have h₂ : (u,x) ≠ (y,z) := fun h => huy (congrArg Prod.fst h)
  have h₃ : (u,x) ≠ (z,v) := fun h => huz (congrArg Prod.fst h)
  have h₄ : (x,y) ≠ (y,z) := fun h => hxy (congrArg Prod.fst h)
  have h₅ : (x,y) ≠ (z,v) := fun h => hxz (congrArg Prod.fst h)
  have h₆ : (y,z) ≠ (z,v) := fun h => hyz (congrArg Prod.fst h)
  refine ⟨{
    distinct := huv
    arcs := {(u,x), (x,y), (y,z), (z,v)}
    internal := {x,y,z}
    subset := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨huxE,hxyE,hyzE,hzvE⟩
    short := by simp [h₁,h₂,h₃,h₄,h₅,h₆]
    source_not_internal := by simp [hux,huy,huz]
    target_not_internal := by simp [hxv.symm,hyv.symm,hzv.symm]
    out_count := ?_
    in_count := ?_ }, ?_⟩
  · intro w
    by_cases hwU : w = u <;> by_cases hwX : w = x <;> by_cases hwY : w = y <;>
      by_cases hwZ : w = z <;> simp_all [arcOut, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · intro w
    by_cases hwV : w = v <;> by_cases hwX : w = x <;> by_cases hwY : w = y <;>
      by_cases hwZ : w = z <;> simp_all [arcIn, Finset.filter_insert, Finset.filter_singleton, eq_comm]
  · simp [hxF,hyF,hzF]

theorem exists_outside_image {X : Type*} [DecidableEq X]
    (f : X → V) (hf : Function.Injective f) (S : Finset X) (F : Finset V)
    (hcard : F.card < S.card) : ∃ x ∈ S, f x ∉ F := by
  by_contra! h
  have hsub : S.image f ⊆ F := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact h x hx
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S hf] at hc
  omega

theorem inter_card_bound {X : Type*} [Fintype X] [DecidableEq X]
    (S T : Finset X) : S.card + T.card ≤ (S ∩ T).card + Fintype.card X := by
  have h := Finset.card_union_add_card_inter S T
  have hu := Finset.card_le_univ (S ∪ T)
  omega

variable {A B W : Type*}

abbrev Vertex (A B W : Type*) := A ⊕ B ⊕ W

def arc (G : TripartiteGraph A B W) : Vertex A B W → Vertex A B W → Prop
  | .inl a, .inr (.inl b) => G.ab a b
  | .inr (.inl b), .inr (.inr w) => G.bw b w
  | .inr (.inr w), .inl a => G.aw a w
  | _, _ => False

variable [Fintype A] [Fintype B] [Fintype W]

noncomputable def arcSet (G : TripartiteGraph A B W) :
    Finset (Vertex A B W × Vertex A B W) := univ.filter (fun e => arc G e.1 e.2)

@[simp] theorem mem_arcSet (G : TripartiteGraph A B W) (u v : Vertex A B W) :
    (u,v) ∈ arcSet G ↔ arc G u v := by simp [arcSet]

/-- Explicit margins sufficient for routing after edge and vertex exclusions.
The real bounds permit direct use of the manuscript's density estimates. -/
structure RoutingConditions (G : TripartiteGraph A B W) (q k : ℝ) : Prop where
  q_nonneg : 0 ≤ q
  largeA : q+k+2 < Fintype.card A
  largeB : q+k+2 < Fintype.card B
  largeW : 2*q+k+2 < Fintype.card W
  degreeA : ∀ a, q+k+2 < ((G.neighborsB a).card : ℝ)
  degreeB : ∀ b, q+k+2 < ((G.neighborsA b).card : ℝ)
  missingA : ∀ a, (Fintype.card W : ℝ) ≤ (G.neighborsWA a).card + q
  missingB : ∀ b, (Fintype.card W : ℝ) ≤ (G.neighborsWB b).card + q
  missingWA : ∀ w, (Fintype.card A : ℝ) ≤ (G.linkA w).card + q
  missingWB : ∀ w, (Fintype.card B : ℝ) ≤ (G.linkB w).card + q

variable [DecidableEq A] [DecidableEq B] [DecidableEq W]

omit [Fintype A] [Fintype B] [Fintype W] in
theorem choose_from_large_set {X : Type*} [DecidableEq X]
    (f : X → Vertex A B W) (hf : Function.Injective f)
    (S : Finset X) (F : Finset (Vertex A B W)) (k : ℝ)
    (hF : (F.card : ℝ) ≤ k+2) (hS : k+2 < (S.card : ℝ)) :
    ∃ x ∈ S, f x ∉ F := by
  apply exists_outside_image f hf S F
  exact_mod_cast hF.trans_lt hS

omit [Fintype A] [Fintype B] [Fintype W] in
theorem choose_from_intersection {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Vertex A B W) (hf : Function.Injective f)
    (S T : Finset X) (F : Finset (Vertex A B W)) (q k : ℝ)
    (hF : (F.card : ℝ) ≤ k+2) (hS : q+k+2 < (S.card : ℝ))
    (hT : (Fintype.card X : ℝ) ≤ T.card+q) :
    ∃ x, x ∈ S ∧ x ∈ T ∧ f x ∉ F := by
  have hcount : (S.card : ℝ) + T.card ≤ (S ∩ T).card + Fintype.card X := by
    exact_mod_cast inter_card_bound S T
  obtain ⟨x,hx,hxF⟩ := choose_from_large_set f hf (S ∩ T) F k hF (by linarith)
  exact ⟨x,(Finset.mem_inter.mp hx).1,(Finset.mem_inter.mp hx).2,hxF⟩

omit [Fintype A] [Fintype B] [Fintype W] in
theorem choose_from_two_almost_complete_sets {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Vertex A B W) (hf : Function.Injective f)
    (S T : Finset X) (F : Finset (Vertex A B W)) (q k : ℝ)
    (hF : (F.card : ℝ) ≤ k+2) (hlarge : 2*q+k+2 < Fintype.card X)
    (hS : (Fintype.card X : ℝ) ≤ S.card+q)
    (hT : (Fintype.card X : ℝ) ≤ T.card+q) :
    ∃ x, x ∈ S ∧ x ∈ T ∧ f x ∉ F := by
  exact choose_from_intersection f hf S T F q k hF (by linarith) hT

end Overfull.Dense.BalanceRepair
