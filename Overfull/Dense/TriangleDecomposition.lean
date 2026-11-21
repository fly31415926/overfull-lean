import Overfull.Dense.TripartiteGraph

/-!
# Finite triangle decompositions of actual tripartite graphs

A selected finite set of actual triangles covers each indicated edge exactly
once and every other edge zero times. The target may be a subgraph's edge set.
-/

namespace Overfull.TripartiteGraph

open Finset Classical

variable {A B W : Type*} (G : TripartiteGraph A B W)

/-- Whether an edge coordinate is an actual edge of the graph. -/
def IsEdge : EdgePosition (A := A) (B := B) (W := W) → Prop
  | .inl (a,b) => G.ab a b
  | .inr (.inl (a,w)) => G.aw a w
  | .inr (.inr (b,w)) => G.bw b w

/-- The three actual edges of a triangle, identified by their coordinates. -/
def ContainsEdge (t : G.Triangle) :
    EdgePosition (A := A) (B := B) (W := W) → Prop
  | .inl (a,b) => t.val.1 = a ∧ t.val.2.1 = b
  | .inr (.inl (a,w)) => t.val.1 = a ∧ t.val.2.2 = w
  | .inr (.inr (b,w)) => t.val.2.1 = b ∧ t.val.2.2 = w

theorem containsEdge_isEdge (t : G.Triangle)
    (e : EdgePosition (A := A) (B := B) (W := W))
    (h : G.ContainsEdge t e) : G.IsEdge e := by
  rcases t with ⟨⟨a,b,w⟩, hab, haw, hbw⟩
  cases e with
  | inl ab =>
      rcases ab with ⟨a',b'⟩
      rcases h with ⟨rfl,rfl⟩
      exact hab
  | inr z =>
      cases z with
      | inl aw =>
          rcases aw with ⟨a',w'⟩
          rcases h with ⟨rfl,rfl⟩
          exact haw
      | inr bw =>
          rcases bw with ⟨b',w'⟩
          rcases h with ⟨rfl,rfl⟩
          exact hbw

variable [Fintype A] [Fintype B] [Fintype W]

noncomputable def edgeFinset : Finset (EdgePosition (A := A) (B := B) (W := W)) :=
  univ.filter G.IsEdge

@[simp] theorem mem_edgeFinset (e : EdgePosition (A := A) (B := B) (W := W)) :
    e ∈ G.edgeFinset ↔ G.IsEdge e := by simp [edgeFinset]

noncomputable def trianglesAt (T : Finset G.Triangle)
    (e : EdgePosition (A := A) (B := B) (W := W)) : Finset G.Triangle :=
  T.filter (fun t => G.ContainsEdge t e)

/-- Exact edge coverage by a finite collection of actual triangles. -/
def IsTriangleDecomposition (T : Finset G.Triangle)
    (E : Finset (EdgePosition (A := A) (B := B) (W := W))) : Prop :=
  ∀ e, (G.trianglesAt T e).card = if e ∈ E then 1 else 0

def HasTriangleDecomposition : Prop :=
  ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T G.edgeFinset

omit [Fintype A] [Fintype B] [Fintype W] in
theorem IsTriangleDecomposition.unique {T : Finset G.Triangle}
    {E : Finset (EdgePosition (A := A) (B := B) (W := W))}
    (hT : G.IsTriangleDecomposition T E) {e} (he : e ∈ E) :
    ∃! t : G.Triangle, t ∈ T ∧ G.ContainsEdge t e := by
  have hc : (G.trianglesAt T e).card = 1 := by rw [hT e, if_pos he]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  have hmem (s : G.Triangle) : s ∈ T ∧ G.ContainsEdge s e ↔ s = t := by
    have hh : s ∈ G.trianglesAt T e ↔ s = t := by
      rw [ht, Finset.mem_singleton]
    simpa only [trianglesAt, Finset.mem_filter] using hh
  exact ⟨t, (hmem t).mpr rfl, fun s hs => (hmem s).mp hs⟩

omit [Fintype A] [Fintype B] [Fintype W] in
theorem IsTriangleDecomposition.support {T : Finset G.Triangle}
    {E : Finset (EdgePosition (A := A) (B := B) (W := W))}
    (hT : G.IsTriangleDecomposition T E) {t : G.Triangle} (ht : t ∈ T)
    {e} (he : G.ContainsEdge t e) : e ∈ E := by
  by_contra h
  have hz : (G.trianglesAt T e).card = 0 := by rw [hT e, if_neg h]
  have hh : t ∈ G.trianglesAt T e := Finset.mem_filter.mpr ⟨ht,he⟩
  rw [Finset.card_eq_zero.mp hz] at hh
  exact Finset.notMem_empty _ hh

omit [Fintype A] [Fintype B] [Fintype W] in
theorem isTriangleDecomposition_of_unique (T : Finset G.Triangle)
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hsupport : ∀ t ∈ T, ∀ e, G.ContainsEdge t e → e ∈ E)
    (hcover : ∀ e ∈ E, ∃! t : G.Triangle, t ∈ T ∧ G.ContainsEdge t e) :
    G.IsTriangleDecomposition T E := by
  intro e
  by_cases he : e ∈ E
  · rw [if_pos he]
    obtain ⟨t, ht, huniq⟩ := hcover e he
    apply Finset.card_eq_one.mpr
    refine ⟨t, ?_⟩
    ext s
    simp only [trianglesAt, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hs => huniq s hs, fun hs => hs ▸ ht⟩
  · rw [if_neg he]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact he (hsupport t (Finset.mem_filter.mp ht).1 e (Finset.mem_filter.mp ht).2)

theorem isTriangleDecomposition_of_full_unique (T : Finset G.Triangle)
    (hcover : ∀ e, G.IsEdge e → ∃! t : G.Triangle, t ∈ T ∧ G.ContainsEdge t e) :
    G.IsTriangleDecomposition T G.edgeFinset :=
  G.isTriangleDecomposition_of_unique T G.edgeFinset
    (fun t _ e he => (G.mem_edgeFinset e).mpr (G.containsEdge_isEdge t e he))
    (fun e he => hcover e ((G.mem_edgeFinset e).mp he))

theorem IsTriangleDecomposition.full_unique {T : Finset G.Triangle}
    (hT : G.IsTriangleDecomposition T G.edgeFinset) {e}
    (he : G.IsEdge e) : ∃! t : G.Triangle, t ∈ T ∧ G.ContainsEdge t e :=
  hT.unique G ((G.mem_edgeFinset e).mpr he)

end Overfull.TripartiteGraph

