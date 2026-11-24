import Overfull.Dense.SignedFlow

/-!
# Simple tripartite graphs and weighted local balance

The three adjacency relations specify the actual edges between three disjoint
vertex classes. There is one possible edge for each pair from different classes,
so this is an explicit model of a simple tripartite graph.
-/

namespace Overfull

open Finset Classical

/-- An actual simple tripartite graph, with its three ordered vertex classes. -/
structure TripartiteGraph (A B W : Type*) where
  ab : A → B → Prop
  aw : A → W → Prop
  bw : B → W → Prop

namespace TripartiteGraph

variable {A B W : Type*} (G : TripartiteGraph A B W)

/-- The corresponding simple graph on the disjoint union of its three parts. -/
def toSimpleGraph : SimpleGraph (A ⊕ B ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inr (.inl b) => G.ab a b
    | .inr (.inl b), .inl a => G.ab a b
    | .inl a, .inr (.inr w) => G.aw a w
    | .inr (.inr w), .inl a => G.aw a w
    | .inr (.inl b), .inr (.inr w) => G.bw b w
    | .inr (.inr w), .inr (.inl b) => G.bw b w
    | _, _ => False
  symm := by rintro (a | b | w) (a' | b' | w') h <;> exact h
  loopless := by
    intro x
    cases x with
    | inl a => exact not_false
    | inr z => cases z <;> exact not_false

/-- The coordinates of an edge weighting, including zero coordinates on nonedges. -/
abbrev EdgePosition := (A × B) ⊕ (A × W) ⊕ (B × W)

def abPos (a : A) (b : B) : EdgePosition (A := A) (B := B) (W := W) := .inl (a,b)
def awPos (a : A) (w : W) : EdgePosition (A := A) (B := B) (W := W) := .inr (.inl (a,w))
def bwPos (b : B) (w : W) : EdgePosition (A := A) (B := B) (W := W) := .inr (.inr (b,w))

def IsTriangle (a : A) (b : B) (w : W) : Prop := G.ab a b ∧ G.aw a w ∧ G.bw b w

abbrev Triangle := {t : A × B × W // G.IsTriangle t.1 t.2.1 t.2.2}

noncomputable def extendTriangle (p : G.Triangle → ℝ) (a : A) (b : B) (w : W) : ℝ :=
  if h : G.IsTriangle a b w then p ⟨(a,b,w),h⟩ else 0

@[simp] theorem extendTriangle_of_triangle (p : G.Triangle → ℝ) (a : A) (b : B) (w : W)
    (h : G.IsTriangle a b w) : G.extendTriangle p a b w = p ⟨(a,b,w),h⟩ := by
  simp [extendTriangle,h]

@[simp] theorem extendTriangle_of_not_triangle (p : G.Triangle → ℝ) (a : A) (b : B) (w : W)
    (h : ¬ G.IsTriangle a b w) : G.extendTriangle p a b w = 0 := by
  simp [extendTriangle,h]

variable [Fintype A] [Fintype B] [Fintype W]

noncomputable def neighborsB (a : A) : Finset B := univ.filter (G.ab a)
noncomputable def neighborsA (b : B) : Finset A := univ.filter (fun a => G.ab a b)
noncomputable def neighborsWA (a : A) : Finset W := univ.filter (G.aw a)
noncomputable def neighborsWB (b : B) : Finset W := univ.filter (G.bw b)
noncomputable def linkA (w : W) : Finset A := univ.filter (fun a => G.aw a w)
noncomputable def linkB (w : W) : Finset B := univ.filter (fun b => G.bw b w)

noncomputable def IsLocallyBalanced : Prop :=
  (∀ a, (G.neighborsB a).card = (G.neighborsWA a).card) ∧
  (∀ b, (G.neighborsA b).card = (G.neighborsWB b).card) ∧
  ∀ w, (G.linkA w).card = (G.linkB w).card

/-- An edge weighting is supported on actual edges and satisfies all three
weighted local-balance identities. -/
def BalancedWeight (r : EdgePosition (A := A) (B := B) (W := W) → ℝ) : Prop :=
  (∀ a b, ¬ G.ab a b → r (abPos a b) = 0) ∧
  (∀ a w, ¬ G.aw a w → r (awPos a w) = 0) ∧
  (∀ b w, ¬ G.bw b w → r (bwPos b w) = 0) ∧
  (∀ a, ∑ b, r (abPos a b) = ∑ w, r (awPos a w)) ∧
  (∀ b, ∑ a, r (abPos a b) = ∑ w, r (bwPos b w)) ∧
  ∀ w, ∑ a, r (awPos a w) = ∑ b, r (bwPos b w)

noncomputable def balancedSpace : Submodule ℝ
    (EdgePosition (A := A) (B := B) (W := W) → ℝ) where
  carrier := G.BalancedWeight
  zero_mem' := by
    change G.BalancedWeight (fun _ => 0)
    simp [BalancedWeight]
  add_mem' := by
    intro r s hr hs
    rcases hr with ⟨hrab,hraw,hrbw,hrA,hrB,hrW⟩
    rcases hs with ⟨hsab,hsaw,hsbw,hsA,hsB,hsW⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro a b h; simp [hrab a b h,hsab a b h]
    · intro a w h; simp [hraw a w h,hsaw a w h]
    · intro b w h; simp [hrbw b w h,hsbw b w h]
    · intro a; simp [sum_add_distrib,hrA,hsA]
    · intro b; simp [sum_add_distrib,hrB,hsB]
    · intro w; simp [sum_add_distrib,hrW,hsW]
  smul_mem' := by
    intro c r hr
    rcases hr with ⟨hrab,hraw,hrbw,hrA,hrB,hrW⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro a b h; simp [hrab a b h]
    · intro a w h; simp [hraw a w h]
    · intro b w h; simp [hrbw b w h]
    · intro a; simp [← mul_sum,hrA]
    · intro b; simp [← mul_sum,hrB]
    · intro w; simp [← mul_sum,hrW]

noncomputable def incidence (p : G.Triangle → ℝ) :
    EdgePosition (A := A) (B := B) (W := W) → ℝ
  | .inl (a,b) => ∑ w, G.extendTriangle p a b w
  | .inr (.inl (a,w)) => ∑ b, G.extendTriangle p a b w
  | .inr (.inr (b,w)) => ∑ a, G.extendTriangle p a b w

noncomputable def incidenceLinear : (G.Triangle → ℝ) →ₗ[ℝ]
    (EdgePosition (A := A) (B := B) (W := W) → ℝ) where
  toFun := G.incidence
  map_add' := by
    intro p q
    have h (a : A) (b : B) (w : W) : G.extendTriangle (p+q) a b w =
        G.extendTriangle p a b w + G.extendTriangle q a b w := by
      by_cases h : G.IsTriangle a b w <;> simp [extendTriangle,h]
    funext e
    cases e with
    | inl ab => simp [incidence,h,sum_add_distrib]
    | inr z => cases z <;> simp [incidence,h,sum_add_distrib]
  map_smul' := by
    intro c p
    have h (a : A) (b : B) (w : W) : G.extendTriangle (c • p) a b w =
        c * G.extendTriangle p a b w := by
      by_cases h : G.IsTriangle a b w <;> simp [extendTriangle,h]
    funext e
    cases e with
    | inl ab => simp [incidence,h,mul_sum]
    | inr z => cases z <;> simp [incidence,h,mul_sum]

theorem incidence_balanced (p : G.Triangle → ℝ) : G.BalancedWeight (G.incidence p) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a b h
    simp [incidence,abPos,extendTriangle,IsTriangle,h]
  · intro a w h
    simp [incidence,awPos,extendTriangle,IsTriangle,h]
  · intro b w h
    simp [incidence,bwPos,extendTriangle,IsTriangle,h]
  · intro a; exact sum_comm
  · intro b; exact sum_comm
  · intro w; exact sum_comm

noncomputable def edgeOne : EdgePosition (A := A) (B := B) (W := W) → ℝ
  | .inl (a,b) => if G.ab a b then 1 else 0
  | .inr (.inl (a,w)) => if G.aw a w then 1 else 0
  | .inr (.inr (b,w)) => if G.bw b w then 1 else 0

theorem edgeOne_balanced (hG : G.IsLocallyBalanced) : G.BalancedWeight G.edgeOne := by
  rcases hG with ⟨hA,hB,hW⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a b h; simp [edgeOne,abPos,h]
  · intro a w h; simp [edgeOne,awPos,h]
  · intro b w h; simp [edgeOne,bwPos,h]
  · intro a
    have h := congrArg (fun n : ℕ => (n : ℝ)) (hA a)
    simpa [neighborsB,neighborsWA,edgeOne,abPos,awPos] using h
  · intro b
    have h := congrArg (fun n : ℕ => (n : ℝ)) (hB b)
    simpa [neighborsA,neighborsWB,edgeOne,abPos,bwPos] using h
  · intro w
    have h := congrArg (fun n : ℕ => (n : ℝ)) (hW w)
    simpa [linkA,linkB,edgeOne,awPos,bwPos] using h

/-- The actual degree and missing-neighbor hypotheses of Lemma 5.7. -/
structure DensityConditions (η ε : ℝ) : Prop where
  partSizes : Fintype.card A = Fintype.card B
  localBalance : G.IsLocallyBalanced
  degreeA : ∀ a, (1 / 2 + η) * Fintype.card A ≤ ((G.neighborsB a).card : ℝ)
  degreeB : ∀ b, (1 / 2 + η) * Fintype.card A ≤ ((G.neighborsA b).card : ℝ)
  missingA : ∀ a, (Fintype.card W : ℝ) - (G.neighborsWA a).card ≤ ε * Fintype.card A
  missingB : ∀ b, (Fintype.card W : ℝ) - (G.neighborsWB b).card ≤ ε * Fintype.card A
  missingWA : ∀ w, (Fintype.card A : ℝ) - (G.linkA w).card ≤ ε * Fintype.card A
  missingWB : ∀ w, (Fintype.card A : ℝ) - (G.linkB w).card ≤ ε * Fintype.card A

omit [Fintype A] [Fintype B] [Fintype W] in
/-- Extending a triangle weighting by zero never increases a coordinate bound. -/
theorem extendTriangle_abs_le (p : G.Triangle → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hp : ∀ t, |p t| ≤ d) (a : A) (b : B) (w : W) :
    |G.extendTriangle p a b w| ≤ d := by
  by_cases h : G.IsTriangle a b w
  · simpa [extendTriangle,h] using hp ⟨(a,b,w),h⟩
  · simpa [extendTriangle,h] using hd

/-- Restricting a supported three-index array gives an actual triangle weighting. -/
noncomputable def restrictTriangles (P : A → B → W → ℝ) : G.Triangle → ℝ :=
  fun t => P t.val.1 t.val.2.1 t.val.2.2

omit [Fintype A] [Fintype B] [Fintype W] in
theorem extend_restrictTriangles (P : A → B → W → ℝ)
    (hP : ∀ a b w, ¬ G.IsTriangle a b w → P a b w = 0) (a : A) (b : B) (w : W) :
    G.extendTriangle (G.restrictTriangles P) a b w = P a b w := by
  by_cases h : G.IsTriangle a b w <;> simp [extendTriangle,restrictTriangles,h,hP a b w]

end TripartiteGraph
end Overfull
