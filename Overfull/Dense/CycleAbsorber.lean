import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
The explicit cycle absorber from Lemma `dense:cycle` of the manuscript.

Edges below are unordered pairs of actual vertices. A triangle has three
distinct vertices, and a triangle decomposition covers each graph edge
exactly once. The template works for every positive cycle length.
-/

namespace Overfull.Dense

/-- Three distinct vertices, with their three actual unordered edges. -/
structure Triangle (V : Type*) where
  a : V
  b : V
  c : V
  ab : a ≠ b
  bc : b ≠ c
  ca : c ≠ a

def Triangle.edge {V : Type*} (T : Triangle V) : Fin 3 → Sym2 V
  | 0 => s(T.a, T.b)
  | 1 => s(T.b, T.c)
  | 2 => s(T.c, T.a)

theorem Triangle.edge_not_diag {V : Type*} (T : Triangle V) (j : Fin 3) :
    ¬ (T.edge j).IsDiag := by
  fin_cases j <;> simp [Triangle.edge, T.ab, T.bc, T.ca]

def triangleEdges {V I : Type*} [DecidableEq V] [Fintype I]
    (T : I → Triangle V) : Finset (Sym2 V) :=
  Finset.univ.image (fun p : I × Fin 3 => (T p.1).edge p.2)

/-- The indicated triangles use every edge of `G` exactly once.

Injectivity excludes reuse both within a triangle and between triangles;
the edge-set equality supplies coverage and requires every used edge to
be an actual edge of `G`.
-/
def IsTriangleDecomposition {V I : Type*} [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (T : I → Triangle V) : Prop :=
  Function.Injective (fun p : I × Fin 3 => (T p.1).edge p.2) ∧
  G.edgeSet = (triangleEdges T : Set (Sym2 V))

theorem triangleEdges_card {V I : Type*} [DecidableEq V] [Fintype I]
    (T : I → Triangle V)
    (hT : Function.Injective (fun p : I × Fin 3 => (T p.1).edge p.2)) :
    (triangleEdges T).card = Fintype.card I * 3 := by
  classical
  simp [triangleEdges, Finset.card_image_of_injective _ hT]

theorem triangleEdges_not_diag {V I : Type*} [DecidableEq V] [Fintype I]
    (T : I → Triangle V) {e : Sym2 V} (he : e ∈ triangleEdges T) :
    ¬ e.IsDiag := by
  obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp he
  exact (T i).edge_not_diag j

theorem edgeSet_from_finset {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).edgeSet = E := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq]
  exact ⟨And.left, fun he => ⟨he, hE e he⟩⟩

def Triangle.map {V W : Type*} (f : V ↪ W) (T : Triangle V) : Triangle W :=
  ⟨f T.a, f T.b, f T.c, f.injective.ne T.ab, f.injective.ne T.bc,
    f.injective.ne T.ca⟩

@[simp] theorem Triangle.map_edge {V W : Type*} (f : V ↪ W)
    (T : Triangle V) (j : Fin 3) :
    (T.map f).edge j = Sym2.map f (T.edge j) := by
  fin_cases j <;> rfl

theorem triangleEdges_map {V W I : Type*} [DecidableEq V] [DecidableEq W]
    [Fintype I] (f : V ↪ W) (T : I → Triangle V) :
    triangleEdges (fun i => (T i).map f) = (triangleEdges T).image (Sym2.map f) := by
  simp [triangleEdges, Finset.image_image, Function.comp_def]

theorem IsTriangleDecomposition.map {V W I : Type*} [DecidableEq V] [DecidableEq W]
    [Fintype I] {G : SimpleGraph V} {T : I → Triangle V}
    (h : IsTriangleDecomposition G T) (f : V ↪ W) :
    IsTriangleDecomposition (G.map f) (fun i => (T i).map f) := by
  refine ⟨?_, ?_⟩
  · intro p q hpq
    apply h.1
    apply Sym2.map.injective f.injective
    simpa using hpq
  · rw [SimpleGraph.edgeSet_map, h.2, triangleEdges_map, Finset.coe_image]
    rfl

/-- The vertices incident with the explicitly specified edge set. -/
def edgeVertices {V : Type*} [DecidableEq V] (E : Finset (Sym2 V)) : Finset V :=
  E.biUnion Sym2.toFinset

@[simp] theorem mem_edgeVertices {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (v : V) :
    v ∈ edgeVertices E ↔ ∃ e ∈ E, v ∈ e := by
  simp [edgeVertices]

theorem edgeVertices_eq_support {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : G.edgeSet = (E : Set (Sym2 V))) :
    (edgeVertices E : Set V) = G.support := by
  ext v
  simp only [Finset.mem_coe, mem_edgeVertices, SimpleGraph.mem_support]
  constructor
  · rintro ⟨e, he, hv⟩
    have heG : e ∈ G.edgeSet := by simpa [hE] using he
    induction e using Sym2.ind with
    | _ x y =>
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ⟨y, heG⟩
      · exact ⟨x, heG.symm⟩
  · rintro ⟨w, hvw⟩
    refine ⟨s(v, w), ?_, by simp⟩
    have heG : s(v, w) ∈ G.edgeSet := hvw
    simpa [hE] using heG

namespace CycleAbsorber

inductive Vertex (ℓ : ℕ)
  | x (i : Fin ℓ)
  | y (i : Fin ℓ)
  | w (i : Fin ℓ)
  | xAux (i : Fin ℓ)
  | yAux (i : Fin ℓ)
  | center
  deriving DecidableEq, Fintype

open Vertex

/-- Successor modulo the cycle length. `finRotate` is an actual permutation. -/
abbrev next (ℓ : ℕ) : Equiv.Perm (Fin ℓ) := finRotate ℓ

/-- The nine listed absorber edges for a cycle index. -/
def absorberEdge {ℓ : ℕ} (p : Fin 9 × Fin ℓ) : Sym2 (Vertex ℓ) :=
  match p.1 with
  | 0 => s(x (next ℓ p.2), yAux p.2)
  | 1 => s(yAux p.2, xAux p.2)
  | 2 => s(xAux p.2, y p.2)
  | 3 => s(x (next ℓ p.2), center)
  | 4 => s(yAux p.2, center)
  | 5 => s(xAux p.2, center)
  | 6 => s(y p.2, center)
  | 7 => s(yAux p.2, w p.2)
  | 8 => s(xAux p.2, w p.2)

/-- The original cycle has edges `x_i y_i`, `y_i w_i`, `w_i x_(i+1)`. -/
def cycleEdge {ℓ : ℕ} (p : Fin 3 × Fin ℓ) : Sym2 (Vertex ℓ) :=
  match p.1 with
  | 0 => s(x p.2, y p.2)
  | 1 => s(y p.2, w p.2)
  | 2 => s(w p.2, x (next ℓ p.2))

def absorberEdges (ℓ : ℕ) : Finset (Sym2 (Vertex ℓ)) :=
  Finset.univ.image absorberEdge

def cycleEdges (ℓ : ℕ) : Finset (Sym2 (Vertex ℓ)) :=
  Finset.univ.image cycleEdge

def absorberGraph (ℓ : ℕ) : SimpleGraph (Vertex ℓ) :=
  SimpleGraph.fromEdgeSet (absorberEdges ℓ : Set (Sym2 (Vertex ℓ)))

def cycleGraph (ℓ : ℕ) : SimpleGraph (Vertex ℓ) :=
  SimpleGraph.fromEdgeSet (cycleEdges ℓ : Set (Sym2 (Vertex ℓ)))

def defaultTriangle {ℓ : ℕ} (p : Fin 3 × Fin ℓ) : Triangle (Vertex ℓ) :=
  match p.1 with
  | 0 => ⟨x (next ℓ p.2), yAux p.2, center, by simp, by simp, by simp⟩
  | 1 => ⟨yAux p.2, xAux p.2, w p.2, by simp, by simp, by simp⟩
  | 2 => ⟨xAux p.2, y p.2, center, by simp, by simp, by simp⟩

def activatedTriangle {ℓ : ℕ} (p : Fin 4 × Fin ℓ) : Triangle (Vertex ℓ) :=
  match p.1 with
  | 0 => ⟨x p.2, y p.2, center, by simp, by simp, by simp⟩
  | 1 => ⟨x (next ℓ p.2), yAux p.2, w p.2, by simp, by simp, by simp⟩
  | 2 => ⟨yAux p.2, xAux p.2, center, by simp, by simp, by simp⟩
  | 3 => ⟨xAux p.2, y p.2, w p.2, by simp, by simp, by simp⟩

theorem absorberEdge_injective (ℓ : ℕ) :
    Function.Injective (@absorberEdge ℓ) := by
  rintro ⟨t, i⟩ ⟨u, j⟩ h
  fin_cases t <;> fin_cases u <;>
    simp [absorberEdge, (next ℓ).injective.eq_iff] at h ⊢ <;>
    exact h

theorem cycleEdge_injective (ℓ : ℕ) :
    Function.Injective (@cycleEdge ℓ) := by
  rintro ⟨t, i⟩ ⟨u, j⟩ h
  fin_cases t <;> fin_cases u <;>
    simp [cycleEdge, (next ℓ).injective.eq_iff] at h ⊢ <;>
    exact h

theorem default_edges_injective (ℓ : ℕ) :
    Function.Injective
      (fun p : (Fin 3 × Fin ℓ) × Fin 3 => (defaultTriangle p.1).edge p.2) := by
  rintro ⟨⟨t, i⟩, s⟩ ⟨⟨u, j⟩, r⟩ h
  fin_cases t <;> fin_cases u <;> fin_cases s <;> fin_cases r <;>
    simp [Triangle.edge, defaultTriangle,
      (next ℓ).injective.eq_iff] at h ⊢ <;> exact h

theorem activated_edges_injective (ℓ : ℕ) :
    Function.Injective
      (fun p : (Fin 4 × Fin ℓ) × Fin 3 => (activatedTriangle p.1).edge p.2) := by
  rintro ⟨⟨t, i⟩, s⟩ ⟨⟨u, j⟩, r⟩ h
  fin_cases t <;> fin_cases u <;> fin_cases s <;> fin_cases r <;>
    simp [Triangle.edge, activatedTriangle,
      (next ℓ).injective.eq_iff] at h ⊢ <;> exact h

theorem absorberEdges_card (ℓ : ℕ) : (absorberEdges ℓ).card = 9 * ℓ := by
  simp [absorberEdges, Finset.card_image_of_injective _ (absorberEdge_injective ℓ)]

theorem cycleEdges_card (ℓ : ℕ) : (cycleEdges ℓ).card = 3 * ℓ := by
  simp [cycleEdges, Finset.card_image_of_injective _ (cycleEdge_injective ℓ)]

theorem absorberEdge_not_diag {ℓ : ℕ} (p : Fin 9 × Fin ℓ) :
    ¬ (absorberEdge p).IsDiag := by
  rcases p with ⟨t, i⟩
  fin_cases t <;> simp [absorberEdge]

theorem cycleEdge_not_diag {ℓ : ℕ} (p : Fin 3 × Fin ℓ) :
    ¬ (cycleEdge p).IsDiag := by
  rcases p with ⟨t, i⟩
  fin_cases t <;> simp [cycleEdge]

@[simp] theorem absorberGraph_edgeSet (ℓ : ℕ) :
    (absorberGraph ℓ).edgeSet = (absorberEdges ℓ : Set (Sym2 (Vertex ℓ))) := by
  apply edgeSet_from_finset
  intro e he
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
  exact absorberEdge_not_diag p

@[simp] theorem cycleGraph_edgeSet (ℓ : ℕ) :
    (cycleGraph ℓ).edgeSet = (cycleEdges ℓ : Set (Sym2 (Vertex ℓ))) := by
  apply edgeSet_from_finset
  intro e he
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
  exact cycleEdge_not_diag p

theorem edge_sets_disjoint (ℓ : ℕ) : Disjoint (absorberEdges ℓ) (cycleEdges ℓ) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  obtain ⟨⟨t, i⟩, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨⟨u, j⟩, _, h⟩ := Finset.mem_image.mp hc
  fin_cases t <;> fin_cases u <;> simp [absorberEdge, cycleEdge] at h

private def defaultEdgeIndex : Fin 3 → Fin 3 → Fin 9
  | 0, 0 => 0
  | 0, 1 => 4
  | 0, 2 => 3
  | 1, 0 => 1
  | 1, 1 => 8
  | 1, 2 => 7
  | 2, 0 => 2
  | 2, 1 => 6
  | 2, 2 => 5

private theorem default_edge_eq {ℓ : ℕ} (t : Fin 3) (i : Fin ℓ) (s : Fin 3) :
    (defaultTriangle (t, i)).edge s = absorberEdge (defaultEdgeIndex t s, i) := by
  fin_cases t <;> fin_cases s <;>
    simp [defaultTriangle, Triangle.edge, absorberEdge, defaultEdgeIndex]

theorem default_triangle_edges (ℓ : ℕ) :
    triangleEdges (@defaultTriangle ℓ) = absorberEdges ℓ := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨⟨⟨t, i⟩, s⟩, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr
      ⟨(defaultEdgeIndex t s, i), Finset.mem_univ _, (default_edge_eq t i s).symm⟩
  · rw [triangleEdges_card _ (default_edges_injective ℓ), absorberEdges_card]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega

private def activatedEdgeIndex {ℓ : ℕ} :
    Fin 4 → Fin ℓ → Fin 3 → (Fin 9 × Fin ℓ) ⊕ (Fin 3 × Fin ℓ)
  | 0, i, 0 => .inr (0, i)
  | 0, i, 1 => .inl (6, i)
  | 0, i, 2 => .inl (3, (next ℓ).symm i)
  | 1, i, 0 => .inl (0, i)
  | 1, i, 1 => .inl (7, i)
  | 1, i, 2 => .inr (2, i)
  | 2, i, 0 => .inl (1, i)
  | 2, i, 1 => .inl (5, i)
  | 2, i, 2 => .inl (4, i)
  | 3, i, 0 => .inl (2, i)
  | 3, i, 1 => .inr (1, i)
  | 3, i, 2 => .inl (8, i)

private theorem activated_edge_eq {ℓ : ℕ} (t : Fin 4) (i : Fin ℓ) (s : Fin 3) :
    (activatedTriangle (t, i)).edge s =
      Sum.elim absorberEdge cycleEdge (activatedEdgeIndex t i s) := by
  fin_cases t <;> fin_cases s <;>
    simp [activatedTriangle, Triangle.edge, absorberEdge, cycleEdge, activatedEdgeIndex]

theorem activated_triangle_edges (ℓ : ℕ) :
    triangleEdges (@activatedTriangle ℓ) = absorberEdges ℓ ∪ cycleEdges ℓ := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨⟨⟨t, i⟩, s⟩, _, rfl⟩ := Finset.mem_image.mp he
    rw [activated_edge_eq]
    cases activatedEdgeIndex t i s with
    | inl p =>
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
    | inr p =>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  · rw [triangleEdges_card _ (activated_edges_injective ℓ),
      Finset.card_union_of_disjoint (edge_sets_disjoint ℓ),
      absorberEdges_card, cycleEdges_card]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega

/-- The first displayed triangle family decomposes the absorber by itself. -/
theorem default_decomposition (ℓ : ℕ) :
    IsTriangleDecomposition (absorberGraph ℓ) (@defaultTriangle ℓ) := by
  refine ⟨default_edges_injective ℓ, ?_⟩
  rw [absorberGraph_edgeSet, default_triangle_edges]

/-- The second displayed family decomposes the absorber together with its cycle. -/
theorem activated_decomposition (ℓ : ℕ) :
    IsTriangleDecomposition (absorberGraph ℓ ⊔ cycleGraph ℓ) (@activatedTriangle ℓ) := by
  refine ⟨activated_edges_injective ℓ, ?_⟩
  rw [SimpleGraph.edgeSet_sup, absorberGraph_edgeSet, cycleGraph_edgeSet,
    activated_triangle_edges, Finset.coe_union]

instance (ℓ : ℕ) : DecidableRel (absorberGraph ℓ).Adj := by
  dsimp [absorberGraph]
  infer_instance

instance (ℓ : ℕ) : DecidableRel (cycleGraph ℓ).Adj := by
  dsimp [cycleGraph]
  infer_instance

@[simp] theorem absorberGraph_edgeFinset (ℓ : ℕ) :
    (absorberGraph ℓ).edgeFinset = absorberEdges ℓ := by
  ext e
  simp [absorberGraph_edgeSet]

@[simp] theorem cycleGraph_edgeFinset (ℓ : ℕ) :
    (cycleGraph ℓ).edgeFinset = cycleEdges ℓ := by
  ext e
  simp [cycleGraph_edgeSet]

theorem absorberGraph_edge_count (ℓ : ℕ) :
    (absorberGraph ℓ).edgeFinset.card = 9 * ℓ := by
  rw [absorberGraph_edgeFinset, absorberEdges_card]

theorem cycleGraph_edge_count (ℓ : ℕ) :
    (cycleGraph ℓ).edgeFinset.card = 3 * ℓ := by
  rw [cycleGraph_edgeFinset, cycleEdges_card]

private def auxiliaryEmbedding (ℓ : ℕ) : ((Fin ℓ ⊕ Fin ℓ) ⊕ Unit) ↪ Vertex ℓ where
  toFun
    | .inl (.inl i) => xAux i
    | .inl (.inr i) => yAux i
    | .inr _ => center
  inj' := by
    rintro (a | a) (b | b) h
    · rcases a with a | a <;> rcases b with b | b <;> simp_all
    · rcases a with a | a <;> cases h
    · rcases b with b | b <;> cases h
    · cases a; cases b; rfl

def auxiliaryVertices (ℓ : ℕ) : Finset (Vertex ℓ) :=
  Finset.univ.map (auxiliaryEmbedding ℓ)

def IsAuxiliary {ℓ : ℕ} : Vertex ℓ → Prop
  | .xAux _ | .yAux _ | .center => True
  | _ => False

@[simp] theorem mem_auxiliaryVertices {ℓ : ℕ} (v : Vertex ℓ) :
    v ∈ auxiliaryVertices ℓ ↔ IsAuxiliary v := by
  cases v <;> simp [auxiliaryVertices, auxiliaryEmbedding, IsAuxiliary]

theorem auxiliaryVertices_card (ℓ : ℕ) : (auxiliaryVertices ℓ).card = 2 * ℓ + 1 := by
  simp [auxiliaryVertices, two_mul]

theorem cycle_vertices {ℓ : ℕ} (v : Vertex ℓ) :
    v ∈ edgeVertices (cycleEdges ℓ) ↔ ¬ IsAuxiliary v := by
  constructor
  · intro hv
    obtain ⟨e, he, hv⟩ := (mem_edgeVertices _ _).mp hv
    obtain ⟨⟨t, i⟩, _, rfl⟩ := Finset.mem_image.mp he
    fin_cases t <;> simp [cycleEdge] at hv <;>
      rcases hv with rfl | rfl <;> simp [IsAuxiliary]
  · intro hv
    cases v with
    | x i =>
      exact (mem_edgeVertices _ _).mpr
        ⟨cycleEdge (0, i), Finset.mem_image.mpr ⟨(0, i), Finset.mem_univ _, rfl⟩,
          by simp [cycleEdge]⟩
    | y i =>
      exact (mem_edgeVertices _ _).mpr
        ⟨cycleEdge (0, i), Finset.mem_image.mpr ⟨(0, i), Finset.mem_univ _, rfl⟩,
          by simp [cycleEdge]⟩
    | w i =>
      exact (mem_edgeVertices _ _).mpr
        ⟨cycleEdge (1, i), Finset.mem_image.mpr ⟨(1, i), Finset.mem_univ _, rfl⟩,
          by simp [cycleEdge]⟩
    | xAux i => simp [IsAuxiliary] at hv
    | yAux i => simp [IsAuxiliary] at hv
    | center => simp [IsAuxiliary] at hv

theorem auxiliary_mem_absorber {ℓ : ℕ} (hℓ : 0 < ℓ) (v : Vertex ℓ)
    (hv : IsAuxiliary v) : v ∈ edgeVertices (absorberEdges ℓ) := by
  cases v with
  | x i => simp [IsAuxiliary] at hv
  | y i => simp [IsAuxiliary] at hv
  | w i => simp [IsAuxiliary] at hv
  | xAux i =>
    exact (mem_edgeVertices _ _).mpr
      ⟨absorberEdge (5, i), Finset.mem_image.mpr ⟨(5, i), Finset.mem_univ _, rfl⟩,
        by simp [absorberEdge]⟩
  | yAux i =>
    exact (mem_edgeVertices _ _).mpr
      ⟨absorberEdge (4, i), Finset.mem_image.mpr ⟨(4, i), Finset.mem_univ _, rfl⟩,
        by simp [absorberEdge]⟩
  | center =>
      let i : Fin ℓ := ⟨0, hℓ⟩
      exact (mem_edgeVertices _ _).mpr
        ⟨absorberEdge (3, i), Finset.mem_image.mpr ⟨(3, i), Finset.mem_univ _, rfl⟩,
          by simp [absorberEdge]⟩

theorem auxiliary_vertices_exact {ℓ : ℕ} (hℓ : 0 < ℓ) :
    edgeVertices (absorberEdges ℓ) \ edgeVertices (cycleEdges ℓ) = auxiliaryVertices ℓ := by
  ext v
  simp only [Finset.mem_sdiff, cycle_vertices, not_not, mem_auxiliaryVertices]
  exact ⟨And.right, fun hv => ⟨auxiliary_mem_absorber hℓ v hv, hv⟩⟩

theorem auxiliary_vertex_count {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (edgeVertices (absorberEdges ℓ) \ edgeVertices (cycleEdges ℓ)).card = 2 * ℓ + 1 := by
  rw [auxiliary_vertices_exact hℓ, auxiliaryVertices_card]

theorem every_edge_has_auxiliary_endpoint {ℓ : ℕ} {e : Sym2 (Vertex ℓ)}
    (he : e ∈ absorberEdges ℓ) : ∃ v ∈ e, v ∈ auxiliaryVertices ℓ := by
  obtain ⟨⟨t, i⟩, _, rfl⟩ := Finset.mem_image.mp he
  fin_cases t
  · exact ⟨yAux i, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨yAux i, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨xAux i, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨center, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨center, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨center, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨center, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨yAux i, by simp [absorberEdge], by simp [IsAuxiliary]⟩
  · exact ⟨xAux i, by simp [absorberEdge], by simp [IsAuxiliary]⟩

theorem every_edge_meets_outside_cycle {ℓ : ℕ} {e : Sym2 (Vertex ℓ)}
    (he : e ∈ (absorberGraph ℓ).edgeSet) :
    ∃ v ∈ e, v ∉ (cycleGraph ℓ).support := by
  rw [absorberGraph_edgeSet] at he
  obtain ⟨v, hve, hv⟩ := every_edge_has_auxiliary_endpoint he
  refine ⟨v, hve, ?_⟩
  rw [← edgeVertices_eq_support (cycleGraph ℓ) (cycleEdges ℓ) (cycleGraph_edgeSet ℓ)]
  change v ∉ edgeVertices (cycleEdges ℓ)
  rw [cycle_vertices]
  exact not_not.mpr ((mem_auxiliaryVertices v).mp hv)

/-- The count refers to actual nonisolated vertices of the two graphs. -/
theorem auxiliary_support_count {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ((absorberGraph ℓ).support \ (cycleGraph ℓ).support).ncard = 2 * ℓ + 1 := by
  rw [← edgeVertices_eq_support (absorberGraph ℓ) (absorberEdges ℓ)
      (absorberGraph_edgeSet ℓ),
    ← edgeVertices_eq_support (cycleGraph ℓ) (cycleEdges ℓ) (cycleGraph_edgeSet ℓ),
    ← Finset.coe_sdiff, Set.ncard_coe_finset, auxiliary_vertex_count hℓ]

private theorem map_sup_eq {V W : Type*} (f : V ↪ W) (G H : SimpleGraph V) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  apply SimpleGraph.edgeSet_inj.mp
  simp only [SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_sup, Set.image_union]

theorem embedded_default_decomposition {V : Type*} [DecidableEq V]
    (ℓ : ℕ) (f : Vertex ℓ ↪ V) :
    IsTriangleDecomposition ((absorberGraph ℓ).map f)
      (fun i => (defaultTriangle i).map f) :=
  (default_decomposition ℓ).map f

theorem embedded_activated_decomposition {V : Type*} [DecidableEq V]
    (ℓ : ℕ) (f : Vertex ℓ ↪ V) :
    IsTriangleDecomposition ((absorberGraph ℓ).map f ⊔ (cycleGraph ℓ).map f)
      (fun i => (activatedTriangle i).map f) := by
  rw [← map_sup_eq]
  exact (activated_decomposition ℓ).map f

theorem embedded_edge_disjoint {V : Type*} (ℓ : ℕ) (f : Vertex ℓ ↪ V) :
    Disjoint ((absorberGraph ℓ).map f).edgeSet ((cycleGraph ℓ).map f).edgeSet := by
  rw [SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map]
  apply Set.disjoint_image_of_injective f.sym2Map.injective
  rw [absorberGraph_edgeSet, cycleGraph_edgeSet]
  exact_mod_cast edge_sets_disjoint ℓ

theorem embedded_edge_count {V : Type*} (ℓ : ℕ) (f : Vertex ℓ ↪ V) :
    ((absorberGraph ℓ).map f).edgeSet.ncard = 9 * ℓ := by
  rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ f.sym2Map.injective,
    absorberGraph_edgeSet, Set.ncard_coe_finset, absorberEdges_card]

theorem embedded_auxiliary_support_count {V : Type*} {ℓ : ℕ}
    (hℓ : 0 < ℓ) (f : Vertex ℓ ↪ V) :
    (((absorberGraph ℓ).map f).support \ ((cycleGraph ℓ).map f).support).ncard =
      2 * ℓ + 1 := by
  rw [SimpleGraph.support_map, SimpleGraph.support_map, ← Set.image_diff f.injective,
    Set.ncard_image_of_injective _ f.injective, auxiliary_support_count hℓ]

theorem embedded_edge_meets_outside_cycle {V : Type*} {ℓ : ℕ}
    (f : Vertex ℓ ↪ V) {e : Sym2 V}
    (he : e ∈ ((absorberGraph ℓ).map f).edgeSet) :
    ∃ v ∈ e, v ∉ ((cycleGraph ℓ).map f).support := by
  rw [SimpleGraph.edgeSet_map] at he
  obtain ⟨e, he, rfl⟩ := he
  obtain ⟨v, hve, hv⟩ := every_edge_meets_outside_cycle he
  refine ⟨f v, Sym2.mem_map.mpr ⟨v, hve, rfl⟩, ?_⟩
  rw [SimpleGraph.support_map]
  rintro ⟨u, hu, huv⟩
  exact hv (f.injective huv ▸ hu)

/-- Host-graph form of the manuscript's cycle absorber lemma.

The embedding expresses that all tagged cycle and auxiliary vertices are
distinct. The only host hypothesis asks for the explicitly listed cycle
and absorber edges to be present. No triangle decomposition is assumed.
The two resulting graphs are actual subgraphs of the given host `G`.
-/
theorem in_host {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (f : Vertex ℓ ↪ V)
    (hedges : ∀ e ∈ absorberEdges ℓ ∪ cycleEdges ℓ, Sym2.map f e ∈ G.edgeSet) :
    let H := (absorberGraph ℓ).map f
    let C := (cycleGraph ℓ).map f
    H ≤ G ∧ C ≤ G ∧
    Disjoint H.edgeSet C.edgeSet ∧
    IsTriangleDecomposition H (fun i => (defaultTriangle i).map f) ∧
    IsTriangleDecomposition (H ⊔ C) (fun i => (activatedTriangle i).map f) ∧
    H.edgeSet.ncard = 9 * ℓ ∧
    (H.support \ C.support).ncard = 2 * ℓ + 1 ∧
    (∀ e ∈ H.edgeSet, ∃ v ∈ e, v ∉ C.support) := by
  dsimp only
  refine ⟨?_, ?_, embedded_edge_disjoint ℓ f, embedded_default_decomposition ℓ f,
    embedded_activated_decomposition ℓ f, embedded_edge_count ℓ f,
    embedded_auxiliary_support_count hℓ f, ?_⟩
  · apply SimpleGraph.edgeSet_subset_edgeSet.mp
    intro e he
    rw [SimpleGraph.edgeSet_map, absorberGraph_edgeSet] at he
    obtain ⟨e, he, rfl⟩ := he
    exact hedges e (Finset.mem_union_left _ he)
  · apply SimpleGraph.edgeSet_subset_edgeSet.mp
    intro e he
    rw [SimpleGraph.edgeSet_map, cycleGraph_edgeSet] at he
    obtain ⟨e, he, rfl⟩ := he
    exact hedges e (Finset.mem_union_right _ he)
  · intro e he
    exact embedded_edge_meets_outside_cycle f he

end CycleAbsorber
end Overfull.Dense
