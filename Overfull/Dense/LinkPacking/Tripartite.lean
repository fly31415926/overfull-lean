import Overfull.Dense.TripartiteGraph

/-!
# Exact tripartite geometry for link packing

The three parts are actual finite subsets of the disjoint-union vertex type.
A finite set omitting one part has two canonical local sides. Its induced
degrees are exactly the neighbor counts in the opposite local side.
-/

noncomputable section

namespace Overfull.DenseLinkPacking.TripartiteGeometry

open Finset Classical SimpleGraph

variable {A B W : Type*}

/-- The label of a vertex in the disjoint union of the three host parts. -/
def partIndex : A ⊕ B ⊕ W → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

variable [Fintype A] [Fintype B] [Fintype W]

/-- The actual vertex set of one of the three host parts. -/
def part (j : Fin 3) : Finset (A ⊕ B ⊕ W) :=
  univ.filter (fun v => partIndex v = j)

@[simp] theorem mem_part (v : A ⊕ B ⊕ W) (j : Fin 3) :
    v ∈ part j ↔ partIndex v = j := by
  simp [part]

theorem parts_pairwise_disjoint :
    Pairwise (fun i j : Fin 3 =>
      Disjoint (part (A := A) (B := B) (W := W) i) (part j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact hij (((mem_part v i).mp hvi).symm.trans ((mem_part v j).mp hvj))

theorem parts_cover :
    univ.biUnion (part (A := A) (B := B) (W := W)) = univ := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact ⟨partIndex v, (mem_part v _).mpr rfl⟩

@[simp] theorem card_part_zero :
    (part (A := A) (B := B) (W := W) 0).card = Fintype.card A := by
  have h : part (A := A) (B := B) (W := W) 0 =
      (univ : Finset A).image (Sum.inl : A → A ⊕ B ⊕ W) := by
    ext v
    rcases v with a | b | w <;> simp [part, partIndex]
  rw [h, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ]

@[simp] theorem card_part_one :
    (part (A := A) (B := B) (W := W) 1).card = Fintype.card B := by
  let f : B → A ⊕ B ⊕ W := fun b => .inr (.inl b)
  have hf : Function.Injective f := by
    intro b c h
    exact Sum.inl_injective (Sum.inr_injective h)
  have h : part (A := A) (B := B) (W := W) 1 =
      (univ : Finset B).image f := by
    ext v
    rcases v with a | b | w <;> simp [part, partIndex, f]
  rw [h, Finset.card_image_of_injective _ hf, Finset.card_univ]

@[simp] theorem card_part_two :
    (part (A := A) (B := B) (W := W) 2).card = Fintype.card W := by
  let f : W → A ⊕ B ⊕ W := fun w => .inr (.inr w)
  have hf : Function.Injective f := by
    intro w z h
    exact Sum.inr_injective (Sum.inr_injective h)
  have h : part (A := A) (B := B) (W := W) 2 =
      (univ : Finset W).image f := by
    ext v
    rcases v with a | b | w <;> simp [part, partIndex, f]
  rw [h, Finset.card_image_of_injective _ hf, Finset.card_univ]

theorem card_part (n : ℕ) (hA : Fintype.card A = n)
    (hB : Fintype.card B = n) (hW : Fintype.card W = n) (j : Fin 3) :
    (part (A := A) (B := B) (W := W) j).card = n := by
  fin_cases j <;> simp [hA, hB, hW]

theorem card_vertices (n : ℕ) (hA : Fintype.card A = n)
    (hB : Fintype.card B = n) (hW : Fintype.card W = n) :
    Fintype.card (A ⊕ B ⊕ W) = 3 * n := by
  simp only [Fintype.card_sum, hA, hB, hW]
  omega

/-- The host graph has no edges within any of its actual parts. -/
theorem not_adj_of_mem_part (G : TripartiteGraph A B W) (j : Fin 3)
    {v w : A ⊕ B ⊕ W} (hv : v ∈ part j) (hw : w ∈ part j) :
    ¬ G.toSimpleGraph.Adj v w := by
  have hindex : partIndex v = partIndex w :=
    ((mem_part v j).mp hv).trans ((mem_part w j).mp hw).symm
  clear hv hw
  rcases v with a | b | c
  all_goals rcases w with a' | b' | w'
  all_goals simp_all [partIndex, TripartiteGraph.toSimpleGraph]

/-- The first retained part when the indicated part is omitted. -/
def leftIndex (omitted : Fin 3) : Fin 3 := if omitted = 0 then 1 else 0

/-- The second retained part when the indicated part is omitted. -/
def rightIndex (omitted : Fin 3) : Fin 3 := if omitted = 2 then 1 else 2

@[simp] theorem leftIndex_ne_omitted (omitted : Fin 3) :
    leftIndex omitted ≠ omitted := by
  fin_cases omitted <;> decide

@[simp] theorem rightIndex_ne_omitted (omitted : Fin 3) :
    rightIndex omitted ≠ omitted := by
  fin_cases omitted <;> decide

theorem leftIndex_ne_rightIndex (omitted : Fin 3) :
    leftIndex omitted ≠ rightIndex omitted := by
  fin_cases omitted <;> decide

theorem index_cases (omitted j : Fin 3) :
    j = omitted ∨ j = leftIndex omitted ∨ j = rightIndex omitted := by
  fin_cases omitted <;> fin_cases j <;> decide

def localLeft (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3) :
    Finset (A ⊕ B ⊕ W) := Y ∩ part (leftIndex omitted)

def localRight (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3) :
    Finset (A ⊕ B ⊕ W) := Y ∩ part (rightIndex omitted)

theorem local_disjoint (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3) :
    Disjoint (localLeft Y omitted) (localRight Y omitted) := by
  apply Finset.disjoint_left.mpr
  intro v hvL hvR
  exact Finset.disjoint_left.mp
    (parts_pairwise_disjoint (leftIndex_ne_rightIndex omitted))
    (Finset.mem_inter.mp hvL).2 (Finset.mem_inter.mp hvR).2

theorem local_union (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3)
    (homit : Y ∩ part omitted = ∅) :
    localLeft Y omitted ∪ localRight Y omitted = Y := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_inter.mp hv).1
    · exact (Finset.mem_inter.mp hv).1
  · intro v hv
    rcases index_cases omitted (partIndex v) with ho | hL | hR
    · have hbad : v ∈ Y ∩ part omitted :=
        Finset.mem_inter.mpr ⟨hv, (mem_part v _).mpr ho⟩
      rw [homit] at hbad
      exact False.elim (Finset.notMem_empty v hbad)
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨hv, (mem_part v _).mpr hL⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hv, (mem_part v _).mpr hR⟩)

theorem neighbors_local_left (G : TripartiteGraph A B W)
    (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3)
    (homit : Y ∩ part omitted = ∅) {v : A ⊕ B ⊕ W}
    (hv : v ∈ localLeft Y omitted) :
    G.toSimpleGraph.neighborFinset v ∩ Y =
      G.toSimpleGraph.neighborFinset v ∩ localRight Y omitted := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hadj, hw⟩
    have hu : w ∈ localLeft Y omitted ∪ localRight Y omitted := by
      rw [local_union Y omitted homit]
      exact hw
    rcases Finset.mem_union.mp hu with hwL | hwR
    · exact False.elim ((not_adj_of_mem_part G (leftIndex omitted)
        (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hwL).2) hadj)
    · exact ⟨hadj, hwR⟩
  · rintro ⟨hadj, hw⟩
    exact ⟨hadj, (Finset.mem_inter.mp hw).1⟩

theorem neighbors_local_right (G : TripartiteGraph A B W)
    (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3)
    (homit : Y ∩ part omitted = ∅) {v : A ⊕ B ⊕ W}
    (hv : v ∈ localRight Y omitted) :
    G.toSimpleGraph.neighborFinset v ∩ Y =
      G.toSimpleGraph.neighborFinset v ∩ localLeft Y omitted := by
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hadj, hw⟩
    have hu : w ∈ localLeft Y omitted ∪ localRight Y omitted := by
      rw [local_union Y omitted homit]
      exact hw
    rcases Finset.mem_union.mp hu with hwL | hwR
    · exact ⟨hadj, hwL⟩
    · exact False.elim ((not_adj_of_mem_part G (rightIndex omitted)
        (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hwR).2) hadj)
  · rintro ⟨hadj, hw⟩
    exact ⟨hadj, (Finset.mem_inter.mp hw).1⟩

/-- Exact local sides and neighborhood identities for an omitted-part set. -/
structure LocalSides (G : TripartiteGraph A B W)
    (Y : Finset (A ⊕ B ⊕ W)) (s : ℕ) where
  left : Finset (A ⊕ B ⊕ W)
  right : Finset (A ⊕ B ⊕ W)
  left_subset : left ⊆ Y
  right_subset : right ⊆ Y
  disjoint : Disjoint left right
  union_eq : left ∪ right = Y
  left_card : left.card = s
  right_card : right.card = s
  left_neighbors : ∀ v ∈ left,
    G.toSimpleGraph.neighborFinset v ∩ Y = G.toSimpleGraph.neighborFinset v ∩ right
  right_neighbors : ∀ v ∈ right,
    G.toSimpleGraph.neighborFinset v ∩ Y = G.toSimpleGraph.neighborFinset v ∩ left

/-- Construct balanced local sides directly from the three actual part counts. -/
def localSides (G : TripartiteGraph A B W)
    (Y : Finset (A ⊕ B ⊕ W)) (omitted : Fin 3) (s : ℕ)
    (hcounts : ∀ j, (Y ∩ part j).card = if j = omitted then 0 else s) :
    LocalSides G Y s := by
  have homit : Y ∩ part omitted = ∅ :=
    Finset.card_eq_zero.mp (by simpa using hcounts omitted)
  refine {
    left := localLeft Y omitted
    right := localRight Y omitted
    left_subset := Finset.inter_subset_left
    right_subset := Finset.inter_subset_left
    disjoint := local_disjoint Y omitted
    union_eq := local_union Y omitted homit
    left_card := ?_
    right_card := ?_
    left_neighbors := fun v hv => neighbors_local_left G Y omitted homit hv
    right_neighbors := fun v hv => neighbors_local_right G Y omitted homit hv }
  · simpa [localLeft] using hcounts (leftIndex omitted)
  · simpa [localRight] using hcounts (rightIndex omitted)

/-- An induced degree is the cardinality of the actual ambient neighbor set
restricted to the inducing finite set. -/
theorem induced_degree_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (Y : Finset V) (v : Y) :
    (H.induce (↑Y : Set V)).degree v = (H.neighborFinset v.val ∩ Y).card := by
  have hmap : ((H.induce (↑Y : Set V)).neighborFinset v).map
      (Function.Embedding.subtype (fun x => x ∈ Y)) =
      H.neighborFinset v.val ∩ Y := by
    ext w
    simp only [Finset.mem_map, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      change x.val = w at hxeq
      subst w
      exact ⟨hx, x.property⟩
    · rintro ⟨hadj, hw⟩
      exact ⟨⟨w, hw⟩, hadj, rfl⟩
  simpa using congrArg Finset.card hmap

theorem LocalSides.card_Y {G : TripartiteGraph A B W}
    {Y : Finset (A ⊕ B ⊕ W)} {s : ℕ} (D : LocalSides G Y s) :
    Y.card = 2 * s := by
  rw [← D.union_eq, Finset.card_union_of_disjoint D.disjoint,
    D.left_card, D.right_card]
  omega

theorem LocalSides.degree_left {G : TripartiteGraph A B W}
    {Y : Finset (A ⊕ B ⊕ W)} {s : ℕ} (D : LocalSides G Y s)
    (v : A ⊕ B ⊕ W) (hv : v ∈ D.left) :
    (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).degree
      ⟨v, D.left_subset hv⟩ =
      (G.toSimpleGraph.neighborFinset v ∩ D.right).card := by
  rw [induced_degree_eq]
  exact congrArg Finset.card (D.left_neighbors v hv)

theorem LocalSides.degree_right {G : TripartiteGraph A B W}
    {Y : Finset (A ⊕ B ⊕ W)} {s : ℕ} (D : LocalSides G Y s)
    (v : A ⊕ B ⊕ W) (hv : v ∈ D.right) :
    (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).degree
      ⟨v, D.right_subset hv⟩ =
      (G.toSimpleGraph.neighborFinset v ∩ D.left).card := by
  rw [induced_degree_eq]
  exact congrArg Finset.card (D.right_neighbors v hv)

theorem LocalSides.minDegree_le_left {G : TripartiteGraph A B W}
    {Y : Finset (A ⊕ B ⊕ W)} {s : ℕ} (D : LocalSides G Y s)
    (v : A ⊕ B ⊕ W) (hv : v ∈ D.left) :
    (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).minDegree ≤
      (G.toSimpleGraph.neighborFinset v ∩ D.right).card := by
  have h := (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).minDegree_le_degree
    ⟨v, D.left_subset hv⟩
  rwa [D.degree_left v hv] at h

theorem LocalSides.minDegree_le_right {G : TripartiteGraph A B W}
    {Y : Finset (A ⊕ B ⊕ W)} {s : ℕ} (D : LocalSides G Y s)
    (v : A ⊕ B ⊕ W) (hv : v ∈ D.right) :
    (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).minDegree ≤
      (G.toSimpleGraph.neighborFinset v ∩ D.left).card := by
  have h := (G.toSimpleGraph.induce (↑Y : Set (A ⊕ B ⊕ W))).minDegree_le_degree
    ⟨v, D.right_subset hv⟩
  rwa [D.degree_right v hv] at h

end Overfull.DenseLinkPacking.TripartiteGeometry
