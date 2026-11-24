import Overfull.Dense.FiniteAbsorberCycles
import Overfull.Dense.TripartiteTriangleBridge

/-!
# Enumerating all finite balanced remainders

Every remainder is an actual subset of the host edges inside the specified
vertex set. Its cycles are obtained from local balance. The finite enumeration
keeps separate copies of a cycle when different remainders contain it.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph
open scoped BigOperators

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

noncomputable def internalEdges (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    Finset (EdgePosition (A := A) (B := B) (W := W)) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ edgePair e, v ∈ U)

@[simp] theorem mem_internalEdges
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    (e : EdgePosition (A := A) (B := B) (W := W)) :
    e ∈ internalEdges G U ↔ G.IsEdge e ∧ ∀ v ∈ edgePair e, v ∈ U := by
  simp [internalEdges]

theorem internalEdges_subset
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    internalEdges G U ⊆ G.edgeFinset := Finset.filter_subset _ _

omit [Fintype A] [Fintype B] [Fintype W] in
def edgeGraph (E : Finset (EdgePosition (A := A) (B := B) (W := W))) :
    TripartiteGraph A B W where
  ab a b := abPos a b ∈ E
  aw a w := awPos a w ∈ E
  bw b w := bwPos b w ∈ E

@[simp] theorem edgeGraph_edgeFinset
    (E : Finset (EdgePosition (A := A) (B := B) (W := W))) :
    (edgeGraph E).edgeFinset = E := by
  ext e
  rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩ <;>
    simp [TripartiteGraph.edgeFinset,IsEdge,edgeGraph,abPos,awPos,bwPos]

private def orderedEnds : EdgePosition (A := A) (B := B) (W := W) →
    HostVertex (A := A) (B := B) (W := W) × HostVertex (A := A) (B := B) (W := W)
  | .inl (a,b) => (.inl a,.inr (.inl b))
  | .inr (.inl (a,w)) => (.inl a,.inr (.inr w))
  | .inr (.inr (b,w)) => (.inr (.inl b),.inr (.inr w))

omit [Fintype A] [Fintype B] [Fintype W] in
private theorem orderedEnds_injective :
    Function.Injective (orderedEnds (A := A) (B := B) (W := W)) := by
  rintro (⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩) (⟨a',b'⟩ | ⟨a',w'⟩ | ⟨b',w'⟩) h <;>
    simp only [orderedEnds,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,and_false] at h <;>
    first | contradiction | rcases h with ⟨rfl,rfl⟩; rfl

theorem internalEdges_card_le
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    (internalEdges G U).card ≤ U.card ^ 2 := by
  have hcard : (internalEdges G U).card ≤ (U ×ˢ U).card := by
    apply Finset.card_le_card_of_injOn orderedEnds
    · intro e he
      have hU := ((mem_internalEdges G U e).mp he).2
      apply Finset.mem_product.mpr
      rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩ <;>
        simp only [orderedEnds] <;>
        exact ⟨hU _ (by simp [edgePair]),hU _ (by simp [edgePair])⟩
    · exact orderedEnds_injective.injOn
  simpa [Finset.card_product,pow_two] using hcard

noncomputable def remainders
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    Finset (Finset (EdgePosition (A := A) (B := B) (W := W))) :=
  (internalEdges G U).powerset.filter (fun E => (edgeGraph E).IsLocallyBalanced)

@[simp] theorem mem_remainders
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    (E : Finset (EdgePosition (A := A) (B := B) (W := W))) :
    E ∈ remainders G U ↔ E ⊆ internalEdges G U ∧ (edgeGraph E).IsLocallyBalanced := by
  simp [remainders]

theorem remainders_card_le
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    (remainders G U).card ≤ 2 ^ (U.card ^ 2) := by
  calc
    _ ≤ ((internalEdges G U).powerset).card := Finset.card_filter_le _ _
    _ = 2 ^ (internalEdges G U).card := Finset.card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (internalEdges_card_le G U)

theorem remainder_card_le
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    {E : Finset (EdgePosition (A := A) (B := B) (W := W))}
    (hE : E ∈ remainders G U) : E.card ≤ U.card ^ 2 :=
  (Finset.card_le_card ((mem_remainders G U E).mp hE).1).trans
    (internalEdges_card_le G U)

/-- A finite list of all cycles, tagged by the remainder they partition. -/
structure RemainderCycles
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) where
  count : ℕ
  length : Fin count → ℕ
  cycle : ∀ i, Cycle G (length i)
  positive : ∀ i, 0 < length i
  xInside : ∀ i j, Sum.inl ((cycle i).x j) ∈ U
  yInside : ∀ i j, Sum.inr (Sum.inl ((cycle i).y j)) ∈ U
  wInside : ∀ i j, Sum.inr (Sum.inr ((cycle i).w j)) ∈ U
  small : ∀ i, 3 * length i ≤ U.card
  tag : Fin count → Finset (EdgePosition (A := A) (B := B) (W := W))
  sameTagDisjoint : ∀ i j, i ≠ j → tag i = tag j →
    Disjoint ((cycle i).graph G).edgeFinset ((cycle j).graph G).edgeFinset
  cover : ∀ E, E ⊆ internalEdges G U → (edgeGraph E).IsLocallyBalanced →
    (univ.filter (fun i => tag i = E)).biUnion
      (fun i => ((cycle i).graph G).edgeFinset) = E
  budget : ∑ i, 3 * length i ≤ U.card ^ 2 * 2 ^ (U.card ^ 2)

variable {G}

theorem Cycle.vertices_inside {ℓ : ℕ} (C : Cycle G ℓ)
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hC : (C.graph G).edgeFinset ⊆ internalEdges G U) :
    (∀ j, Sum.inl (C.x j) ∈ U) ∧
    (∀ j, Sum.inr (Sum.inl (C.y j)) ∈ U) ∧
    (∀ j, Sum.inr (Sum.inr (C.w j)) ∈ U) := by
  have hab (j : Fin ℓ) : abPos (C.x j) (C.y j) ∈ (C.graph G).edgeFinset := by
    apply ((C.graph G).mem_edgeFinset _).mpr
    exact ⟨j,rfl,rfl⟩
  have hbw (j : Fin ℓ) : bwPos (C.y j) (C.w j) ∈ (C.graph G).edgeFinset := by
    apply ((C.graph G).mem_edgeFinset _).mpr
    exact ⟨j,rfl,rfl⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ((mem_internalEdges G U _).mp (hC (hab j))).2 _ (by simp [edgePair,abPos])
  · intro j
    exact ((mem_internalEdges G U _).mp (hC (hab j))).2 _ (by simp [edgePair,abPos])
  · intro j
    exact ((mem_internalEdges G U _).mp (hC (hbw j))).2 _ (by simp [edgePair,bwPos])

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Cycle.length_le_card {ℓ : ℕ} (C : Cycle G ℓ)
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hx : ∀ j, Sum.inl (C.x j) ∈ U)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ U)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ U) :
    3 * ℓ ≤ U.card := by
  let f : (Fin ℓ ⊕ Fin ℓ ⊕ Fin ℓ) → {v // v ∈ U}
    | .inl j => ⟨.inl (C.x j),hx j⟩
    | .inr (.inl j) => ⟨.inr (.inl (C.y j)),hy j⟩
    | .inr (.inr j) => ⟨.inr (.inr (C.w j)),hw j⟩
  have hf : Function.Injective f := by
    rintro (i | i | i) (j | j | j) h <;>
      have hh := congrArg Subtype.val h <;> simp only [f] at hh
    all_goals first
      | cases hh
      | exact congrArg Sum.inl (C.x.injective (Sum.inl_injective hh))
      | exact congrArg (Sum.inr ∘ Sum.inl)
          (C.y.injective (Sum.inl_injective (Sum.inr_injective hh)))
      | exact congrArg (Sum.inr ∘ Sum.inr)
          (C.w.injective (Sum.inr_injective (Sum.inr_injective hh)))
  have h := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sum,Fintype.card_coe,show ℓ+ (ℓ+ℓ) = 3*ℓ by omega] using h

variable (G)

abbrev Remainder (U : Finset (HostVertex (A := A) (B := B) (W := W))) :=
  {E // E ∈ remainders G U}

noncomputable def remainderPartition
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) (E : Remainder G U) :
    CyclePartition (edgeGraph E.val) :=
  Classical.choice (cyclePartition_exists (edgeGraph E.val)
    ((mem_remainders G U E.val).mp E.property).2)

noncomputable def remainderCycle
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) (E : Remainder G U)
    (i : Fin (remainderPartition G U E).count) :
    Cycle G ((remainderPartition G U E).length i) :=
  ((remainderPartition G U E).cycle i).lift G (by
    rw [edgeGraph_edgeFinset]
    exact (((mem_remainders G U E.val).mp E.property).1).trans
      (internalEdges_subset G U))

@[simp] theorem remainderCycle_graph
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) (E : Remainder G U)
    (i : Fin (remainderPartition G U E).count) :
    (remainderCycle G U E i).graph G =
      ((remainderPartition G U E).cycle i).graph (edgeGraph E.val) := rfl

theorem remainderCycle_subset
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) (E : Remainder G U)
    (i : Fin (remainderPartition G U E).count) :
    ((remainderCycle G U E i).graph G).edgeFinset ⊆ E.val := by
  rw [remainderCycle_graph]
  simpa only [edgeGraph_edgeFinset] using
    ((remainderPartition G U E).cycle i).edgeFinset_subset (edgeGraph E.val)

/-- Enumerate all actual balanced remainders and all their cycles at once.
The construction proves its cardinal budget, rather than assuming a
bounded family of cycle decompositions. -/
theorem remainderCycles_exists
    (U : Finset (HostVertex (A := A) (B := B) (W := W))) :
    Nonempty (RemainderCycles G U) := by
  classical
  let P := remainderPartition G U
  let I := (E : Remainder G U) × Fin (P E).count
  let C (i : I) := remainderCycle G U i.1 i.2
  let f : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hinside (i : I) := (C i).vertices_inside U
    ((remainderCycle_subset G U i.1 i.2).trans
      ((mem_remainders G U i.1.val).mp i.1.property).1)
  have hdis : ∀ i j : I, i ≠ j → i.1.val = j.1.val →
      Disjoint ((C i).graph G).edgeFinset ((C j).graph G).edgeFinset := by
    rintro ⟨E,i⟩ ⟨F,j⟩ hne htag
    have hEF : E = F := Subtype.ext htag
    subst F
    have hij : i ≠ j := by intro h; subst j; exact hne rfl
    exact (P E).disjoint hij
  have hcover (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
      (hE : E ⊆ internalEdges G U) (hb : (edgeGraph E).IsLocallyBalanced) :
      (univ.filter (fun i : I => i.1.val = E)).biUnion
        (fun i => ((C i).graph G).edgeFinset) = E := by
    let r : Remainder G U := ⟨E,(mem_remainders G U E).mpr ⟨hE,hb⟩⟩
    ext e
    constructor
    · intro he
      obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he
      have hei := remainderCycle_subset G U i.1 i.2 he
      rwa [(Finset.mem_filter.mp hi).2] at hei
    · intro he
      have he' : e ∈ (edgeGraph r.val).edgeFinset := by
        rw [edgeGraph_edgeFinset]
        exact he
      rw [← (P r).cover] at he'
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he'
      exact Finset.mem_biUnion.mpr ⟨⟨r,i⟩,by simp [r],hi⟩
  have hsum : (∑ i : I, 3 * (P i.1).length i.2) ≤ U.card ^ 2 * 2 ^ (U.card ^ 2) := by
    calc
      _ = ∑ E : Remainder G U, E.val.card := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro E _
        rw [(P E).sum,edgeGraph_edgeFinset]
      _ ≤ ∑ _E : Remainder G U, U.card ^ 2 :=
        Finset.sum_le_sum (fun E _ => remainder_card_le G U E.property)
      _ = (remainders G U).card * U.card ^ 2 := by simp
      _ ≤ _ := by
        calc
          _ ≤ 2 ^ (U.card ^ 2) * U.card ^ 2 :=
            Nat.mul_le_mul_right _ (remainders_card_le G U)
          _ = _ := Nat.mul_comm _ _
  refine ⟨{
    count := Fintype.card I
    length := fun i => (P (f i).1).length (f i).2
    cycle := fun i => C (f i)
    positive := fun i => (P (f i).1).positive (f i).2
    xInside := fun i => (hinside (f i)).1
    yInside := fun i => (hinside (f i)).2.1
    wInside := fun i => (hinside (f i)).2.2
    small := fun i => (C (f i)).length_le_card U
      (hinside (f i)).1 (hinside (f i)).2.1 (hinside (f i)).2.2
    tag := fun i => (f i).1.val
    sameTagDisjoint := fun i j hij htag => hdis _ _ (fun h => hij (f.injective h)) htag
    cover := ?_
    budget := ?_ }⟩
  · intro E hE hb
    calc
      _ = (univ.filter (fun i : I => i.1.val = E)).biUnion
          (fun i => ((C i).graph G).edgeFinset) := by
        ext e
        simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · rintro ⟨i,hi,he⟩
          exact ⟨f i,hi,he⟩
        · rintro ⟨i,hi,he⟩
          refine ⟨f.symm i,?_,?_⟩
          · simpa only [f.apply_symm_apply] using hi
          · exact (congrArg (fun j : I => e ∈ ((C j).graph G).edgeFinset)
              (f.apply_symm_apply i)).mpr he
      _ = E := hcover E hE hb
  · rw [f.sum_comp (fun i : I => 3 * (P i.1).length i.2)]
    exact hsum

theorem RemainderCycles.budget_of_card_le
    {U : Finset (HostVertex (A := A) (B := B) (W := W))}
    (R : RemainderCycles G U) {h : ℕ} (hU : U.card ≤ h) :
    ∑ i, 3 * R.length i ≤ h ^ 2 * 2 ^ (h ^ 2) := by
  have hs : U.card ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left hU 2
  exact R.budget.trans (Nat.mul_le_mul hs (Nat.pow_le_pow_right (by decide) hs))

end Overfull.Dense.FiniteAbsorber
