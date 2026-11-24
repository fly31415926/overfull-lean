import Overfull.Dense.FiniteAbsorberEmbedding
import Overfull.Dense.TriangleDecomposition
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Directed cycles in locally balanced tripartite graphs

The cyclic orientation is from A to B, from B to W, and from W to A.
All cycles below use actual graph edges.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

private theorem exists_positive_period {V : Type*} [Finite V] (f : V → V) (v : V) :
    ∃ x, 0 < Function.minimalPeriod f x := by
  obtain ⟨m,n,heq,hne⟩ : ∃ m n, f^[m] v = f^[n] v ∧ m ≠ n := by
    simpa [Function.Injective] using not_injective_infinite_finite (f^[·] v)
  have hrep {m n : ℕ} (hlt : m < n) (he : f^[m] v = f^[n] v) :
      ∃ x, 0 < Function.minimalPeriod f x := by
    refine ⟨f^[m] v, Function.IsPeriodicPt.minimalPeriod_pos (n := n-m) (by omega) ?_⟩
    change f^[n-m] (f^[m] v) = f^[m] v
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact he.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hrep hlt heq
  · exact hrep hlt heq.symm

/-- A finite nonempty functional digraph contains a simple directed cycle. -/
theorem exists_cyclic_orbit {V : Type*} [Finite V] (f : V → V) (v : V) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ x : Fin ℓ ↪ V,
      ∀ j, f (x j) = x (CycleAbsorber.next ℓ j) := by
  obtain ⟨z,hz⟩ := exists_positive_period f v
  let ℓ := Function.minimalPeriod f z
  have hℓ : 0 < ℓ := hz
  let x : Fin ℓ ↪ V := ⟨fun j => f^[j.val] z, by
    intro i j h
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h⟩
  refine ⟨ℓ,hℓ,x,?_⟩
  intro j
  change f (f^[j.val] z) = f^[(CycleAbsorber.next ℓ j).val] z
  have hmod := Function.iterate_mod_minimalPeriod_eq (f := f) (x := z)
    (n := j.val+1)
  have hrot' (n : ℕ) (hn : 0 < n) (i : Fin n) :
      (CycleAbsorber.next n i).val = (i.val+1)%n := by
    cases n with
    | zero => omega
    | succ n => simp [CycleAbsorber.next,finRotate_succ_apply,Fin.val_add,
        Nat.add_mod]
  have hrot := hrot' ℓ hℓ j
  rw [hrot]
  exact (Function.iterate_succ_apply' f j.val z).symm.trans hmod.symm

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- Every nonempty locally balanced tripartite graph contains a simple cycle
in the cyclic orientation of its parts. -/
theorem exists_cycle (hG : G.IsLocallyBalanced) (hE : G.edgeFinset.Nonempty) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ Nonempty (Cycle G ℓ) := by
  let ActiveA := {a : A // ∃ b, G.ab a b}
  let ActiveB := {b : B // ∃ w, G.bw b w}
  let ActiveW := {w : W // ∃ a, G.aw a w}
  have hAB : ∀ a : ActiveA, ∃ b : ActiveB, G.ab a.val b.val := by
    rintro ⟨a,b,hab⟩
    have hp : 0 < (G.neighborsA b).card := Finset.card_pos.mpr
      ⟨a,by simpa [neighborsA] using hab⟩
    rw [hG.2.1 b] at hp
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hp
    refine ⟨⟨b,w,?_⟩,hab⟩
    simpa [neighborsWB] using hw
  have hBW : ∀ b : ActiveB, ∃ w : ActiveW, G.bw b.val w.val := by
    rintro ⟨b,w,hbw⟩
    have hp : 0 < (G.linkB w).card := Finset.card_pos.mpr
      ⟨b,by simpa [linkB] using hbw⟩
    rw [← hG.2.2 w] at hp
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
    refine ⟨⟨w,a,?_⟩,hbw⟩
    simpa [linkA] using ha
  have hWA : ∀ w : ActiveW, ∃ a : ActiveA, G.aw a.val w.val := by
    rintro ⟨w,a,haw⟩
    have hp : 0 < (G.neighborsWA a).card := Finset.card_pos.mpr
      ⟨w,by simpa [neighborsWA] using haw⟩
    rw [← hG.1 a] at hp
    obtain ⟨b,hb⟩ := Finset.card_pos.mp hp
    refine ⟨⟨a,b,?_⟩,haw⟩
    simpa [neighborsB] using hb
  choose fAB hfAB using hAB
  choose fBW hfBW using hBW
  choose fWA hfWA using hWA
  have hA : Nonempty ActiveA := by
    obtain ⟨e,he⟩ := hE
    have hh := (G.mem_edgeFinset e).mp he
    rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩
    · exact ⟨⟨a,b,hh⟩⟩
    · exact ⟨fWA ⟨w,a,hh⟩⟩
    · exact ⟨fWA (fBW ⟨b,w,hh⟩)⟩
  let f : ActiveA → ActiveA := fun a => fWA (fBW (fAB a))
  obtain ⟨ℓ,hℓ,x₀,hnext⟩ := exists_cyclic_orbit f (Classical.choice hA)
  let x : Fin ℓ ↪ A := ⟨fun j => (x₀ j).val,
    Subtype.val_injective.comp x₀.injective⟩
  let y : Fin ℓ ↪ B := ⟨fun j => (fAB (x₀ j)).val, by
    intro i j hij
    have hh : fAB (x₀ i) = fAB (x₀ j) := Subtype.ext hij
    have hf : f (x₀ i) = f (x₀ j) := congrArg (fun b => fWA (fBW b)) hh
    rw [hnext i,hnext j] at hf
    exact (CycleAbsorber.next ℓ).injective (x₀.injective hf)⟩
  let w : Fin ℓ ↪ W := ⟨fun j => (fBW (fAB (x₀ j))).val, by
    intro i j hij
    have hh : fBW (fAB (x₀ i)) = fBW (fAB (x₀ j)) := Subtype.ext hij
    have hf : f (x₀ i) = f (x₀ j) := congrArg fWA hh
    rw [hnext i,hnext j] at hf
    exact (CycleAbsorber.next ℓ).injective (x₀.injective hf)⟩
  refine ⟨ℓ,hℓ,⟨x,y,w,fun j => hfAB (x₀ j),fun j => hfBW (fAB (x₀ j)),?_⟩⟩
  intro j
  change G.aw (x₀ (CycleAbsorber.next ℓ j)).val (fBW (fAB (x₀ j))).val
  rw [← hnext j]
  exact hfWA (fBW (fAB (x₀ j)))

def Cycle.graph {ℓ : ℕ} (C : Cycle G ℓ) : TripartiteGraph A B W where
  ab a b := ∃ j, C.x j = a ∧ C.y j = b
  aw a w := ∃ j, C.x j = a ∧ C.w ((CycleAbsorber.next ℓ).symm j) = w
  bw b w := ∃ j, C.y j = b ∧ C.w j = w

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Cycle.graph_aw {ℓ : ℕ} (C : Cycle G ℓ) (a : A) (w : W) :
    (C.graph G).aw a w ↔ ∃ j, C.x (CycleAbsorber.next ℓ j) = a ∧ C.w j = w := by
  constructor
  · rintro ⟨j,hx,hw⟩
    exact ⟨(CycleAbsorber.next ℓ).symm j,by simpa using hx,hw⟩
  · rintro ⟨j,hx,hw⟩
    exact ⟨CycleAbsorber.next ℓ j,hx,by simpa using hw⟩

private theorem neighbor_card {I X Y : Type*} [Fintype I] [Fintype Y]
    (f : I ↪ X) (g : I ↪ Y) (x : X) :
    (univ.filter (fun y => ∃ i, f i = x ∧ g i = y)).card =
      (univ.filter (fun i => f i = x)).card := by
  have he : univ.filter (fun y => ∃ i, f i = x ∧ g i = y) =
      (univ.filter (fun i => f i = x)).image g := by
    ext y
    simp
  rw [he,Finset.card_image_of_injective _ g.injective]

/-- Each simple directed cycle is locally balanced. -/
theorem Cycle.graph_balanced {ℓ : ℕ} (C : Cycle G ℓ) :
    (C.graph G).IsLocallyBalanced := by
  refine ⟨?_,?_,?_⟩
  · intro a
    dsimp only [neighborsB,neighborsWA,Cycle.graph]
    convert (neighbor_card C.x C.y a).trans
      (neighbor_card C.x ((CycleAbsorber.next ℓ).symm.toEmbedding.trans C.w) a).symm
      using 1 <;> congr 2
  · intro b
    simp only [neighborsA,neighborsWB,Cycle.graph,
      and_comm (a := C.x _ = _) (b := C.y _ = b)]
    convert (neighbor_card C.y C.x b).trans (neighbor_card C.y C.w b).symm
      using 1 <;> congr 2
  · intro w
    simp only [linkA,linkB]
    simp_rw [C.graph_aw G]
    simp only [Cycle.graph,
      and_comm (a := C.x _ = _) (b := C.w _ = w),
      and_comm (a := C.y _ = _) (b := C.w _ = w)]
    convert (neighbor_card C.w ((CycleAbsorber.next ℓ).toEmbedding.trans C.x) w).trans
      (neighbor_card C.w C.y w).symm using 1 <;> congr 2

def Cycle.edgePosition {ℓ : ℕ} (C : Cycle G ℓ) :
    Fin 3 × Fin ℓ → EdgePosition (A := A) (B := B) (W := W)
  | (0,j) => abPos (C.x j) (C.y j)
  | (1,j) => bwPos (C.y j) (C.w j)
  | (2,j) => awPos (C.x (CycleAbsorber.next ℓ j)) (C.w j)

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Cycle.edgePosition_injective {ℓ : ℕ} (C : Cycle G ℓ) :
    Function.Injective (C.edgePosition G) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ hh
  fin_cases i <;> fin_cases i' <;>
    simp only [Cycle.edgePosition,abPos,awPos,bwPos,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Prod.mk.injEq,
      C.x.injective.eq_iff,C.y.injective.eq_iff,C.w.injective.eq_iff,
      (CycleAbsorber.next ℓ).injective.eq_iff] at hh <;>
    first | contradiction | rcases hh with ⟨rfl,_⟩; rfl

theorem Cycle.edgeFinset_eq {ℓ : ℕ} (C : Cycle G ℓ) :
    (C.graph G).edgeFinset = univ.image (C.edgePosition G) := by
  ext e
  rw [(C.graph G).mem_edgeFinset]
  constructor
  · intro he
    rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩
    · obtain ⟨j,rfl,rfl⟩ := he
      exact Finset.mem_image.mpr ⟨(0,j),Finset.mem_univ _,rfl⟩
    · obtain ⟨j,rfl,rfl⟩ := (C.graph_aw G a w).mp he
      exact Finset.mem_image.mpr ⟨(2,j),Finset.mem_univ _,rfl⟩
    · obtain ⟨j,rfl,rfl⟩ := he
      exact Finset.mem_image.mpr ⟨(1,j),Finset.mem_univ _,rfl⟩
  · rintro he
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp he
    fin_cases i
    · exact ⟨j,rfl,rfl⟩
    · exact ⟨j,rfl,rfl⟩
    · exact (C.graph_aw G _ _).mpr ⟨j,rfl,rfl⟩

theorem Cycle.edgeFinset_card {ℓ : ℕ} (C : Cycle G ℓ) :
    (C.graph G).edgeFinset.card = 3*ℓ := by
  rw [C.edgeFinset_eq G,Finset.card_image_of_injective _ (C.edgePosition_injective G)]
  simp

theorem Cycle.edgeFinset_subset {ℓ : ℕ} (C : Cycle G ℓ) :
    (C.graph G).edgeFinset ⊆ G.edgeFinset := by
  intro e he
  rw [C.edgeFinset_eq G] at he
  obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp he
  rw [G.mem_edgeFinset]
  fin_cases i
  · exact C.xy j
  · exact C.yw j
  · exact C.wx j

/-- Delete precisely the edges of the second graph. -/
def deleteGraph (H : TripartiteGraph A B W) : TripartiteGraph A B W where
  ab a b := G.ab a b ∧ ¬ H.ab a b
  aw a w := G.aw a w ∧ ¬ H.aw a w
  bw b w := G.bw b w ∧ ¬ H.bw b w

theorem deleteGraph_edgeFinset (H : TripartiteGraph A B W) :
    (deleteGraph G H).edgeFinset = G.edgeFinset \ H.edgeFinset := by
  ext e
  rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩ <;>
    simp [edgeFinset,IsEdge,deleteGraph]

private theorem filter_delete_card {X : Type*} [Fintype X] (P Q : X → Prop)
    (hsub : ∀ x, Q x → P x) :
    (univ.filter (fun x => P x ∧ ¬ Q x)).card =
      (univ.filter P).card-(univ.filter Q).card := by
  have he : univ.filter (fun x => P x ∧ ¬ Q x) =
      (univ.filter P) \ (univ.filter Q) := by ext x; simp
  rw [he,Finset.card_sdiff_of_subset]
  intro x hx
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
  exact hsub x hx

/-- Deleting a locally balanced subgraph preserves local balance. -/
theorem deleteGraph_balanced (H : TripartiteGraph A B W)
    (hsub : H.edgeFinset ⊆ G.edgeFinset)
    (hG : G.IsLocallyBalanced) (hH : H.IsLocallyBalanced) :
    (deleteGraph G H).IsLocallyBalanced := by
  have hab : ∀ a b, H.ab a b → G.ab a b := fun a b h =>
    (G.mem_edgeFinset (abPos a b)).mp (hsub ((H.mem_edgeFinset (abPos a b)).mpr h))
  have haw : ∀ a w, H.aw a w → G.aw a w := fun a w h =>
    (G.mem_edgeFinset (awPos a w)).mp (hsub ((H.mem_edgeFinset (awPos a w)).mpr h))
  have hbw : ∀ b w, H.bw b w → G.bw b w := fun b w h =>
    (G.mem_edgeFinset (bwPos b w)).mp (hsub ((H.mem_edgeFinset (bwPos b w)).mpr h))
  have habA (a : A) : ((deleteGraph G H).neighborsB a).card =
      (G.neighborsB a).card-(H.neighborsB a).card := by
    dsimp only [neighborsB,deleteGraph]
    convert filter_delete_card _ _ (hab a) using 1
    congr 2
  have habB (b : B) : ((deleteGraph G H).neighborsA b).card =
      (G.neighborsA b).card-(H.neighborsA b).card := by
    dsimp only [neighborsA,deleteGraph]
    convert filter_delete_card _ _ (fun a => hab a b) using 1
    congr 2
  have hawA (a : A) : ((deleteGraph G H).neighborsWA a).card =
      (G.neighborsWA a).card-(H.neighborsWA a).card := by
    dsimp only [neighborsWA,deleteGraph]
    convert filter_delete_card _ _ (haw a) using 1
    congr 2
  have hawW (w : W) : ((deleteGraph G H).linkA w).card =
      (G.linkA w).card-(H.linkA w).card := by
    dsimp only [linkA,deleteGraph]
    convert filter_delete_card _ _ (fun a => haw a w) using 1
    congr 2
  have hbwB (b : B) : ((deleteGraph G H).neighborsWB b).card =
      (G.neighborsWB b).card-(H.neighborsWB b).card := by
    dsimp only [neighborsWB,deleteGraph]
    convert filter_delete_card _ _ (hbw b) using 1
    congr 2
  have hbwW (w : W) : ((deleteGraph G H).linkB w).card =
      (G.linkB w).card-(H.linkB w).card := by
    dsimp only [linkB,deleteGraph]
    convert filter_delete_card _ _ (fun b => hbw b w) using 1
    congr 2
  refine ⟨?_,?_,?_⟩
  · intro a
    rw [habA,hawA]
    exact congrArg₂ (fun x y : ℕ => x-y) (hG.1 a) (hH.1 a)
  · intro b
    rw [habB,hbwB]
    exact congrArg₂ (fun x y : ℕ => x-y) (hG.2.1 b) (hH.2.1 b)
  · intro w
    rw [hawW,hbwW]
    exact congrArg₂ (fun x y : ℕ => x-y) (hG.2.2 w) (hH.2.2 w)

/-- A cycle of a subgraph is a cycle of the host on the same vertices. -/
def Cycle.lift {H : TripartiteGraph A B W} {ℓ : ℕ} (C : Cycle H ℓ)
    (hsub : H.edgeFinset ⊆ G.edgeFinset) : Cycle G ℓ where
  x := C.x
  y := C.y
  w := C.w
  xy j := (G.mem_edgeFinset (abPos (C.x j) (C.y j))).mp
    (hsub ((H.mem_edgeFinset _).mpr (C.xy j)))
  yw j := (G.mem_edgeFinset (bwPos (C.y j) (C.w j))).mp
    (hsub ((H.mem_edgeFinset _).mpr (C.yw j)))
  wx j := (G.mem_edgeFinset (awPos (C.x (CycleAbsorber.next ℓ j)) (C.w j))).mp
    (hsub ((H.mem_edgeFinset _).mpr (C.wx j)))

@[simp] theorem Cycle.graph_lift {H : TripartiteGraph A B W} {ℓ : ℕ} (C : Cycle H ℓ)
    (hsub : H.edgeFinset ⊆ G.edgeFinset) :
    (C.lift G hsub).graph G = C.graph H := rfl

/-- A finite edge-disjoint partition into actual simple directed cycles. -/
structure CyclePartition where
  count : ℕ
  length : Fin count → ℕ
  cycle : ∀ i, Cycle G (length i)
  positive : ∀ i, 0 < length i
  disjoint : Pairwise (fun i j =>
    Disjoint ((cycle i).graph G).edgeFinset ((cycle j).graph G).edgeFinset)
  cover : univ.biUnion (fun i => ((cycle i).graph G).edgeFinset) = G.edgeFinset
  sum : ∑ i, 3*length i = G.edgeFinset.card

/-- Local balance suffices for a full partition into simple directed cycles. -/
theorem cyclePartition_exists (hG : G.IsLocallyBalanced) : Nonempty (CyclePartition G) := by
  suffices ∀ n, ∀ H : TripartiteGraph A B W,
      H.edgeFinset.card = n → H.IsLocallyBalanced → Nonempty (CyclePartition H) from
    this _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hcard hH
    by_cases hempty : H.edgeFinset = ∅
    · refine ⟨{
        count := 0
        length := Fin.elim0
        cycle := fun i => Fin.elim0 i
        positive := fun i => Fin.elim0 i
        disjoint := fun i => Fin.elim0 i
        cover := ?_
        sum := ?_ }⟩ <;> simp [hempty]
    obtain ⟨ℓ,hℓ,⟨C⟩⟩ := exists_cycle H hH (Finset.nonempty_iff_ne_empty.mpr hempty)
    let K := deleteGraph H (C.graph H)
    have hKedges : K.edgeFinset = H.edgeFinset \ (C.graph H).edgeFinset :=
      deleteGraph_edgeFinset H (C.graph H)
    have hCsub := C.edgeFinset_subset H
    have hCcard : (C.graph H).edgeFinset.card ≤ H.edgeFinset.card :=
      Finset.card_le_card hCsub
    have hKcard : K.edgeFinset.card < n := by
      rw [hKedges,Finset.card_sdiff_of_subset hCsub,C.edgeFinset_card H]
      rw [C.edgeFinset_card H] at hCcard
      omega
    have hKsub : K.edgeFinset ⊆ H.edgeFinset := by
      rw [hKedges]
      exact Finset.sdiff_subset
    obtain ⟨P⟩ := ih K.edgeFinset.card hKcard K rfl
      (deleteGraph_balanced H (C.graph H) hCsub hH (C.graph_balanced H))
    let lengths : Fin (P.count+1) → ℕ := Fin.cons ℓ P.length
    let cycles : ∀ i : Fin (P.count+1), Cycle H (lengths i) :=
      Fin.cases C (fun i => (P.cycle i).lift H hKsub)
    have hCdis (i : Fin P.count) : Disjoint (C.graph H).edgeFinset
        (((P.cycle i).lift H hKsub).graph H).edgeFinset := by
      rw [Cycle.graph_lift]
      apply Finset.disjoint_left.mpr
      intro e heC heP
      have heK := (P.cycle i).edgeFinset_subset K heP
      rw [hKedges] at heK
      exact (Finset.mem_sdiff.mp heK).2 heC
    refine ⟨{
      count := P.count+1
      length := lengths
      cycle := cycles
      positive := ?_
      disjoint := ?_
      cover := ?_
      sum := ?_ }⟩
    · intro i
      cases i using Fin.cases
      · exact hℓ
      · exact P.positive _
    · intro i j hij
      cases i using Fin.cases <;> cases j using Fin.cases
      · exact (hij rfl).elim
      · exact hCdis _
      · exact (hCdis _).symm
      · simp only [cycles,Fin.cases_succ,Cycle.graph_lift]
        apply P.disjoint
        intro h
        exact hij (congrArg Fin.succ h)
    · have hunion : univ.biUnion (fun i => ((cycles i).graph H).edgeFinset) =
          (C.graph H).edgeFinset ∪ K.edgeFinset := by
        rw [← P.cover]
        ext e
        simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,
          Fin.exists_fin_succ,cycles,Fin.cases_zero,Fin.cases_succ,Cycle.graph_lift]
      rw [hunion,hKedges,Finset.union_sdiff_of_subset hCsub]
    · rw [Fin.sum_univ_succ]
      simp only [lengths,Fin.cons_zero,Fin.cons_succ]
      rw [P.sum,hKedges,Finset.card_sdiff_of_subset hCsub,C.edgeFinset_card H]
      rw [C.edgeFinset_card H] at hCcard
      omega

end Overfull.Dense.FiniteAbsorber
