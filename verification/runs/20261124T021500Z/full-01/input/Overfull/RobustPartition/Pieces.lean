import Overfull.RobustPartition.Counting
import Overfull.RobustPartition.Induced
import Mathlib.Data.List.Pairwise

/-!
# Actual graph pieces and finite partition refinement

A piece is either one ordinary vertex set or two ordered bipartite shores.
The underlying shore list is a disjoint partition of the ambient vertex set.
Refinement replaces one ordinary set by two disjoint sets with the same union;
its rank is the number of shores, so it increases by exactly one.
-/

namespace Overfull.RobustPartition

attribute [local instance] Classical.propDecidable

variable {V : Type*}

inductive Piece (V : Type*) where
  | ordinary (U : Finset V)
  | bipartite (A B : Finset V)

def Piece.shoreList : Piece V → List (Finset V)
  | .ordinary U => [U]
  | .bipartite A B => [A, B]

noncomputable def Piece.vertices : Piece V → Finset V
  | .ordinary U => U
  | .bipartite A B => A ∪ B

noncomputable def unionList : List (Finset V) → Finset V
  | [] => ∅
  | U :: L => U ∪ unionList L

def shoreList (L : List (Piece V)) : List (Finset V) :=
  L.flatMap Piece.shoreList

def rank (L : List (Piece V)) : ℕ := (shoreList L).length

noncomputable def IsPartition [Fintype V] (L : List (Piece V)) : Prop :=
  (shoreList L).Pairwise Disjoint ∧ unionList (shoreList L) = Finset.univ

@[simp] theorem unionList_nil : unionList ([] : List (Finset V)) = ∅ := rfl

@[simp] theorem unionList_cons (U : Finset V) (L : List (Finset V)) :
    unionList (U :: L) = U ∪ unionList L := rfl

theorem unionList_append (L R : List (Finset V)) :
    unionList (L ++ R) = unionList L ∪ unionList R := by
  induction L with
  | nil => simp
  | cons U L ih => simp [ih, Finset.union_assoc]

theorem disjoint_unionList_right (U : Finset V) (L : List (Finset V))
    (h : ∀ X ∈ L, Disjoint U X) : Disjoint U (unionList L) := by
  induction L with
  | nil => simp
  | cons X L ih =>
      exact Finset.disjoint_union_right.mpr
        ⟨h X (by simp), ih (fun Y hY => h Y (by simp [hY]))⟩

theorem lower_mul_length_le_union_card (L : List (Finset V))
    (hdisj : L.Pairwise Disjoint) (b : ℝ)
    (hsize : ∀ U ∈ L, b ≤ (U.card : ℝ)) :
    (L.length : ℝ) * b ≤ (unionList L).card := by
  induction L with
  | nil => simp
  | cons U L ih =>
      obtain ⟨hU, hL⟩ := List.pairwise_cons.mp hdisj
      have htail := ih hL (fun X hX => hsize X (by simp [hX]))
      have hhead := hsize U (by simp)
      have hcard := Finset.card_union_of_disjoint (disjoint_unionList_right U L hU)
      simp only [unionList_cons, hcard, Nat.cast_add, List.length_cons, Nat.cast_one]
      nlinarith

theorem pairwise_replace_shore (L R : List (Finset V)) (U P Q : Finset V)
    (h : (L ++ U :: R).Pairwise Disjoint)
    (hPQ : Disjoint P Q) (hP : P ⊆ U) (hQ : Q ⊆ U) :
    (L ++ P :: Q :: R).Pairwise Disjoint := by
  obtain ⟨hL, hUR, hcross⟩ := List.pairwise_append.mp h
  obtain ⟨hU, hR⟩ := List.pairwise_cons.mp hUR
  apply List.pairwise_append.mpr
  refine ⟨hL, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    constructor
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact hPQ
      · exact (hU X hX).mono hP (Finset.Subset.refl _)
    · apply List.pairwise_cons.mpr
      exact ⟨fun X hX => (hU X hX).mono hQ (Finset.Subset.refl _), hR⟩
  · intro X hX Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact (hcross X hX U (by simp)).mono (Finset.Subset.refl _) hP
    · rcases List.mem_cons.mp hY with rfl | hY
      · exact (hcross X hX U (by simp)).mono (Finset.Subset.refl _) hQ
      · exact hcross X hX Y (by simp [hY])

theorem unionList_replace_shore (L R : List (Finset V)) (U P Q : Finset V)
    (hunion : P ∪ Q = U) :
    unionList (L ++ P :: Q :: R) = unionList (L ++ U :: R) := by
  simp only [unionList_append, unionList_cons]
  rw [← Finset.union_assoc P Q, hunion]

@[simp] theorem shoreList_append (L R : List (Piece V)) :
    shoreList (L ++ R) = shoreList L ++ shoreList R := by
  simp [shoreList]

@[simp] theorem shoreList_cons (p : Piece V) (L : List (Piece V)) :
    shoreList (p :: L) = p.shoreList ++ shoreList L := by
  simp [shoreList]

@[simp] theorem shoreList_nil : shoreList ([] : List (Piece V)) = [] := rfl

@[simp] theorem rank_append (L R : List (Piece V)) :
    rank (L ++ R) = rank L + rank R := by simp [rank]

@[simp] theorem rank_ordinary_cons (U : Finset V) (L : List (Piece V)) :
    rank (.ordinary U :: L) = 1 + rank L := by
  simp [rank, Piece.shoreList, Nat.add_comm]

@[simp] theorem rank_bipartite_cons (A B : Finset V) (L : List (Piece V)) :
    rank (.bipartite A B :: L) = 2 + rank L := by
  simp only [rank, shoreList_cons, Piece.shoreList, List.cons_append,
    List.nil_append, List.length_cons]
  omega

theorem partition_replace_ordinary [Fintype V]
    (L R : List (Piece V)) (U P Q : Finset V)
    (h : IsPartition (L ++ .ordinary U :: R))
    (hPQ : Disjoint P Q) (hunion : P ∪ Q = U) :
    IsPartition (L ++ .ordinary P :: .ordinary Q :: R) ∧
      IsPartition (L ++ .bipartite P Q :: R) := by
  have hP : P ⊆ U := hunion ▸ Finset.subset_union_left
  have hQ : Q ⊆ U := hunion ▸ Finset.subset_union_right
  have hold : (shoreList L ++ U :: shoreList R).Pairwise Disjoint ∧
      unionList (shoreList L ++ U :: shoreList R) = Finset.univ := by
    simpa only [IsPartition, shoreList_append, shoreList_cons,
      Piece.shoreList, List.singleton_append] using h
  have hnew : (shoreList L ++ P :: Q :: shoreList R).Pairwise Disjoint ∧
      unionList (shoreList L ++ P :: Q :: shoreList R) = Finset.univ :=
    ⟨pairwise_replace_shore _ _ _ _ _ hold.1 hPQ hP hQ,
      (unionList_replace_shore _ _ _ _ _ hunion).trans hold.2⟩
  constructor <;>
    simpa only [IsPartition, shoreList_append, shoreList_cons, Piece.shoreList,
      List.cons_append, List.nil_append] using hnew

variable [Fintype V]

noncomputable def Piece.Valid (G : SimpleGraph V) (a ε : ℝ) : Piece V → Prop
  | .ordinary U =>
      a * Fintype.card V / 2 ≤ (U.card : ℝ) ∧
        cut G U ≤ ε * (Fintype.card V : ℝ)^2
  | .bipartite A B =>
      Disjoint A B ∧ a * Fintype.card V / 2 ≤ (A.card : ℝ) ∧
        a * Fintype.card V / 2 ≤ (B.card : ℝ) ∧
        bad G A B ≤ ε * (Fintype.card V : ℝ)^2 ∧
        |(A.card : ℝ) - B.card| ≤ ε * Fintype.card V

noncomputable def Piece.Terminal (G : SimpleGraph V) (ν τ : ℝ) : Piece V → Prop
  | .ordinary U => IsRobustExpander (G.induce (↑U : Set V)) ν τ
  | .bipartite _ _ => True

theorem Piece.valid_mono (G : SimpleGraph V) (a ε μ : ℝ) (hεμ : ε ≤ μ)
    (p : Piece V) (hp : p.Valid G a ε) : p.Valid G a μ := by
  have h2 := mul_le_mul_of_nonneg_right hεμ (sq_nonneg (Fintype.card V : ℝ))
  have h1 := mul_le_mul_of_nonneg_right hεμ (Nat.cast_nonneg (Fintype.card V))
  cases p with
  | ordinary U => exact ⟨hp.1, hp.2.trans h2⟩
  | bipartite A B => exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1.trans h2,
      hp.2.2.2.2.trans h1⟩

theorem valid_shore_lower (G : SimpleGraph V) (a ε : ℝ)
    (L : List (Piece V)) (hvalid : ∀ p ∈ L, p.Valid G a ε) :
    ∀ U ∈ shoreList L, a * Fintype.card V / 2 ≤ (U.card : ℝ) := by
  intro U hU
  obtain ⟨p, hp, hUp⟩ := List.mem_flatMap.mp hU
  have hv := hvalid p hp
  cases p with
  | ordinary X =>
      have hUX : U = X := by simpa [Piece.shoreList] using hUp
      subst U
      exact hv.1
  | bipartite A B =>
      have hUAB : U = A ∨ U = B := by simpa [Piece.shoreList] using hUp
      rcases hUAB with rfl | rfl
      · exact hv.2.1
      · exact hv.2.2.1

theorem valid_rank_bound (G : SimpleGraph V) (a ε : ℝ)
    (hn : 0 < (Fintype.card V : ℝ)) (L : List (Piece V))
    (hpart : IsPartition L) (hvalid : ∀ p ∈ L, p.Valid G a ε) :
    (rank L : ℝ) * a ≤ 2 := by
  have hmass := lower_mul_length_le_union_card (shoreList L) hpart.1
    (a * Fintype.card V / 2) (valid_shore_lower G a ε L hvalid)
  rw [hpart.2, Finset.card_univ] at hmass
  exact coarse_count_bound _ _ _ hn hmass

theorem valid_initial (G : SimpleGraph V) (a ε : ℝ)
    (ha : a ≤ 1) (hε : 0 ≤ ε) :
    IsPartition [.ordinary (Finset.univ : Finset V)] ∧
      ∀ p ∈ [Piece.ordinary (Finset.univ : Finset V)], p.Valid G a ε := by
  constructor
  · simp [IsPartition, shoreList, Piece.shoreList]
  · intro p hp
    have hp' : p = Piece.ordinary (Finset.univ : Finset V) := by simpa using hp
    subst p
    constructor
    · simp only [Finset.card_univ]
      have hn : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_right ha hn
      nlinarith
    · have hzero : cut G (Finset.univ : Finset V) = 0 := by
        simp [cut, ecount, SimpleGraph.interedges_def]
      rw [hzero]
      positivity

end Overfull.RobustPartition
