import Overfull.BipartiteAugmentation

/-!
# Choosing disjoint short augmenting paths

The paths are constructed from robust expansion. They are not additional
input to the packing argument. During induction the unused pair of ends
is forbidden, so all chosen paths remain disjoint from that pair.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

namespace BipartiteAugmentingPath

variable {A B : Type*} {G : SimpleGraph (A ⊕ B)}
  {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
  {W W' : Finset (A ⊕ B)} {x : A} {y : B}

/-- A path avoiding a larger forbidden set also avoids a smaller one. -/
def weakenForbidden (p : BipartiteAugmentingPath G M W' x y) (h : W ⊆ W') :
    BipartiteAugmentingPath G M W x y :=
  { p with
    left_avoids := fun i hi => p.left_avoids i (h hi)
    right_avoids := fun i hi => p.right_avoids i (h hi) }

@[simp] theorem weakenForbidden_length
    (p : BipartiteAugmentingPath G M W' x y) (h : W ⊆ W') :
    (p.weakenForbidden h).length = p.length := rfl

@[simp] theorem weakenForbidden_vertexSet
    (p : BipartiteAugmentingPath G M W' x y) (h : W ⊆ W') :
    (p.weakenForbidden h).vertexSet = p.vertexSet := rfl

end BipartiteAugmentingPath

namespace BipartitePathPacking

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The union of actual path vertices has the expected elementary size bound. -/
theorem path_union_card {I : Type*} [Fintype I]
    {G : SimpleGraph (A ⊕ B)} {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
    {W : I → Finset (A ⊕ B)} {x : I → A} {y : I → B}
    (p : ∀ i, BipartiteAugmentingPath G M (W i) (x i) (y i))
    (ℓ : ℕ) (hlen : ∀ i, (p i).length + 1 ≤ ℓ) :
    (univ.biUnion (fun i => (p i).vertexSet.toFinset)).card ≤
      2 * ℓ * Fintype.card I := by
  calc
    _ ≤ ∑ i : I, (p i).vertexSet.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 2 * ℓ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Set.ncard_eq_toFinset_card', (p i).vertexSet_ncard]
      exact Nat.mul_le_mul_left 2 (hlen i)
    _ = _ := by simp [Nat.mul_comm]

/-- Short disjoint augmenting paths for every uncovered pair outside a
partner-closed forbidden set. The budget includes all path vertices. -/
theorem exists_disjoint_paths
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (hM : IsCrossingMatching M)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G θ τ)
    (ℓ : ℕ) (hℓ : Nat.ceil (2 / θ) + 2 ≤ ℓ)
    (h : ℕ) (W : Finset (A ⊕ B)) (x : Fin h → A) (y : Fin h → B)
    (hxin : Function.Injective x) (hyin : Function.Injective y)
    (hxM : ∀ i, (.inl (x i) : A ⊕ B) ∉ M.verts)
    (hyM : ∀ i, (.inr (y i) : A ⊕ B) ∉ M.verts)
    (hxW : ∀ i, (.inl (x i) : A ⊕ B) ∉ W)
    (hyW : ∀ i, (.inr (y i) : A ⊕ B) ∉ W)
    (hclosed : ∀ v w, v ∈ W → M.Adj v w → w ∈ W)
    (hends : ∀ v : A ⊕ B, v ∉ W → v ∉ M.verts →
      (∃ i, v = .inl (x i)) ∨ ∃ i, v = .inr (y i))
    (hbudget : (W.card : ℝ) + 2 * ℓ * h ≤ min θ δ * Fintype.card A / 2 - 1) :
    ∃ p : ∀ i, BipartiteAugmentingPath G M W (x i) (y i),
      (∀ i, (p i).length + 1 ≤ ℓ) ∧
      Pairwise (fun i j => Disjoint (p i).vertexSet (p j).vertexSet) := by
  classical
  induction h generalizing W with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    let W' : Finset (A ⊕ B) := insert (.inl (x (Fin.last n)))
      (insert (.inr (y (Fin.last n))) W)
    have hWW' : W ⊆ W' := by intro v hv; simp [W', hv]
    have hW'card : W'.card ≤ W.card + 2 := by
      dsimp [W']
      have h₁ := Finset.card_insert_le (.inl (x (Fin.last n)))
        (insert (.inr (y (Fin.last n))) W)
      have h₂ := Finset.card_insert_le (.inr (y (Fin.last n))) W
      omega
    have hbudget' : (W'.card : ℝ) + 2 * ℓ * n ≤
        min θ δ * Fintype.card A / 2 - 1 := by
      have hc : (W'.card : ℝ) ≤ W.card + 2 := by exact_mod_cast hW'card
      have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
      push_cast at hbudget
      nlinarith
    have hxW' (i : Fin n) : (.inl (x i.castSucc) : A ⊕ B) ∉ W' := by
      simp only [W', Finset.mem_insert, Sum.inl.injEq, Sum.inl_ne_inr, false_or,
        not_or]
      exact ⟨fun heq => (ne_of_lt i.castSucc_lt_last) (hxin heq), hxW i.castSucc⟩
    have hyW' (i : Fin n) : (.inr (y i.castSucc) : A ⊕ B) ∉ W' := by
      simp only [W', Finset.mem_insert, Sum.inr_ne_inl, Sum.inr.injEq, false_or,
        not_or]
      exact ⟨fun heq => (ne_of_lt i.castSucc_lt_last) (hyin heq), hyW i.castSucc⟩
    have hclosed' : ∀ v w, v ∈ W' → M.Adj v w → w ∈ W' := by
      intro v w hv hvw
      rcases Finset.mem_insert.mp hv with hv | hv
      · subst v
        exact (hxM (Fin.last n) (M.edge_vert hvw)).elim
      · rcases Finset.mem_insert.mp hv with hv | hv
        · subst v
          exact (hyM (Fin.last n) (M.edge_vert hvw)).elim
        · exact hWW' (hclosed v w hv hvw)
    have hends' : ∀ v : A ⊕ B, v ∉ W' → v ∉ M.verts →
        (∃ i : Fin n, v = .inl (x i.castSucc)) ∨
          ∃ i : Fin n, v = .inr (y i.castSucc) := by
      intro v hv hnot
      rcases hends v (fun hvW => hv (hWW' hvW)) hnot with ⟨i, hi⟩ | ⟨i, hi⟩
      · induction i using Fin.lastCases with
        | last => exact (hv (by simp [W', hi])).elim
        | cast i => exact Or.inl ⟨i, hi⟩
      · induction i using Fin.lastCases with
        | last => exact (hv (by simp [W', hi])).elim
        | cast i => exact Or.inr ⟨i, hi⟩
    obtain ⟨p, hlen, hdisj⟩ := ih W' (fun i => x i.castSucc) (fun i => y i.castSucc)
      (hxin.comp (Fin.castSucc_injective n)) (hyin.comp (Fin.castSucc_injective n))
      (fun i => hxM i.castSucc) (fun i => hyM i.castSucc) hxW' hyW'
      hclosed' hends' hbudget'
    let P : Finset (A ⊕ B) := univ.biUnion (fun i : Fin n => (p i).vertexSet.toFinset)
    have hPmem (v : A ⊕ B) : v ∈ P ↔ ∃ i, v ∈ (p i).vertexSet := by
      simp [P]
    have hPcard : P.card ≤ 2 * ℓ * n := by
      simpa only [Fintype.card_fin] using path_union_card p ℓ hlen
    let W'' := W ∪ P
    have hWW'' : W ⊆ W'' := Finset.subset_union_left
    have hbudget'' : (W''.card : ℝ) ≤ min θ δ * Fintype.card A / 2 - 1 := by
      have hU := Finset.card_union_le W P
      have hU' : (W''.card : ℝ) ≤ W.card + P.card := by exact_mod_cast hU
      have hP' : (P.card : ℝ) ≤ 2 * ℓ * n := by exact_mod_cast hPcard
      have hℓR : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
      push_cast at hbudget
      nlinarith
    have hxW'' : (.inl (x (Fin.last n)) : A ⊕ B) ∉ W'' := by
      intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hxW (Fin.last n) hv
      · obtain ⟨i, hi⟩ := (hPmem _).mp hv
        exact (p i).vertexSet_avoids hi (by simp [W'])
    have hyW'' : (.inr (y (Fin.last n)) : A ⊕ B) ∉ W'' := by
      intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hyW (Fin.last n) hv
      · obtain ⟨i, hi⟩ := (hPmem _).mp hv
        exact (p i).vertexSet_avoids hi (by simp [W'])
    have hclosed'' : ∀ v w, v ∈ W'' → M.Adj v w → w ∈ W'' := by
      intro v w hv hvw
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left P (hclosed v w hv hvw)
      · obtain ⟨i, hi⟩ := (hPmem v).mp hv
        exact Finset.mem_union_right W ((hPmem w).mpr ⟨i,
          (p i).vertexSet_partner_closed hM.1 (hxM i.castSucc) (hyM i.castSucc)
            v w hi hvw⟩)
    have hcovered : ∀ v : A ⊕ B, v ∉ W'' →
        v ≠ .inl (x (Fin.last n)) → v ≠ .inr (y (Fin.last n)) → v ∈ M.verts := by
      intro v hv hx hy
      by_contra hnot
      rcases hends v (fun hvW => hv (hWW'' hvW)) hnot with ⟨i, hi⟩ | ⟨i, hi⟩
      · induction i using Fin.lastCases with
        | last => exact hx hi
        | cast i =>
          exact hv (Finset.mem_union_right W ((hPmem v).mpr
            ⟨i, hi.symm ▸ (p i).start_mem_vertexSet⟩))
      · induction i using Fin.lastCases with
        | last => exact hy hi
        | cast i =>
          exact hv (Finset.mem_union_right W ((hPmem v).mpr
            ⟨i, hi.symm ▸ (p i).finish_mem_vertexSet⟩))
    obtain ⟨q, hq⟩ := bipartite_robust_augmenting_path G M hM W''
      (x (Fin.last n)) (y (Fin.last n)) (hxM _) (hyM _) hxW'' hyW''
      hcovered hclosed'' θ τ δ hθ hτ hδ hbudget'' hleft hright hexpand
    have hqp (i : Fin n) : Disjoint q.vertexSet (p i).vertexSet := by
      rw [Set.disjoint_left]
      intro v hvq hvp
      exact q.vertexSet_avoids hvq
        (Finset.mem_union_right W ((hPmem v).mpr ⟨i, hvp⟩))
    let r : ∀ i : Fin (n + 1), BipartiteAugmentingPath G M W (x i) (y i) :=
      Fin.lastCases (q.weakenForbidden hWW'') (fun i => (p i).weakenForbidden hWW')
    refine ⟨r, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [r, Fin.lastCases_last, BipartiteAugmentingPath.weakenForbidden_length]
          using (show q.length + 1 ≤ ℓ by omega)
      | cast i => simpa only [r, Fin.lastCases_castSucc,
          BipartiteAugmentingPath.weakenForbidden_length] using hlen i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact (hij rfl).elim
        | cast j => simpa only [r, Fin.lastCases_last, Fin.lastCases_castSucc,
            BipartiteAugmentingPath.weakenForbidden_vertexSet] using hqp j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa only [r, Fin.lastCases_last, Fin.lastCases_castSucc,
            BipartiteAugmentingPath.weakenForbidden_vertexSet] using (hqp i).symm
        | cast j =>
          have hij' : i ≠ j := fun h => hij (congrArg Fin.castSucc h)
          simpa only [r, Fin.lastCases_castSucc,
            BipartiteAugmentingPath.weakenForbidden_vertexSet] using hdisj hij'

end BipartitePathPacking
end Overfull
