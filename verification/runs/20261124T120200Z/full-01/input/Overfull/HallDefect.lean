import Overfull.BipartiteMatching
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Hall's theorem and its deficiency form

The conclusions are actual matching subgraphs. The deficiency argument adds
`h` dummy vertices on the right, applies finite Hall, and retains precisely
the matching edges whose right endpoints are original vertices.
-/

namespace Overfull

open Finset

variable {A B C : Type*}

private def matchingFromPartialMap (G : SimpleGraph (A ⊕ B))
    (f : A → B ⊕ C)
    (hadj : ∀ a b, f a = .inl b → G.Adj (.inl a) (.inr b)) : G.Subgraph where
  verts v := match v with
    | .inl a => ∃ b, f a = .inl b
    | .inr b => ∃ a, f a = .inl b
  Adj v w := match v, w with
    | .inl a, .inr b => f a = .inl b
    | .inr b, .inl a => f a = .inl b
    | _, _ => False
  adj_sub := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl a' => exact h.elim
      | inr b => exact hadj a b h
    | inr b =>
      cases w with
      | inl a => exact (hadj a b h).symm
      | inr b' => exact h.elim
  edge_vert := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl a' => exact h.elim
      | inr b => exact ⟨b, h⟩
    | inr b =>
      cases w with
      | inl a => exact ⟨a, h⟩
      | inr b' => exact h.elim
  symm := by intro v w h; cases v <;> cases w <;> exact h

private theorem matchingFromPartialMap_isMatching
    (G : SimpleGraph (A ⊕ B)) (f : A → B ⊕ C)
    (hadj : ∀ a b, f a = .inl b → G.Adj (.inl a) (.inr b))
    (hf : Function.Injective f) : (matchingFromPartialMap G f hadj).IsMatching := by
  intro v hv
  cases v with
  | inl a =>
    obtain ⟨b, hb⟩ := hv
    refine ⟨.inr b, hb, ?_⟩
    intro w hw
    cases w with
    | inl a' => exact hw.elim
    | inr b' =>
      change f a = .inl b' at hw
      exact congrArg Sum.inr (Sum.inl.inj (hw.symm.trans hb))
  | inr b =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨.inl a, ha, ?_⟩
    intro w hw
    cases w with
    | inl a' =>
      change f a' = .inl b at hw
      exact congrArg Sum.inl (hf (hw.trans ha.symm))
    | inr b' => exact hw.elim

/-- The vertices of the left side not covered by a matching subgraph. -/
noncomputable def uncoveredLeft [Fintype A] {G : SimpleGraph (A ⊕ B)}
    (M : G.Subgraph) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => (.inl a : A ⊕ B) ∉ M.verts)

private theorem matchingFromPartialMap_misses
    [Fintype A] [Fintype C] [DecidableEq A]
    (G : SimpleGraph (A ⊕ B)) (f : A → B ⊕ C)
    (hadj : ∀ a b, f a = .inl b → G.Adj (.inl a) (.inr b))
    (hf : Function.Injective f) :
    (uncoveredLeft (matchingFromPartialMap G f hadj)).card ≤ Fintype.card C := by
  classical
  let U := uncoveredLeft (matchingFromPartialMap G f hadj)
  have hcount : U.card ≤ ((Finset.univ : Finset C).image (Sum.inr : C → B ⊕ C)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      have ha' : ¬∃ b, f a = .inl b := (Finset.mem_filter.mp ha).2
      cases hfa : f a with
      | inl b => exact (ha' ⟨b, hfa⟩).elim
      | inr c => exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
    · exact hf.injOn
  simpa [U, Finset.card_image_of_injective _ Sum.inr_injective] using hcount

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- Corollary 2.4: the Hall deficiency bound gives a matching missing at most
`h` vertices of the left side. Only genuine crossing edges of `G` are used. -/
theorem bipartite_hall_defect (h : ℕ)
    (hdefect : ∀ S : Finset A, S.card - h ≤ (S.biUnion (rightNeighbors G)).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      (uncoveredLeft M).card ≤ h := by
  classical
  let T : A → Finset (B ⊕ Fin h) := fun a => (rightNeighbors G a).disjSum Finset.univ
  have hHall : ∀ S : Finset A, S.card ≤ (S.biUnion T).card := by
    intro S
    by_cases hS : S.Nonempty
    · have hUnion : S.biUnion T = (S.biUnion (rightNeighbors G)).disjSum Finset.univ := by
        ext z
        cases z with
        | inl b => simp [T]
        | inr c => simpa [T] using hS
      rw [hUnion, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      have hd := hdefect S
      omega
    · have hzero := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hzero]
  obtain ⟨f, hf, hfT⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hHall
  have hadj : ∀ a b, f a = .inl b → G.Adj (.inl a) (.inr b) := by
    intro a b hab
    have hb := hfT a
    rw [hab] at hb
    simpa [T, rightNeighbors] using hb
  refine ⟨matchingFromPartialMap G f hadj,
    matchingFromPartialMap_isMatching G f hadj hf, ?_⟩
  simpa using matchingFromPartialMap_misses G f hadj hf

/-- Theorem 2.3: Hall's condition is equivalent to a matching that covers
all vertices of the left side of a bipartite graph. The two sides need not
have equal sizes. -/
theorem bipartite_hall_iff
    (hG : G.IsBipartiteWith (Set.range (Sum.inl : A → A ⊕ B))
      (Set.range (Sum.inr : B → A ⊕ B))) :
    (∃ M : G.Subgraph, M.IsMatching ∧ ∀ a : A, (.inl a : A ⊕ B) ∈ M.verts) ↔
      ∀ S : Finset A, S.card ≤ (S.biUnion (rightNeighbors G)).card := by
  classical
  constructor
  · rintro ⟨M, hM, hcover⟩
    have hpartner : ∀ a : A, ∃ b : B, M.Adj (.inl a) (.inr b) := by
      intro a
      obtain ⟨v, hv, _⟩ := hM (hcover a)
      obtain ⟨b, rfl⟩ := hG.mem_of_mem_adj (Set.mem_range_self a) (M.adj_sub hv)
      exact ⟨b, hv⟩
    choose f hf using hpartner
    have hfi : Function.Injective f := by
      intro a a' haa'
      have ha' : M.Adj (.inl a') (.inr (f a)) := by rw [haa']; exact hf a'
      exact Sum.inl.inj (hM.eq_of_adj_right (hf a) ha')
    apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (rightNeighbors G)).mpr
    refine ⟨f, hfi, ?_⟩
    intro a
    simpa [rightNeighbors] using M.adj_sub (hf a)
  · intro hHall
    obtain ⟨M, hM, hmiss⟩ := bipartite_hall_defect G 0 (by simpa using hHall)
    refine ⟨M, hM, ?_⟩
    have hempty : uncoveredLeft M = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hmiss)
    intro a
    by_contra ha
    have ha' : a ∈ uncoveredLeft M := by simp [uncoveredLeft, ha]
    rw [hempty] at ha'
    exact Finset.notMem_empty a ha'

end Overfull
