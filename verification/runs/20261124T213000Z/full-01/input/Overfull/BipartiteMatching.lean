import Overfull.RobustExpansion
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# A perfect matching in a balanced bipartite robust expander

The two vertex classes are represented by the two summands. Only actual
crossing edges of `G` are used. The conclusion is mathlib's perfect matching.
-/

namespace Overfull

open Finset

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

def rightNeighbors (a : A) : Finset B :=
  univ.filter (fun b => G.Adj (.inl a) (.inr b))

def leftNeighbors (b : B) : Finset A :=
  univ.filter (fun a => G.Adj (.inl a) (.inr b))

noncomputable def bipartiteRobustNeighbors (ν : ℝ) (S : Finset A) : Finset B := by
  classical
  exact univ.filter (fun b => ν * Fintype.card A ≤
    ((S ∩ leftNeighbors G b).card : ℝ))

noncomputable def IsBipartiteRobustExpander (ν τ : ℝ) : Prop :=
  ∀ S : Finset A,
    τ * Fintype.card A ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * Fintype.card A →
    (S.card : ℝ) + ν * Fintype.card A ≤
      (bipartiteRobustNeighbors G ν S).card

theorem bipartite_robust_hall (ν τ : ℝ) (hν : 0 < ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, τ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, τ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G ν τ) :
    ∀ S : Finset A, S.card ≤ (S.biUnion (rightNeighbors G)).card := by
  classical
  intro S
  by_cases hS : S.Nonempty
  · have hm : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr hS) (Finset.card_le_univ S)
    by_cases hsmall : (S.card : ℝ) ≤ τ * Fintype.card A
    · obtain ⟨a, ha⟩ := hS
      have hsub : rightNeighbors G a ⊆ S.biUnion (rightNeighbors G) := by
        intro b hb
        exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
      have hs : S.card ≤ (rightNeighbors G a).card := by
        exact_mod_cast hsmall.trans (hleft a)
      exact hs.trans (Finset.card_le_card hsub)
    · by_cases hmiddle : (S.card : ℝ) ≤ (1 - τ) * Fintype.card A
      · have hex := hexpand S (le_of_not_ge hsmall) hmiddle
        have hsub : bipartiteRobustNeighbors G ν S ⊆ S.biUnion (rightNeighbors G) := by
          intro b hb
          have hcount : ν * Fintype.card A ≤ ((S ∩ leftNeighbors G b).card : ℝ) := by
            simpa [bipartiteRobustNeighbors] using hb
          have hpos : 0 < (S ∩ leftNeighbors G b).card := by
            exact_mod_cast lt_of_lt_of_le (mul_pos hν hm) hcount
          obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
          rcases Finset.mem_inter.mp ha with ⟨haS, haG⟩
          apply Finset.mem_biUnion.mpr
          refine ⟨a, haS, ?_⟩
          simpa [leftNeighbors, rightNeighbors] using haG
        have hs : S.card ≤ (bipartiteRobustNeighbors G ν S).card := by
          have hnonneg : (0 : ℝ) ≤ ν * Fintype.card A := (mul_pos hν hm).le
          have hr : (S.card : ℝ) ≤ (bipartiteRobustNeighbors G ν S).card := by linarith
          exact_mod_cast hr
        exact hs.trans (Finset.card_le_card hsub)
      · have hlarge := lt_of_not_ge hmiddle
        have hall : S.biUnion (rightNeighbors G) = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro b
          by_contra hb
          have hsub : leftNeighbors G b ⊆ Finset.univ \ S := by
            intro a ha
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
            intro haS
            apply hb
            apply Finset.mem_biUnion.mpr
            refine ⟨a, haS, ?_⟩
            simpa [leftNeighbors, rightNeighbors] using ha
          have hc := Finset.card_le_card hsub
          have ht : (Finset.univ \ S).card + S.card = Fintype.card A := by
            simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
          have hn : (leftNeighbors G b).card + S.card ≤ Fintype.card A := by omega
          have hnR : ((leftNeighbors G b).card : ℝ) + S.card ≤ Fintype.card A := by
            exact_mod_cast hn
          have hdeg := hright b
          linarith
        rw [hall, Finset.card_univ, ← hbalance]
        exact Finset.card_le_univ S
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hempty]

theorem bipartite_robust_bijection (ν τ : ℝ) (hν : 0 < ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, τ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, τ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G ν τ) :
    ∃ f : A → B, Function.Bijective f ∧ ∀ a, G.Adj (.inl a) (.inr (f a)) := by
  classical
  obtain ⟨f, hinj, hadj⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (rightNeighbors G)).mp
      (bipartite_robust_hall G ν τ hν hbalance hleft hright hexpand)
  refine ⟨f, ?_, ?_⟩
  · exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hbalance⟩
  · intro a
    simpa [rightNeighbors] using hadj a

private def matchingOfBijection (f : A → B)
    (hadj : ∀ a, G.Adj (.inl a) (.inr (f a))) : G.Subgraph where
  verts := Set.univ
  Adj v w := match v, w with
    | .inl a, .inr b => f a = b
    | .inr b, .inl a => f a = b
    | _, _ => False
  adj_sub := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl a' => exact False.elim h
      | inr b => exact h ▸ hadj a
    | inr b =>
      cases w with
      | inl a => exact h ▸ (hadj a).symm
      | inr b' => exact False.elim h
  edge_vert := by intro _ _ _; trivial
  symm := by intro v w h; cases v <;> cases w <;> exact h

theorem bipartite_robust_perfect_matching (ν τ : ℝ) (hν : 0 < ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, τ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, τ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G ν τ) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨f, hf, hadj⟩ := bipartite_robust_bijection G ν τ hν hbalance hleft hright hexpand
  refine ⟨matchingOfBijection G f hadj, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  cases v with
  | inl a =>
    refine ⟨.inr (f a), rfl, ?_⟩
    intro w hw
    cases w with
    | inl a' => exact False.elim hw
    | inr b =>
      change f a = b at hw
      exact congrArg Sum.inr hw.symm
  | inr b =>
    obtain ⟨a, rfl⟩ := hf.2 b
    refine ⟨.inl a, rfl, ?_⟩
    intro w hw
    cases w with
    | inl a' => exact congrArg Sum.inl (hf.1 hw)
    | inr b' => exact False.elim hw

end Overfull
