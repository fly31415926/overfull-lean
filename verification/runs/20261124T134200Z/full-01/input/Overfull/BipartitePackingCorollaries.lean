import Overfull.BipartitePacking

/-!
# Matching sequences from adaptive packing

These forms of the theorem have explicit forbidden sets and matching
sequences in their statements. In particular, taking every forbidden set
empty gives the edge-disjoint perfect matchings asserted after Theorem 2.16.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

/-- If the remainder after removing the whole matching family is robust,
then the remainder after removing any subfamily is robust. In particular,
this applies to every initial segment of the packing. -/
theorem packing_remainder_robust_of_subfamily
    {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (G : SimpleGraph (A ⊕ B)) (M : I → G.Subgraph) (ν τ : ℝ)
    (hrob : IsBipartiteRobustExpander
      (G \ BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) univ) ν τ)
    (T : Finset I) :
    IsBipartiteRobustExpander
      (G \ BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) T) ν τ := by
  classical
  apply hrob.mono_graph _ _
  intro v w hvw
  refine ⟨hvw.1, ?_⟩
  rintro ⟨i, _, hi⟩
  exact hvw.2 ⟨i, Finset.mem_univ _, hi⟩

/-- A prescribed sequence of balanced forbidden sets admits edge-disjoint
matchings perfect outside their respective sets. The remainder is robust
after removing any subfamily, and hence after each prefix. -/
theorem bipartite_matching_packing (α γ p ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hp : 0 < p) (hpγ : p < γ / 8) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ < p * α / 100) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (A B : Type*) [Fintype A] [Fintype B]
        (G : SimpleGraph (A ⊕ B)) (Δ : ℝ),
        G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        IsBipartiteRobustExpander G ν τ → α * Fintype.card A ≤ Δ →
        (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) →
        ∀ S : ℕ → Finset (A ⊕ B),
          (∀ i < Nat.floor (Δ - γ * Fintype.card A),
            (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ S i)).card =
            (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ S i)).card) →
          (∀ i < Nat.floor (Δ - γ * Fintype.card A),
            ((S i).card : ℝ) ≤ ε * Fintype.card A) →
          (∀ v, (((univ : Finset (Fin (Nat.floor (Δ - γ * Fintype.card A)))).filter
            (fun i => v ∈ S i.val)).card : ℝ) ≤ ε * Fintype.card A) →
          ∃ M : Fin (Nat.floor (Δ - γ * Fintype.card A)) → G.Subgraph,
            (∀ i, (M i).IsMatching) ∧
            (∀ i, (M i).verts = (S i.val : Set (A ⊕ B))ᶜ) ∧
            Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
            ∀ T : Finset (Fin (Nat.floor (Δ - γ * Fintype.card A))),
              IsBipartiteRobustExpander
                (G \ BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) T)
                (p * ν / 4) τ := by
  classical
  obtain ⟨ε, hε, m₀, hpacking⟩ := adaptive_bipartite_packing α γ p ν τ
    hα hα1 hγ hγ1 hp hpγ hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro A B _ _ G Δ hbip hbalance hm hrob hΔ hdegree S hbalanced hsize hincidences
  obtain ⟨rule, hstrategy⟩ := hpacking A B G Δ hbip hbalance hm hrob hΔ hdegree
  let q := Nat.floor (Δ - γ * Fintype.card A)
  let adversary := fun (s : ℕ) (_ : Fin s → Finset (A ⊕ B) × G.Subgraph) => S s
  have hinput (s : ℕ) (i : Fin s) :
      (BipartitePackingOnline.history rule adversary s i).1 = S i.val :=
    BipartitePackingOnline.run_input rule S s i
  have hallowed : ∀ s < q, BipartitePackingStrategy.Allowed G (Fintype.card A) ε s
      (BipartitePackingOnline.history rule adversary s)
      (adversary s (BipartitePackingOnline.history rule adversary s)) := by
    intro s hs
    refine ⟨?_, hsize s hs, ?_⟩
    · exact hbalanced s hs
    · intro v
      have heq : (univ.filter (fun i : Fin s =>
          v ∈ (BipartitePackingOnline.history rule adversary s i).1)) =
          univ.filter (fun i : Fin s => v ∈ S i.val) := by
        ext i
        simp only [Finset.mem_filter, hinput]
      rw [heq]
      have hcard : (univ.filter (fun i : Fin s => v ∈ S i.val)).card ≤
          (univ.filter (fun i : Fin q => v ∈ S i.val)).card := by
        apply Finset.card_le_card_of_injOn (Fin.castLE (Nat.le_of_lt hs))
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        · intro i _ j _ hij
          exact Fin.ext (congrArg (fun k : Fin q => k.val) hij)
      exact (by exact_mod_cast hcard :
        ((univ.filter (fun i : Fin s => v ∈ S i.val)).card : ℝ) ≤
          (univ.filter (fun i : Fin q => v ∈ S i.val)).card).trans (hincidences v)
  obtain ⟨hH, hremaining⟩ := hstrategy adversary hallowed q le_rfl
  let M : Fin q → G.Subgraph :=
    fun i => (BipartitePackingOnline.history rule adversary q i).2
  refine ⟨M, hH.1, ?_, hH.2.2,
    fun T => packing_remainder_robust_of_subfamily G M (p * ν / 4) τ hremaining T⟩
  intro i
  have hi := hH.2.1 i
  rw [hinput] at hi
  exact hi

/-- The empty-forbidden-set case of Theorem 2.16 gives
`max(0, floor(Δ - γm))` actual pairwise edge-disjoint perfect matchings,
such that removing any subfamily leaves a bipartite robust `(pν/4, τ)`-expander. -/
theorem bipartite_perfect_matching_packing (α γ p ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hp : 0 < p) (hpγ : p < γ / 8) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ < p * α / 100) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (A B : Type*) [Fintype A] [Fintype B]
        (G : SimpleGraph (A ⊕ B)) (Δ : ℝ),
        G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        IsBipartiteRobustExpander G ν τ → α * Fintype.card A ≤ Δ →
        (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) →
        ∃ M : Fin (Nat.floor (Δ - γ * Fintype.card A)) → G.Subgraph,
          (∀ i, (M i).IsPerfectMatching) ∧
          Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
          ∀ T : Finset (Fin (Nat.floor (Δ - γ * Fintype.card A))),
            IsBipartiteRobustExpander
              (G \ BipartitePackingAccounting.edgeUnion (fun i => (M i).spanningCoe) T)
              (p * ν / 4) τ := by
  classical
  obtain ⟨ε, hε, m₀, hpacking⟩ := bipartite_matching_packing α γ p ν τ
    hα hα1 hγ hγ1 hp hpγ hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro A B _ _ G Δ hbip hbalance hm hrob hΔ hdegree
  obtain ⟨M, hM, hverts, hdisjoint, hremaining⟩ :=
    hpacking A B G Δ hbip hbalance hm hrob hΔ hdegree (fun _ => ∅)
      (by intros; simp) (by intros; simpa using mul_nonneg hε.le (Nat.cast_nonneg (Fintype.card A)))
      (by intro v; simpa using mul_nonneg hε.le (Nat.cast_nonneg (Fintype.card A)))
  refine ⟨M, ?_, hdisjoint, hremaining⟩
  intro i
  refine ⟨hM i, Subgraph.isSpanning_iff.mpr ?_⟩
  simpa using hverts i

end Overfull
