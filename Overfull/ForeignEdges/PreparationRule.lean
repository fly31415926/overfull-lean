import Overfull.SafePrescription.Adaptive

/-!
# A reusable certificate for safe preparation

This predicate is the full actual-graph conclusion of the proved safe
preparation theorem. It permits all four restart parameter choices to be
made before the graph and its exceptional order are supplied.
-/

namespace Overfull.ForeignEpochParameters

open Finset Classical MatchingProbability ForceMatching SafePrescription

/-- The uniform preparation guarantee, with its error and order already fixed. -/
def PreparationRule (α ν τ η : ℝ) (t0 : ℕ) (ε : ℝ) (n₀ : ℕ) : Prop :=
  ∀ (V I : Type*) [Fintype V] [Fintype I]
    (G : SimpleGraph V) (U : I → Finset V) (Z Z0 : Finset V)
    (c : V → Fin 4) (p : I → Fin 4) (H : ∀ i, SimpleGraph (U i))
    (h k0 : ℕ) (a : ℝ) (M : G.Subgraph),
    n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 →
    Pairwise (fun i j => Disjoint (U i) (U j)) →
    (∀ i, Disjoint (U i) Z) → Z0 ⊆ Z → Z0.card ≤ t0 →
    (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
    (∀ i v, v ∈ U i → c v = p i) →
    (∀ v, G.degree v = h) → α*Fintype.card V ≤ h →
    h ≤ k0 → (k0 : ℝ)/1024 < h →
    (∀ X : Finset V, ¬ IsOverfull G h X) →
    0 ≤ a → a+(Z.card : ℝ)+1 ≤ ε*Fintype.card V →
    (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
    (∀ i, H i ≤ G.induce (U i : Set V)) →
    (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
    (∀ i, IsRobustExpander (H i) ν τ) →
    (clusterCrossingEdges G c Z0).card ≤ 6*k0 →
    (∀ v ∈ Z, v ∉ Z0 →
      (((G.neighborFinset v).filter (fun w => w ∉ Z0 ∧ c w ≠ c v)).card : ℝ) ≤
        (k0 : ℝ)/1024000) →
    (∀ X : Finset V, X.card % 2 = 1 →
      (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤
        h+((2*(Z.card+t0+4096*(t0+6)+30) : ℕ) : ℝ) →
      ∀ i j, p i = p j → (coreMajority U X i ↔ coreMajority U X j)) →
    M.IsMatching →
    (∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z) →
    (∀ u v, M.Adj u v → c u = c v) →
    ∃ K B F : G.Subgraph,
      K.IsPerfectMatching ∧ ¬ FamilyFailure K h (wholeUnions (clusterSets c Z0) Z0) ∧
      B.IsMatching ∧ B ≤ K ∧ B.edgeSet.ncard ≤ 4096*(t0+6) ∧
      (∀ u v, B.Adj u v ↔ K.Adj u v ∧ (u ∈ Z0 ∨ v ∈ Z0 ∨ c u ≠ c v)) ∧
      F.IsMatching ∧ B ≤ F ∧ (Z : Set V) ⊆ F.verts ∧
      F.edgeSet.ncard ≤ 4096*(t0+6)+Z.card+3 ∧
      (∀ i, Even (((U i : Set V) \ F.verts).ncard)) ∧
      (∀ u v, F.Adj u v → B.Adj u v ∨ (u ∉ Z0 ∧ v ∉ Z0 ∧ c u = c v)) ∧
      (M.edgeSet \ F.edgeSet).ncard ≤ 2*(4096*(t0+6))+135720 ∧
      F.verts.ncard ≤ 2*(4096*(t0+6)+Z.card+3) ∧
      (∀ i, ((coveredCore (U i) G F).card : ℝ) ≤ η*(U i).card) ∧
      (∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v) ∧
      ∀ (N : G.Subgraph) (R : ∀ i, SimpleGraph (U i)),
        N.IsPerfectMatching → F ≤ N →
        (∀ v w, N.Adj v w → F.Adj v w ∨ ∃ i, v ∈ U i ∧ w ∈ U i) →
        (∀ i, R i ≤ (G \ N.spanningCoe).induce (U i : Set V)) →
        (∀ i, IsRobustExpander (R i) (ν/2) τ) →
        (∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ ((R i).degree v : ℝ)) →
        (M.edgeSet \ N.edgeSet).ncard ≤ 2*(4096*(t0+6))+4*135720 ∧
        (∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X)

structure SafeParameters (α ν τ η : ℝ) (t0 : ℕ) where
  error : ℝ
  order : ℕ
  error_pos : 0 < error
  rule : PreparationRule α ν τ η t0 error order

/-- The certificate is supplied by the proved safe-preparation theorem. -/
theorem exists_safe_parameters (α ν τ η : ℝ) (t0 : ℕ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α/1000) (hη : 0 < η) :
    Nonempty (SafeParameters α ν τ η t0) := by
  obtain ⟨ε, hε, n₀, h⟩ := prepare_safe_prescription α ν τ η t0
    hα hα1 hν hντ hτ hη
  exact ⟨⟨ε, n₀, hε, h⟩⟩

end Overfull.ForeignEpochParameters
