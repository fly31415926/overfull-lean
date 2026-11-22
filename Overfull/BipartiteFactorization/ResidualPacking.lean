import Overfull.BipartitePackingCorollaries
import Overfull.BipartiteRange

/-!
# Fixed bipartite packing with an arbitrarily small positive residual density

The original robust range is reduced using the actual minimum degree before
the adaptive bipartite packing theorem is applied. All constants precede the
graph and every prescribed forbidden-set family. The output retains the
actual unused graph and its exact degree accounting.
-/

namespace Overfull.BipartiteFactorization

open Finset Classical SimpleGraph
open BipartitePackingAccounting

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Actual disjoint matchings completing the supplied balanced footprints,
together with robustness of the graph left by their precise edge union. -/
structure BipartiteCorePacking (G : SimpleGraph (A ⊕ B)) (q : ℕ)
    (S : Fin q → Finset (A ⊕ B)) (θ σ : ℝ) where
  matching : Fin q → G.Subgraph
  isMatching : ∀ j, (matching j).IsMatching
  verts : ∀ j, (matching j).verts = (S j : Set (A ⊕ B))ᶜ
  disjoint : Pairwise (fun i j => Disjoint (matching i).spanningCoe (matching j).spanningCoe)
  robust : IsBipartiteRobustExpander
    (G \ edgeUnion (fun j => (matching j).spanningCoe) univ) θ σ

namespace BipartiteCorePacking

variable {G : SimpleGraph (A ⊕ B)} {q : ℕ}
  {S : Fin q → Finset (A ⊕ B)} {θ σ : ℝ}

/-- The complete unused core, including all unused reserve edges. -/
def remaining (P : BipartiteCorePacking G q S θ σ) : SimpleGraph (A ⊕ B) :=
  G \ edgeUnion (fun j => (P.matching j).spanningCoe) univ

/-- The actual unused graph remains a subgraph of the original core. -/
theorem remaining_le (P : BipartiteCorePacking G q S θ σ) : P.remaining ≤ G :=
  sdiff_le

theorem remaining_bipartite (P : BipartiteCorePacking G q S θ σ)
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) :
    P.remaining.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) :=
  ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj (P.remaining_le h)⟩

/-- Every omitted round contributes exactly its forbidden incidence to the
residual degree. The equality includes empty families and isolated vertices. -/
theorem degree_identity (P : BipartiteCorePacking G q S θ σ) (v : A ⊕ B) :
    P.remaining.degree v + q =
      G.degree v + (univ.filter (fun j : Fin q => v ∈ S j)).card := by
  have huse := matchingUnion_degree_add_missing G P.matching univ
    (fun j _ => P.isMatching j) (fun i _ j _ hij => P.disjoint hij) v
  have hmiss := missingCount_eq_forbidden G P.matching univ S (fun j _ => P.verts j) v
  have hremain := degree_sdiff_add_of_le G
    (edgeUnion (fun j => (P.matching j).spanningCoe) univ)
    (edgeUnion_le (fun j => (P.matching j).spanningCoe) univ G
      (fun j _ => (P.matching j).spanningCoe_le)) v
  rw [hmiss] at huse
  simp only [Finset.card_univ, Fintype.card_fin] at huse
  have hremain' : P.remaining.degree v +
      (edgeUnion (fun j => (P.matching j).spanningCoe) univ).degree v = G.degree v := by
    simpa only [remaining, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hremain
  have huse' : (edgeUnion (fun j => (P.matching j).spanningCoe) univ).degree v +
      (univ.filter (fun j : Fin q => v ∈ S j)).card = q := by
    convert huse using 1
    congr 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem degree_lower (P : BipartiteCorePacking G q S θ σ) (d a : ℝ)
    (hdegree : ∀ v, d - a ≤ G.degree v) (v : A ⊕ B) :
    d - q - a ≤ (P.remaining.degree v : ℝ) := by
  have h := P.degree_identity v
  have hreal : (P.remaining.degree v : ℝ) + q =
      G.degree v + (univ.filter (fun j : Fin q => v ∈ S j)).card := by exact_mod_cast h
  have hnonneg := Nat.cast_nonneg (α := ℝ) (univ.filter (fun j : Fin q => v ∈ S j)).card
  linarith [hdegree v]

theorem degree_upper (P : BipartiteCorePacking G q S θ σ) (d a b : ℝ)
    (hdegree : ∀ v, (G.degree v : ℝ) ≤ d + a)
    (hload : ∀ v, ((univ.filter (fun j : Fin q => v ∈ S j)).card : ℝ) ≤ b)
    (v : A ⊕ B) : (P.remaining.degree v : ℝ) ≤ d - q + a + b := by
  have h := P.degree_identity v
  have hreal : (P.remaining.degree v : ℝ) + q =
      G.degree v + (univ.filter (fun j : Fin q => v ∈ S j)).card := by exact_mod_cast h
  linarith [hdegree v, hload v]

/-- Original degree error and actual footprint load add in the remaining
graph. In particular, two bounds of `εm` give residual error `2εm`. -/
theorem degree_error (P : BipartiteCorePacking G q S θ σ) (d a b : ℝ)
    (hdegree : ∀ v, |(G.degree v : ℝ) - d| ≤ a)
    (hload : ∀ v, ((univ.filter (fun j : Fin q => v ∈ S j)).card : ℝ) ≤ b)
    (v : A ⊕ B) : |(P.remaining.degree v : ℝ) - (d - q)| ≤ a + b := by
  have hb : 0 ≤ b := (Nat.cast_nonneg _).trans (hload v)
  have hlower := P.degree_lower d a (fun w => by
    have hw := (abs_le.mp (hdegree w)).1
    linarith) v
  have hupper := P.degree_upper d a b (fun w => by
    have hw := (abs_le.mp (hdegree w)).2
    linarith) hload v
  apply abs_le.mpr
  constructor <;> linarith

/-- Deleting any subfamily, in particular any prefix, leaves the same
certified robust parameters. -/
theorem subfamily_robust (P : BipartiteCorePacking G q S θ σ) (T : Finset (Fin q)) :
    IsBipartiteRobustExpander
      (G \ edgeUnion (fun j => (P.matching j).spanningCoe) T) θ σ :=
  packing_remainder_robust_of_subfamily G P.matching θ σ P.robust T

end BipartiteCorePacking

/-- A finite prescribed family may be shorter than the whole packing
horizon. Empty future footprints preserve the exact total incidence count. -/
private theorem padded_incidence_card {V : Type*} (q Q : ℕ) (hq : q ≤ Q)
    (S : Fin q → Finset V) (v : V) :
    (univ.filter (fun i : Fin Q => v ∈
      (if h : i.val < q then S ⟨i.val, h⟩ else ∅))).card =
        (univ.filter (fun i : Fin q => v ∈ S i)).card := by
  classical
  let T : Finset (Fin Q) := univ.filter (fun i => v ∈
    (if h : i.val < q then S ⟨i.val, h⟩ else ∅))
  have hsmall (i : Fin Q) (hi : i ∈ T) : i.val < q := by
    have hv := (Finset.mem_filter.mp hi).2
    by_contra hn
    simp only [dif_neg hn, Finset.notMem_empty] at hv
  apply Finset.card_bij (fun i hi => (⟨i.val, hsmall i hi⟩ : Fin q))
  · intro i hi
    have hv := (Finset.mem_filter.mp hi).2
    simp only [dif_pos (hsmall i hi)] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin q => k.val) hij)
  · intro j hj
    refine ⟨Fin.castLE hq j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Fin.coe_castLE, dif_pos j.isLt] using (Finset.mem_filter.mp hj).2
    · rfl

/-- Uniform fixed-footprint bipartite packing for every positive reserve
fraction `γ`. The range needed by the packing theorem is obtained from the
actual degree bounds, rather than assumed for the original graph.

The original range may be as large as `α/16`; the positive output range
`σ ≤ τ` and every other constant are fixed before the graph and the number
or location of the forbidden footprints. -/
theorem pack_fixed_bipartite_forbidden_sets (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 16) :
    ∃ ε θ σ : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < σ ∧ σ ≤ τ ∧ ∃ m₀ : ℕ,
      ∀ (A B : Type*) [Fintype A] [Fintype B]
        (G : SimpleGraph (A ⊕ B)) (d : ℝ),
        G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        IsBipartiteRobustExpander G ν τ → α * Fintype.card A ≤ d →
        (∀ v, |(G.degree v : ℝ) - d| ≤ ε * Fintype.card A) →
        ∀ (q : ℕ) (S : Fin q → Finset (A ⊕ B)),
          q ≤ Nat.floor (d - γ * Fintype.card A) →
          (∀ j, (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ S j)).card =
            (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ S j)).card) →
          (∀ j, ((S j).card : ℝ) ≤ ε * Fintype.card A) →
          (∀ v, ((univ.filter (fun j : Fin q => v ∈ S j)).card : ℝ) ≤
            ε * Fintype.card A) →
          Nonempty (BipartiteCorePacking G q S θ σ) := by
  classical
  let p : ℝ := γ / 16
  let σ : ℝ := min τ (p * α / 200) / 2
  let μ : ℝ := min ν ((α / 2) * σ / 4)
  have hp : 0 < p := by dsimp [p]; positivity
  have hpγ : p < γ / 8 := by dsimp [p]; linarith
  have hτpos : 0 < τ := hν.trans_le hντ
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hστ : σ ≤ τ := by
    have hh := min_le_left τ (p * α / 200)
    dsimp only [σ]
    linarith
  have hσsmall : σ < p * α / 100 := by
    have hh := min_le_right τ (p * α / 200)
    have hpa : 0 < p * α := mul_pos hp hα
    dsimp only [σ]
    linarith
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμσ : μ ≤ σ := by
    have hh := min_le_right ν ((α / 2) * σ / 4)
    have haσ : α * σ < σ := by nlinarith
    dsimp only [μ]
    nlinarith
  obtain ⟨ε₀, hε₀, m₀, hpack⟩ := bipartite_matching_packing α γ p μ σ
    hα hα1 hγ hγ1 hp hpγ hμ hμσ hσsmall
  let ε : ℝ := min ε₀ (α / 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεα : ε ≤ α / 2 := min_le_right _ _
  refine ⟨ε, p * μ / 4, σ, hε, by positivity, hσ, hστ, m₀, ?_⟩
  intro A B _ _ G d hbip hbalance hm hrob hd hdegree q S hq hbalanced hsize hload
  have herr (v : A ⊕ B) : |(G.degree v : ℝ) - d| ≤ ε₀ * Fintype.card A :=
    (hdegree v).trans (mul_le_mul_of_nonneg_right hε₀le (Nat.cast_nonneg _))
  have hminimum (v : A ⊕ B) : (α / 2) * Fintype.card A ≤ (G.degree v : ℝ) := by
    have hh := (abs_le.mp (hdegree v)).1
    have hmul := mul_le_mul_of_nonneg_right hεα (Nat.cast_nonneg (Fintype.card A))
    linarith
  have hleft (a : A) : (α / 2) * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ) := by
    have heq : (rightNeighbors G a).card = G.degree (.inl a) :=
      RandomReserve.crossingDegree_eq_degree G hbip (.inl a)
    rw [heq]
    exact hminimum _
  have hright (b : B) : (α / 2) * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ) := by
    have heq : (leftNeighbors G b).card = G.degree (.inr b) :=
      RandomReserve.crossingDegree_eq_degree G hbip (.inr b)
    rw [heq]
    exact hminimum _
  have hreduced : IsBipartiteRobustExpander G μ σ :=
    bipartite_robust_range_reduction G (α / 2) ν τ σ hν hντ
      (by linarith) (by linarith) hσ hστ hbalance hleft hright hrob
  let input : ℕ → Finset (A ⊕ B) :=
    fun j => if h : j < q then S ⟨j, h⟩ else ∅
  have hinput (j : Fin q) : input j.val = S j := by simp only [input, dif_pos j.isLt]
  have hinputBalanced (j : ℕ) :
      (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ input j)).card =
      (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ input j)).card := by
    by_cases hj : j < q
    · simpa only [input, dif_pos hj] using hbalanced ⟨j, hj⟩
    · simp only [input, dif_neg hj, Finset.notMem_empty, Finset.filter_false, Finset.card_empty]
  have hinputSize (j : ℕ) : ((input j).card : ℝ) ≤ ε₀ * Fintype.card A := by
    by_cases hj : j < q
    · rw [show input j = S ⟨j, hj⟩ from hinput ⟨j, hj⟩]
      exact (hsize ⟨j, hj⟩).trans
        (mul_le_mul_of_nonneg_right hε₀le (Nat.cast_nonneg _))
    · simp only [input, dif_neg hj, Finset.card_empty, Nat.cast_zero]
      positivity
  have hinputLoad (v : A ⊕ B) :
      ((univ.filter (fun j : Fin (Nat.floor (d - γ * Fintype.card A)) =>
        v ∈ input j.val)).card : ℝ) ≤ ε₀ * Fintype.card A := by
    rw [show (univ.filter (fun j : Fin (Nat.floor (d - γ * Fintype.card A)) =>
      v ∈ input j.val)).card = (univ.filter (fun j : Fin q => v ∈ S j)).card from
        by
          convert padded_incidence_card q _ hq S v using 1
          all_goals
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, input]]
    exact (hload v).trans (mul_le_mul_of_nonneg_right hε₀le (Nat.cast_nonneg _))
  obtain ⟨M, hM, hverts, hdisjoint, hremaining⟩ :=
    hpack A B G d hbip hbalance hm hreduced hd herr input
      (fun j _ => hinputBalanced j) (fun j _ => hinputSize j) hinputLoad
  let N : Fin q → G.Subgraph := fun j => M (Fin.castLE hq j)
  refine ⟨⟨N, (fun j => hM (Fin.castLE hq j)), ?_, ?_, ?_⟩⟩
  · intro j
    simpa only [N, Fin.coe_castLE, hinput] using hverts (Fin.castLE hq j)
  · intro i j hij
    apply hdisjoint
    intro hh
    apply hij
    exact Fin.ext (congrArg (fun k : Fin (Nat.floor (d - γ * Fintype.card A)) => k.val) hh)
  · apply (hremaining univ).mono_graph _ _
    intro v w hvw
    refine ⟨hvw.1, ?_⟩
    rintro ⟨j, _, hj⟩
    exact hvw.2 ⟨Fin.castLE hq j, Finset.mem_univ _, hj⟩

end Overfull.BipartiteFactorization
