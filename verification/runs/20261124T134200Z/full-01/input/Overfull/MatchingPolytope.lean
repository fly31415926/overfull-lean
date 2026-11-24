import Overfull.External.PerfectBMatching
import Overfull.Multigraph
import Mathlib.Analysis.Convex.Combination

/-!
# The matching polytope for finite loopless multigraphs

Individual edge copies are indexed by a finite type. The two endpoint maps
may give the same pair to different edge copies, so parallel edges are retained.
The degree inequalities are reduced to perfect-matching degree equations by
using two copies of the graph and an edge between the two copies of each vertex.
-/

namespace Overfull.MatchingPolytope

open Finset Classical Lovasz.BMatch
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The degree and odd-set inequalities of the matching polytope. -/
def fractional (u v : E → V) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ w, dsum u v univ x w ≤ 1) ∧
    ∀ X : Finset V, Odd X.card →
      2 * ∑ e ∈ inside u v univ X, x e ≤ (X.card : ℝ) - 1}

/-- Integral edge vectors with at most one chosen edge at any vertex. -/
def integral (u v : E → V) : Set (E → ℝ) :=
  {z | (∀ e, z e = 0 ∨ z e = 1) ∧ ∀ w, dsum u v univ z w ≤ 1}

omit [Fintype V] in
theorem fractional_degree_nonneg {u v : E → V} {x : E → ℝ}
    (hx : x ∈ fractional u v) (w : V) : 0 ≤ dsum u v univ x w :=
  Finset.sum_nonneg (fun e _ => hx.1 e)

theorem fractional_inside_bound {u v : E → V} (hloop : ∀ e, u e ≠ v e)
    {x : E → ℝ} (hx : x ∈ fractional u v) (X : Finset V) :
    2 * ∑ e ∈ inside u v univ X, x e ≤ (X.card : ℝ) := by
  have hhand := handshake u v univ (fun e _ => hloop e) X x
  have hdeg : (∑ w ∈ X, dsum u v univ x w) ≤ (X.card : ℝ) := by
    calc
      _ ≤ ∑ _w ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun w _ => hx.2.1 w)
      _ = _ := by simp
  have hcut : 0 ≤ ∑ e ∈ cut u v univ X, x e :=
    Finset.sum_nonneg (fun e _ => hx.1 e)
  linarith

def doubledFirst (u : E → V) : (E × Bool) ⊕ V → V × Bool
  | .inl (e, b) => (u e, b)
  | .inr w => (w, false)

def doubledSecond (v : E → V) : (E × Bool) ⊕ V → V × Bool
  | .inl (e, b) => (v e, b)
  | .inr w => (w, true)

noncomputable def doubledWeight (u v : E → V) (x : E → ℝ) : (E × Bool) ⊕ V → ℝ
  | .inl (e, _) => x e
  | .inr w => 1 - dsum u v univ x w

omit [Fintype V] [Fintype E] in
theorem doubled_loopless {u v : E → V} (hloop : ∀ e, u e ≠ v e)
    (e : (E × Bool) ⊕ V) : doubledFirst u e ≠ doubledSecond v e := by
  cases e with
  | inl e => exact fun h => hloop e.1 (congrArg Prod.fst h)
  | inr w => simp [doubledFirst, doubledSecond]

omit [Fintype V] in
theorem doubled_nonneg {u v : E → V} {x : E → ℝ}
    (hx : x ∈ fractional u v) (e : (E × Bool) ⊕ V) :
    0 ≤ doubledWeight u v x e := by
  cases e with
  | inl e => exact hx.1 e.1
  | inr w => exact sub_nonneg.mpr (hx.2.1 w)

theorem doubled_degree (u v : E → V) (x : E → ℝ) (w : V × Bool) :
    dsum (doubledFirst u) (doubledSecond v) univ (doubledWeight u v x) w = 1 := by
  rcases w with ⟨w, b⟩
  cases b <;>
    simp [dsum, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type,
      doubledFirst, doubledSecond, doubledWeight, Prod.mk.injEq]

/-- The vertices selected in just the first or just the second copy. -/
noncomputable def firstOnly (U : Finset (V × Bool)) : Finset V :=
  univ.filter (fun w => (w, false) ∈ U ∧ (w, true) ∉ U)

noncomputable def secondOnly (U : Finset (V × Bool)) : Finset V :=
  univ.filter (fun w => (w, true) ∈ U ∧ (w, false) ∉ U)

noncomputable def bothCopies (U : Finset (V × Bool)) : Finset V :=
  univ.filter (fun w => (w, false) ∈ U ∧ (w, true) ∈ U)

theorem doubled_set_card (U : Finset (V × Bool)) :
    U.card = (firstOnly U).card + (secondOnly U).card + 2 * (bothCopies U).card := by
  have hU : U = univ.filter (fun w => w ∈ U) := by ext w; simp
  conv_lhs => rw [hU, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, firstOnly, secondOnly, bothCopies,
    Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h0 : (w, false) ∈ U <;> by_cases h1 : (w, true) ∈ U <;> simp [h0, h1]

noncomputable def copySet (U : Finset (V × Bool)) (b : Bool) : Finset V :=
  univ.filter (fun w => (w, b) ∈ U)

theorem firstOnly_eq_sdiff (U : Finset (V × Bool)) :
    firstOnly U = copySet U false \ copySet U true := by
  ext w
  simp [firstOnly, copySet]

theorem secondOnly_eq_sdiff (U : Finset (V × Bool)) :
    secondOnly U = copySet U true \ copySet U false := by
  ext w
  simp [secondOnly, copySet]

omit [Fintype V] in
/-- The weighted cut function satisfies the difference-set form of
submodularity for every nonnegative edge weighting. -/
theorem cut_posimodular (u v : E → V) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e)
    (A B : Finset V) :
    (∑ e ∈ cut u v univ (A \ B), x e) + (∑ e ∈ cut u v univ (B \ A), x e) ≤
      (∑ e ∈ cut u v univ A, x e) + (∑ e ∈ cut u v univ B, x e) := by
  simp only [cut, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := hx e
  by_cases h1 : u e ∈ A <;> by_cases h2 : u e ∈ B <;>
    by_cases h3 : v e ∈ A <;> by_cases h4 : v e ∈ B <;>
    simp [h1, h2, h3, h4] <;> linarith

theorem doubled_cut_sum (u v : E → V) (x : E → ℝ) (U : Finset (V × Bool)) :
    (∑ e ∈ cut (doubledFirst u) (doubledSecond v) univ U, doubledWeight u v x e) =
      (∑ e ∈ cut u v univ (copySet U false), x e) +
      (∑ e ∈ cut u v univ (copySet U true), x e) +
      (firstOnly U).card + (secondOnly U).card -
      (∑ w ∈ firstOnly U, dsum u v univ x w) -
      (∑ w ∈ secondOnly U, dsum u v univ x w) := by
  have hvert (w : V) :
      (if ((w, false) ∈ U) ≠ ((w, true) ∈ U) then 1 - dsum u v univ x w else 0) =
      (if w ∈ firstOnly U then 1 - dsum u v univ x w else 0) +
      (if w ∈ secondOnly U then 1 - dsum u v univ x w else 0) := by
    by_cases h0 : (w, false) ∈ U <;> by_cases h1 : (w, true) ∈ U <;>
      simp [firstOnly, secondOnly, h0, h1]
  have hvsum : (∑ w : V,
      if ((w, false) ∈ U) ≠ ((w, true) ∈ U) then 1 - dsum u v univ x w else 0) =
      ((firstOnly U).card : ℝ) + (secondOnly U).card -
      (∑ w ∈ firstOnly U, dsum u v univ x w) -
      (∑ w ∈ secondOnly U, dsum u v univ x w) := by
    simp_rw [hvert]
    rw [Finset.sum_add_distrib]
    simp only [← Finset.sum_filter]
    have hP : univ.filter (fun w => w ∈ firstOnly U) = firstOnly U := by ext w; simp
    have hQ : univ.filter (fun w => w ∈ secondOnly U) = secondOnly U := by ext w; simp
    rw [hP, hQ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  unfold cut
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubledFirst, doubledSecond,
    doubledWeight, Finset.sum_add_distrib]
  rw [hvsum]
  simp only [Finset.sum_filter, copySet, Finset.mem_filter, Finset.mem_univ, true_and]
  ring

/-- Odd sets in the doubled graph satisfy the perfect-matching cut inequality. -/
theorem doubled_odd_cut {u v : E → V} (hloop : ∀ e, u e ≠ v e)
    {x : E → ℝ} (hx : x ∈ fractional u v) (U : Finset (V × Bool))
    (hU : Odd U.card) :
    1 ≤ ∑ e ∈ cut (doubledFirst u) (doubledSecond v) univ U,
      doubledWeight u v x e := by
  let P := firstOnly U
  let Q := secondOnly U
  have hPQodd : (P.card + Q.card) % 2 = 1 := by
    have hcard := doubled_set_card U
    have hodd := Nat.odd_iff.mp hU
    change (P.card + Q.card) % 2 = 1
    dsimp [P, Q]
    omega
  have hP := fractional_inside_bound hloop hx P
  have hQ := fractional_inside_bound hloop hx Q
  have hinside : 2 * (∑ e ∈ inside u v univ P, x e) +
      2 * (∑ e ∈ inside u v univ Q, x e) ≤ (P.card : ℝ) + Q.card - 1 := by
    by_cases hodd : P.card % 2 = 1
    · have hp := hx.2.2 P (Nat.odd_iff.mpr hodd)
      linarith
    · have hoddQ : Q.card % 2 = 1 := by omega
      have hq := hx.2.2 Q (Nat.odd_iff.mpr hoddQ)
      linarith
  have hpdeg := handshake u v univ (fun e _ => hloop e) P x
  have hqdeg := handshake u v univ (fun e _ => hloop e) Q x
  have hcut := cut_posimodular u v x hx.1 (copySet U false) (copySet U true)
  rw [← firstOnly_eq_sdiff, ← secondOnly_eq_sdiff] at hcut
  rw [doubled_cut_sum]
  change (1 : ℝ) ≤ _ + _ + P.card + Q.card - _ - _
  linarith

theorem doubled_mem_perfect_polytope {u v : E → V} (hloop : ∀ e, u e ≠ v e)
    {x : E → ℝ} (hx : x ∈ fractional u v) :
    doubledWeight u v x ∈ PS (doubledFirst u) (doubledSecond v) univ
      (fun _ : V × Bool => 1) := by
  refine ⟨doubled_nonneg hx, ?_, ?_, ?_⟩
  · intro e he
    exact False.elim (he (Finset.mem_univ e))
  · intro w
    simpa only [Nat.cast_one] using doubled_degree u v x w
  · intro U hU
    apply doubled_odd_cut hloop hx U
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] using hU

theorem projected_degree (u v : E → V) (z : (E × Bool) ⊕ V → ℝ) (w : V) :
    dsum (doubledFirst u) (doubledSecond v) univ z (w, false) =
      dsum u v univ (fun e => z (.inl (e, false))) w + z (.inr w) := by
  simp [dsum, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type,
    doubledFirst, doubledSecond, Prod.mk.injEq]

/-- Every fractional matching is a convex combination of integral matchings. -/
theorem fractional_subset_convexHull_integral (u v : E → V)
    (hloop : ∀ e, u e ≠ v e) :
    fractional u v ⊆ convexHull ℝ (integral u v) := by
  intro x hx
  have hgood : Good (doubledFirst u) (doubledSecond v) univ
      (fun _ : V × Bool => 1) :=
    ⟨fun e _ => doubled_loopless hloop e, fun _ _ => Or.inl rfl⟩
  have hconv := thmA _ (doubledFirst u) (doubledSecond v) univ
    (fun _ : V × Bool => 1) rfl hgood (doubled_mem_perfect_polytope hloop hx)
  let projection : ((E × Bool) ⊕ V → ℝ) →ₗ[ℝ] (E → ℝ) :=
    LinearMap.funLeft ℝ ℝ (fun e => Sum.inl (e, false))
  have hprojection : projection (doubledWeight u v x) = x := rfl
  rw [← hprojection]
  have hmem : projection (doubledWeight u v x) ∈
      projection '' convexHull ℝ (IS (doubledFirst u) (doubledSecond v) univ
        (fun _ : V × Bool => 1)) := Set.mem_image_of_mem _ hconv
  rw [LinearMap.image_convexHull] at hmem
  refine convexHull_mono ?_ hmem
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨fun e => hz.1 (.inl (e, false)), fun w => ?_⟩
  have hdeg := hz.2.2 (w, false)
  rw [projected_degree] at hdeg
  have hnonneg : 0 ≤ z (.inr w) := by rcases hz.1 (.inr w) with h | h <;> simp [h]
  change dsum u v univ (fun e => z (.inl (e, false))) w ≤ 1
  norm_num only [Nat.cast_one] at hdeg
  linarith

omit [Fintype V] in
/-- The defining inequalities are preserved by convex combinations. -/
theorem convex_fractional (u v : E → V) : Convex ℝ (fractional u v) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change 0 ≤ a * x e + b * y e
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · intro w
    have hlin : dsum u v univ (a • x + b • y) w =
        a * dsum u v univ x w + b * dsum u v univ y w := by
      simp [dsum, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hlin]
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 w) ha)
        (mul_le_mul_of_nonneg_left (hy.2.1 w) hb)
      _ = 1 := by simpa using hab
  · intro X hX
    have hlin : (∑ e ∈ inside u v univ X, (a • x + b • y) e) =
        a * (∑ e ∈ inside u v univ X, x e) +
        b * (∑ e ∈ inside u v univ X, y e) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hlin]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 X hX) ha)
      (mul_le_mul_of_nonneg_left (hy.2.2 X hX) hb)
    nlinarith [mul_eq_mul_right_iff.mp (congrArg (fun t : ℝ => t * ((X.card : ℝ) - 1)) hab)]

/-- A zero-one vector of degree at most one satisfies every odd-set inequality. -/
theorem integral_subset_fractional (u v : E → V) (hloop : ∀ e, u e ≠ v e) :
    integral u v ⊆ fractional u v := by
  intro z hz
  have hznonneg : ∀ e, 0 ≤ z e := by
    intro e
    rcases hz.1 e with h | h <;> simp [h]
  refine ⟨hznonneg, hz.2, ?_⟩
  intro X hX
  let N := ((inside u v univ X).filter (fun e => z e = 1)).card
  have hsum : (∑ e ∈ inside u v univ X, z e) = (N : ℝ) := by
    calc
      _ = ∑ e ∈ inside u v univ X, if z e = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        rcases hz.1 e with h | h <;> simp [h]
      _ = _ := by simp [N]
  have hhand := handshake u v univ (fun e _ => hloop e) X z
  have hdeg : (∑ w ∈ X, dsum u v univ z w) ≤ (X.card : ℝ) := by
    calc
      _ ≤ ∑ _w ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun w _ => hz.2 w)
      _ = _ := by simp
  have hcut : 0 ≤ ∑ e ∈ cut u v univ X, z e :=
    Finset.sum_nonneg (fun e _ => hznonneg e)
  have hbound : (2 : ℝ) * N ≤ X.card := by linarith
  have hboundNat : 2 * N ≤ X.card := by exact_mod_cast hbound
  have hodd := Nat.odd_iff.mp hX
  have hstrict : 2 * N + 1 ≤ X.card := by omega
  have hstrictReal : (2 : ℝ) * N + 1 ≤ X.card := by exact_mod_cast hstrict
  rw [hsum]
  linarith

/-- Edmonds' matching-polytope theorem for finitely many edge copies. -/
theorem matching_polytope (u v : E → V) (hloop : ∀ e, u e ≠ v e) :
    convexHull ℝ (integral u v) = fractional u v := by
  exact Set.Subset.antisymm
    (convexHull_min (integral_subset_fractional u v hloop) (convex_fractional u v))
    (fractional_subset_convexHull_integral u v hloop)

end Overfull.MatchingPolytope

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

/-- A matching is an edge-copy set whose distinct edges have no common vertex. -/
def IsMatching (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, ∀ w : V, w ∈ G.edge e → w ∈ G.edge f → e = f

theorem isMatching_iff_incident_card_le_one (M : Finset E) :
    G.IsMatching M ↔ ∀ w : V, (M.filter (fun e => w ∈ G.edge e)).card ≤ 1 := by
  constructor
  · intro h w
    apply Finset.card_le_one.mpr
    intro e he f hf
    exact h e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 w
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
  · intro h e he f hf w hwe hwf
    exact Finset.card_le_one.mp (h w) e (Finset.mem_filter.mpr ⟨he, hwe⟩)
      f (Finset.mem_filter.mpr ⟨hf, hwf⟩)

noncomputable def matchingIndicator (M : Finset E) (e : E) : ℝ :=
  if e ∈ M then 1 else 0

/-- Indicators of actual edge-copy matchings. -/
def matchingIndicators : Set (E → ℝ) :=
  {z | ∃ M : Finset E, G.IsMatching M ∧ z = matchingIndicator M}

variable [Fintype E]

theorem matchingIndicator_degree (M : Finset E) (w : V) :
    Lovasz.BMatch.dsum G.firstEnd G.secondEnd univ (matchingIndicator M) w =
      ((M.filter (fun e => w ∈ G.edge e)).card : ℝ) := by
  simp only [Lovasz.BMatch.dsum, matchingIndicator, Finset.sum_boole,
    Finset.filter_filter, ← G.incident_iff]
  congr 2
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem integral_eq_matchingIndicators :
    MatchingPolytope.integral G.firstEnd G.secondEnd = G.matchingIndicators := by
  apply Set.Subset.antisymm
  · intro z hz
    let M := univ.filter (fun e => z e = 1)
    have hzindicator : matchingIndicator M = z := by
      funext e
      rcases hz.1 e with h | h <;> simp [matchingIndicator, M, h]
    refine ⟨M, ?_, hzindicator.symm⟩
    apply (G.isMatching_iff_incident_card_le_one M).mpr
    intro w
    have hdeg : ((M.filter (fun e => w ∈ G.edge e)).card : ℝ) ≤ 1 := by
      rw [← G.matchingIndicator_degree, hzindicator]
      exact hz.2 w
    exact_mod_cast hdeg
  · rintro z ⟨M, hM, rfl⟩
    refine ⟨?_, ?_⟩
    · intro e
      by_cases he : e ∈ M <;> simp [matchingIndicator, he]
    · intro w
      rw [G.matchingIndicator_degree]
      exact_mod_cast (G.isMatching_iff_incident_card_le_one M).mp hM w

/-- The usual degree and odd-set inequalities, counting every edge copy. -/
def matchingPolytope : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ w, ∑ e ∈ G.incidenceEdges w, x e ≤ 1) ∧
    ∀ X : Finset V, Odd X.card →
      ∑ e ∈ G.internalEdges X, x e ≤ ((X.card : ℝ) - 1) / 2}

theorem matchingPolytope_eq_fractional :
    G.matchingPolytope = MatchingPolytope.fractional G.firstEnd G.secondEnd := by
  have hinc (w : V) : G.incidenceEdges w =
      univ.filter (fun e => G.firstEnd e = w ∨ G.secondEnd e = w) := by
    ext e
    simp [G.incident_iff]
  have hint (X : Finset V) : G.internalEdges X =
      Lovasz.BMatch.inside G.firstEnd G.secondEnd univ X := by
    ext e
    simp [Lovasz.BMatch.inside]
  ext x
  simp only [matchingPolytope, MatchingPolytope.fractional, Set.mem_setOf_eq,
    Lovasz.BMatch.dsum, hinc, hint]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro X
  apply imp_congr_right
  intro _
  constructor <;> intro h <;> linarith

variable [Fintype V]

/-- **Matching-polytope theorem (manuscript Theorem 2.9).** For a finite
loopless multigraph, the convex hull of matching indicators is exactly the
nonnegative edge weights satisfying the degree and odd-set inequalities. -/
theorem matching_polytope :
    convexHull ℝ G.matchingIndicators = G.matchingPolytope := by
  rw [← G.integral_eq_matchingIndicators, G.matchingPolytope_eq_fractional]
  exact MatchingPolytope.matching_polytope G.firstEnd G.secondEnd G.endpoints_distinct

/-- Every point of the matching polytope is realized by a finite distribution
on actual matchings, with its coordinates as the edge marginals. -/
theorem exists_matching_distribution {x : E → ℝ} (hx : x ∈ G.matchingPolytope) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (M : ι → Finset E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, G.IsMatching (M i)) ∧
      ∀ e : E, ∑ i ∈ univ.filter (fun i => e ∈ M i), w i = x e := by
  have hmem : x ∈ convexHull ℝ G.matchingIndicators := by rwa [G.matching_polytope]
  obtain ⟨ι, inst, w, z, hw, hsum, hz, hcoords⟩ :=
    mem_convexHull_iff_exists_fintype.mp hmem
  letI := inst
  change ∀ i, ∃ M : Finset E, G.IsMatching M ∧ z i = matchingIndicator M at hz
  choose M hM hMz using hz
  refine ⟨ι, inst, w, M, hw, hsum, hM, ?_⟩
  intro e
  have he := congrFun hcoords e
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hMz, matchingIndicator] at he
  simpa only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter] using he

/-- Overfullness relative to the palette size, with parallel copies counted. -/
def IsOverfull (k : ℕ) (X : Finset V) : Prop :=
  k * (X.card / 2) < (G.internalEdges X).card

omit [Fintype V] in
theorem uniform_mem_matchingPolytope {k : ℕ} (hk : 0 < k)
    (hdegree : ∀ v, G.degree v ≤ k) (hno : ∀ X : Finset V, ¬ G.IsOverfull k X) :
    (fun _ : E => (1 : ℝ) / k) ∈ G.matchingPolytope := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun _ => div_nonneg zero_le_one hkR.le, ?_, ?_⟩
  · intro v
    have hdegreeR : (G.degree v : ℝ) ≤ k := by exact_mod_cast hdegree v
    calc
      _ = (G.degree v : ℝ) / k := by simp [degree, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hkR).mpr hdegreeR
  · intro X hX
    have hcount : (G.internalEdges X).card ≤ k * (X.card / 2) :=
      Nat.le_of_not_lt (hno X)
    have hcountR : ((G.internalEdges X).card : ℝ) ≤ (k : ℝ) * (X.card / 2 : ℕ) := by
      exact_mod_cast hcount
    have hodd : 2 * (X.card / 2) + 1 = X.card := by
      have := Nat.odd_iff.mp hX
      omega
    have hoddR : (2 : ℝ) * (X.card / 2 : ℕ) + 1 = X.card := by exact_mod_cast hodd
    calc
      _ = ((G.internalEdges X).card : ℝ) / k := by simp [div_eq_mul_inv]
      _ ≤ ((X.card : ℝ) - 1) / 2 := by
        apply (div_le_iff₀ hkR).mpr
        nlinarith

omit [Fintype V] in
/-- Saturated expected degree forces every positive-weight matching to cover
the vertex. The edge marginals refer to the actual edge copies of `G`. -/
theorem positive_weight_matching_covers {ι : Type*} [Fintype ι]
    {w : ι → ℝ} {M : ι → Finset E} {x : E → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hM : ∀ i, G.IsMatching (M i))
    (hmarginal : ∀ e, ∑ i ∈ univ.filter (fun i => e ∈ M i), w i = x e)
    {v : V} (hv : ∑ e ∈ G.incidenceEdges v, x e = 1)
    {i : ι} (hi : 0 < w i) : ∃ e ∈ M i, v ∈ G.edge e := by
  let d : ι → ℝ := fun j => ((M j).filter (fun e => v ∈ G.edge e)).card
  have hbound (j : ι) : d j ≤ 1 := by
    dsimp [d]
    exact_mod_cast (G.isMatching_iff_incident_card_le_one (M j)).mp (hM j) v
  have hdsum (j : ι) : d j = ∑ e ∈ G.incidenceEdges v, matchingIndicator (M j) e := by
    dsimp [d]
    rw [← G.matchingIndicator_degree]
    simp only [Lovasz.BMatch.dsum, incidenceEdges, G.incident_iff]
  have hexpect : ∑ j, w j * d j = 1 := by
    calc
      _ = ∑ j, ∑ e ∈ G.incidenceEdges v, w j * matchingIndicator (M j) e := by
        simp only [hdsum, Finset.mul_sum]
      _ = ∑ e ∈ G.incidenceEdges v, ∑ j, w j * matchingIndicator (M j) e :=
        Finset.sum_comm
      _ = ∑ e ∈ G.incidenceEdges v, x e := by
        apply Finset.sum_congr rfl
        intro e _
        simpa only [matchingIndicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
          using hmarginal e
      _ = 1 := hv
  have hle (j : ι) (_ : j ∈ (univ : Finset ι)) : w j * d j ≤ w j := by
    simpa using mul_le_mul_of_nonneg_left (hbound j) (hw j)
  have heq : w i * d i = w i :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (hexpect.trans hsum.symm) i (Finset.mem_univ i)
  have hd : d i = 1 := by nlinarith
  have hcard : 0 < ((M i).filter (fun e => v ∈ G.edge e)).card := by
    have hdpos : (0 : ℝ) < d i := by rw [hd]; norm_num
    dsimp [d] at hdpos
    exact_mod_cast hdpos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

/-- The uniform fractional-matching consequence used in the manuscript also
holds for nonregular multigraphs. Every positive-weight matching covers all
vertices of degree `k`. -/
theorem exists_uniform_matching_distribution {k : ℕ} (hk : 0 < k)
    (hdegree : ∀ v, G.degree v ≤ k) (hno : ∀ X : Finset V, ¬ G.IsOverfull k X) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (M : ι → Finset E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, G.IsMatching (M i)) ∧
      (∀ e : E, ∑ i ∈ univ.filter (fun i => e ∈ M i), w i = (1 : ℝ) / k) ∧
      ∀ v, G.degree v = k → ∀ i, 0 < w i → ∃ e ∈ M i, v ∈ G.edge e := by
  obtain ⟨ι, inst, w, M, hw, hsum, hM, hmarginal⟩ :=
    G.exists_matching_distribution (G.uniform_mem_matchingPolytope hk hdegree hno)
  letI := inst
  refine ⟨ι, inst, w, M, hw, hsum, hM, hmarginal, ?_⟩
  intro v hv i hi
  apply G.positive_weight_matching_covers hw hsum hM hmarginal ?_ hi
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  change (∑ _e ∈ G.incidenceEdges v, (1 : ℝ) / k) = 1
  calc
    _ = (G.degree v : ℝ) / k := by simp [degree, div_eq_mul_inv]
    _ = 1 := by rw [hv, div_self hkR]

/-- A perfect matching has exactly one selected edge copy at every vertex. -/
def IsPerfectMatching (M : Finset E) : Prop :=
  ∀ v : V, (M.filter (fun e => v ∈ G.edge e)).card = 1

omit [Fintype V] [Fintype E] in
theorem IsPerfectMatching.isMatching {M : Finset E} (hM : G.IsPerfectMatching M) :
    G.IsMatching M := by
  apply (G.isMatching_iff_incident_card_le_one M).mpr
  intro v
  exact (hM v).le

omit [Fintype V] [Fintype E] in
theorem isPerfectMatching_iff {M : Finset E} :
    G.IsPerfectMatching M ↔ G.IsMatching M ∧ ∀ v, ∃ e ∈ M, v ∈ G.edge e := by
  constructor
  · intro hM
    refine ⟨hM.isMatching G, ?_⟩
    intro v
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by rw [hM v]; decide)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · rintro ⟨hM, hcover⟩ v
    have hle := (G.isMatching_iff_incident_card_le_one M).mp hM v
    obtain ⟨e, he, hev⟩ := hcover v
    have hpos : 0 < (M.filter (fun e => v ∈ G.edge e)).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
    omega

/-- The finite perfect-matching distribution for a regular loopless
multigraph. Indices of weight zero are removed from the distribution. -/
theorem exists_perfectMatching_distribution {k : ℕ} (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k) (hno : ∀ X : Finset V, ¬ G.IsOverfull k X) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (M : ι → Finset E),
      (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧ (∀ i, G.IsPerfectMatching (M i)) ∧
      ∀ e : E, ∑ i ∈ univ.filter (fun i => e ∈ M i), w i = (1 : ℝ) / k := by
  obtain ⟨ι, inst, w, M, hw, hsum, hM, hmarginal, hcover⟩ :=
    G.exists_uniform_matching_distribution hk (fun v => (hregular v).le) hno
  letI := inst
  let I := {i : ι // 0 < w i}
  have hrestriction (f : ι → ℝ) (hf : ∀ i, w i = 0 → f i = 0) :
      (∑ i : I, f i.val) = ∑ i : ι, f i := by
    symm
    apply Finset.sum_congr_set {i : ι | 0 < w i}
      f (fun i => f i.val)
    · intro i _
      rfl
    · intro i hi
      have hi0 : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
      exact hf i hi0
  refine ⟨I, inferInstance, (fun i => w i.val), (fun i => M i.val),
    (fun i => i.property), ?_, ?_, ?_⟩
  · calc
      _ = ∑ i, w i := hrestriction w (fun _ hi => hi)
      _ = 1 := hsum
  · intro i
    apply G.isPerfectMatching_iff.mpr
    exact ⟨hM i.val, fun v => hcover v (hregular v) i.val i.property⟩
  · intro e
    simp only [Finset.sum_filter]
    calc
      _ = ∑ i : I, if e ∈ M i.val then w i.val else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : e ∈ M i.val <;> simp [he]
      _ = ∑ i : ι, if e ∈ M i then w i else 0 :=
        hrestriction (fun i => if e ∈ M i then w i else 0) (fun i hi => by simp [hi])
      _ = (1 : ℝ) / k := by simpa only [Finset.sum_filter] using hmarginal e

end Overfull.Multigraph
