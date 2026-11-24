import Overfull.Probability.IndependentBernoulli

/-!
# Independent orientations of prescribed pairs

The vertices are labelled by a pair index and a Boolean endpoint. One fair
bit for each pair selects one endpoint on each side. The deviation of an
arbitrary set is exactly a Bernoulli deviation on its single-end pairs.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {I : Type*} [Fintype I]

noncomputable def leftVertices (ω : I → Bool) : Finset (I × Bool) :=
  univ.image (fun i => (i,ω i))

noncomputable def rightVertices (ω : I → Bool) : Finset (I × Bool) :=
  leftVertices (fun i => !(ω i))

@[simp] theorem mem_leftVertices (ω : I → Bool) (i : I) (b : Bool) :
    (i,b) ∈ leftVertices ω ↔ b = ω i := by
  simp [leftVertices,eq_comm]

@[simp] theorem mem_rightVertices (ω : I → Bool) (i : I) (b : Bool) :
    (i,b) ∈ rightVertices ω ↔ b = !(ω i) := by
  simp [rightVertices]

theorem leftVertices_card (ω : I → Bool) : (leftVertices ω).card = Fintype.card I := by
  rw [leftVertices, Finset.card_image_of_injective _ (by
    intro i j hij
    exact congrArg Prod.fst hij), Finset.card_univ]

theorem rightVertices_card (ω : I → Bool) : (rightVertices ω).card = Fintype.card I :=
  leftVertices_card _

theorem rightVertices_eq_compl (ω : I → Bool) : rightVertices ω = (leftVertices ω)ᶜ := by
  ext ⟨i,b⟩
  cases hω : ω i <;> cases b <;> simp [hω]

theorem sides_disjoint (ω : I → Bool) : Disjoint (leftVertices ω) (rightVertices ω) := by
  rw [rightVertices_eq_compl]
  exact Finset.disjoint_left.mpr (fun _ h₁ h₂ => Finset.mem_compl.mp h₂ h₁)

theorem sides_union (ω : I → Bool) : leftVertices ω ∪ rightVertices ω = univ := by
  rw [rightVertices_eq_compl,Finset.union_compl]

/-- Every prescribed pair has one endpoint on each side for every outcome. -/
theorem pair_split (ω : I → Bool) (i : I) :
    (i,ω i) ∈ leftVertices ω ∧ (i,!(ω i)) ∈ rightVertices ω := by simp

noncomputable def splitCount (S : Finset (I × Bool)) (ω : I → Bool) : ℕ :=
  (univ.filter (fun i => (i,ω i) ∈ S)).card

theorem splitCount_eq_inter (S : Finset (I × Bool)) (ω : I → Bool) :
    splitCount S ω = (S ∩ leftVertices ω).card := by
  have heq : (univ.filter (fun i => (i,ω i) ∈ S)).image (fun i => (i,ω i)) =
      S ∩ leftVertices ω := by
    ext ⟨i,b⟩
    simp [leftVertices, Prod.mk.injEq,eq_comm,and_comm]
    intro hb
    rw [hb]
  rw [← heq,Finset.card_image_of_injective _ (by
    intro i j hij
    exact congrArg Prod.fst hij)]
  rfl

noncomputable def bothPairs (S : Finset (I × Bool)) : Finset I :=
  univ.filter (fun i => (i,false) ∈ S ∧ (i,true) ∈ S)

noncomputable def singlePairs (S : Finset (I × Bool)) : Finset I :=
  univ.filter (fun i => ((i,false) ∈ S) ≠ ((i,true) ∈ S))

/-- Flip the coin exactly when the true endpoint does not belong to `S`.
Only single-end pairs enter the variable part of the count. -/
noncomputable def flip (S : Finset (I × Bool)) (ω : I → Bool) : I → Bool :=
  fun i => if (i,true) ∈ S then ω i else !(ω i)

omit [Fintype I] in
theorem flip_involutive (S : Finset (I × Bool)) : Function.Involutive (flip S) := by
  intro ω
  funext i
  by_cases hi : (i,true) ∈ S <;> simp [flip,hi]

theorem splitCount_identity (S : Finset (I × Bool)) (ω : I → Bool) :
    splitCount S ω = (bothPairs S).card + Bernoulli.retainedCount (singlePairs S) (flip S ω) := by
  simp only [splitCount,bothPairs,singlePairs,Bernoulli.retainedCount,
    Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hfalse : (i,false) ∈ S <;> by_cases htrue : (i,true) ∈ S <;>
    cases hω : ω i <;> simp [flip,hfalse,htrue,hω]

theorem set_card_identity (S : Finset (I × Bool)) :
    S.card = 2 * (bothPairs S).card + (singlePairs S).card := by
  have hcard : S.card = ∑ v : I × Bool, if v ∈ S then (1 : ℕ) else 0 := by simp
  rw [hcard,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  simp only [bothPairs,singlePairs,Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hfalse : (i,false) ∈ S <;> by_cases htrue : (i,true) ∈ S <;>
    simp [hfalse,htrue]

theorem singlePairs_card_le (S : Finset (I × Bool)) : (singlePairs S).card ≤ S.card := by
  have h := set_card_identity S
  omega

theorem splitCount_deviation (S : Finset (I × Bool)) (ω : I → Bool) :
    (splitCount S ω : ℝ) - S.card / 2 =
      (Bernoulli.retainedCount (singlePairs S) (flip S ω) : ℝ) - (singlePairs S).card / 2 := by
  have hc := splitCount_identity S ω
  have hs := set_card_identity S
  rw [hc,hs]
  push_cast
  ring

theorem fair_mass (b : Bool) : Bernoulli.mass (1 / 2) b = (1 / 2 : ℝ) := by
  cases b <;> norm_num [Bernoulli.mass]

/-- Flipping any prescribed collection of the independent fair coins
preserves their complete joint distribution. -/
theorem probability_flip (S : Finset (I × Bool)) (P : (I → Bool) → Prop) :
    Bernoulli.probability (1 / 2) (fun ω => P (flip S ω)) =
      Bernoulli.probability (1 / 2) P := by
  have hjoint (σ : I → Bool) :
      MatchingProbability.probability (Bernoulli.weight (1 / 2))
        (fun ω => flip S ω = σ) = IndependentBernoulli.weight (fun _ : I => 1 / 2) σ := by
    have heq : (fun ω : I → Bool => flip S ω = σ) = (fun ω => ω = flip S σ) := by
      funext ω
      apply propext
      constructor
      · intro h
        have h' := congrArg (flip S) h
        simpa only [flip_involutive S ω] using h'
      · rintro rfl
        exact flip_involutive S σ
    rw [heq]
    have h := Bernoulli.probability_assignment (1 / 2) univ (flip S σ)
    simpa only [Finset.mem_univ,forall_const,← funext_iff,
      Bernoulli.probability,IndependentBernoulli.weight,fair_mass] using h
  exact IndependentBernoulli.probability_of_joint_law (Bernoulli.weight (1 / 2))
    (flip S) (fun _ : I => 1 / 2) hjoint P

/-- Concentration for the actual number of vertices of `S` assigned to
the first side. No independence among vertices in the same pair is used. -/
theorem splitCount_concentration (S : Finset (I × Bool)) (a m : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hSm : (S.card : ℝ) ≤ m) :
    Bernoulli.probability (1 / 2) (fun ω => a * m ≤
      |(splitCount S ω : ℝ) - S.card / 2|) ≤
      2 * Real.exp (-(2 : ℝ) * a ^ 2 * m / 3) := by
  simp_rw [splitCount_deviation]
  rw [probability_flip S (fun ω => a * m ≤
    |(Bernoulli.retainedCount (singlePairs S) ω : ℝ) - (singlePairs S).card / 2|)]
  have hsc : ((singlePairs S).card : ℝ) ≤ S.card := by exact_mod_cast singlePairs_card_le S
  have hs : ((singlePairs S).card : ℝ) ≤ m := hsc.trans hSm
  have h := Bernoulli.additive_chernoff (1 / 2) a m (by norm_num) (by norm_num)
    ha ha1 (singlePairs S) hs
  rw [show (1 / 2 : ℝ) * (singlePairs S).card = (singlePairs S).card / 2 by ring,
    show -a ^ 2 * m / (3 * (1 / 2 : ℝ)) = -(2 : ℝ) * a ^ 2 * m / 3 by ring] at h
  exact h

theorem side_count_sum (S : Finset (I × Bool)) (ω : I → Bool) :
    (S ∩ leftVertices ω).card + (S ∩ rightVertices ω).card = S.card := by
  have heq : S ∩ rightVertices ω = S \ leftVertices ω := by
    rw [rightVertices_eq_compl]
    ext v
    simp
  rw [heq]
  exact Finset.card_inter_add_card_sdiff S (leftVertices ω)

/-- The actual crossing graph of the selected pair orientation. -/
noncomputable def cutGraph (G : SimpleGraph (I × Bool)) (ω : I → Bool) :
    SimpleGraph (I × Bool) where
  Adj v w := G.Adj v w ∧ (v ∈ leftVertices ω) ≠ (w ∈ leftVertices ω)
  symm := by intro v w h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro v h; exact h.2 rfl

theorem cutGraph_le (G : SimpleGraph (I × Bool)) (ω : I → Bool) : cutGraph G ω ≤ G :=
  fun _ _ h => h.1

theorem cutGraph_degree (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj]
    (ω : I → Bool) (v : I × Bool) :
    (cutGraph G ω).degree v = if v ∈ leftVertices ω then
      (G.neighborFinset v ∩ rightVertices ω).card else
      (G.neighborFinset v ∩ leftVertices ω).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v ∈ leftVertices ω
  · rw [if_pos hv]
    congr 1
    ext w
    simp [cutGraph,hv,rightVertices_eq_compl]
  · rw [if_neg hv]
    congr 1
    ext w
    simp [cutGraph,hv]

end Overfull.PairedCut
