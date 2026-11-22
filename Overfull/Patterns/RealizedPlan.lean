import Overfull.Patterns.Plan

/-!
# Actual boundary matchings for every accepted pattern copy

The copy set is a finite dependent sum. Its enumeration is fixed once,
so the natural-number schedule has exactly the accepted multiplicities.
-/

namespace Overfull.Patterns

open Finset Classical SimpleGraph ForceMatching Compression MatchingProbability
open PatternRealization
open scoped BigOperators

variable {P : Type*} [Fintype P]

/-- One index for every requested copy of every pattern. -/
abbrev MultiplicityCopy (m : P → ℕ) := (p : P) × Fin (m p)

@[simp] theorem cardinal_multiplicityCopy (m : P → ℕ) :
    Fintype.card (MultiplicityCopy m) = ∑ p, m p := by
  simp [MultiplicityCopy, Fintype.card_sigma]

/-- A fixed ordering of the finite copy set. -/
noncomputable def multiplicityEnumeration (m : P → ℕ) :
    Fin (∑ p, m p) ≃ MultiplicityCopy m :=
  (Fintype.equivFinOfCardEq (cardinal_multiplicityCopy m)).symm

/-- Unused later schedule entries carry an arbitrary fixed default. -/
noncomputable def scheduledPattern (m : P → ℕ) (p₀ : P) (j : ℕ) : P :=
  if hj : j < ∑ p, m p then (multiplicityEnumeration m ⟨j,hj⟩).1 else p₀

noncomputable def prefixPatternCount (p : ℕ → P) (s : ℕ) (x : P) : ℕ :=
  ((range s).filter (fun j => p j = x)).card

theorem copy_fiber_count (m : P → ℕ) (p : P) :
    ((univ : Finset (MultiplicityCopy m)).filter (fun c => c.1 = p)).card = m p := by
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  rw [sum_eq_single p]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

/-- Every requested copy occurs exactly once in the complete schedule. -/
theorem scheduledPattern_total (m : P → ℕ) (p₀ p : P) :
    prefixPatternCount (scheduledPattern m p₀) (∑ p, m p) p = m p := by
  rw [← copy_fiber_count m p]
  unfold prefixPatternCount
  refine Finset.card_bij (fun j hj => multiplicityEnumeration m
    ⟨j,mem_range.mp (mem_filter.mp hj).1⟩) ?_ ?_ ?_
  · intro j hj
    have hjq := mem_range.mp (mem_filter.mp hj).1
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    simpa only [scheduledPattern, dif_pos hjq] using (mem_filter.mp hj).2
  · intro j hj l hl h
    exact congrArg Fin.val ((multiplicityEnumeration m).injective h)
  · intro c hc
    let j := (multiplicityEnumeration m).symm c
    have hj : scheduledPattern m p₀ j.val = c.1 := by
      simp only [scheduledPattern, dif_pos j.isLt]
      exact congrArg Sigma.fst ((multiplicityEnumeration m).apply_symm_apply c)
    refine ⟨j.val,mem_filter.mpr ⟨mem_range.mpr j.isLt,hj.trans (mem_filter.mp hc).2⟩,?_⟩
    exact (multiplicityEnumeration m).apply_symm_apply c

omit [Fintype P] in
theorem prefixPatternCount_mono (p : ℕ → P) {s q : ℕ} (hs : s ≤ q) (x : P) :
    prefixPatternCount p s x ≤ prefixPatternCount p q x := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.range_mono hs)

theorem prefixPatternCount_sum (p : ℕ → P) (s : ℕ) :
    (∑ x, prefixPatternCount p s x) = s := by
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := range s) (t := (univ : Finset P)) (f := p) (fun _ _ => mem_univ _)
  simpa only [prefixPatternCount, card_range] using hh.symm

/-- Regroup a natural-valued statistic by its exact prefix multiplicities. -/
theorem prefixPatternCount_statistic (p : ℕ → P) (s : ℕ) (f : P → ℕ) :
    (∑ x, prefixPatternCount p s x * f x) = ∑ j ∈ range s, f (p j) := by
  calc
    _ = ∑ x, ∑ j ∈ (range s).filter (fun j => p j = x), f (p j) := by
      apply sum_congr rfl
      intro x _
      calc
        _ = ∑ _j ∈ (range s).filter (fun j => p j = x), f x := by simp [prefixPatternCount]
        _ = _ := sum_congr rfl (fun j hj => congrArg f (mem_filter.mp hj).2.symm)
    _ = _ := Finset.sum_fiberwise (range s) p (fun j => f (p j))

section Actual

variable {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)

/-- A natural-number boundary schedule with exactly prescribed multiplicities. -/
structure RealizedPlan (m : Pattern Z → ℕ) where
  pattern : ℕ → Pattern Z
  boundary : ℕ → G.Subgraph
  realizes : ∀ j < ∑ p, m p, RealizesPattern G U Z code (pattern j) (boundary j)
  disjoint : ∀ j < ∑ p, m p, ∀ l < ∑ p, m p, j ≠ l →
    Disjoint (boundary j).spanningCoe (boundary l).spanningCoe
  total_count : ∀ p, prefixPatternCount pattern (∑ p, m p) p = m p

theorem RealizedPlan.prefix_count_le {m : Pattern Z → ℕ}
    (R : RealizedPlan G U Z code m) (s : ℕ) (hs : s ≤ ∑ p, m p) (p : Pattern Z) :
    prefixPatternCount R.pattern s p ≤ m p := by
  rw [← R.total_count p]
  exact prefixPatternCount_mono R.pattern hs p

/-- Reindex the finite actual matching family once and retain every property. -/
theorem reindex_realized_copies (m : Pattern Z → ℕ) (p₀ : Pattern Z)
    (F : MultiplicityCopy m → G.Subgraph)
    (hF : ∀ j, RealizesPattern G U Z code j.1 (F j))
    (hdisj : ∀ j l, j ≠ l → Disjoint (F j).spanningCoe (F l).spanningCoe) :
    Nonempty (RealizedPlan G U Z code m) := by
  let B : ℕ → G.Subgraph := fun j =>
    if hj : j < ∑ p, m p then F (multiplicityEnumeration m ⟨j,hj⟩) else ⊥
  refine ⟨⟨scheduledPattern m p₀,B,?_,?_,scheduledPattern_total m p₀⟩⟩
  · intro j hj
    simpa only [B, scheduledPattern, dif_pos hj] using hF (multiplicityEnumeration m ⟨j,hj⟩)
  · intro j hj l hl hjl
    have hh := hdisj (multiplicityEnumeration m ⟨j,hj⟩)
      (multiplicityEnumeration m ⟨l,hl⟩)
      (fun he => hjl (congrArg Fin.val ((multiplicityEnumeration m).injective he)))
    simpa only [B, dif_pos hj, dif_pos hl] using hh

omit [Fintype V] in
/-- The demand of a quotient pair is its sum over the accepted multiplicities. -/
theorem copy_pair_demand (m : Pattern Z → ℕ) (b : Finset (Z ⊕ Fin 4)) :
    demandCount (slotKind Z (fun j : MultiplicityCopy m => j.1)) b =
      ∑ p, m p * (if b ∈ p.boundaryEdges then 1 else 0) := by
  rw [demandCount_slots, Fintype.sum_sigma]
  apply sum_congr rfl
  intro p _
  by_cases hb : b ∈ p.boundaryEdges <;> simp [hb]

/-- The actual core footprint is bounded by the number of covered
nonexceptional vertices. -/
theorem RealizedPlan.core_footprint_bound {m : Pattern Z → ℕ}
    (R : RealizedPlan G U Z code m) (hUZ : ∀ i, Disjoint (U i) Z)
    (j : ℕ) (hj : j < ∑ p, m p) (i : I) :
    (coveredCore (U i) G (R.boundary j)).card ≤ Z.card+6 := by
  rw [coveredCore_card]
  apply le_trans (Finset.card_le_card ?_) (R.realizes j hj).core_footprint
  intro v hv
  obtain ⟨hF,hi⟩ := mem_inter.mp hv
  exact mem_sdiff.mpr ⟨hF,fun hz => disjoint_left.mp (hUZ i) hi hz⟩

theorem RealizedPlan.whole_cut_count {m : Pattern Z → ℕ}
    (R : RealizedPlan G U Z code m) (j : ℕ) (hj : j < ∑ p, m p)
    (Q : Finset (Z ⊕ Fin 4)) :
    cutCount (matchingEdges (R.boundary j)) (wholeUnion U Z code Q) =
      (R.pattern j).cutCount Q :=
  cutCount_eq_pattern_of_boundary U Z code (matchingEdges (R.boundary j))
    (R.pattern j) (R.realizes j hj).projection_injective (R.realizes j hj).boundary_image Q

end Actual

namespace EncodedDistribution

variable {V I S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}

set_option maxHeartbeats 500000 in
/-- Every accepted pattern copy is realized in the original host. Pool
capacities, incidence bounds, and positive slack are derived from the
actual fractional distribution and original core degrees. -/
theorem exists_planned_realization (D : EncodedDistribution G U Z code k S)
    (hk : 0 < k) (η a : ℝ) (t : ℕ) (p₀ : Pattern Z) (r : ℕ)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hr : (r : ℝ) ≤ D.weight p₀) (hZ : Z.card ≤ t)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v) :
    Nonempty (RealizedPlan G U Z code (D.plannedMultiplicity η a t p₀ r)) := by
  let m := D.plannedMultiplicity η a t p₀ r
  let Pcopy : MultiplicityCopy m → Pattern Z := fun j => j.1
  have hpos (j : MultiplicityCopy m) : 0 < m j.1 := Nat.zero_lt_of_lt j.2.isLt
  have hselected (j : MultiplicityCopy m) :=
    D.selected_pattern_witness hk η p₀ j.1 r (m j.1) hη₀ hη₁ hr
      (D.planned_le_proposed η a t p₀ j.1 r) (hpos j)
  have hPcopy (j : MultiplicityCopy m) : (Pcopy j).internalPairs = ∅ := (hselected j).1
  have hsource (j : MultiplicityCopy m) :
      ∃ M : G.Subgraph, Encodes G U Z code M (Pcopy j) ∧
        ∀ i, Even (((U i : Set V) \ M.verts).ncard) := by
    obtain ⟨s,_hs,henc,hpar⟩ := (hselected j).2
    exact ⟨D.part s,henc,hpar⟩
  have hdegree' (i : I) (v : U i) : (k : ℝ) ≤ (H i).degree v+a := by
    linarith [hdegree i v]
  have hcap (s : BoundarySlot Z Pcopy) :
      demandCount (slotKind Z Pcopy) (slotKind Z Pcopy s) + (Z.card+6)*⌊a⌋₊ <
        (boundaryPool G U Z code (slotKind Z Pcopy s)).card := by
    let b := slotKind Z Pcopy s
    have hb : b ∈ (Pcopy s.1).boundaryEdges := s.2.property
    obtain ⟨M,hM,_⟩ := hsource s.1
    have hapos : 0 < a := by
      have hh := one_le_error_of_boundary G U Z code (Pcopy s.1) (hPcopy s.1) M hM
        hdisjoint hUZ hcover H hH k a hregular hdegree' b hb
      linarith
    have hcount : demandCount (slotKind Z Pcopy) b = ∑ p, m p*pairUse b p := by
      simpa only [Pcopy, pairUse] using copy_pair_demand Z m b
    have hcountR : (demandCount (slotKind Z Pcopy) b : ℝ) =
        ∑ p, (m p : ℝ)*(pairUse b p : ℝ) := by exact_mod_cast hcount
    have huse : (demandCount (slotKind Z Pcopy) b : ℝ) ≤
        (1-η)*(boundaryPool G U Z code b).card := by
      have hh := D.planned_pair_demand hk η a t p₀ r hη₁ hr b
      change (∑ p, (m p : ℝ)*pairUse b p) ≤ _ at hh
      rw [← hcountR] at hh
      have hn : 0 ≤ (1-η)*(r : ℝ)*pairUse b p₀ :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hη₁) (Nat.cast_nonneg r))
          (Nat.cast_nonneg _)
      nlinarith only [hh,hn]
    have hpool := D.planned_pool_lower η a t p₀ s.1.1 r (hpos s.1) b hb
    have hpool' := (div_le_iff₀ hη₀).mp hpool
    have hZr : (Z.card : ℝ) ≤ t := by exact_mod_cast hZ
    have hZa := mul_le_mul_of_nonneg_right (add_le_add_right hZr 8) ha
    have hslack : (((Z.card+6 : ℕ) : ℝ)+2)*a ≤
        η*(boundaryPool G U Z code b).card := by
      push_cast
      nlinarith only [hpool',hZa]
    exact capacity_of_real_slack (boundaryPool G U Z code b).card
      (demandCount (slotKind Z Pcopy) b) (Z.card+6) a η hapos huse hslack
  obtain ⟨F,hF,hdisj⟩ := realize_patterns G U Z code Pcopy hPcopy hsource
    hdisjoint hUZ hcover H hH k a hregular hdegree' hcap
  exact reindex_realized_copies G U Z code m p₀ F hF hdisj

end EncodedDistribution
end Overfull.Patterns
