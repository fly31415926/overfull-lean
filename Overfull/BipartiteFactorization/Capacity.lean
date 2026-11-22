import Overfull.BipartiteFactorization.Moves

/-!
# Selecting actual correction copies with bounded exceptional rows

The finite capacity is realized by a set of distinct original copies.
Weighted scores give sufficient capacities, including after an arbitrary
deletion of copies. No independence of the deleted set is assumed.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.CorrectionCapacity

open Finset Classical

variable {I E : Type*} [Fintype I]

/-- The exact maximum size allowed by disjoint copy pools and row caps. -/
def capacity (F : I → Finset E) (cap : I → ℕ) : ℕ :=
  ∑ i, min (F i).card (cap i)

/-- A weighted lower bound on the actual capped capacity. -/
def score (F : I → Finset E) (cap : I → ℕ) (w : I → ℝ) : ℝ :=
  ∑ i, min (w i * (F i).card) (cap i)

/-- Every size up to the finite capacity is realized by actual distinct
copies, with the cap respected in every row. -/
theorem exists_capped_subset (F : I → Finset E) (cap : I → ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (t : ℕ) (ht : t ≤ capacity F cap) :
    ∃ T : Finset E, T ⊆ univ.biUnion F ∧ T.card = t ∧
      ∀ i, (T ∩ F i).card ≤ cap i := by
  have hex (i : I) : ∃ S : Finset E,
      S ⊆ F i ∧ S.card = min (F i).card (cap i) :=
    Finset.exists_subset_card_eq (min_le_left _ _)
  choose S hsub hcard using hex
  have hdisjS (i j : I) (hij : i ≠ j) : Disjoint (S i) (S j) :=
    (hdisj i j hij).mono (hsub i) (hsub j)
  have htotal : (univ.biUnion S).card = capacity F cap := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisjS i j hij)]
    simp only [hcard, capacity]
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq (ht.trans_eq htotal.symm)
  refine ⟨T, ?_, hTcard, ?_⟩
  · intro e he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp (hT he)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hsub i hei⟩
  · intro i
    have hTi : T ∩ F i ⊆ S i := by
      intro e he
      obtain ⟨heT, hei⟩ := Finset.mem_inter.mp he
      obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp (hT heT)
      by_cases hji : j = i
      · simpa only [hji] using hej
      · exact False.elim ((Finset.disjoint_left.mp (hdisj j i hji)) (hsub j hej) hei)
    exact (Finset.card_le_card hTi).trans ((hcard i).le.trans (min_le_right _ _))

/-- The same capacity is an upper bound for every allowed actual selection. -/
theorem card_le_capacity (F : I → Finset E) (cap : I → ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (T : Finset E) (hT : T ⊆ univ.biUnion F)
    (hcap : ∀ i, (T ∩ F i).card ≤ cap i) :
    T.card ≤ capacity F cap := by
  have hdecomp : T = univ.biUnion (fun i => T ∩ F i) := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp (hT he)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨he, hei⟩⟩
    · intro he
      obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_inter.mp hei).1
  calc
    T.card = ∑ i, (T ∩ F i).card := by
      conv_lhs => rw [hdecomp]
      exact Finset.card_biUnion (fun i _ j _ hij =>
        (hdisj i j hij).mono Finset.inter_subset_right Finset.inter_subset_right)
    _ ≤ capacity F cap := by
      apply Finset.sum_le_sum
      intro i _
      exact le_min (Finset.card_le_card Finset.inter_subset_right) (hcap i)

theorem exists_capped_subset_iff (F : I → Finset E) (cap : I → ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (t : ℕ) :
    (∃ T : Finset E, T ⊆ univ.biUnion F ∧ T.card = t ∧
      ∀ i, (T ∩ F i).card ≤ cap i) ↔ t ≤ capacity F cap := by
  constructor
  · rintro ⟨T, hT, rfl, hcap⟩
    exact card_le_capacity F cap hdisj T hT hcap
  · exact exists_capped_subset F cap hdisj t

/-- A score with weights at most one never exceeds the actual integer capacity. -/
theorem score_le_capacity (F : I → Finset E) (cap : I → ℕ) (w : I → ℝ)
    (hw : ∀ i, w i ≤ 1) : score F cap w ≤ (capacity F cap : ℝ) := by
  simp only [score, capacity, Nat.cast_sum, Nat.cast_min]
  apply Finset.sum_le_sum
  intro i _
  apply min_le_min_right
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (F i).card)

theorem sum_deleted_card_le (F : I → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (D : Finset E) :
    (∑ i, (F i ∩ D).card) ≤ D.card := by
  have hd (i j : I) (hij : i ≠ j) : Disjoint (F i ∩ D) (F j ∩ D) :=
    (hdisj i j hij).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  apply Finset.card_le_card
  intro e he
  obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_inter.mp hei).2

omit [Fintype I] in
theorem min_add_loss (x y c : ℝ) (hy : 0 ≤ y) :
    min (x + y) c ≤ min x c + y := by
  by_cases hx : x ≤ c
  · rw [min_eq_left hx]
    exact min_le_left _ _
  · rw [min_eq_right (le_of_not_ge hx)]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right hy)

/-- Arbitrary copy deletion lowers the weighted score by at most the
maximum weight times the number of deleted copies. -/
theorem score_after_deletion (F : I → Finset E) (cap : I → ℕ) (w : I → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ W) (D : Finset E) :
    score F cap w - W * D.card ≤ score (fun i => F i \ D) cap w := by
  have hrow (i : I) :
      min (w i * (F i).card) (cap i : ℝ) ≤
        min (w i * (F i \ D).card) (cap i : ℝ) + w i * (F i ∩ D).card := by
    have hc := Finset.card_sdiff_add_card_inter (F i) D
    have hc' : ((F i \ D).card : ℝ) + (F i ∩ D).card = (F i).card := by
      exact_mod_cast hc
    rw [← hc', mul_add]
    exact min_add_loss _ _ _ (mul_nonneg (hw i).1 (Nat.cast_nonneg _))
  have hsum := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hrow i)
  simp only [Finset.sum_add_distrib] at hsum
  have hweight : (∑ i, w i * (F i ∩ D).card) ≤ W * D.card := by
    calc
      _ ≤ ∑ i, W * (F i ∩ D).card := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hw i).2 (Nat.cast_nonneg _)
      _ = W * ∑ i, ((F i ∩ D).card : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ W * D.card := by
        apply mul_le_mul_of_nonneg_left _ hW
        exact_mod_cast sum_deleted_card_le F hdisj D
  dsimp [score]
  linarith

/-- A lower score bound after an adaptive deletion constructs an actual
selection avoiding the deleted copies and respecting every row cap. -/
theorem exists_capped_subset_after_deletion
    (F : I → Finset E) (cap : I → ℕ) (w : I → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ W)
    (hwone : ∀ i, w i ≤ 1) (D : Finset E) (t : ℕ)
    (ht : (t : ℝ) ≤ score F cap w - W * D.card) :
    ∃ T : Finset E, T ⊆ univ.biUnion F ∧ Disjoint T D ∧ T.card = t ∧
      ∀ i, (T ∩ F i).card ≤ cap i := by
  have hscore := score_after_deletion F cap w hdisj W hW hw D
  have hcap := score_le_capacity (fun i => F i \ D) cap w hwone
  have ht' : t ≤ capacity (fun i => F i \ D) cap := by
    exact_mod_cast ht.trans (hscore.trans hcap)
  have hdisj' (i j : I) (hij : i ≠ j) : Disjoint (F i \ D) (F j \ D) :=
    (hdisj i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
  obtain ⟨T, hT, hcard, hcaps⟩ := exists_capped_subset (fun i => F i \ D) cap hdisj' t ht'
  have havoid : Disjoint T D := by
    apply Finset.disjoint_left.mpr
    intro e he heD
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp (hT he)
    exact (Finset.mem_sdiff.mp hei).2 heD
  refine ⟨T, ?_, havoid, hcard, ?_⟩
  · intro e he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp (hT he)
    exact Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_sdiff.mp hei).1⟩
  · intro i
    have heq : T ∩ F i = T ∩ (F i \ D) := by
      ext e
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · exact fun h => ⟨h.1, h.2, fun heD => (Finset.disjoint_left.mp havoid) h.1 heD⟩
      · exact fun h => ⟨h.1, h.2.1⟩
    rw [heq]
    exact hcaps i

omit [Fintype I] in
/-- Adjoin the uncapped internal pool as a separate row. -/
theorem internal_rows_pairwise (F₀ : Finset E) (F : I → Finset E)
    (h₀ : ∀ i, Disjoint F₀ (F i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    ∀ i j : Option I, i ≠ j →
      Disjoint (i.elim F₀ F) (j.elim F₀ F) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some j => exact h₀ j
  | some i =>
    cases j with
    | none => exact (h₀ i).symm
    | some j => exact hdisj i j (fun h => hij (congrArg Option.some h))

theorem internal_rows_union (F₀ : Finset E) (F : I → Finset E) :
    univ.biUnion (fun i : Option I => i.elim F₀ F) = F₀ ∪ univ.biUnion F := by
  ext e
  constructor
  · intro he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
    cases i with
    | none => exact Finset.mem_union.mpr (Or.inl hei)
    | some i => exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hei⟩))
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, he⟩
    · obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨some i, Finset.mem_univ _, hei⟩

/-- The correction pool has the asserted exact finite capacity. -/
theorem internal_rows_capacity (F₀ : Finset E) (F : I → Finset E) (cap : I → ℕ) :
    capacity (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap) =
      F₀.card + ∑ i, min (F i).card (cap i) := by
  simp only [capacity, Fintype.sum_option, Option.elim_none, Option.elim_some, min_self]

/-- Select any prescribed number of actual correction copies, while
respecting the exceptional-row caps and leaving the internal pool uncapped. -/
theorem exists_correction_subset (F₀ : Finset E) (F : I → Finset E) (cap : I → ℕ)
    (h₀ : ∀ i, Disjoint F₀ (F i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (t : ℕ) (ht : t ≤ F₀.card + ∑ i, min (F i).card (cap i)) :
    ∃ T : Finset E, T ⊆ F₀ ∪ univ.biUnion F ∧ T.card = t ∧
      ∀ i, (T ∩ F i).card ≤ cap i := by
  have ht' : t ≤ capacity (fun i : Option I => i.elim F₀ F)
      (fun i => i.elim F₀.card cap) := by
    rwa [internal_rows_capacity]
  obtain ⟨T, hT, hcard, hcap⟩ := exists_capped_subset
    (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap)
    (internal_rows_pairwise F₀ F h₀ hdisj) t ht'
  refine ⟨T, ?_, hcard, fun i => hcap (some i)⟩
  rwa [internal_rows_union] at hT

/-- The manuscript's weighted correction score is bounded by the exact
capacity of its actual internal and exceptional-row copy pools. -/
theorem correction_score_le_capacity
    (F₀ : Finset E) (F : I → Finset E) (cap : I → ℕ)
    (ω₁ ω₂ : ℝ) (hω₁ : ω₁ ≤ 1) (hω₂ : ω₂ ≤ 1) :
    ω₂ * F₀.card + ∑ i, min (ω₁ * (F i).card) (cap i : ℝ) ≤
      ((F₀.card + ∑ i, min (F i).card (cap i) : ℕ) : ℝ) := by
  have h₀ : ω₂ * F₀.card ≤ (F₀.card : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hω₂ (Nat.cast_nonneg F₀.card)
  have h := score_le_capacity
    (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap)
    (fun i => i.elim ω₂ (fun _ => ω₁)) (by
      intro i
      cases i with
      | none => exact hω₂
      | some _ => exact hω₁)
  rw [internal_rows_capacity] at h
  simpa only [score, Fintype.sum_option, Option.elim_none, Option.elim_some,
    min_eq_left h₀] using h

/-- The correction score survives an arbitrary deletion with the claimed
linear loss; the deleted copies may be chosen adaptively. -/
theorem correction_score_after_deletion
    (F₀ : Finset E) (F : I → Finset E) (cap : I → ℕ)
    (h₀ : ∀ i, Disjoint F₀ (F i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂) (hω₂ : ω₂ ≤ 1)
    (D : Finset E) :
    ω₂ * F₀.card + (∑ i, min (ω₁ * (F i).card) (cap i : ℝ)) - ω₂ * D.card ≤
      ω₂ * (F₀ \ D).card + ∑ i, min (ω₁ * (F i \ D).card) (cap i : ℝ) := by
  have hpre : ω₂ * F₀.card ≤ (F₀.card : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hω₂ (Nat.cast_nonneg F₀.card)
  have hpost : ω₂ * (F₀ \ D).card ≤ (F₀.card : ℝ) := by
    calc
      _ ≤ ((F₀ \ D).card : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hω₂
          (Nat.cast_nonneg (F₀ \ D).card)
      _ ≤ F₀.card := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : F₀ \ D ⊆ F₀)
  have h := score_after_deletion
    (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap)
    (fun i => i.elim ω₂ (fun _ => ω₁)) (internal_rows_pairwise F₀ F h₀ hdisj)
    ω₂ (hω₁.trans hω₁₂) (by
      intro i
      cases i with
      | none => exact ⟨hω₁.trans hω₁₂, le_rfl⟩
      | some _ => exact ⟨hω₁, hω₁₂⟩) D
  simpa only [score, Fintype.sum_option, Option.elim_none, Option.elim_some,
    min_eq_left hpre, min_eq_left hpost] using h

/-- Turn the surviving weighted capacity into an actual correction set
of the requested size, avoiding the arbitrary deleted set. -/
theorem exists_correction_subset_after_deletion
    (F₀ : Finset E) (F : I → Finset E) (cap : I → ℕ)
    (h₀ : ∀ i, Disjoint F₀ (F i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂) (hω₂ : ω₂ ≤ 1)
    (D : Finset E) (t : ℕ)
    (ht : (t : ℝ) ≤ ω₂ * F₀.card +
      (∑ i, min (ω₁ * (F i).card) (cap i : ℝ)) - ω₂ * D.card) :
    ∃ T : Finset E, T ⊆ F₀ ∪ univ.biUnion F ∧ Disjoint T D ∧ T.card = t ∧
      ∀ i, (T ∩ F i).card ≤ cap i := by
  have hpre : ω₂ * F₀.card ≤ (F₀.card : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hω₂ (Nat.cast_nonneg F₀.card)
  have ht' : (t : ℝ) ≤ score
      (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap)
      (fun i => i.elim ω₂ (fun _ => ω₁)) - ω₂ * D.card := by
    simpa only [score, Fintype.sum_option, Option.elim_none, Option.elim_some,
      min_eq_left hpre] using ht
  obtain ⟨T, hT, havoid, hcard, hcap⟩ := exists_capped_subset_after_deletion
    (fun i : Option I => i.elim F₀ F) (fun i => i.elim F₀.card cap)
    (fun i => i.elim ω₂ (fun _ => ω₁)) (internal_rows_pairwise F₀ F h₀ hdisj)
    ω₂ (hω₁.trans hω₁₂) (by
      intro i
      cases i with
      | none => exact ⟨hω₁.trans hω₁₂, le_rfl⟩
      | some _ => exact ⟨hω₁, hω₁₂⟩) (by
      intro i
      cases i with
      | none => exact hω₂
      | some _ => exact hω₁₂.trans hω₂) D t ht'
  refine ⟨T, ?_, havoid, hcard, fun i => hcap (some i)⟩
  rwa [internal_rows_union] at hT

end Overfull.BipartiteFactorization.CorrectionCapacity

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- Actual correction copies inside the side and at active exceptional
vertices form disjoint pools. Parallel copies remain distinct. -/
theorem correction_pools_disjoint (B Z : Finset V) (hBZ : Disjoint B Z) :
    (∀ x : Z, Disjoint (G.internalEdges B) (G.edgesTo x.val B)) ∧
      (∀ x y : Z, x ≠ y → Disjoint (G.edgesTo x.val B) (G.edgesTo y.val B)) := by
  constructor
  · intro x
    apply Finset.disjoint_left.mpr
    intro e heB hex
    obtain ⟨hxe, _⟩ := (G.mem_edgesTo x.val B e).mp hex
    have hxB := ((G.internalEdges_iff_of_edge e x.val (G.otherEnd x.val e)
      (G.edge_eq_otherEnd x.val e hxe) B).mp heB).1
    exact (Finset.disjoint_left.mp hBZ) hxB x.property
  · intro x y hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    obtain ⟨hxe, hxB⟩ := (G.mem_edgesTo x.val B e).mp hex
    obtain ⟨hye, _⟩ := (G.mem_edgesTo y.val B e).mp hey
    rw [G.edge_eq_otherEnd x.val e hxe] at hye
    rcases Sym2.mem_iff.mp hye with hyx | hyo
    · exact hxy (Subtype.ext hyx.symm)
    · exact (Finset.disjoint_left.mp hBZ) (hyo.symm ▸ hxB) y.property

/-- Every incidence at an active exceptional vertex in the actual
correction pool belongs to that vertex's own row. -/
theorem correction_pool_incidence (B Z : Finset V) (hBZ : Disjoint B Z)
    (x : Z) (e : E)
    (he : e ∈ G.internalEdges B ∪ univ.biUnion (fun y : Z => G.edgesTo y.val B))
    (hxe : x.val ∈ G.edge e) : e ∈ G.edgesTo x.val B := by
  rcases Finset.mem_union.mp he with heB | heZ
  · have hxB := ((G.internalEdges_iff_of_edge e x.val (G.otherEnd x.val e)
      (G.edge_eq_otherEnd x.val e hxe) B).mp heB).1
    exact False.elim ((Finset.disjoint_left.mp hBZ) hxB x.property)
  · obtain ⟨y, _, hey⟩ := Finset.mem_biUnion.mp heZ
    obtain ⟨hye, hyB⟩ := (G.mem_edgesTo y.val B e).mp hey
    rw [G.edge_eq_otherEnd y.val e hye] at hxe
    rcases Sym2.mem_iff.mp hxe with hxy | hxo
    · simpa only [hxy] using hey
    · exact False.elim ((Finset.disjoint_left.mp hBZ) (hxo.symm ▸ hyB) x.property)

/-- The row cap is the actual degree cap at the exceptional vertex. -/
theorem correction_selection_degree (B Z : Finset V) (hBZ : Disjoint B Z)
    (T : Finset E)
    (hT : T ⊆ G.internalEdges B ∪ univ.biUnion (fun y : Z => G.edgesTo y.val B))
    (x : Z) : (G.restrictEdges T).degree x.val = (T ∩ G.edgesTo x.val B).card := by
  rw [Multigraph.restrictEdges_degree]
  congr 1
  ext e
  simp only [Finset.mem_inter, Multigraph.mem_incidenceEdges]
  constructor
  · exact fun h => ⟨h.1, correction_pool_incidence G B Z hBZ x e (hT h.1) h.2⟩
  · exact fun h => ⟨h.1, ((G.mem_edgesTo x.val B e).mp h.2).1⟩

/-- Construct actual graph correction copies of any prescribed size up
to the exact capacity, with the requested exceptional degrees. -/
theorem exists_graph_correction_subset
    (B Z : Finset V) (hBZ : Disjoint B Z) (cap : Z → ℕ)
    (t : ℕ) (ht : t ≤ (G.internalEdges B).card +
      ∑ x : Z, min (G.edgesTo x.val B).card (cap x)) :
    ∃ T : Finset E,
      T ⊆ G.internalEdges B ∪ univ.biUnion (fun x : Z => G.edgesTo x.val B) ∧
      T.card = t ∧ ∀ x : Z, (G.restrictEdges T).degree x.val ≤ cap x := by
  obtain ⟨h₀, hdisj⟩ := correction_pools_disjoint G B Z hBZ
  obtain ⟨T, hT, hcard, hcap⟩ := CorrectionCapacity.exists_correction_subset
    (G.internalEdges B) (fun x : Z => G.edgesTo x.val B) cap h₀ hdisj t ht
  refine ⟨T, hT, hcard, ?_⟩
  intro x
  rw [correction_selection_degree G B Z hBZ T hT x]
  exact hcap x

/-- The score in the manuscript constructs an actual correction set
after any deletion satisfying its weighted loss budget. -/
theorem exists_graph_correction_subset_after_deletion
    (B Z : Finset V) (hBZ : Disjoint B Z) (cap : Z → ℕ)
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂) (hω₂ : ω₂ ≤ 1)
    (D : Finset E) (t : ℕ)
    (ht : (t : ℝ) ≤ ω₂ * (G.internalEdges B).card +
      (∑ x : Z, min (ω₁ * (G.edgesTo x.val B).card) (cap x : ℝ)) - ω₂ * D.card) :
    ∃ T : Finset E,
      T ⊆ G.internalEdges B ∪ univ.biUnion (fun x : Z => G.edgesTo x.val B) ∧
      Disjoint T D ∧ T.card = t ∧
      ∀ x : Z, (G.restrictEdges T).degree x.val ≤ cap x := by
  obtain ⟨h₀, hdisj⟩ := correction_pools_disjoint G B Z hBZ
  obtain ⟨T, hT, havoid, hcard, hcap⟩ := CorrectionCapacity.exists_correction_subset_after_deletion
    (G.internalEdges B) (fun x : Z => G.edgesTo x.val B) cap h₀ hdisj
    ω₁ ω₂ hω₁ hω₁₂ hω₂ D t ht
  refine ⟨T, hT, havoid, hcard, ?_⟩
  intro x
  rw [correction_selection_degree G B Z hBZ T hT x]
  exact hcap x

/-- Only deleted copies belonging to this correction pool consume its score
budget. The selected actual copies still avoid the entire deleted set. -/
theorem exists_graph_correction_subset_after_pool_deletion
    (B Z : Finset V) (hBZ : Disjoint B Z) (cap : Z → ℕ)
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂) (hω₂ : ω₂ ≤ 1)
    (D : Finset E) (t : ℕ)
    (ht : (t : ℝ) ≤ ω₂ * (G.internalEdges B).card +
      (∑ x : Z, min (ω₁ * (G.edgesTo x.val B).card) (cap x : ℝ)) -
        ω₂ * (D ∩ (G.internalEdges B ∪
          univ.biUnion (fun x : Z => G.edgesTo x.val B))).card) :
    ∃ T : Finset E,
      T ⊆ G.internalEdges B ∪ univ.biUnion (fun x : Z => G.edgesTo x.val B) ∧
      Disjoint T D ∧ T.card = t ∧
      ∀ x : Z, (G.restrictEdges T).degree x.val ≤ cap x := by
  obtain ⟨T, hT, havoid, hcard, hcap⟩ :=
    exists_graph_correction_subset_after_deletion G B Z hBZ cap
      ω₁ ω₂ hω₁ hω₁₂ hω₂
      (D ∩ (G.internalEdges B ∪ univ.biUnion (fun x : Z => G.edgesTo x.val B))) t ht
  refine ⟨T, hT, ?_, hcard, hcap⟩
  apply Finset.disjoint_left.mpr
  intro e he heD
  exact (Finset.disjoint_left.mp havoid) he (Finset.mem_inter.mpr ⟨heD, hT he⟩)

end Overfull.BipartiteFactorization
