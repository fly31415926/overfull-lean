import Mathlib.Tactic

/-!
# Selecting incidence classes while meeting every tight class

The incidence set is a finite set of actual edge copies. A class is tight
when it contains exactly half of these copies. Coarsening by one tight
class and its complement preserves the half-size bounds; any pair in
distinct coarse classes meets every original tight class.

These are selection tools for the three-label compatible-circuit problem.
They do not assert that a safely removable circuit exists.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K L : Type*}

/-- Two nonconstant coordinates on the same finite set have a pair on which
both coordinates differ. The copies themselves are necessarily distinct. -/
theorem exists_pair_distinct_both_coordinates
    (S : Finset E) (f : E → K) (g : E → L)
    (hf : ∃ e ∈ S, ∃ h ∈ S, f e ≠ f h)
    (hg : ∃ e ∈ S, ∃ h ∈ S, g e ≠ g h) :
    ∃ e ∈ S, ∃ h ∈ S, e ≠ h ∧ f e ≠ f h ∧ g e ≠ g h := by
  by_contra hnone
  have hsame {e h : E} (he : e ∈ S) (hh : h ∈ S)
      (hfd : f e ≠ f h) : g e = g h := by
    by_contra hgd
    exact hnone ⟨e, he, h, hh, fun heq => hfd (congrArg f heq), hfd, hgd⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hf
  have hgab := hsame ha hb hab
  have hconstant (e : E) (he : e ∈ S) : g e = g a := by
    by_cases hae : f a = f e
    · have hbe : f b ≠ f e := fun h => hab (hae.trans h.symm)
      exact (hsame hb he hbe).symm.trans hgab.symm
    · exact (hsame ha he hae).symm
  obtain ⟨c, hc, d, hd, hcd⟩ := hg
  exact hcd ((hconstant c hc).trans (hconstant d hd).symm)

/-- A subset larger than half the ambient incidence set cannot be
monochromatic when every class has at most half the ambient size. -/
theorem exists_distinct_classes_of_large_subset
    (S T : Finset E) (classOf : E → K) (hST : S ⊆ T)
    (hhalf : ∀ k, 2 * (T.filter (fun e => classOf e = k)).card ≤ T.card)
    (hlarge : T.card < 2 * S.card) :
    ∃ e ∈ S, ∃ h ∈ S, classOf e ≠ classOf h := by
  have hpos : 0 < S.card := by omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  by_contra! hconstant
  have hsub : S ⊆ T.filter (fun e => classOf e = classOf a) := by
    intro e he
    exact mem_filter.mpr ⟨hST he, hconstant e he a ha⟩
  have hcard := card_le_card hsub
  have hh := hhalf (classOf a)
  omega

/-- Two different tight classes cover every incidence: their disjoint
fibers each contain exactly half of the ambient finite set. -/
theorem mem_one_of_two_distinct_tight_classes
    (S : Finset E) (classOf : E → K) {k l : K} (hkl : k ≠ l)
    (hk : 2 * (S.filter (fun e => classOf e = k)).card = S.card)
    (hl : 2 * (S.filter (fun e => classOf e = l)).card = S.card)
    {e : E} (he : e ∈ S) : classOf e = k ∨ classOf e = l := by
  let A := S.filter (fun e => classOf e = k)
  let B := S.filter (fun e => classOf e = l)
  have hdisjoint : Disjoint A B := by
    apply disjoint_left.mpr
    intro a ha hb
    exact hkl ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
  have hsub : A ∪ B ⊆ S :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard : S.card ≤ (A ∪ B).card := by
    rw [card_union_of_disjoint hdisjoint]
    dsimp [A, B]
    omega
  have hcover : A ∪ B = S := eq_of_subset_of_card_le hsub hcard
  have hemem : e ∈ A ∪ B := by rw [hcover]; exact he
  rcases mem_union.mp hemem with ha | hb
  · exact Or.inl (mem_filter.mp ha).2
  · exact Or.inr (mem_filter.mp hb).2

/-- A coarser incidence map whose distinct pairs preserve original
compatibility and meet every tight original incidence class. -/
structure LocalCoarsening (S : Finset E) (classOf : E → K) where
  coarse : E → K ⊕ Bool
  identity_or_tight : (∀ e, coarse e = Sum.inl (classOf e)) ∨
    ∃ k, 2 * (S.filter (fun e => classOf e = k)).card = S.card ∧
      ∀ e, coarse e = Sum.inr (decide (classOf e = k))
  refines : ∀ e h, coarse e ≠ coarse h → classOf e ≠ classOf h
  half_bound : ∀ k, 2 * (S.filter (fun e => coarse e = k)).card ≤ S.card
  meets_tight : ∀ k, 2 * (S.filter (fun e => classOf e = k)).card = S.card →
    ∀ e ∈ S, ∀ h ∈ S, coarse e ≠ coarse h → classOf e = k ∨ classOf h = k

/-- Every finite incidence partition satisfying the local half-size bounds
admits a coarsening meeting all tight classes. No positivity, finiteness
of the class type, or parity hypothesis is needed. -/
theorem exists_localCoarsening (S : Finset E) (classOf : E → K)
    (hhalf : ∀ k, 2 * (S.filter (fun e => classOf e = k)).card ≤ S.card) :
    Nonempty (LocalCoarsening S classOf) := by
  by_cases htight : ∃ k, 2 * (S.filter (fun e => classOf e = k)).card = S.card
  · obtain ⟨k, hk⟩ := htight
    have hsum := S.filter_card_add_filter_neg_card_eq_card (fun e => classOf e = k)
    have hsum' : (S.filter (fun e => classOf e = k)).card +
        (S.filter (fun e => classOf e ≠ k)).card = S.card := by
      simpa only [ne_eq] using hsum
    have hcomplement :
        2 * (S.filter (fun e => classOf e ≠ k)).card = S.card := by omega
    refine ⟨{
      coarse := fun e => Sum.inr (decide (classOf e = k))
      identity_or_tight := Or.inr ⟨k, hk, fun _ => rfl⟩
      refines := ?_
      half_bound := ?_
      meets_tight := ?_
    }⟩
    · intro e h hdiff heq
      apply hdiff
      rw [heq]
    · intro q
      rcases q with q | q
      · simp
      · cases q
        · simpa using hcomplement.le
        · simpa using hk.le
    · intro l hl e he h hh hdiff
      by_cases hlk : l = k
      · subst l
        by_contra! hne
        apply hdiff
        simp [hne.1, hne.2]
      · rcases mem_one_of_two_distinct_tight_classes S classOf (Ne.symm hlk) hk hl he with
          heq | heq
        · rcases mem_one_of_two_distinct_tight_classes S classOf (Ne.symm hlk) hk hl hh with
            hhq | hhq
          · exact False.elim (hdiff (by simp [heq, hhq]))
          · exact Or.inr hhq
        · exact Or.inl heq
  · refine ⟨{
      coarse := fun e => Sum.inl (classOf e)
      identity_or_tight := Or.inl (fun _ => rfl)
      refines := ?_
      half_bound := ?_
      meets_tight := ?_
    }⟩
    · intro e h hdiff heq
      exact hdiff (congrArg Sum.inl heq)
    · intro q
      rcases q with q | q
      · simpa using hhalf q
      · simp
    · intro k hk
      exact False.elim (htight ⟨k, hk⟩)

/-- A local coarsening is nonconstant on any subset larger than half of
the ambient incidence set. -/
theorem LocalCoarsening.nonconstant_on_large_subset
    {S T : Finset E} {classOf : E → K} (L : LocalCoarsening T classOf)
    (hST : S ⊆ T) (hlarge : T.card < 2 * S.card) :
    ∃ e ∈ S, ∃ h ∈ S, L.coarse e ≠ L.coarse h := by
  apply exists_distinct_classes_of_large_subset S T L.coarse hST _ hlarge
  intro k
  convert L.half_bound k using 1
  congr 2
  ext e
  simp

/-- If a bundle exceeds half of each endpoint's incidence set, it has
a compatible pair meeting every local tight class at both endpoints. -/
theorem exists_pair_meeting_tight_classes_of_large_subset
    (B S T : Finset E) (f : E → K) (g : E → L)
    (hBS : B ⊆ S) (hBT : B ⊆ T)
    (hf : ∀ k, 2 * (S.filter (fun e => f e = k)).card ≤ S.card)
    (hg : ∀ l, 2 * (T.filter (fun e => g e = l)).card ≤ T.card)
    (hS : S.card < 2 * B.card) (hT : T.card < 2 * B.card) :
    ∃ e ∈ B, ∃ h ∈ B, e ≠ h ∧ f e ≠ f h ∧ g e ≠ g h ∧
      (∀ k, 2 * (S.filter (fun a => f a = k)).card = S.card → f e = k ∨ f h = k) ∧
      (∀ l, 2 * (T.filter (fun a => g a = l)).card = T.card → g e = l ∨ g h = l) := by
  obtain ⟨Lf⟩ := exists_localCoarsening S f hf
  obtain ⟨Lg⟩ := exists_localCoarsening T g hg
  obtain ⟨e, he, h, hh, hne, hfe, hge⟩ :=
    exists_pair_distinct_both_coordinates B Lf.coarse Lg.coarse
      (Lf.nonconstant_on_large_subset hBS hS) (Lg.nonconstant_on_large_subset hBT hT)
  refine ⟨e, he, h, hh, hne, Lf.refines e h hfe, Lg.refines e h hge, ?_, ?_⟩
  · intro k hk
    exact Lf.meets_tight k hk e (hBS he) h (hBS hh) hfe
  · intro l hl
    exact Lg.meets_tight l hl e (hBT he) h (hBT hh) hge

end Overfull.CompatibleCircuits
