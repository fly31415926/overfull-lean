import Overfull.WeightedPalette.Loads

/-!
# Dynamic weighted extension of a prescribed palette

A finite greedy construction retains the prescribed primary labels while
controlling each whole color class, both by its number of pieces and by
every resource weight. Protected labels are excluded only for new pieces;
the initial primary pieces may already occupy those labels.

The total resource bounds count all target pieces, including the seeds.
They control the dynamically overloaded colors at every insertion.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {J κ : Type*} [Fintype κ]

/-- Extend a proper prescribed coloring while retaining bounded class
cardinality and every resource load. Only surplus pieces must avoid the
fixed protected palette labels. Resource totals include all seed pieces. -/
theorem exists_weighted_palette_extension
    (R : J → J → Prop) (hsymm : Symmetric R) (hirrefl : Irreflexive R)
    (T P : Finset J) (hPT : P ⊆ T) {h B K L q W : ℕ}
    (c₀ : J → Fin h) (Q : Finset (Fin h)) (w : κ → J → ℕ)
    (hproper : ∀ x ∈ P, ∀ y ∈ P, R x y → c₀ x ≠ c₀ y)
    (hload : ∀ i, (P.filter (fun x => c₀ x = i)).card ≤ L)
    (hseedWeight : ∀ r i, paletteWeight P c₀ (w r) i ≤ W)
    (hdegree : ∀ x ∈ T \ P, (T.filter (R x)).card ≤ B)
    (hweight : ∀ r, ∀ x ∈ T \ P, w r x ≤ q)
    (htotal : ∀ r, ∑ x ∈ T, w r x ≤ K * (W - q + 1))
    (hqW : q ≤ W)
    (hmargin : B + Q.card + Fintype.card κ * K < h)
    (hsize : T.card ≤ L * (h - (B + Q.card + Fintype.card κ * K))) :
    ∃ c : J → Fin h,
      (∀ x ∈ P, c x = c₀ x) ∧
      (∀ x ∈ T, ∀ y ∈ T, R x y → c x ≠ c y) ∧
      (∀ x ∈ T \ P, c x ∉ Q) ∧
      (∀ i, (T.filter (fun x => c x = i)).card ≤ L) ∧
      (∀ r i, paletteWeight T c (w r) i ≤ W) := by
  have hstep : ∀ U : Finset J, U ⊆ T \ P →
      ∃ c : J → Fin h,
        (∀ x ∈ P, c x = c₀ x) ∧
        (∀ x ∈ P ∪ U, ∀ y ∈ P ∪ U, R x y → c x ≠ c y) ∧
        (∀ x ∈ U, c x ∉ Q) ∧
        (∀ i, ((P ∪ U).filter (fun x => c x = i)).card ≤ L) ∧
        (∀ r i, paletteWeight (P ∪ U) c (w r) i ≤ W) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨c₀, fun _ _ => rfl, by simpa using hproper,
        by simp, by simpa using hload, by simpa using hseedWeight⟩
    | @insert x U hxU ih =>
      intro hUT
      have hxTP := hUT (mem_insert_self x U)
      have hxP : x ∉ P := (mem_sdiff.mp hxTP).2
      have hUT' : U ⊆ T \ P := (subset_insert _ _).trans hUT
      obtain ⟨c, hcP, hcproper, hcavoid, hcload, hcweight⟩ := ih hUT'
      let A := P ∪ U
      have hAT : A ⊆ T := union_subset hPT (hUT'.trans sdiff_subset)
      have hxA : x ∉ A := by simp [A, hxP, hxU]
      have hcardA : A.card < L * (h - (B + Q.card + Fintype.card κ * K)) := by
        have hsub : insert x A ⊆ T := insert_subset (mem_sdiff.mp hxTP).1 hAT
        have hc := card_le_card hsub
        rw [card_insert_of_notMem hxA] at hc
        omega
      let F₀ : Finset (Fin h) := (A.filter (R x)).image c
      have hF₀ : F₀.card ≤ B :=
        (card_image_le).trans ((card_le_card (filter_subset_filter _ hAT)).trans
          (hdegree x hxTP))
      have hpartial (r : κ) : ∑ y ∈ A, w r y ≤ K * (W - q + 1) := by
        exact (sum_le_sum_of_subset hAT).trans (htotal r)
      have hover (r : κ) : (overloadedPalettes A c (w r) q W).card ≤ K := by
        exact overloadedPalettes_card_le A c (w r) hqW (hpartial r)
      let Fw : Finset (Fin h) := univ.biUnion (fun r : κ =>
        overloadedPalettes A c (w r) q W)
      have hFw : Fw.card ≤ Fintype.card κ * K := by
        calc
          _ ≤ ∑ r : κ, (overloadedPalettes A c (w r) q W).card := card_biUnion_le
          _ ≤ ∑ _r : κ, K := sum_le_sum (fun r _ => hover r)
          _ = Fintype.card κ * K := by simp
      let F := F₀ ∪ Q ∪ Fw
      have hF : F.card ≤ B + Q.card + Fintype.card κ * K := by
        have hfirst := card_union_le F₀ Q
        have hsecond := card_union_le (F₀ ∪ Q) Fw
        change (F₀ ∪ Q ∪ Fw).card ≤ _
        omega
      obtain ⟨i, hiF, hiL⟩ := exists_available_palette A c F hF hmargin hcardA
      have hiF₀ : i ∉ F₀ := by
        intro hi
        exact hiF (mem_union_left _ (mem_union_left _ hi))
      have hiQ : i ∉ Q := by
        intro hi
        exact hiF (mem_union_left _ (mem_union_right _ hi))
      have hiweight (r : κ) : paletteWeight A c (w r) i ≤ W - q := by
        by_contra hn
        have hi : i ∈ overloadedPalettes A c (w r) q W := by
          exact mem_filter.mpr ⟨mem_univ _, Nat.lt_of_not_ge hn⟩
        exact hiF (mem_union_right _ (mem_biUnion.mpr ⟨r, mem_univ _, hi⟩))
      let d := Function.update c x i
      have hdx : d x = i := Function.update_self ..
      have hd (y : J) (hy : y ∈ A) : d y = c y := by
        apply Function.update_of_ne
        intro heq
        exact hxA (heq ▸ hy)
      have hfree (y : J) (hy : y ∈ A) (hxy : R x y) : i ≠ c y := by
        intro heq
        exact hiF₀ (heq ▸ mem_image_of_mem c (mem_filter.mpr ⟨hy, hxy⟩))
      have hdomain : P ∪ insert x U = insert x A := by
        ext y
        simp only [A, mem_union, mem_insert]
        tauto
      have hfilter (j : Fin h) : (A.filter (fun y => d y = j)) =
          A.filter (fun y => c y = j) := by
        apply filter_congr
        intro y hy
        rw [hd y hy]
      refine ⟨d, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rw [hd y (mem_union_left _ hy)]
        exact hcP y hy
      · rw [hdomain]
        intro y hy z hz hyz
        rcases mem_insert.mp hy with hyx | hyA
        · subst y
          rcases mem_insert.mp hz with hzx | hzA
          · subst z
            exact (hirrefl _ hyz).elim
          · rw [hdx, hd z hzA]
            exact hfree z hzA hyz
        · rcases mem_insert.mp hz with hzx | hzA
          · subst z
            rw [hd y hyA, hdx]
            exact (hfree y hyA (hsymm hyz)).symm
          · rw [hd y hyA, hd z hzA]
            exact hcproper y hyA z hzA hyz
      · intro y hy
        rcases mem_insert.mp hy with hyx | hyU
        · subst y
          rw [hdx]
          exact hiQ
        · rw [hd y (mem_union_right _ hyU)]
          exact hcavoid y hyU
      · rw [hdomain]
        intro j
        rw [filter_insert, hdx, hfilter]
        split_ifs with hij
        · subst j
          rw [card_insert_of_notMem (fun hh => hxA (mem_filter.mp hh).1)]
          omega
        · exact hcload j
      · rw [hdomain]
        intro r j
        unfold paletteWeight
        rw [filter_insert, hdx, hfilter]
        split_ifs with hij
        · subst j
          rw [sum_insert (fun hh => hxA (mem_filter.mp hh).1)]
          have hwi := hiweight r
          have hwx := hweight r x hxTP
          unfold paletteWeight at hwi
          omega
        · exact hcweight r j
  obtain ⟨c, hcP, hcproper, hcavoid, hcload, hcweight⟩ := hstep (T \ P) (by rfl)
  rw [union_sdiff_of_subset hPT] at hcproper hcload hcweight
  exact ⟨c, hcP, hcproper, hcavoid, hcload, hcweight⟩

end Overfull.NativeReserve
