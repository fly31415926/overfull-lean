import Overfull.RobustPartition.Counting
import Overfull.RobustPartition.Induced

/-!
# Splitting a block which is not a robust expander

The construction uses an actual failed robust-neighborhood test.  A block with
a small external boundary either splits into two large blocks with small
boundaries, or admits two large shores with few incidences away from the
opposite shore.  The ambient graph need only have degrees in a short interval.
-/

namespace Overfull.RobustPartition

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- The two possible outcomes of splitting an ordinary component. -/
def SplitOutcome (G : SimpleGraph V) (a μ : ℝ) (U : Finset V) : Prop :=
  ∃ P Q : Finset V, Disjoint P Q ∧ P ∪ Q = U ∧
    a * (Fintype.card V : ℝ) / 2 ≤ (P.card : ℝ) ∧
    a * (Fintype.card V : ℝ) / 2 ≤ (Q.card : ℝ) ∧
    ((cut G P ≤ μ * (Fintype.card V : ℝ)^2 ∧
      cut G Q ≤ μ * (Fintype.card V : ℝ)^2) ∨
     (bad G P Q ≤ μ * (Fintype.card V : ℝ)^2 ∧
      |(P.card : ℝ) - Q.card| ≤ μ * (Fintype.card V : ℝ)))

/-- A positive source shore and a small off-target incidence count force the
target shore to be large.  The product formulation avoids dividing by the
source size in subsequent applications. -/
private theorem target_size_of_off_incidence (G : SimpleGraph V)
    (a d n r t c : ℝ) (hn : 0 < n) (hr : 0 < r) (hta : t ≤ a)
    (had : a * n ≤ d) (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (A X : Finset V) (hA : r * n ≤ (A.card : ℝ))
    (hoff : ecount G A Xᶜ ≤ c * n^2) (hc : c ≤ (a - t) * r) :
    t * n ≤ (X.card : ℝ) := by
  by_contra hX
  have hXlt : (X.card : ℝ) < t * n := lt_of_not_ge hX
  have hApos : 0 < (A.card : ℝ) := (mul_pos hr hn).trans_le hA
  have hinc := min_degree_mul_card_le G d hdegree A X
  have hmax := ecount_le_mul_card G A X
  have hlow : (a - t) * n * (r * n) ≤
      (a - t) * n * (A.card : ℝ) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg (sub_nonneg.mpr hta) hn.le)
  have hstrict : (a - t) * n * (A.card : ℝ) <
      (d - (X.card : ℝ)) * (A.card : ℝ) :=
    mul_lt_mul_of_pos_right (by nlinarith only [had, hXlt]) hApos
  have hbudget := mul_le_mul_of_nonneg_right hc (sq_nonneg n)
  nlinarith only [hinc, hmax, hoff, hlow, hstrict, hbudget]

/-- Every vertex outside the local robust neighborhood sends fewer than the
threshold number of incidences into the tested set. -/
private theorem outside_localRN_incidence (G : SimpleGraph V)
    (U S : Finset V) (ν : ℝ) (hν : 0 ≤ ν) :
    ecount G S (U \ localRN G U ν S) ≤
      ν * (Fintype.card V : ℝ)^2 := by
  let n : ℝ := Fintype.card V
  let N := localRN G U ν S
  have hUn : (U.card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ U
  have hRn : ((U \ N).card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ (U \ N)
  have hsum : ecount G (U \ N) S ≤
      ((U \ N).card : ℝ) * (ν * n) := by
    rw [ecount_eq_sum]
    calc
      _ ≤ ∑ _v ∈ U \ N, ν * n := by
        apply Finset.sum_le_sum
        intro v hv
        have hvU := (Finset.mem_sdiff.mp hv).1
        have hvN := (Finset.mem_sdiff.mp hv).2
        have hbelow : ((G.neighborFinset v ∩ S).card : ℝ) <
            ν * (U.card : ℝ) := by
          apply lt_of_not_ge
          intro hcount
          apply hvN
          exact Finset.mem_filter.mpr ⟨hvU, hcount⟩
        exact hbelow.le.trans (mul_le_mul_of_nonneg_left hUn hν)
      _ = _ := by simp
  have hbound := mul_le_mul_of_nonneg_right hRn (mul_nonneg hν (by positivity : 0 ≤ n))
  rw [ecount_symm G S]
  change ecount G (U \ N) S ≤ ν * n^2
  nlinarith only [hsum, hbound]

/-- A failed robust-neighborhood test produces a genuine split or a genuine
approximately bipartite block, with quantitative uniform error bounds. -/
theorem split_of_nonexpanding_witness (G : SimpleGraph V)
    (a τ d γ ε ν μ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hn : 0 < (Fintype.card V : ℝ))
    (_hγ : 0 ≤ γ) (_hε : 0 ≤ ε) (hν : 0 < ν) (hμ : 0 < μ)
    (hμsmall : 100 * μ ≤ τ * a^2) (hνsmall : 200 * ν ≤ a * μ)
    (hεν : ε ≤ ν) (hγν : γ ≤ ν)
    (had : a * (Fintype.card V : ℝ) ≤ d)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hdegree' : ∀ v, (G.degree v : ℝ) ≤ d + γ * (Fintype.card V : ℝ))
    (U : Finset V)
    (hUsize : a * (Fintype.card V : ℝ) / 2 ≤ (U.card : ℝ))
    (hUcut : cut G U ≤ ε * (Fintype.card V : ℝ)^2)
    (S : Finset V) (hSU : S ⊆ U)
    (hSlow : τ * (U.card : ℝ) ≤ (S.card : ℝ))
    (hShigh : (S.card : ℝ) ≤ (1 - τ) * U.card)
    (hfail : (localRN G U ν S).card < (S.card : ℝ) + ν * U.card) :
    SplitOutcome G a μ U := by
  let n : ℝ := Fintype.card V
  let N := localRN G U ν S
  let Y := S \ N
  let Z := N \ S
  let h : ℝ := μ / 10
  change 0 < n at hn
  change a * n ≤ d at had
  change a * n / 2 ≤ (U.card : ℝ) at hUsize
  change cut G U ≤ ε * n^2 at hUcut
  change (N.card : ℝ) < (S.card : ℝ) + ν * U.card at hfail
  have hh : 0 < h := by dsimp [h]; positivity
  have hμh : μ = 10 * h := by dsimp [h]; ring
  rw [hμh] at hμsmall hνsmall
  have ha2 : a^2 ≤ a := by
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  have ha21 : a^2 ≤ 1 := ha2.trans ha1
  have hh1 : h ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left ha21 hτ.le
    nlinarith only [ht, hμsmall, hτhalf]
  have h20 : 20 * ν ≤ a * h := by nlinarith only [hνsmall]
  have h20' : 20 * ν ≤ h :=
    h20.trans (mul_le_of_le_one_left hh.le ha1)
  have hνh : ν ≤ h := by linarith only [h20', hν]
  have hνa : ν ≤ a / 4 := by
    have ht := mul_le_mul_of_nonneg_left hh1 ha.le
    nlinarith only [ht, h20, hν]
  have hspan : h + ν ≤ τ * a / 4 := by
    have ht := mul_le_mul_of_nonneg_left ha2 hτ.le
    nlinarith only [ht, hμsmall, h20', hh]
  have hboot : 2 * h ≤ (a - a / 2) * (τ * a / 4) := by
    nlinarith only [hμsmall, hh]
  have hbadbudget : 8 * ν + h ≤ μ := by
    rw [hμh]
    linarith only [h20', hh]
  have himbalancebudget : 3 * ν + a * h ≤ a * μ := by
    rw [hμh]
    nlinarith only [h20, mul_pos ha hh]
  have hNsub : N ⊆ U := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hYnS : Y ⊆ S := Finset.sdiff_subset
  have hZnN : Z ⊆ N := Finset.sdiff_subset
  have hZnU : Z ⊆ U := hZnN.trans hNsub
  have hYnU : Y ⊆ U := hYnS.trans hSU
  have hUn : (U.card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ U
  have hNn : (N.card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ N
  have hYn : (Y.card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ Y
  have hZn : (Z.card : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast Finset.card_le_univ Z
  have hY0 : 0 ≤ (Y.card : ℝ) := Nat.cast_nonneg _
  have hZ0 : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := (mul_pos ha hn).le.trans had
  have hdn : d ≤ n := by
    have hUpos : 0 < U.card := by
      exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < a * n / 2) hUsize)
    obtain ⟨v, _hv⟩ := Finset.card_pos.mp hUpos
    have hdv : (G.degree v : ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast (G.degree_lt_card_verts v).le
    exact (hdegree v).trans hdv
  have houtside : ecount G S (U \ N) ≤ ν * n^2 :=
    outside_localRN_incidence G U S ν hν.le
  have hloss : ecount G S Nᶜ ≤ 2 * ν * n^2 := by
    have hcomp : Nᶜ ⊆ (U \ N) ∪ Uᶜ := by
      intro v hv
      simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union] at hv ⊢
      tauto
    have hleft := ecount_mono G (Finset.Subset.refl S) hcomp
    have hsum := ecount_union_right_le G S (U \ N) Uᶜ
    have hexternal : ecount G S Uᶜ ≤ cut G U :=
      ecount_mono G hSU (Finset.Subset.refl _)
    have hbudget := mul_le_mul_of_nonneg_right hεν (sq_nonneg n)
    linarith only [hleft, hsum, hexternal, houtside, hUcut, hbudget]
  have hbalance : a * ((S.card : ℝ) - N.card) ≤ 3 * ν * n := by
    by_cases hSN : (S.card : ℝ) ≤ N.card
    · have hleft : a * ((S.card : ℝ) - N.card) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hSN)
      exact hleft.trans (by positivity)
    · have hSN' : 0 ≤ (S.card : ℝ) - N.card := by linarith only [hSN]
      have hlow := min_degree_mul_card_le G d hdegree S N
      have hupp := ecount_le_max_degree_mul_card G (d + γ * n) hdegree' N S
      rw [ecount_symm G N S] at hupp
      have hdeg := mul_le_mul_of_nonneg_right had hSN'
      have hg1 := mul_le_mul_of_nonneg_right hγν
        (mul_nonneg hn.le (Nat.cast_nonneg N.card))
      have hg2 := mul_le_mul_of_nonneg_left hNn (mul_nonneg hν.le hn.le)
      have hscaled : n * (a * ((S.card : ℝ) - N.card)) ≤ n * (3 * ν * n) := by
        nlinarith only [hlow, hupp, hdeg, hg1, hg2, hloss]
      exact (mul_le_mul_iff_right₀ hn).mp hscaled
  have hreverse : (N.card : ℝ) - S.card ≤ ν * n := by
    have hmul := mul_le_mul_of_nonneg_left hUn hν.le
    linarith only [hmul, hfail]
  have hYZ : (Y.card : ℝ) - Z.card = (S.card : ℝ) - N.card := by
    have hS' : ((S ∩ N).card : ℝ) + Y.card = S.card := by
      exact_mod_cast Finset.card_inter_add_card_sdiff S N
    have hN' : ((S ∩ N).card : ℝ) + Z.card = N.card := by
      simpa only [Finset.inter_comm] using
        (show ((N ∩ S).card : ℝ) + (N \ S).card = N.card by
          exact_mod_cast Finset.card_inter_add_card_sdiff N S)
    linarith only [hS', hN']
  have hYZbalance : a * ((Y.card : ℝ) - Z.card) ≤ 3 * ν * n := by
    rw [hYZ]
    exact hbalance
  have hYZreverse : (Z.card : ℝ) - Y.card ≤ ν * n := by
    linarith only [hYZ, hreverse]
  have hYZdisj : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    exact (Finset.mem_sdiff.mp hvY).2 (Finset.mem_sdiff.mp hvZ).1
  -- The two cases distinguish a nearly closed neighborhood from two shores.
  by_cases hsmall : (Y.card : ℝ) ≤ h * n
  · let P := S ∪ N
    let Q := U \ P
    have hPsub : P ⊆ U := Finset.union_subset hSU hNsub
    have hPQ : P ∪ Q = U := by
      exact Finset.union_sdiff_of_subset hPsub
    have hPQdisj : Disjoint P Q := disjoint_sdiff_self_right
    have hPdecomp : P = S ∪ Z := by
      ext v
      simp only [P, Z, Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hSZ : Disjoint S Z := disjoint_sdiff_self_right
    have hPcard : (P.card : ℝ) = S.card + Z.card := by
      rw [hPdecomp, Finset.card_union_of_disjoint hSZ, Nat.cast_add]
    have hQcard : (Q.card : ℝ) + P.card = U.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hPsub
    have hZsmall : (Z.card : ℝ) ≤ (h + ν) * n := by
      nlinarith only [hsmall, hYZreverse]
    have hPseed : (τ * a / 4) * n ≤ (P.card : ℝ) := by
      have hlow := mul_le_mul_of_nonneg_left hUsize hτ.le
      nlinarith only [hlow, hSlow, hPcard, hZ0, mul_pos hτ (mul_pos ha hn)]
    have hQseed : (τ * a / 4) * n ≤ (Q.card : ℝ) := by
      have hlow := mul_le_mul_of_nonneg_left hUsize hτ.le
      have hwidth := mul_le_mul_of_nonneg_right hspan hn.le
      nlinarith only [hlow, hwidth, hQcard, hPcard, hShigh, hZsmall]
    have hPcut : cut G P ≤ (h + 3 * ν) * n^2 := by
      have hcomp : Pᶜ ⊆ Nᶜ := by
        intro v hv
        simp only [P, Finset.mem_compl, Finset.mem_union] at hv ⊢
        tauto
      have hsum := ecount_union_left_le G S Z Pᶜ
      have hSbound := ecount_mono G (Finset.Subset.refl S) hcomp
      have hZbound := ecount_le_mul_card G Z Pᶜ
      have hPn : ((Pᶜ).card : ℝ) ≤ n := by
        dsimp only [n]
        exact_mod_cast Finset.card_le_univ Pᶜ
      have hZprod := mul_le_mul_of_nonneg_left hPn hZ0
      have hZtotal := mul_le_mul_of_nonneg_right hZsmall hn.le
      have hPsum : cut G P ≤ ecount G S Pᶜ + ecount G Z Pᶜ := by
        calc
          cut G P = ecount G (S ∪ Z) Pᶜ := congrArg (fun T => ecount G T Pᶜ) hPdecomp
          _ ≤ _ := hsum
      nlinarith only [hPsum, hSbound, hloss, hZbound, hZprod, hZtotal]
    have hPcut' : cut G P ≤ 2 * h * n^2 := by
      have hparam : h + 3 * ν ≤ 2 * h := by linarith only [h20', hν]
      exact hPcut.trans (mul_le_mul_of_nonneg_right hparam (sq_nonneg n))
    have hQcut' : cut G Q ≤ 2 * h * n^2 := by
      have hcut := cut_sdiff_le G U P
      have hbudget := mul_le_mul_of_nonneg_right hεν (sq_nonneg n)
      have hparam : h + 4 * ν ≤ 2 * h := by linarith only [h20', hν]
      have hparam' := mul_le_mul_of_nonneg_right hparam (sq_nonneg n)
      change cut G Q ≤ cut G U + cut G P at hcut
      linarith only [hcut, hUcut, hPcut, hbudget, hparam']
    have hPsize : a * n / 2 ≤ (P.card : ℝ) := by
      have hm := target_size_of_off_incidence G a d n (τ * a / 4) (a / 2)
        (2 * h) hn (by positivity) (by linarith only [ha]) had hdegree P P hPseed hPcut' hboot
      nlinarith only [hm]
    have hQsize : a * n / 2 ≤ (Q.card : ℝ) := by
      have hm := target_size_of_off_incidence G a d n (τ * a / 4) (a / 2)
        (2 * h) hn (by positivity) (by linarith only [ha]) had hdegree Q Q hQseed hQcut' hboot
      nlinarith only [hm]
    refine ⟨P, Q, hPQdisj, hPQ, hPsize, hQsize, Or.inl ⟨?_, ?_⟩⟩
    · exact hPcut'.trans (mul_le_mul_of_nonneg_right (by linarith only [hμh, hh]) (sq_nonneg n))
    · exact hQcut'.trans (mul_le_mul_of_nonneg_right (by linarith only [hμh, hh]) (sq_nonneg n))
  · have hlarge : h * n ≤ (Y.card : ℝ) := (lt_of_not_ge hsmall).le
    have hYS : ecount G Y S ≤ ν * n^2 := by
      have hsub : Y ⊆ U \ N := by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨hSU (Finset.mem_sdiff.mp hv).1,
          (Finset.mem_sdiff.mp hv).2⟩
      rw [ecount_symm G Y S]
      exact (ecount_mono G (Finset.Subset.refl _) hsub).trans houtside
    have hYoff : ecount G Y Zᶜ ≤ 3 * ν * n^2 := by
      have hcomp : Zᶜ = S ∪ Nᶜ := by
        ext v
        simp only [Z, Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
        tauto
      rw [hcomp]
      have hsum := ecount_union_right_le G Y S Nᶜ
      have hmono := ecount_mono G hYnS (Finset.Subset.refl Nᶜ)
      linarith only [hsum, hmono, hYS, hloss]
    have hZlarge : 3 * a / 4 * n ≤ (Z.card : ℝ) := by
      exact target_size_of_off_incidence G a d n h (3 * a / 4) (3 * ν)
        hn hh (by linarith only [ha]) had hdegree Y Z hlarge hYoff
        (by nlinarith only [h20, hν])
    have hZsize : a * n / 2 ≤ (Z.card : ℝ) := by
      have hap := mul_pos ha hn
      nlinarith only [hZlarge, hap]
    have hYsize : a * n / 2 ≤ (Y.card : ℝ) := by
      have hνan := mul_le_mul_of_nonneg_right hνa hn.le
      nlinarith only [hZlarge, hνan, hYZreverse]
    have hZoff : ecount G Z Yᶜ ≤ 5 * ν * n^2 := by
      have hlow := min_degree_mul_card_le G d hdegree Y Z
      have hsum := ecount_add_compl G Z Y
      have hupp := ecount_le_max_degree_mul_card G (d + γ * n) hdegree' Z univ
      rw [ecount_univ] at hupp
      rw [ecount_symm G Z Y] at hsum
      have hdrev := mul_le_mul_of_nonneg_left hYZreverse hd0
      have hdν := mul_le_mul_of_nonneg_right hdn (mul_nonneg hν.le hn.le)
      have hg1 := mul_le_mul_of_nonneg_right hγν (mul_nonneg hn.le hZ0)
      have hg2 := mul_le_mul_of_nonneg_left hZn (mul_nonneg hν.le hn.le)
      nlinarith only [hlow, hsum, hupp, hdrev, hdν, hg1, hg2, hYoff]
    have hbad : bad G Y Z ≤ 8 * ν * n^2 := by
      unfold bad
      linarith only [hYoff, hZoff]
    let P := Y ∪ Z
    let Q := U \ P
    have hPsub : P ⊆ U := Finset.union_subset hYnU hZnU
    have hPQ : P ∪ Q = U := Finset.union_sdiff_of_subset hPsub
    have hPQdisj : Disjoint P Q := disjoint_sdiff_self_right
    have hPcut : cut G P ≤ 8 * ν * n^2 :=
      (cut_union_le_bad G Y Z).trans hbad
    have hQcut : cut G Q ≤ 9 * ν * n^2 := by
      have hcut := cut_sdiff_le G U P
      have hbudget := mul_le_mul_of_nonneg_right hεν (sq_nonneg n)
      change cut G Q ≤ cut G U + cut G P at hcut
      linarith only [hcut, hUcut, hPcut, hbudget]
    by_cases hQlarge : h * n ≤ (Q.card : ℝ)
    · have hPsize : a * n / 2 ≤ (P.card : ℝ) :=
        hYsize.trans (by exact_mod_cast Finset.card_le_card (show Y ⊆ P from Finset.subset_union_left))
      have hQsize : a * n / 2 ≤ (Q.card : ℝ) := by
        have hboot' : 9 * ν ≤ (a - a / 2) * h := by nlinarith only [h20, hν]
        have hm := target_size_of_off_incidence G a d n h (a / 2) (9 * ν)
          hn hh (by linarith only [ha]) had hdegree Q Q hQlarge hQcut hboot'
        nlinarith only [hm]
      refine ⟨P, Q, hPQdisj, hPQ, hPsize, hQsize, Or.inl ⟨?_, ?_⟩⟩
      · exact hPcut.trans (mul_le_mul_of_nonneg_right
          (by linarith only [h20', hμh, hh]) (sq_nonneg n))
      · exact hQcut.trans (mul_le_mul_of_nonneg_right
          (by linarith only [h20', hμh, hh]) (sq_nonneg n))
    · let A := Y ∪ Q
      have hQsmall : (Q.card : ℝ) ≤ h * n := (lt_of_not_ge hQlarge).le
      have hQY : Disjoint Y Q := by
        exact hPQdisj.mono_left Finset.subset_union_left
      have hQZ : Disjoint Q Z := by
        exact (hPQdisj.mono_left Finset.subset_union_right).symm
      have hAZ : Disjoint A Z := Finset.disjoint_union_left.mpr ⟨hYZdisj, hQZ⟩
      have hAZunion : A ∪ Z = U := by
        calc
          _ = (Y ∪ Z) ∪ Q := by
            ext v
            simp only [A, Finset.mem_union]
            tauto
          _ = U := hPQ
      have hAsize : a * n / 2 ≤ (A.card : ℝ) :=
        hYsize.trans (by exact_mod_cast Finset.card_le_card (show Y ⊆ A from Finset.subset_union_left))
      have hAcard : (A.card : ℝ) = Y.card + Q.card := by
        dsimp only [A]
        rw [Finset.card_union_of_disjoint hQY, Nat.cast_add]
      have hAbad : bad G A Z ≤ (8 * ν + h) * n^2 := by
        have hcomp : Aᶜ ⊆ Yᶜ := by
          intro v hv
          simp only [A, Finset.mem_compl, Finset.mem_union] at hv ⊢
          tauto
        have hmono := ecount_mono G (Finset.Subset.refl Z) hcomp
        have hsum := ecount_union_left_le G Y Q Zᶜ
        have hQbound := ecount_le_mul_card G Q Zᶜ
        have hZn' : ((Zᶜ).card : ℝ) ≤ n := by
          dsimp only [n]
          exact_mod_cast Finset.card_le_univ Zᶜ
        have hQprod := mul_le_mul_of_nonneg_left hZn' (Nat.cast_nonneg Q.card)
        have hQtotal := mul_le_mul_of_nonneg_right hQsmall hn.le
        change ecount G A Zᶜ ≤ ecount G Y Zᶜ + ecount G Q Zᶜ at hsum
        unfold bad at hbad ⊢
        nlinarith only [hmono, hsum, hQbound, hQprod, hQtotal, hbad]
      have hAimbalance : |(A.card : ℝ) - Z.card| ≤ μ * n := by
        apply abs_le.mpr
        constructor
        · have hparam : ν ≤ μ := by linarith only [h20', hμh, hh]
          have hbudget := mul_le_mul_of_nonneg_right hparam hn.le
          have hQ0 : 0 ≤ (Q.card : ℝ) := Nat.cast_nonneg _
          linarith only [hbudget, hQ0, hAcard, hYZreverse]
        · have hQweighted := mul_le_mul_of_nonneg_left hQsmall ha.le
          have hbudget := mul_le_mul_of_nonneg_right himbalancebudget hn.le
          have hweighted : a * ((A.card : ℝ) - Z.card) ≤ a * (μ * n) := by
            rw [hAcard]
            nlinarith only [hQweighted, hbudget, hYZbalance]
          exact (mul_le_mul_iff_right₀ ha).mp hweighted
      refine ⟨A, Z, hAZ, hAZunion, hAsize, hZsize, Or.inr ⟨?_, hAimbalance⟩⟩
      exact hAbad.trans (mul_le_mul_of_nonneg_right hbadbudget (sq_nonneg n))

/-- The quantitative dichotomy for failure of robust expansion in the actual
induced graph.  No partition or expansion assertion is assumed as an oracle. -/
theorem nonexpanding_block_split (G : SimpleGraph V)
    (a τ d γ ε ν μ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hn : 0 < (Fintype.card V : ℝ))
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hν : 0 < ν) (hμ : 0 < μ)
    (hμsmall : 100 * μ ≤ τ * a^2) (hνsmall : 200 * ν ≤ a * μ)
    (hεν : ε ≤ ν) (hγν : γ ≤ ν)
    (had : a * (Fintype.card V : ℝ) ≤ d)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hdegree' : ∀ v, (G.degree v : ℝ) ≤ d + γ * (Fintype.card V : ℝ))
    (U : Finset V)
    (hUsize : a * (Fintype.card V : ℝ) / 2 ≤ (U.card : ℝ))
    (hUcut : cut G U ≤ ε * (Fintype.card V : ℝ)^2)
    (hnot : ¬ IsRobustExpander (G.induce (U : Set V)) ν τ) :
    SplitOutcome G a μ U := by
  obtain ⟨S, hSU, hSlow, hShigh, hfail⟩ :=
    exists_bad_set_of_not_induced_robust G U ν τ hnot
  exact split_of_nonexpanding_witness G a τ d γ ε ν μ ha ha1 hτ hτhalf
    hn hγ hε hν hμ hμsmall hνsmall hεν hγν had hdegree hdegree'
    U hUsize hUcut S hSU hSlow hShigh hfail

end Overfull.RobustPartition
