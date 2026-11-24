import Overfull.Probability.WeightedSampling

/-!
# Weighted swap variance for uniform finite subsets

The proof conditions on a maximum-weight element of the ground set.
An exact add-one coupling controls the two conditional means.
-/

noncomputable section

namespace Overfull.SwapVariance

open Finset Classical

variable {E : Type*}

/-- Mean over all subsets of the prescribed size in an actual ground set. -/
def sliceMean (S : Finset E) (s : ℕ) (f : Finset E → ℝ) : ℝ :=
  (∑ T ∈ S.powersetCard s, f T) / (S.card.choose s : ℝ)

/-- Variance for the uniform fixed-cardinality distribution. -/
def sliceVariance (S : Finset E) (s : ℕ) (f : Finset E → ℝ) : ℝ :=
  sliceMean S s (fun T => (f T - sliceMean S s f) ^ 2)

theorem sliceMean_congr (S : Finset E) (s : ℕ) {f g : Finset E → ℝ}
    (h : ∀ T ∈ S.powersetCard s, f T = g T) : sliceMean S s f = sliceMean S s g := by
  unfold sliceMean
  rw [Finset.sum_congr rfl h]

theorem sliceMean_const (S : Finset E) (s : ℕ) (hs : s ≤ S.card) (a : ℝ) :
    sliceMean S s (fun _ => a) = a := by
  have hden : (S.card.choose s : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hs
  simp only [sliceMean, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  field_simp

theorem sliceMean_add (S : Finset E) (s : ℕ) (f g : Finset E → ℝ) :
    sliceMean S s (fun T => f T + g T) = sliceMean S s f + sliceMean S s g := by
  simp only [sliceMean, Finset.sum_add_distrib, add_div]

theorem sliceMean_sub (S : Finset E) (s : ℕ) (f g : Finset E → ℝ) :
    sliceMean S s (fun T => f T - g T) = sliceMean S s f - sliceMean S s g := by
  simp only [sliceMean, Finset.sum_sub_distrib, sub_div]

theorem sliceMean_const_mul (S : Finset E) (s : ℕ) (a : ℝ) (f : Finset E → ℝ) :
    sliceMean S s (fun T => a * f T) = a * sliceMean S s f := by
  simp only [sliceMean, ← Finset.mul_sum, mul_div_assoc]

theorem sliceMean_mono (S : Finset E) (s : ℕ) {f g : Finset E → ℝ}
    (h : ∀ T ∈ S.powersetCard s, f T ≤ g T) : sliceMean S s f ≤ sliceMean S s g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

theorem sliceVariance_eq (S : Finset E) (s : ℕ) (hs : s ≤ S.card)
    (f : Finset E → ℝ) :
    sliceVariance S s f = sliceMean S s (fun T => f T ^ 2) - sliceMean S s f ^ 2 := by
  have heq (T : Finset E) :
      (f T - sliceMean S s f) ^ 2 =
        (f T ^ 2 - (2 * sliceMean S s f) * f T) + sliceMean S s f ^ 2 := by ring
  simp only [sliceVariance, heq, sliceMean_add, sliceMean_sub, sliceMean_const_mul,
    sliceMean_const S s hs]
  ring

@[simp] theorem sliceMean_zero (S : Finset E) (f : Finset E → ℝ) :
    sliceMean S 0 f = f ∅ := by simp [sliceMean]

@[simp] theorem sliceMean_full (S : Finset E) (f : Finset E → ℝ) :
    sliceMean S S.card f = f S := by simp [sliceMean]

@[simp] theorem sliceVariance_zero (S : Finset E) (f : Finset E → ℝ) :
    sliceVariance S 0 f = 0 := by simp [sliceVariance]

@[simp] theorem sliceVariance_full (S : Finset E) (f : Finset E → ℝ) :
    sliceVariance S S.card f = 0 := by simp [sliceVariance]

/-- The two pieces of a slice according to membership of one element. -/
theorem slice_sum_insert (S : Finset E) (x : E) (hx : x ∉ S) (s : ℕ)
    (f : Finset E → ℝ) :
    (∑ T ∈ (insert x S).powersetCard (s + 1), f T) =
      (∑ T ∈ S.powersetCard s, f (insert x T)) +
        ∑ T ∈ S.powersetCard (s + 1), f T := by
  have hdisj : Disjoint (S.powersetCard (s + 1))
      ((S.powersetCard s).image (insert x)) := by
    apply Finset.disjoint_left.mpr
    intro T hT hTx
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hTx
    exact hx ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (insert x) (↑(S.powersetCard s) : Set (Finset E)) := by
    intro T hT R hR heq
    have hxT : x ∉ T := fun ht => hx ((Finset.mem_powersetCard.mp hT).1 ht)
    have hxR : x ∉ R := fun hr => hx ((Finset.mem_powersetCard.mp hR).1 hr)
    have h := congrArg (fun Q : Finset E => Q.erase x) heq
    simpa only [Finset.erase_insert hxT, Finset.erase_insert hxR] using h
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union hdisj,
    Finset.sum_image hinj, add_comm]

/-- Exact double counting of a uniformly chosen subset followed by one
uniformly chosen new element. Each larger subset has `s+1` preimages. -/
theorem add_one_sum (S : Finset E) (s : ℕ) (f : Finset E → ℝ) :
    (∑ T ∈ S.powersetCard s, ∑ y ∈ S \ T, f (insert y T)) =
      (s + 1 : ℝ) * ∑ T ∈ S.powersetCard (s + 1), f T := by
  have hsum :
      (∑ a ∈ (S.powersetCard s).sigma (fun T => S \ T), f (insert a.2 a.1)) =
      ∑ a ∈ (S.powersetCard (s + 1)).sigma (fun T => T), f a.1 := by
    apply Finset.sum_bij (fun a _ => ⟨insert a.2 a.1, a.2⟩)
    · intro a ha
      obtain ⟨hT, hy⟩ := Finset.mem_sigma.mp ha
      obtain ⟨hTS, hcard⟩ := Finset.mem_powersetCard.mp hT
      obtain ⟨hyS, hyT⟩ := Finset.mem_sdiff.mp hy
      apply Finset.mem_sigma.mpr
      exact ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset hyS hTS, by rw [Finset.card_insert_of_notMem hyT, hcard]⟩,
        Finset.mem_insert_self _ _⟩
    · intro a ha b hb hab
      have hy : a.2 = b.2 := congrArg Sigma.snd hab
      have hset : insert a.2 a.1 = insert b.2 b.1 := congrArg Sigma.fst hab
      have ha' := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp ha).2).2
      have hb' := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hb).2).2
      have hbase := congrArg (fun Q : Finset E => Q.erase a.2) hset
      dsimp only at hbase
      rw [Finset.erase_insert ha', hy, Finset.erase_insert hb'] at hbase
      exact Sigma.ext hbase (heq_of_eq hy)
    · intro b hb
      obtain ⟨hT, hy⟩ := Finset.mem_sigma.mp hb
      obtain ⟨hTS, hcard⟩ := Finset.mem_powersetCard.mp hT
      refine ⟨⟨b.1.erase b.2, b.2⟩, ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _ |>.trans hTS, ?_⟩,
          Finset.mem_sdiff.mpr ⟨hTS hy, Finset.notMem_erase _ _⟩⟩
        rw [Finset.card_erase_of_mem hy, hcard]
        omega
      · simp only [Finset.insert_erase hy]
    · intro a _
      rfl
  simp only [Finset.sum_sigma] at hsum
  calc
    _ = ∑ T ∈ S.powersetCard (s + 1), ∑ _y ∈ T, f T := hsum
    _ = ∑ T ∈ S.powersetCard (s + 1), (s + 1 : ℝ) * f T := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hT).2,
        Nat.cast_add, Nat.cast_one]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Uniform means on adjacent slices are coupled by adding one new
element. A pointwise difference bound therefore bounds their means. -/
theorem adjacent_slice_means (S : Finset E) (s : ℕ) (hs : s < S.card)
    (f g : Finset E → ℝ) (c : ℝ)
    (hfg : ∀ T ∈ S.powersetCard s, ∀ y ∈ S \ T,
      |g T - f (insert y T)| ≤ c) :
    |sliceMean S s g - sliceMean S (s + 1) f| ≤ c := by
  let b : ℝ := S.card - s
  have hb : 0 < b := by
    dsimp only [b]
    exact sub_pos.mpr (by exact_mod_cast hs)
  have hk : (0 : ℝ) < s + 1 := by positivity
  have hd₁ : (0 : ℝ) < S.card.choose s := by
    exact_mod_cast Nat.choose_pos hs.le
  have hd₂ : (0 : ℝ) < S.card.choose (s + 1) := by
    exact_mod_cast Nat.choose_pos hs
  have hcard (T : Finset E) (hT : T ∈ S.powersetCard s) : ((S \ T).card : ℝ) = b := by
    obtain ⟨hTS, ht⟩ := Finset.mem_powersetCard.mp hT
    rw [Finset.card_sdiff_of_subset hTS, ht, Nat.cast_sub hs.le]
  have hleft (g : Finset E → ℝ) :
      (∑ T ∈ S.powersetCard s, ∑ _y ∈ S \ T, g T) =
        b * ∑ T ∈ S.powersetCard s, g T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [Finset.sum_const, nsmul_eq_mul, hcard T hT]
  let Z := ∑ T ∈ S.powersetCard s, ∑ y ∈ S \ T, (g T - f (insert y T))
  have hZ : Z = b * (∑ T ∈ S.powersetCard s, g T) -
      (s + 1 : ℝ) * ∑ T ∈ S.powersetCard (s + 1), f T := by
    simp only [Z, Finset.sum_sub_distrib, hleft, add_one_sum]
  have hbound : |Z| ≤ b * (S.card.choose s : ℝ) * c := by
    calc
      |Z| ≤ ∑ T ∈ S.powersetCard s, |∑ y ∈ S \ T, (g T - f (insert y T))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ S.powersetCard s, ∑ y ∈ S \ T, |g T - f (insert y T)| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ T ∈ S.powersetCard s, ∑ _y ∈ S \ T, c :=
        Finset.sum_le_sum (fun T hT => Finset.sum_le_sum (hfg T hT))
      _ = b * (S.card.choose s : ℝ) * c := by
        rw [hleft]
        simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        ring
  have hchoose : (S.card.choose (s + 1) : ℝ) * (s + 1) =
      (S.card.choose s : ℝ) * b := by
    have h := Nat.choose_succ_right_eq S.card s
    dsimp only [b]
    have hr : (S.card.choose (s + 1) : ℝ) * (s + 1) =
        (S.card.choose s : ℝ) * (S.card - s : ℕ) := by exact_mod_cast h
    rwa [Nat.cast_sub hs.le] at hr
  have hmean : Z / (b * (S.card.choose s : ℝ)) =
      sliceMean S s g - sliceMean S (s + 1) f := by
    rw [hZ, sub_div, mul_div_mul_left _ _ hb.ne']
    rw [mul_comm b, ← hchoose, mul_comm (S.card.choose (s + 1) : ℝ),
      mul_div_mul_left _ _ hk.ne']
    rfl
  rw [← hmean, abs_div, abs_of_pos (mul_pos hb hd₁)]
  exact (div_le_iff₀ (mul_pos hb hd₁)).mpr (by simpa only [mul_comm c] using hbound)

/-- Conditioning a uniform slice on one distinguished element. -/
theorem sliceMean_insert (S : Finset E) (x : E) (hx : x ∉ S)
    (s : ℕ) (hs : s < S.card) (f : Finset E → ℝ) :
    sliceMean (insert x S) (s + 1) f =
      ((s + 1 : ℝ) / (S.card + 1)) * sliceMean S s (fun T => f (insert x T)) +
        (1 - (s + 1 : ℝ) / (S.card + 1)) * sliceMean S (s + 1) f := by
  have hd₁ : (S.card.choose s : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hs.le
  have hd₂ : (S.card.choose (s + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hs
  have hd : ((S.card + 1).choose (s + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.succ_le_succ hs.le)
  have hn : (S.card + 1 : ℝ) ≠ 0 := by positivity
  have hratio : (S.card.choose s : ℝ) / (S.card + 1).choose (s + 1) =
      (s + 1 : ℝ) / (S.card + 1) := by
    apply (div_eq_div_iff hd hn).mpr
    have h := Nat.succ_mul_choose_eq S.card s
    have hr : (S.card + 1 : ℝ) * S.card.choose s =
        ((S.card + 1).choose (s + 1) : ℝ) * (s + 1) := by exact_mod_cast h
    nlinarith
  have hratio₂ : (S.card.choose (s + 1) : ℝ) / (S.card + 1).choose (s + 1) =
      1 - (s + 1 : ℝ) / (S.card + 1) := by
    rw [← hratio]
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_div]
    have hpascal : (S.card.choose (s + 1) : ℝ) + S.card.choose s =
        (S.card + 1).choose (s + 1) := by
      rw [Nat.choose_succ_succ', Nat.cast_add, add_comm]
    rw [hpascal, div_self hd]
  simp only [sliceMean, Finset.card_insert_of_notMem hx, slice_sum_insert S x hx s f]
  rw [← hratio₂, ← hratio]
  field_simp [hd₁, hd₂, hd]

/-- Exact conditional-variance decomposition on a finite uniform slice. -/
theorem sliceVariance_insert (S : Finset E) (x : E) (hx : x ∉ S)
    (s : ℕ) (hs : s < S.card) (f : Finset E → ℝ) :
    sliceVariance (insert x S) (s + 1) f =
      ((s + 1 : ℝ) / (S.card + 1)) * sliceVariance S s (fun T => f (insert x T)) +
      (1 - (s + 1 : ℝ) / (S.card + 1)) * sliceVariance S (s + 1) f +
      ((s + 1 : ℝ) / (S.card + 1)) * (1 - (s + 1 : ℝ) / (S.card + 1)) *
        (sliceMean S s (fun T => f (insert x T)) - sliceMean S (s + 1) f) ^ 2 := by
  have hsize : s + 1 ≤ (insert x S).card := by
    rw [Finset.card_insert_of_notMem hx]
    omega
  rw [sliceVariance_eq _ _ hsize, sliceMean_insert S x hx s hs,
    sliceMean_insert S x hx s hs, sliceVariance_eq S s hs.le,
    sliceVariance_eq S (s + 1) hs]
  ring

/-- The actual weighted swap bound on a uniform slice. No variance or
concentration inequality is supplied as an assumption. -/
theorem weighted_slice_variance (S : Finset E) (s : ℕ) (hs : s ≤ S.card)
    (ω : E → ℝ) (hω : ∀ x ∈ S, 0 ≤ ω x) (f : Finset E → ℝ)
    (hswap : ∀ T ⊆ S, T.card = s → ∀ x ∈ T, ∀ y ∈ S, y ∉ T →
      |f (insert y (T.erase x)) - f T| ≤ ω x + ω y) :
    sliceVariance S s f ≤ 4 * ((s : ℝ) / S.card) * ∑ x ∈ S, ω x ^ 2 := by
  induction S using Finset.strongInductionOn generalizing s f with
  | _ S ih =>
    cases s with
    | zero => simp
    | succ s =>
      by_cases hfull : s + 1 = S.card
      · rw [hfull, sliceVariance_full]
        positivity
      have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image S ω hnonempty
      let R := S.erase x
      have hxR : x ∉ R := Finset.notMem_erase _ _
      have hRsub : R ⊆ S := Finset.erase_subset _ _
      have hRstrict : R ⊂ S := Finset.erase_ssubset hx
      have hRcard : R.card + 1 = S.card := Finset.card_erase_add_one hx
      have hRinsert : insert x R = S := Finset.insert_erase hx
      have hsR : s < R.card := by omega
      have hωR : ∀ y ∈ R, 0 ≤ ω y := fun y hy => hω y (hRsub hy)
      have hxω : 0 ≤ ω x := hω x hx
      have hinsertSub (T : Finset E) (hT : T ⊆ R) : insert x T ⊆ S :=
        Finset.insert_subset hx (hT.trans hRsub)
      have hxT (T : Finset E) (hT : T ⊆ R) : x ∉ T := fun h => hxR (hT h)
      have hswap₀ : ∀ T ⊆ R, T.card = s + 1 → ∀ u ∈ T, ∀ v ∈ R, v ∉ T →
          |f (insert v (T.erase u)) - f T| ≤ ω u + ω v := by
        intro T hT ht u hu v hv hvT
        exact hswap T (hT.trans hRsub) ht u hu v (hRsub hv) hvT
      have hswap₁ : ∀ T ⊆ R, T.card = s → ∀ u ∈ T, ∀ v ∈ R, v ∉ T →
          |f (insert x (insert v (T.erase u))) - f (insert x T)| ≤ ω u + ω v := by
        intro T hT ht u hu v hv hvT
        have huX : u ≠ x := fun heq => hxT T hT (heq ▸ hu)
        have hvX : v ≠ x := fun heq => hxR (heq ▸ hv)
        have hvi : v ∉ insert x T := by simp only [Finset.mem_insert]; tauto
        have hi := hswap (insert x T) (hinsertSub T hT)
          (by rw [Finset.card_insert_of_notMem (hxT T hT), ht])
          u (Finset.mem_insert_of_mem hu) v (hRsub hv) hvi
        have heq : insert v ((insert x T).erase u) = insert x (insert v (T.erase u)) := by
          rw [Finset.erase_insert_of_ne huX.symm, Finset.insert_comm]
        simpa only [heq] using hi
      have hv₁ := ih R hRstrict s hsR.le hωR (fun T => f (insert x T)) hswap₁
      have hv₀ := ih R hRstrict (s + 1) hsR hωR f hswap₀
      simp only [Nat.cast_add, Nat.cast_one] at hv₀
      have hmeans : |sliceMean R s (fun T => f (insert x T)) -
          sliceMean R (s + 1) f| ≤ 2 * ω x := by
        apply adjacent_slice_means R s hsR f (fun T => f (insert x T)) (2 * ω x)
        intro T hT y hy
        obtain ⟨hTR, ht⟩ := Finset.mem_powersetCard.mp hT
        obtain ⟨hyR, hyT⟩ := Finset.mem_sdiff.mp hy
        have hyX : y ≠ x := fun heq => hxR (heq ▸ hyR)
        have hyi : y ∉ insert x T := by simp only [Finset.mem_insert]; tauto
        have hh := hswap (insert x T) (hinsertSub T hTR)
          (by rw [Finset.card_insert_of_notMem (hxT T hTR), ht])
          x (Finset.mem_insert_self _ _) y (hRsub hyR) hyi
        rw [Finset.erase_insert (hxT T hTR), abs_sub_comm] at hh
        exact hh.trans (by linarith [hmax y (hRsub hyR)])
      have hmeansSq : (sliceMean R s (fun T => f (insert x T)) -
          sliceMean R (s + 1) f) ^ 2 ≤ 4 * ω x ^ 2 := by
        have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * ω x)).mpr hmeans
        rw [sq_abs] at hh
        nlinarith
      let p : ℝ := (s + 1 : ℝ) / (R.card + 1)
      have hp : 0 ≤ p := by dsimp only [p]; positivity
      have hp₁ : p ≤ 1 := by
        apply (div_le_one (by positivity : (0 : ℝ) < R.card + 1)).mpr
        exact_mod_cast Nat.succ_le_succ hsR.le
      have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
      have hm : (R.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hsR).ne'
      have hm₁ : (R.card + 1 : ℝ) ≠ 0 := by positivity
      have hcombine :
          p * (4 * ((s : ℝ) / R.card) * ∑ y ∈ R, ω y ^ 2) +
          (1 - p) * (4 * ((s + 1 : ℝ) / R.card) * ∑ y ∈ R, ω y ^ 2) =
            4 * p * ∑ y ∈ R, ω y ^ 2 := by
        dsimp only [p]
        field_simp [hm, hm₁]
        ring
      have hbetween : p * (1 - p) * (4 * ω x ^ 2) ≤ 4 * p * ω x ^ 2 := by
        have hh : p * (1 - p) ≤ p := mul_le_of_le_one_right hp (by linarith)
        have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 4 * ω x ^ 2)
        nlinarith
      rw [← hRinsert, sliceVariance_insert R x hxR s hsR]
      change p * _ + (1 - p) * _ + p * (1 - p) * _ ≤ _
      calc
        _ ≤ p * (4 * ((s : ℝ) / R.card) * ∑ y ∈ R, ω y ^ 2) +
            (1 - p) * (4 * ((s + 1 : ℝ) / R.card) * ∑ y ∈ R, ω y ^ 2) +
            p * (1 - p) * (4 * ω x ^ 2) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hv₁ hp)
            (mul_le_mul_of_nonneg_left hv₀ hq))
            (mul_le_mul_of_nonneg_left hmeansSq (mul_nonneg hp hq))
        _ ≤ 4 * p * (∑ y ∈ R, ω y ^ 2) + 4 * p * ω x ^ 2 := by
          rw [hcombine]
          exact add_le_add_left hbetween _
        _ = _ := by
          rw [Finset.card_insert_of_notMem hxR, Finset.sum_insert hxR]
          simp only [Nat.cast_add, Nat.cast_one, p]
          ring

section UniformLaw

variable [Fintype E]

/-- The finite-ground-set mean is the actual uniform-subset expectation. -/
theorem hypergeometric_mean_eq (s : ℕ) (f : Finset E → ℝ) :
    FiniteProbability.mean (Hypergeometric.weight s) f = sliceMean univ s f := by
  have hsets : (univ : Finset (Finset E)).filter (fun T => T.card = s) =
      (univ : Finset E).powersetCard s := by
    ext T
    simp
  simp only [FiniteProbability.mean, Hypergeometric.weight, ite_mul, zero_mul,
    ← Finset.sum_filter, hsets]
  simp only [sliceMean, Finset.card_univ, div_eq_mul_inv, one_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The slice variance uses exactly the same actual sample law as the
previous finite sampling and concentration results. -/
theorem hypergeometric_variance_eq (s : ℕ) (f : Finset E → ℝ) :
    FiniteProbability.variance (Hypergeometric.weight s) f = sliceVariance univ s f := by
  simp only [FiniteProbability.variance, hypergeometric_mean_eq, sliceVariance]

end UniformLaw

end Overfull.SwapVariance

namespace Overfull.Hypergeometric

open Finset Classical FiniteProbability

variable {E : Type*} [Fintype E]

/-- Weighted bounded differences under a single exchange imply the
uniform-subset variance bound, including both endpoint sample sizes. -/
theorem variance_of_swap (s : ℕ) (hs : s ≤ Fintype.card E)
    (ω : E → ℝ) (hω : ∀ x, 0 ≤ ω x) (f : Finset E → ℝ)
    (hswap : ∀ T, T.card = s → ∀ x ∈ T, ∀ y, y ∉ T →
      |f (insert y (T.erase x)) - f T| ≤ ω x + ω y) :
    variance (weight s) f ≤ 4 * ((s : ℝ) / Fintype.card E) * ∑ x, ω x ^ 2 := by
  rw [SwapVariance.hypergeometric_variance_eq]
  simpa only [Finset.card_univ] using SwapVariance.weighted_slice_variance
    (univ : Finset E) s (by simpa only [Finset.card_univ] using hs) ω
    (fun x _ => hω x) f (fun T _ hT x hx y _ hy => hswap T hT x hx y hy)

/-- A maximum weight and a total weight bound give the usable variance
budget for a nonlinear capped score once its swap bound is established. -/
theorem variance_of_swap_bounded (s : ℕ) (hs : s ≤ Fintype.card E)
    (ω : E → ℝ) (hω : ∀ x, 0 ≤ ω x) (f : Finset E → ℝ)
    (hswap : ∀ T, T.card = s → ∀ x ∈ T, ∀ y, y ∉ T →
      |f (insert y (T.erase x)) - f T| ≤ ω x + ω y)
    (W M : ℝ) (hW : 0 ≤ W) (hmax : ∀ x, ω x ≤ W) (hsum : (∑ x, ω x) ≤ M) :
    variance (weight s) f ≤ 4 * ((s : ℝ) / Fintype.card E) * W * M := by
  have hsq : (∑ x, ω x ^ 2) ≤ W * M := by
    calc
      _ ≤ ∑ x, W * ω x := Finset.sum_le_sum (fun x _ => by
        have h := mul_le_mul_of_nonneg_right (hmax x) (hω x)
        nlinarith)
      _ = W * ∑ x, ω x := (Finset.mul_sum _ _ _).symm
      _ ≤ W * M := mul_le_mul_of_nonneg_left hsum hW
  have h := (variance_of_swap s hs ω hω f hswap).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * ((s : ℝ) / Fintype.card E)))
  simpa only [mul_assoc] using h

omit [Fintype E] in
/-- Independent uniform samples in arbitrarily many finite parts obey the
sum of the weighted swap budgets for a general nonlinear statistic. -/
theorem variance_product_of_swap {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)]
    (s : ι → ℕ) (hs : ∀ i, s i ≤ Fintype.card (X i))
    (ω : ∀ i, X i → ℝ) (hω : ∀ i x, 0 ≤ ω i x)
    (f : (∀ i, Finset (X i)) → ℝ)
    (hswap : ∀ i τ T, T.card = s i → ∀ x ∈ T, ∀ y, y ∉ T →
      |f (Function.update τ i (insert y (T.erase x))) -
        f (Function.update τ i T)| ≤ ω i x + ω i y) :
    variance (piWeight (fun i => weight (E := X i) (s i))) f ≤
      ∑ i, 4 * ((s i : ℝ) / Fintype.card (X i)) * ∑ x, ω i x ^ 2 := by
  apply variance_pi_le (fun i => weight (E := X i) (s i))
    (fun i => weight_nonneg (s i)) (fun i => sum_weight (s i) (hs i)) f
    (fun i => 4 * ((s i : ℝ) / Fintype.card (X i)) * ∑ x, ω i x ^ 2)
  intro i τ
  exact variance_of_swap (s i) (hs i) (ω i) (hω i)
    (fun T => f (Function.update τ i T)) (hswap i τ)

omit [Fintype E] in
/-- A common sampling-fraction bound and global weight budgets give the
variance estimate used for the nonlinear correction-capacity score. -/
theorem variance_product_of_swap_bounded {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)]
    (s : ι → ℕ) (hs : ∀ i, s i ≤ Fintype.card (X i))
    (ω : ∀ i, X i → ℝ) (hω : ∀ i x, 0 ≤ ω i x)
    (f : (∀ i, Finset (X i)) → ℝ)
    (hswap : ∀ i τ T, T.card = s i → ∀ x ∈ T, ∀ y, y ∉ T →
      |f (Function.update τ i (insert y (T.erase x))) -
        f (Function.update τ i T)| ≤ ω i x + ω i y)
    (p W M : ℝ) (hp : 0 ≤ p) (hW : 0 ≤ W)
    (hfraction : ∀ i, ((s i : ℝ) / Fintype.card (X i)) ≤ p)
    (hmax : ∀ i x, ω i x ≤ W) (hsum : (∑ i, ∑ x, ω i x) ≤ M) :
    variance (piWeight (fun i => weight (E := X i) (s i))) f ≤ 4 * p * W * M := by
  have hsq : (∑ i, ∑ x, ω i x ^ 2) ≤ W * M := by
    calc
      _ ≤ ∑ i, ∑ x, W * ω i x := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro x _
        have h := mul_le_mul_of_nonneg_right (hmax i x) (hω i x)
        nlinarith
      _ = W * ∑ i, ∑ x, ω i x := by simp only [Finset.mul_sum]
      _ ≤ W * M := mul_le_mul_of_nonneg_left hsum hW
  calc
    _ ≤ ∑ i, 4 * ((s i : ℝ) / Fintype.card (X i)) * ∑ x, ω i x ^ 2 :=
      variance_product_of_swap X s hs ω hω f hswap
    _ ≤ ∑ i, 4 * p * ∑ x, ω i x ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hfraction i) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = (4 * p) * ∑ i, ∑ x, ω i x ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * p) * (W * M) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end Overfull.Hypergeometric
