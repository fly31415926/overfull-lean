import Overfull.ForeignEdges.Phase
import Overfull.ForeignEdges.Incidence

/-!
# Concatenating actual perfect-matching epochs

Every local matching is rehosted without changing its vertices or edges.
The concatenated sequence uses the exact successive residual graphs, and
its global prefixes agree with the corresponding local epoch prefixes.
-/

namespace Overfull.ForeignConcatenation

open Finset Classical SimpleGraph ForeignPhase SafePrescription
open BipartitePackingAccounting

variable {V : Type*}

/-- Regard an actual subgraph of a smaller host as a subgraph of the
original host, retaining every edge and vertex. -/
def liftToHost (G R : SimpleGraph V) (hRG : R ≤ G) (M : R.Subgraph) : G.Subgraph :=
  rehost R G M (fun _ _ he => hRG (M.adj_sub he))

@[simp] theorem liftToHost_spanning (G R : SimpleGraph V) (hRG : R ≤ G) (M : R.Subgraph) :
    (liftToHost G R hRG M).spanningCoe = M.spanningCoe := rfl

@[simp] theorem liftToHost_verts (G R : SimpleGraph V) (hRG : R ≤ G) (M : R.Subgraph) :
    (liftToHost G R hRG M).verts = M.verts := rfl

theorem liftToHost_perfect (G R : SimpleGraph V) (hRG : R ≤ G) (M : R.Subgraph)
    (hM : M.IsPerfectMatching) : (liftToHost G R hRG M).IsPerfectMatching := hM

/-- Append a local epoch after a fixed initial global prefix. -/
def appendEpoch (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (j : ℕ) : G.Subgraph :=
  if j < q then N j else liftToHost G R hRG (M (j-q))

theorem appendEpoch_left (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (j : ℕ) (hj : j < q) :
    appendEpoch G R hRG N q M j = N j := by simp only [appendEpoch,if_pos hj]

theorem appendEpoch_right (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (j : ℕ) :
    appendEpoch G R hRG N q M (q+j) = liftToHost G R hRG (M j) := by
  simp only [appendEpoch,show ¬ q+j < q by omega,if_false,Nat.add_sub_cancel_left]

/-- The residual graph depends only on entries of the specified prefix. -/
theorem afterDeletions_congr_prefix (G : SimpleGraph V)
    (M N : ℕ → G.Subgraph) (s : ℕ) (hMN : ∀ j < s, M j = N j) :
    afterDeletions G M s = afterDeletions G N s := by
  unfold afterDeletions
  congr 1
  ext u v
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by simpa only [hMN j (mem_range.mp hj)] using he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by simpa only [hMN j (mem_range.mp hj)] using he⟩

theorem appendEpoch_prefix (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph)
    (s : ℕ) (hs : s ≤ q) :
    afterDeletions G (appendEpoch G R hRG N q M) s = afterDeletions G N s := by
  apply afterDeletions_congr_prefix
  exact fun j hj => appendEpoch_left G R hRG N q M j (hj.trans_le hs)

/-- At every appended prefix the global residual is exactly the local
epoch residual, not merely a subgraph of it. -/
theorem appendEpoch_suffix (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph)
    (hR : R = afterDeletions G N q) (s : ℕ) :
    afterDeletions G (appendEpoch G R hRG N q M) (q+s) = afterDeletions R M s := by
  induction s with
  | zero => simpa only [Nat.add_zero,afterDeletions_zero] using
      (appendEpoch_prefix G R hRG N q M q le_rfl).trans hR.symm
  | succ s ih =>
    rw [Nat.add_succ,afterDeletions_succ,afterDeletions_succ,ih,
      appendEpoch_right,liftToHost_spanning]

theorem appendEpoch_perfect (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (s : ℕ)
    (hN : ∀ j < q, (N j).IsPerfectMatching)
    (hM : ∀ j < s, (M j).IsPerfectMatching) :
    ∀ j < q+s, (appendEpoch G R hRG N q M j).IsPerfectMatching := by
  intro j hj
  by_cases hjq : j < q
  · rw [appendEpoch_left G R hRG N q M j hjq]
    exact hN j hjq
  · have hjq' : q ≤ j := Nat.le_of_not_gt hjq
    have heq : j = q+(j-q) := by omega
    rw [heq,appendEpoch_right]
    exact liftToHost_perfect G R hRG _ (hM (j-q) (by omega))

/-- Both kinds of current-host membership are preserved under actual
concatenation. -/
theorem appendEpoch_present (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (s : ℕ)
    (hR : R = afterDeletions G N q)
    (hN : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (hM : ∀ j < s, (M j).spanningCoe ≤ afterDeletions R M j) :
    ∀ j < q+s, (appendEpoch G R hRG N q M j).spanningCoe ≤
      afterDeletions G (appendEpoch G R hRG N q M) j := by
  intro j hj
  by_cases hjq : j < q
  · rw [appendEpoch_left G R hRG N q M j hjq,
      appendEpoch_prefix G R hRG N q M j hjq.le]
    exact hN j hjq
  · have heq : j = q+(j-q) := by omega
    rw [heq,appendEpoch_right,liftToHost_spanning,appendEpoch_suffix G R hRG N q M hR]
    exact hM (j-q) (by omega)

theorem appendEpoch_pairwise_disjoint (G R : SimpleGraph V) (hRG : R ≤ G)
    (N : ℕ → G.Subgraph) (q : ℕ) (M : ℕ → R.Subgraph) (s : ℕ)
    (hR : R = afterDeletions G N q)
    (hN : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j)
    (hM : ∀ j < s, (M j).spanningCoe ≤ afterDeletions R M j) :
    ∀ i ∈ range (q+s), ∀ j ∈ range (q+s), i ≠ j →
      Disjoint (appendEpoch G R hRG N q M i).spanningCoe
        (appendEpoch G R hRG N q M j).spanningCoe :=
  ForeignIncidence.deletion_sequence_pairwise G _ (q+s)
    (appendEpoch_present G R hRG N q M s hR hN hM)

/-- The number of global rounds before an epoch begins. -/
def epochOffset (rounds : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => epochOffset rounds j + rounds j

@[simp] theorem epochOffset_zero (rounds : ℕ → ℕ) : epochOffset rounds 0 = 0 := rfl
@[simp] theorem epochOffset_succ (rounds : ℕ → ℕ) (j : ℕ) :
    epochOffset rounds (j+1) = epochOffset rounds j + rounds j := rfl

theorem epochOffset_monotone (rounds : ℕ → ℕ) : Monotone (epochOffset rounds) := by
  apply monotone_nat_of_le_succ
  intro j
  exact Nat.le_add_right _ _

theorem epoch_prefix_le_offset (rounds : ℕ → ℕ) (j r s : ℕ)
    (hj : j < r) (hs : s ≤ rounds j) :
    epochOffset rounds j+s ≤ epochOffset rounds r := by
  calc
    _ ≤ epochOffset rounds j+rounds j := Nat.add_le_add_left hs _
    _ = epochOffset rounds (j+1) := rfl
    _ ≤ epochOffset rounds r := epochOffset_monotone rounds (by omega)

theorem epoch_entry_lt_offset (rounds : ℕ → ℕ) (j r s : ℕ)
    (hj : j < r) (hs : s < rounds j) :
    epochOffset rounds j+s < epochOffset rounds r := by
  calc
    _ < epochOffset rounds j+rounds j := Nat.add_lt_add_left hs _
    _ = epochOffset rounds (j+1) := rfl
    _ ≤ epochOffset rounds r := epochOffset_monotone rounds (by omega)

/-- A finite collection of actual epochs has one perfect-matching
sequence in the original graph. Every checkpoint, every local prefix,
and every individual matching retains its exact graph interpretation. -/
theorem concatenate_epochs (G : SimpleGraph V) (R : ℕ → SimpleGraph V)
    (N : ∀ j, ℕ → (R j).Subgraph) (rounds : ℕ → ℕ) (r : ℕ)
    (hzero : R 0 = G)
    (hstep : ∀ j < r, R (j+1) = afterDeletions (R j) (N j) (rounds j))
    (hperfect : ∀ j < r, ∀ s < rounds j, (N j s).IsPerfectMatching)
    (hpresent : ∀ j < r, ∀ s < rounds j,
      (N j s).spanningCoe ≤ afterDeletions (R j) (N j) s) :
    ∃ P : ℕ → G.Subgraph,
      (∀ s < epochOffset rounds r, (P s).IsPerfectMatching) ∧
      (∀ s < epochOffset rounds r, (P s).spanningCoe ≤ afterDeletions G P s) ∧
      (∀ j ≤ r, afterDeletions G P (epochOffset rounds j) = R j) ∧
      (∀ j < r, ∀ s ≤ rounds j,
        afterDeletions G P (epochOffset rounds j+s) = afterDeletions (R j) (N j) s) ∧
      (∀ j < r, ∀ s < rounds j,
        (P (epochOffset rounds j+s)).spanningCoe = (N j s).spanningCoe) ∧
      (∀ i ∈ range (epochOffset rounds r), ∀ j ∈ range (epochOffset rounds r), i ≠ j →
        Disjoint (P i).spanningCoe (P j).spanningCoe) := by
  induction r with
  | zero =>
    refine ⟨fun _ => ⊥,?_,?_,?_,?_,?_,?_⟩
    · intro s hs; simp only [epochOffset_zero] at hs; omega
    · intro s hs; simp only [epochOffset_zero] at hs; omega
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp only [epochOffset_zero,afterDeletions_zero,hzero]
    · intro j hj; omega
    · intro j hj; omega
    · intro i hi
      simp only [epochOffset_zero,range_zero,notMem_empty] at hi
  | succ r ih =>
    obtain ⟨P,hP,hPpresent,hcheckpoint,hlocal,hentry,_hPdisj⟩ :=
      ih (fun j hj => hstep j (by omega))
        (fun j hj => hperfect j (by omega)) (fun j hj => hpresent j (by omega))
    have hR : R r = afterDeletions G P (epochOffset rounds r) := (hcheckpoint r le_rfl).symm
    have hRG : R r ≤ G := by
      intro u v huv
      have hh : (afterDeletions G P (epochOffset rounds r)).Adj u v := hR ▸ huv
      exact hh.1
    let Q := appendEpoch G (R r) hRG P (epochOffset rounds r) (N r)
    have hQ : ∀ s < epochOffset rounds (r+1), (Q s).IsPerfectMatching :=
      appendEpoch_perfect G (R r) hRG P (epochOffset rounds r) (N r) (rounds r)
        hP (hperfect r (by omega))
    have hQpresent : ∀ s < epochOffset rounds (r+1),
        (Q s).spanningCoe ≤ afterDeletions G Q s :=
      appendEpoch_present G (R r) hRG P (epochOffset rounds r) (N r) (rounds r)
        hR hPpresent (hpresent r (by omega))
    refine ⟨Q,hQ,hQpresent,?_,?_,?_,?_⟩
    · intro j hj
      by_cases hjr : j ≤ r
      · exact (appendEpoch_prefix G (R r) hRG P (epochOffset rounds r) (N r)
          (epochOffset rounds j) (epochOffset_monotone rounds hjr)).trans (hcheckpoint j hjr)
      · have heq : j = r+1 := by omega
        subst j
        exact (appendEpoch_suffix G (R r) hRG P (epochOffset rounds r) (N r)
          hR (rounds r)).trans (hstep r (by omega)).symm
    · intro j hj s hs
      by_cases hjr : j < r
      · exact (appendEpoch_prefix G (R r) hRG P (epochOffset rounds r) (N r)
          (epochOffset rounds j+s) (epoch_prefix_le_offset rounds j r s hjr hs)).trans
          (hlocal j hjr s hs)
      · have heq : j = r := by omega
        subst j
        exact appendEpoch_suffix G (R r) hRG P (epochOffset rounds r) (N r) hR s
    · intro j hj s hs
      by_cases hjr : j < r
      · have hh := appendEpoch_left G (R r) hRG P (epochOffset rounds r) (N r)
          (epochOffset rounds j+s) (epoch_entry_lt_offset rounds j r s hjr hs)
        exact (congrArg Subgraph.spanningCoe hh).trans (hentry j hjr s hs)
      · have heq : j = r := by omega
        subst j
        exact congrArg Subgraph.spanningCoe
          (appendEpoch_right G (R r) hRG P (epochOffset rounds r) (N r) s)
    · exact ForeignIncidence.deletion_sequence_pairwise G Q (epochOffset rounds (r+1)) hQpresent

/-- Every completed or interrupted epoch loses at most three quarters
of its starting degree, so the reserve holds at every checkpoint. -/
theorem epoch_degree_reserve (h rounds : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ j < r, h (j+1) = h j-rounds j)
    (hrounds : ∀ j < r, rounds j ≤ 3*h j/4) :
    h 0 ≤ 4^r*h r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprior := ih (fun j hj => hstep j (by omega)) (fun j hj => hrounds j (by omega))
    have hquarter := (phase_degree_reserve (h r) (rounds r) (hrounds r (by omega))).2
    rw [← hstep r (by omega)] at hquarter
    calc
      _ ≤ 4^r*h r := hprior
      _ ≤ 4^r*(4*h (r+1)) := Nat.mul_le_mul_left _ hquarter
      _ = 4^(r+1)*h (r+1) := by rw [pow_succ]; ring

/-- The degree at every checkpoint is also at most the initial degree. -/
theorem epoch_degree_le_initial (h rounds : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ j < r, h (j+1) = h j-rounds j) : h r ≤ h 0 := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    have hprior := ih (fun j hj => hstep j (by omega))
    rw [hstep r (by omega)]
    exact (Nat.sub_le _ _).trans hprior

/-- The same reserve is valid at every prefix inside the next epoch,
including a prefix at which refinement interrupts the epoch. -/
theorem within_epoch_degree_reserve (k₀ h r s : ℕ)
    (hprior : k₀ ≤ 4^r*h) (hs : s ≤ 3*h/4) :
    k₀ ≤ 4^(r+1)*(h-s) := by
  have hquarter := (phase_degree_reserve h s hs).2
  calc
    _ ≤ 4^r*h := hprior
    _ ≤ 4^r*(4*(h-s)) := Nat.mul_le_mul_left _ hquarter
    _ = 4^(r+1)*(h-s) := by rw [pow_succ]; ring

/-- The reserve at an interior prefix is a bound on its actual graph
degree, obtained from perfect-matching deletion in the actual current host. -/
theorem actual_prefix_degree_reserve [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : ℕ → G.Subgraph) (k₀ h r s : ℕ)
    (hregular : ∀ v, G.degree v = h)
    (hperfect : ∀ j < s, (N j).IsPerfectMatching)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hprior : k₀ ≤ 4^r*h) (hs : s ≤ 3*h/4) (v : V) :
    (afterDeletions G N s).degree v = h-s ∧
      k₀ ≤ 4^(r+1)*(afterDeletions G N s).degree v := by
  have hid := ForeignIncidence.perfect_deletion_degree_identity G N s hperfect hpresent v
  have hreg := hregular v
  have hdegree : (afterDeletions G N s).degree v = h-s := by
    simp only [afterDeletions,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hid hreg ⊢
    omega
  exact ⟨hdegree,hdegree ▸ within_epoch_degree_reserve k₀ h r s hprior hs⟩

/-- Throughout any of the first four epochs, the actual residual degree
retains the factor `1/256`, and hence the strict safe-prescription reserve. -/
theorem actual_prefix_four_epoch_reserve [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : ℕ → G.Subgraph) (k₀ h r s : ℕ)
    (hregular : ∀ v, G.degree v = h)
    (hperfect : ∀ j < s, (N j).IsPerfectMatching)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hprior : k₀ ≤ 4^r*h) (hs : s ≤ 3*h/4) (hr : r < 4)
    (hk₀ : 0 < k₀) (v : V) :
    k₀ ≤ 256*(afterDeletions G N s).degree v ∧
      (k₀ : ℝ)/1024 < (afterDeletions G N s).degree v := by
  have hreserve := (actual_prefix_degree_reserve G N k₀ h r s
    hregular hperfect hpresent hprior hs v).2
  have hpower : 4^(r+1) ≤ 256 := by interval_cases r <;> norm_num
  have hbound : k₀ ≤ 256*(afterDeletions G N s).degree v :=
    hreserve.trans (Nat.mul_le_mul_right _ hpower)
  have hboundR : (k₀ : ℝ) ≤ 256*(afterDeletions G N s).degree v := by exact_mod_cast hbound
  have hkR : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  exact ⟨hbound,by linarith⟩

end Overfull.ForeignConcatenation
