import Std

/-!
# Arithmetic used in the overfull manuscript

These are arithmetic results only. Incidence identities, degree bounds, and
parity properties of actual graphs must be established separately before these
lemmas can be applied. In particular, this file does not assert the existence
or edge chromatic index of any graph, and does not prove the main theorem.

The source manuscript is `Four_Robust_Component_Cases_2026-11-20.tex`.
-/

namespace Overfull.Arithmetic

/-- The deficiency identity follows from the incidence-counting identity.
This is the arithmetic part of equation `two:eq:deficiency`. -/
theorem deficiency_cut_identity (k n e d c : Int)
    (h : d = 2 * e + c) :
    k * n - 2 * e = (k * n - d) + c := by
  omega

/-- The parity of a cut in a regular graph, after the incidence identity
has been supplied. -/
theorem regular_cut_parity (k n e c : Int)
    (h : k * n = 2 * e + c) :
    c % 2 = (k * n) % 2 := by
  omega

/-- An odd integer at least one less than an odd target reaches that target.
Used for partially intersected cliques in `sharp:thm:family`. -/
theorem odd_rounding (f k : Nat)
    (hf : f % 2 = 1) (hk : k % 2 = 1) (h : k - 1 ≤ f) :
    k ≤ f := by
  omega

/-- The parity step for a shore with one auxiliary vertex in
`two:lem:robust-auxiliary-completion`. -/
theorem even_rounding (f d e : Nat)
    (hf : f % 2 = 0) (hd : d ≤ f) (he : 2 * e ≤ d + 1) :
    2 * e ≤ f := by
  omega

/-- There are exactly five nonempty component-count possibilities below
weighted count four; the input bound is the output of the partition argument. -/
theorem five_component_cases (q l : Nat)
    (hnonempty : 0 < q + l) (hbound : q + 2 * l < 4) :
    (q = 1 ∧ l = 0) ∨ (q = 0 ∧ l = 1) ∨
    (q = 2 ∧ l = 0) ∨ (q = 3 ∧ l = 0) ∨
    (q = 1 ∧ l = 1) := by
  omega

/-- The listed five component cases all satisfy the required counting bound. -/
theorem five_component_cases_converse (q l : Nat)
    (h : (q = 1 ∧ l = 0) ∨ (q = 0 ∧ l = 1) ∨
      (q = 2 ∧ l = 0) ∨ (q = 3 ∧ l = 0) ∨
      (q = 1 ∧ l = 1)) :
    0 < q + l ∧ q + 2 * l < 4 := by
  omega

/-- Exact natural-number degree accounting at the end of Section 6.
The hypotheses prevent truncation in each natural-number subtraction. -/
theorem residual_degree (k s r d : Nat)
    (hrs : r ≤ s) (hdegree : 2 * s + d ≤ k) :
    (k - 2 * (s - r) - d) - (k - 2 * s - d) = 2 * r := by
  omega

/-- The nominal core degree exceeds the number of completed colors by `2r`. -/
theorem reserved_degree_slack (k s r : Nat)
    (hrs : r ≤ s) (hdegree : 2 * s ≤ k) :
    k - 2 * (s - r) = (k - 2 * s) + 2 * r := by
  omega

/-- The previously completed colors and the absorber colors total `k`. -/
theorem colors_exhausted (k s : Nat) (h : 2 * s ≤ k) :
    (k - 2 * s) + 2 * s = k := by
  omega

/-- Ten nonspoke edges cannot be partitioned into sets of size four.
The graph-theoretic matching classification is not an input proved here. -/
theorem ten_not_multiple_four : ¬ ∃ t : Nat, 4 * t = 10 := by
  omega

/-- The claimed sharpness order is odd. -/
theorem sharpness_order_odd (delta : Nat) :
    (4 * delta + 5) % 2 = 1 := by
  omega

/-- The family order places its degree strictly below one quarter of its order.
This is an integer inequality, with no graph-existence assertion. -/
theorem sharpness_below_quarter (delta : Nat) :
    4 * delta < 4 * delta + 5 := by
  omega

/-- The order tends to infinity along any unbounded sequence of degrees. -/
theorem sharpness_order_lower_bound (delta n : Nat) (h : n ≤ delta) :
    n ≤ 4 * delta + 5 := by
  omega

/-- The odd-set inequality, expressed without division for a set of order
`2h+1`. This is an integer arithmetic equivalence. -/
theorem odd_deficiency_iff (k h e : Int) :
    k ≤ k * (2 * h + 1) - 2 * e ↔ e ≤ k * h := by
  have hmul : k * (2 * h + 1) = 2 * (k * h) + k := by
    calc
      k * (2 * h + 1) = k * (2 * h) + k := by
        simp only [Int.mul_add, Int.mul_one]
      _ = 2 * (k * h) + k := by rw [Int.mul_left_comm k 2 h]
  omega

/-- An odd degree and odd set size give an odd signed deficiency. -/
theorem odd_deficiency_parity (k n e : Int)
    (hk : k % 2 = 1) (hn : n % 2 = 1) :
    (k * n - 2 * e) % 2 = 1 := by
  simp [Int.sub_emod, Int.mul_emod, hk, hn]

/-- The signed form of the rounding step also permits negative integers. -/
theorem odd_rounding_int (f k : Int)
    (hf : f % 2 = 1) (hk : k % 2 = 1) (h : k - 1 ≤ f) :
    k ≤ f := by
  omega

/-- The absorber parameter equations give the exact reserved degree.
This is the algebra in equation `old:fac:reserved-degree`. -/
theorem absorber_reserved_degree (q r1 r2 r3 rd s r : Int)
    (hdiamond : rd = r1 + r2 + r - (q - 1) * r3)
    (hs : s = q * r3 + 7 * rd) :
    r1 + r2 + r3 + 6 * rd = s - r := by
  have hmul : (q - 1) * r3 = q * r3 - r3 := by
    simp only [Int.sub_mul, Int.one_mul]
  omega

/-- The palette sizes total exactly twice the number of special path systems.
This is the algebra in equation `old:fac:selected-total`. -/
theorem absorber_selected_colors (q k1 k2 r3 rd s : Int)
    (hk1 : k1 = 2 * r3) (hk2 : k2 = 2 * rd)
    (hs : s = q * r3 + 7 * rd) :
    q * k1 + 7 * k2 = 2 * s := by
  have hmul : q * k1 = 2 * (q * r3) := by
    rw [hk1, Int.mul_left_comm q 2 r3]
  omega

/-- The size threshold survives passage to a critical subgraph in the
last paragraph of the main-theorem reduction. -/
theorem critical_subgraph_order_threshold (n n1 n' delta : Nat)
    (hlarge : 4 * n1 ≤ n) (hdensity : n ≤ 4 * delta)
    (horder : delta + 1 ≤ n') :
    n1 ≤ n' := by
  omega

end Overfull.Arithmetic
