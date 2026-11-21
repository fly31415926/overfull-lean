import Overfull.Basic
import Overfull.Sharpness.Family
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# An explicit coloring of the sharpness family with one extra color

Inside a clique the color of labels `a,b` is `(a+b) % Δ`. A spoke at label
`a` has color `2*a % Δ`, while each edge between cliques has the extra color
`Δ`. The five-cycle uses the colors `0`, `2`, and `Δ`. For odd `Δ`, doubling
modulo `Δ` is injective, so the spoke colors avoid `0` and `2`.
-/

namespace Overfull.Sharpness.Family

/-- A symmetric three-color assignment to the five additional vertices. -/
def cycleColor (Δ : ℕ) (w z : Fin 5) : ℕ :=
  if w.val + z.val = 3 then Δ
  else if w.val + z.val = 4 ∨ w.val + z.val = 6 then 2 else 0

/-- The color assigned to an unordered pair, written first as a symmetric
function on ordered pairs. Values on nonedges are immaterial. -/
def rawColor (Δ : ℕ) : Vertex Δ → Vertex Δ → ℕ
  | .inl (i, a), .inl (j, b) => if i = j then (a.val + b.val) % Δ else Δ
  | .inl (_, a), .inr _ => (2 * a.val) % Δ
  | .inr _, .inl (_, a) => (2 * a.val) % Δ
  | .inr w, .inr z => cycleColor Δ w z

theorem rawColor_symmetric (Δ : ℕ) (x y : Vertex Δ) :
    rawColor Δ x y = rawColor Δ y x := by
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    cases y with
    | inl y =>
      rcases y with ⟨j, b⟩
      simp [rawColor, eq_comm, Nat.add_comm]
    | inr w => rfl
  | inr w =>
    cases y with
    | inl y => rfl
    | inr z => simp [rawColor, cycleColor, Nat.add_comm]

theorem rawColor_lt {Δ : ℕ} (hΔ : 3 ≤ Δ) (x y : Vertex Δ) :
    rawColor Δ x y < Δ + 1 := by
  have hpos : 0 < Δ := by omega
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    cases y with
    | inl y =>
      rcases y with ⟨j, b⟩
      dsimp [rawColor]
      split_ifs
      · exact lt_trans (Nat.mod_lt _ hpos) (by omega)
      · omega
    | inr w => exact lt_trans (Nat.mod_lt _ hpos) (by omega)
  | inr w =>
    cases y with
    | inl y => exact lt_trans (Nat.mod_lt _ hpos) (by omega)
    | inr z =>
      dsimp [rawColor, cycleColor]
      split_ifs <;> omega

private theorem add_mod_injective {Δ : ℕ} (a b c : Fin Δ)
    (h : (a.val + b.val) % Δ = (a.val + c.val) % Δ) : b = c := by
  apply Fin.ext
  have hmod : b.val ≡ c.val [MOD Δ] := Nat.ModEq.add_left_cancel' a.val h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt] using hmod

private theorem double_mod_injective {Δ : ℕ} (hodd : Δ % 2 = 1) (a b : Fin Δ)
    (h : (2 * a.val) % Δ = (2 * b.val) % Δ) : a = b := by
  apply Fin.ext
  have hcop : Nat.gcd Δ 2 = 1 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)
  have hmod : a.val ≡ b.val [MOD Δ] := Nat.ModEq.cancel_left_of_coprime hcop h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hmod

private theorem spoke_color_ne_cycleColor {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (hodd : Δ % 2 = 1) (a : Fin Δ) (ha : 2 ≤ a.val) (w z : Fin 5) :
    (2 * a.val) % Δ ≠ cycleColor Δ w z := by
  have hlt : (2 * a.val) % Δ < Δ := Nat.mod_lt _ (by omega)
  have hne0 : (2 * a.val) % Δ ≠ 0 := by
    intro h
    have hh : (2 * a.val) % Δ = (2 * (u hΔ).val) % Δ := by simpa [u] using h
    have he := congrArg Fin.val (double_mod_injective hodd a (u hΔ) hh)
    simp only [u_val] at he
    omega
  have hne2 : (2 * a.val) % Δ ≠ 2 := by
    intro h
    have hh : (2 * a.val) % Δ = (2 * (v hΔ).val) % Δ := by
      simpa [v, Nat.mod_eq_of_lt (show 2 < Δ by omega)] using h
    have he := congrArg Fin.val (double_mod_injective hodd a (v hΔ) hh)
    simp only [v_val] at he
    omega
  intro h
  unfold cycleColor at h
  split_ifs at h <;> omega

private theorem clique_spoke_colors_ne {Δ : ℕ}
    (i j : Fin 4) (a b : Fin Δ) (w : Fin 5)
    (hy : (graph Δ).Adj (.inl (i, a)) (.inl (j, b)))
    (hz : (graph Δ).Adj (.inl (i, a)) (.inr w)) :
    rawColor Δ (.inl (i, a)) (.inl (j, b)) ≠
      rawColor Δ (.inl (i, a)) (.inr w) := by
  change 2 ≤ a.val ∧ w.val = i.val + 1 at hz
  have ha0 : a.val ≠ 0 := by omega
  have ha1 : a.val ≠ 1 := by omega
  have hclique : i = j ∧ a ≠ b := by
    simpa [graph, Adjacent, ha0, ha1] using hy
  obtain ⟨rfl, hab⟩ := hclique
  intro hcolor
  have hmod : (a.val + b.val) % Δ = (a.val + a.val) % Δ := by
    simpa [rawColor, two_mul] using hcolor
  exact hab (add_mod_injective a b a hmod).symm

private theorem rawColor_injective_at_clique {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (i : Fin 4) (a : Fin Δ) {y z : Vertex Δ}
    (hy : (graph Δ).Adj (.inl (i, a)) y)
    (hz : (graph Δ).Adj (.inl (i, a)) z)
    (hcolor : rawColor Δ (.inl (i, a)) y = rawColor Δ (.inl (i, a)) z) :
    y = z := by
  have hpos : 0 < Δ := by omega
  cases y with
  | inl y =>
    rcases y with ⟨j, b⟩
    cases z with
    | inl z =>
      rcases z with ⟨l, d⟩
      by_cases hij : i = j
      · subst j
        by_cases hil : i = l
        · subst l
          have hbd : b = d := add_mod_injective a b d (by simpa [rawColor] using hcolor)
          cases hbd
          rfl
        · have hlt : (a.val + b.val) % Δ < Δ := Nat.mod_lt _ hpos
          have heq : (a.val + b.val) % Δ = Δ := by
            simpa [rawColor, hil] using hcolor
          omega
      · by_cases hil : i = l
        · subst l
          have hlt : (a.val + d.val) % Δ < Δ := Nat.mod_lt _ hpos
          have heq : Δ = (a.val + d.val) % Δ := by
            simpa [rawColor, hij] using hcolor
          omega
        · have hy' :
              (i.val + 1 = j.val ∧ a.val = 1 ∧ b.val = 0) ∨
              (j.val + 1 = i.val ∧ b.val = 1 ∧ a.val = 0) := by
            simpa [graph, Adjacent, hij] using hy
          have hz' :
              (i.val + 1 = l.val ∧ a.val = 1 ∧ d.val = 0) ∨
              (l.val + 1 = i.val ∧ d.val = 1 ∧ a.val = 0) := by
            simpa [graph, Adjacent, hil] using hz
          have hjl : j = l := Fin.ext (by omega)
          have hbd : b = d := Fin.ext (by omega)
          cases hjl
          cases hbd
          rfl
    | inr w => exact False.elim ((clique_spoke_colors_ne i j a b w hy hz) hcolor)
  | inr w =>
    cases z with
    | inl z =>
      rcases z with ⟨j, b⟩
      exact False.elim ((clique_spoke_colors_ne i j a b w hz hy) hcolor.symm)
    | inr z =>
      have hy' : 2 ≤ a.val ∧ w.val = i.val + 1 := hy
      have hz' : 2 ≤ a.val ∧ z.val = i.val + 1 := hz
      have hwz : w = z := Fin.ext (by omega)
      exact congrArg Sum.inr hwz

private theorem rawColor_injective_at_additional {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (hodd : Δ % 2 = 1) (w : Fin 5) {y z : Vertex Δ}
    (hy : (graph Δ).Adj (.inr w) y)
    (hz : (graph Δ).Adj (.inr w) z)
    (hcolor : rawColor Δ (.inr w) y = rawColor Δ (.inr w) z) :
    y = z := by
  cases y with
  | inl y =>
    rcases y with ⟨i, a⟩
    cases z with
    | inl z =>
      rcases z with ⟨j, b⟩
      have hy' : 2 ≤ a.val ∧ w.val = i.val + 1 := hy
      have hz' : 2 ≤ b.val ∧ w.val = j.val + 1 := hz
      have hij : i = j := Fin.ext (by omega)
      have hab : a = b := double_mod_injective hodd a b (by simpa [rawColor] using hcolor)
      cases hij
      cases hab
      rfl
    | inr z =>
      have hy' : 2 ≤ a.val ∧ w.val = i.val + 1 := hy
      have heq : (2 * a.val) % Δ = cycleColor Δ w z := by
        simpa [rawColor] using hcolor
      exact False.elim ((spoke_color_ne_cycleColor hΔ hodd a hy'.1 w z) heq)
  | inr y =>
    cases z with
    | inl z =>
      rcases z with ⟨i, a⟩
      have hz' : 2 ≤ a.val ∧ w.val = i.val + 1 := hz
      have heq : (2 * a.val) % Δ = cycleColor Δ w y := by
        simpa [rawColor] using hcolor.symm
      exact False.elim ((spoke_color_ne_cycleColor hΔ hodd a hz'.1 w y) heq)
    | inr z =>
      fin_cases w <;> fin_cases y <;> fin_cases z <;>
        simp [graph, Adjacent, rawColor, cycleColor] at hy hz hcolor ⊢ <;> omega

/-- The explicit color assignment is injective on the neighbors of each vertex. -/
theorem rawColor_injective_of_adj {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (x : Vertex Δ) {y z : Vertex Δ}
    (hy : (graph Δ).Adj x y) (hz : (graph Δ).Adj x z)
    (hcolor : rawColor Δ x y = rawColor Δ x z) : y = z := by
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    exact rawColor_injective_at_clique hΔ i a hy hz hcolor
  | inr w => exact rawColor_injective_at_additional hΔ hodd w hy hz hcolor

/-- The pair color as an element of the finite palette. -/
def pairColor {Δ : ℕ} (hΔ : 3 ≤ Δ) (x y : Vertex Δ) : Fin (Δ + 1) :=
  ⟨rawColor Δ x y, rawColor_lt hΔ x y⟩

/-- Symmetry makes the pair assignment a well-defined color of an unordered edge. -/
def edgeColor {Δ : ℕ} (hΔ : 3 ≤ Δ) : Sym2 (Vertex Δ) → Fin (Δ + 1) :=
  Sym2.lift ⟨pairColor hΔ, fun x y => Fin.ext (rawColor_symmetric Δ x y)⟩

/-- An explicit proper edge coloring of the full sharpness graph using `Δ+1`
colors. The proof applies to every odd integer `Δ ≥ 3`. -/
def upperColoring {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1) :
    EdgeColoring (graph Δ) (Δ + 1) where
  color e := edgeColor hΔ e.val
  proper := by
    intro e f x hxe hxf hcolor
    obtain ⟨y, he⟩ := Sym2.mem_iff_exists.mp hxe
    obtain ⟨z, hf⟩ := Sym2.mem_iff_exists.mp hxf
    have hy : (graph Δ).Adj x y := by
      have h := e.property
      rw [he] at h
      exact h
    have hz : (graph Δ).Adj x z := by
      have h := f.property
      rw [hf] at h
      exact h
    have hraw : rawColor Δ x y = rawColor Δ x z := by
      have h := congrArg Fin.val hcolor
      change (edgeColor hΔ e.val).val = (edgeColor hΔ f.val).val at h
      simpa only [he, hf, edgeColor, Sym2.lift_mk, pairColor] using h
    have hyz : y = z := rawColor_injective_of_adj hΔ hodd x hy hz hraw
    apply Subtype.ext
    rw [he, hf, hyz]

@[simp] theorem upperColoring_color_val {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (hodd : Δ % 2 = 1) {x y : Vertex Δ} (hxy : (graph Δ).Adj x y) :
    ((upperColoring hΔ hodd).color ⟨s(x, y), hxy⟩).val = rawColor Δ x y := rfl

/-- The sharpness family always admits a coloring with one more than its
maximum degree; no appeal to Vizing's theorem is needed. -/
theorem has_upper_coloring {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1) :
    Nonempty (EdgeColoring (graph Δ) (Δ + 1)) :=
  ⟨upperColoring hΔ hodd⟩

end Overfull.Sharpness.Family
