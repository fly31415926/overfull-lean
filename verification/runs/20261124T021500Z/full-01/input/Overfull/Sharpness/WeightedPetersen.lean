import Overfull.Sharpness.Encoding
import Mathlib.Data.Fintype.Card

/-!
# The weighted Petersen multigraph

`WeightedEdge s` has one copy of each outer and inner cycle edge and `s`
separate copies of each spoke. Its ten vertices and both endpoints of every
edge copy are explicit. Properness is the usual condition that incident
distinct edge copies receive distinct colors.
-/

namespace Overfull.Sharpness

def nextOuter (i : Fin 5) : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
def prevOuter (i : Fin 5) : Fin 5 := ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
def nextInner (i : Fin 5) : Fin 5 := ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
def prevInner (i : Fin 5) : Fin 5 := ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩

theorem cycle_indices : ∀ i : Fin 5,
    nextOuter (prevOuter i) = i ∧ nextInner (prevInner i) = i ∧
    i ≠ prevOuter i ∧ i ≠ prevInner i ∧
    i ≠ nextOuter i ∧ i ≠ nextInner i := by
  decide

theorem cycle_inverse_indices : ∀ i j : Fin 5,
    (nextOuter j = i ↔ j = prevOuter i) ∧
    (nextInner j = i ↔ j = prevInner i) := by
  decide

abbrev WeightedVertex := Sum (Fin 5) (Fin 5)

inductive WeightedEdge (s : Nat) where
  | outer (i : Fin 5)
  | inner (i : Fin 5)
  | spoke (i : Fin 5) (j : Fin s)
  deriving DecidableEq

def firstEnd {s : Nat} : WeightedEdge s → WeightedVertex
  | .outer i => .inl i
  | .inner i => .inr i
  | .spoke i _ => .inl i

def secondEnd {s : Nat} : WeightedEdge s → WeightedVertex
  | .outer i => .inl (nextOuter i)
  | .inner i => .inr (nextInner i)
  | .spoke i _ => .inr i

def Incident {s : Nat} (v : WeightedVertex) (e : WeightedEdge s) : Prop :=
  firstEnd e = v ∨ secondEnd e = v

theorem loopless {s : Nat} (e : WeightedEdge s) : firstEnd e ≠ secondEnd e := by
  cases e with
  | outer i =>
      intro h
      exact (cycle_indices i).2.2.2.2.1 (Sum.inl.inj h)
  | inner i =>
      intro h
      exact (cycle_indices i).2.2.2.2.2 (Sum.inr.inj h)
  | spoke i j => intro h; cases h

def IsProper {s : Nat} {C : Type} (color : WeightedEdge s → C) : Prop :=
  ∀ (v : WeightedVertex) (e f : WeightedEdge s),
    Incident v e → Incident v f → color e = color f → e = f

def localEdges {E : Type} {s : Nat} (a b : E) (spokes : Fin s → E) : Fin (s + 2) → E :=
  Fin.cases a (Fin.cases b spokes)

theorem localEdges_injective {E : Type} {s : Nat} (a b : E) (spokes : Fin s → E)
    (hab : a ≠ b) (has : ∀ j, a ≠ spokes j) (hbs : ∀ j, b ≠ spokes j)
    (hs : Function.Injective spokes) : Function.Injective (localEdges a b spokes) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact False.elim (hab hij)
    · exact False.elim (has j hij)
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact False.elim (hab hij.symm)
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · exact False.elim (hbs j hij)
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact False.elim (has i hij.symm)
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact False.elim (hbs i hij.symm)
  · exact congrArg Fin.succ (congrArg Fin.succ (hs hij))

def outerEdges {s : Nat} (i : Fin 5) : Fin (s + 2) → WeightedEdge s :=
  localEdges (.outer i) (.outer (prevOuter i)) (.spoke i)

def innerEdges {s : Nat} (i : Fin 5) : Fin (s + 2) → WeightedEdge s :=
  localEdges (.inner i) (.inner (prevInner i)) (.spoke i)

theorem outerEdges_injective {s : Nat} (i : Fin 5) : Function.Injective (@outerEdges s i) := by
  apply localEdges_injective
  · intro h
    exact (cycle_indices i).2.2.1 (WeightedEdge.outer.inj h)
  · intro j h; cases h
  · intro j h; cases h
  · intro j k h
    exact (WeightedEdge.spoke.inj h).2

theorem innerEdges_injective {s : Nat} (i : Fin 5) : Function.Injective (@innerEdges s i) := by
  apply localEdges_injective
  · intro h
    exact (cycle_indices i).2.2.2.1 (WeightedEdge.inner.inj h)
  · intro j h; cases h
  · intro j h; cases h
  · intro j k h
    exact (WeightedEdge.spoke.inj h).2

theorem outerEdges_incident {s : Nat} (i : Fin 5) (j : Fin (s + 2)) :
    Incident (.inl i) (outerEdges i j) := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inr (congrArg Sum.inl (cycle_indices i).1)
  · exact Or.inl rfl

theorem innerEdges_incident {s : Nat} (i : Fin 5) (j : Fin (s + 2)) :
    Incident (.inr i) (innerEdges i j) := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inr (congrArg Sum.inr (cycle_indices i).2.1)
  · exact Or.inr rfl

theorem outerEdges_cover {s : Nat} (i : Fin 5) (e : WeightedEdge s)
    (h : Incident (.inl i) e) : ∃ j, outerEdges i j = e := by
  cases e with
  | outer k =>
      rcases h with h | h
      · have hk : k = i := Sum.inl.inj h
        subst k
        exact ⟨0, rfl⟩
      · have hk : k = prevOuter i := (cycle_inverse_indices i k).1.mp (Sum.inl.inj h)
        subst k
        exact ⟨(0 : Fin (s + 1)).succ, rfl⟩
  | inner k => rcases h with h | h <;> cases h
  | spoke k t =>
      rcases h with h | h
      · have hk : k = i := Sum.inl.inj h
        subst k
        exact ⟨t.succ.succ, rfl⟩
      · cases h

theorem innerEdges_cover {s : Nat} (i : Fin 5) (e : WeightedEdge s)
    (h : Incident (.inr i) e) : ∃ j, innerEdges i j = e := by
  cases e with
  | outer k => rcases h with h | h <;> cases h
  | inner k =>
      rcases h with h | h
      · have hk : k = i := Sum.inr.inj h
        subst k
        exact ⟨0, rfl⟩
      · have hk : k = prevInner i := (cycle_inverse_indices i k).2.mp (Sum.inr.inj h)
        subst k
        exact ⟨(0 : Fin (s + 1)).succ, rfl⟩
  | spoke k t =>
      rcases h with h | h
      · cases h
      · have hk : k = i := Sum.inr.inj h
        subst k
        exact ⟨t.succ.succ, rfl⟩

theorem proper_outer_injective {s : Nat} {C : Type} (color : WeightedEdge s → C)
    (h : IsProper color) (i : Fin 5) : Function.Injective (color ∘ outerEdges i) := by
  intro j k hjk
  apply outerEdges_injective i
  exact h (.inl i) _ _ (outerEdges_incident i j) (outerEdges_incident i k) hjk

theorem proper_inner_injective {s : Nat} {C : Type} (color : WeightedEdge s → C)
    (h : IsProper color) (i : Fin 5) : Function.Injective (color ∘ innerEdges i) := by
  intro j k hjk
  apply innerEdges_injective i
  exact h (.inr i) _ _ (innerEdges_incident i j) (innerEdges_incident i k) hjk

/-- The explicit incidence lists are exhaustive, so their injectivity is
equivalent to the usual proper-edge-coloring condition. -/
theorem proper_iff_local_injective {s : Nat} {C : Type} (color : WeightedEdge s → C) :
    IsProper color ↔
      (∀ i, Function.Injective (color ∘ outerEdges i)) ∧
      (∀ i, Function.Injective (color ∘ innerEdges i)) := by
  constructor
  · intro h
    exact ⟨proper_outer_injective color h, proper_inner_injective color h⟩
  · rintro ⟨houter, hinner⟩ v e f he hf heq
    cases v with
    | inl i =>
        obtain ⟨j, hj⟩ := outerEdges_cover i e he
        obtain ⟨k, hk⟩ := outerEdges_cover i f hf
        have hc : (color ∘ outerEdges i) j = (color ∘ outerEdges i) k := by
          change color (outerEdges i j) = color (outerEdges i k)
          rw [hj, hk]
          exact heq
        have hjk := houter i hc
        exact hj.symm.trans ((congrArg (outerEdges i) hjk).trans hk)
    | inr i =>
        obtain ⟨j, hj⟩ := innerEdges_cover i e he
        obtain ⟨k, hk⟩ := innerEdges_cover i f hf
        have hc : (color ∘ innerEdges i) j = (color ∘ innerEdges i) k := by
          change color (innerEdges i j) = color (innerEdges i k)
          rw [hj, hk]
          exact heq
        have hjk := hinner i hc
        exact hj.symm.trans ((congrArg (innerEdges i) hjk).trans hk)

def indicator {n : Nat} (a b : Fin n) : Nat := if a = b then 1 else 0

theorem local_head_forward {s : Nat} (f g : Fin (s + 2) → Fin (s + 2))
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (htail : ∀ j : Fin s, f j.succ.succ = g j.succ.succ) (c : Fin (s + 2))
    (hc : f 0 = c ∨ f 1 = c) : g 0 = c ∨ g 1 = c := by
  obtain ⟨j, hj⟩ := hg c
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inl hj
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact Or.inr hj
  have hfc : f j.succ.succ = c := (htail j).trans hj
  rcases hc with hc | hc
  · have heq := congrArg Fin.val (hf (hfc.trans hc.symm))
    simp only [Fin.val_succ, Fin.val_zero] at heq
    omega
  · have heq := congrArg Fin.val (hf (hfc.trans hc.symm))
    simp only [Fin.val_succ] at heq
    change j.val + 1 + 1 = 1 at heq
    omega

theorem head_count_le_one {s : Nat} (f : Fin (s + 2) → Fin (s + 2))
    (hf : Function.Injective f) (c : Fin (s + 2)) :
    indicator (f 0) c + indicator (f 1) c ≤ 1 := by
  have hne : f 0 ≠ f 1 := by
    intro h
    have heq := congrArg Fin.val (hf h)
    change 0 = 1 at heq
    omega
  by_cases h0 : f 0 = c <;> by_cases h1 : f 1 = c <;>
    simp_all [indicator]

theorem local_head_counts {s : Nat} (f g : Fin (s + 2) → Fin (s + 2))
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (htail : ∀ j : Fin s, f j.succ.succ = g j.succ.succ) (c : Fin (s + 2)) :
    indicator (f 0) c + indicator (f 1) c ≤ 1 ∧
    indicator (g 0) c + indicator (g 1) c ≤ 1 ∧
    indicator (f 0) c + indicator (f 1) c = indicator (g 0) c + indicator (g 1) c := by
  have hf := head_count_le_one f hfi c
  have hg := head_count_le_one g hgi c
  have heq : (f 0 = c ∨ f 1 = c) ↔ (g 0 = c ∨ g 1 = c) :=
    ⟨local_head_forward f g hfi hgs htail c,
     local_head_forward g f hgi hfs (fun j => (htail j).symm) c⟩
  refine ⟨hf, hg, ?_⟩
  by_cases hf0 : f 0 = c <;> by_cases hf1 : f 1 = c <;>
    by_cases hg0 : g 0 = c <;> by_cases hg1 : g 1 = c <;>
    simp_all [indicator]

theorem total_ofFn_congr {α β : Type} {n : Nat} (f : α → Nat) (g : Fin n → α)
    (f' : β → Nat) (g' : Fin n → β) (h : ∀ i, f (g i) = f' (g' i)) :
    total f (List.ofFn g) = total f' (List.ofFn g') := by
  induction n with
  | zero => simp only [List.ofFn_zero, total]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [total]
      rw [h 0, ih (fun i => g i.succ) (fun i => g' i.succ) (fun i => h i.succ)]

theorem total_ofFn_zero {α : Type} {n : Nat} (f : α → Nat) (g : Fin n → α)
    (h : ∀ i, f (g i) = 0) : total f (List.ofFn g) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [total]
      rw [h 0, ih (fun i => g i.succ) (fun i => h i.succ)]

theorem total_color_indicator {n : Nat} (c : Fin n) :
    total (indicator c) (List.ofFn (fun i : Fin n => i)) = 1 := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [total]
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
      · have hz : total (indicator (0 : Fin (n + 1))) (List.ofFn Fin.succ) = 0 := by
          apply total_ofFn_zero
          intro i
          simp [indicator, Ne.symm (Fin.succ_ne_zero i)]
        rw [hz]
        rfl
      · have hz : indicator c.succ 0 = 0 := by simp [indicator, Fin.succ_ne_zero]
        rw [hz, Nat.zero_add]
        have heq : total (indicator c.succ) (List.ofFn Fin.succ) =
            total (indicator c) (List.ofFn (fun i : Fin n => i)) := by
          apply total_ofFn_congr
          intro i
          simp [indicator]
        rw [heq]
        exact ih c

theorem bit_color_mask {n : Nat} (f : Fin 5 → Fin n) (c : Fin n) (i : Fin 5) :
    bit (maskOf (fun j => decide (f j = c))).val i.val = indicator (f i) c := by
  rw [bit_maskOf]
  simp [boolValue, indicator]

def patternOfColor {s : Nat} (color : WeightedEdge s → Fin (s + 2))
    (h : IsProper color)
    (houter : ∀ i, Function.Surjective (color ∘ outerEdges i))
    (hinner : ∀ i, Function.Surjective (color ∘ innerEdges i))
    (c : Fin (s + 2)) : MatchingPattern where
  outer := maskOf (fun i => decide (color (.outer i) = c))
  inner := maskOf (fun i => decide (color (.inner i) = c))
  compatible := by
    intro i
    have hc := local_head_counts (color ∘ outerEdges i) (color ∘ innerEdges i)
      (proper_outer_injective color h i) (proper_inner_injective color h i)
      (houter i) (hinner i) (fun j => rfl) c
    change
      indicator (color (.outer i)) c + indicator (color (.outer (prevOuter i))) c ≤ 1 ∧
      indicator (color (.inner i)) c + indicator (color (.inner (prevInner i))) c ≤ 1 ∧
      indicator (color (.outer i)) c + indicator (color (.outer (prevOuter i))) c =
        indicator (color (.inner i)) c + indicator (color (.inner (prevInner i))) c at hc
    change
      bit (maskOf (fun j => decide (color (.outer j) = c))).val i.val +
        bit (maskOf (fun j => decide (color (.outer j) = c))).val (prevOuter i).val ≤ 1 ∧
      bit (maskOf (fun j => decide (color (.inner j) = c))).val i.val +
        bit (maskOf (fun j => decide (color (.inner j) = c))).val (prevInner i).val ≤ 1 ∧
      bit (maskOf (fun j => decide (color (.outer j) = c))).val i.val +
        bit (maskOf (fun j => decide (color (.outer j) = c))).val (prevOuter i).val =
      bit (maskOf (fun j => decide (color (.inner j) = c))).val i.val +
        bit (maskOf (fun j => decide (color (.inner j) = c))).val (prevInner i).val
    simpa only [bit_color_mask] using hc

theorem colored_outer_coverage {s : Nat} (color : WeightedEdge s → Fin (s + 2))
    (h : IsProper color)
    (houter : ∀ i, Function.Surjective (color ∘ outerEdges i))
    (hinner : ∀ i, Function.Surjective (color ∘ innerEdges i)) (i : Fin 5) :
    outerCoverage (List.ofFn (patternOfColor color h houter hinner)) i.val = 1 := by
  unfold outerCoverage
  calc
    _ = total (indicator (color (.outer i))) (List.ofFn (fun c : Fin (s + 2) => c)) := by
      apply total_ofFn_congr
      intro c
      exact bit_color_mask (fun j => color (.outer j)) c i
    _ = 1 := total_color_indicator (color (.outer i))

theorem colored_inner_coverage {s : Nat} (color : WeightedEdge s → Fin (s + 2))
    (h : IsProper color)
    (houter : ∀ i, Function.Surjective (color ∘ outerEdges i))
    (hinner : ∀ i, Function.Surjective (color ∘ innerEdges i)) (i : Fin 5) :
    innerCoverage (List.ofFn (patternOfColor color h houter hinner)) i.val = 1 := by
  unfold innerCoverage
  calc
    _ = total (indicator (color (.inner i))) (List.ofFn (fun c : Fin (s + 2) => c)) := by
      apply total_ofFn_congr
      intro c
      exact bit_color_mask (fun j => color (.inner j)) c i
    _ = 1 := total_color_indicator (color (.inner i))

theorem no_proper_coloring_of_local_surjectivity {s : Nat}
    (color : WeightedEdge s → Fin (s + 2)) (h : IsProper color)
    (houter : ∀ i, Function.Surjective (color ∘ outerEdges i))
    (hinner : ∀ i, Function.Surjective (color ∘ innerEdges i)) : False := by
  exact no_nonspoke_decomposition (List.ofFn (patternOfColor color h houter hinner))
    (colored_outer_coverage color h houter hinner)
    (colored_inner_coverage color h houter hinner)

/-- The weighted Petersen multigraph with `s` copies of each spoke admits
no proper edge coloring with `s+2` colors. Properness here refers to the
explicit endpoints of every edge copy, rather than to an assumed pattern
decomposition. -/
theorem weighted_petersen_not_edge_colorable (s : Nat)
    (color : WeightedEdge s → Fin (s + 2)) : ¬ IsProper color := by
  letI : Finite (Fin (s + 2)) := .intro (Equiv.refl _)
  intro h
  apply no_proper_coloring_of_local_surjectivity color h
  · intro i
    exact Finite.surjective_of_injective (proper_outer_injective color h i)
  · intro i
    exact Finite.surjective_of_injective (proper_inner_injective color h i)

/-- In particular, the ordinary Petersen graph has no proper 3-edge-coloring. -/
theorem petersen_not_three_edge_colorable (color : WeightedEdge 1 → Fin 3) :
    ¬ IsProper color := weighted_petersen_not_edge_colorable 1 color

/-- The manuscript's parameterization, with spoke multiplicity `Δ-2`. -/
theorem weighted_petersen_not_Delta_edge_colorable (Δ : Nat) (hΔ : 3 ≤ Δ)
    (color : WeightedEdge (Δ - 2) → Fin Δ) : ¬ IsProper color := by
  intro h
  have hk : Δ = (Δ - 2) + 2 := by omega
  let shifted : WeightedEdge (Δ - 2) → Fin ((Δ - 2) + 2) :=
    fun e => Fin.cast hk (color e)
  apply weighted_petersen_not_edge_colorable (Δ - 2) shifted
  intro v e f he hf hef
  apply h v e f he hf
  apply Fin.ext
  have hv := congrArg (fun z : Fin ((Δ - 2) + 2) => z.val) hef
  exact hv

end Overfull.Sharpness
