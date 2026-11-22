import Overfull.OneCore.Complement

/-!
# Actual neighborhood conditions after moving core vertices

Every incidence is an original multigraph edge copy. Distinct neighbors are
counted separately from incidences, so parallel copies are retained throughout.
The final theorem derives the ordinary-vertex conditions after a bounded move,
together with an actual coloring of the new core complement.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype E]
variable (G : Multigraph V E)

/-- The distinct neighbors in `X`, as the image of the actual incident copies. -/
def neighborsIn (x : V) (X : Finset V) : Finset V :=
  (G.edgesTo x X).image (G.otherEnd x)

@[simp] theorem mem_neighborsIn (x v : V) (X : Finset V) :
    v ∈ neighborsIn G x X ↔ v ∈ X ∧ (G.parallelEdges x v).Nonempty := by
  constructor
  · rintro hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hx, hX⟩ := (G.mem_edgesTo x X e).mp he
    exact ⟨hX, ⟨e, (G.mem_parallelEdges x _ e).mpr ⟨hx, rfl⟩⟩⟩
  · rintro ⟨hv, e, he⟩
    obtain ⟨hx, hother⟩ := (G.mem_parallelEdges x v e).mp he
    apply Finset.mem_image.mpr
    exact ⟨e, (G.mem_edgesTo x X e).mpr ⟨hx, hother.symm ▸ hv⟩, hother⟩

theorem neighborsIn_subset (x : V) (X : Finset V) : neighborsIn G x X ⊆ X := by
  intro v hv
  exact ((mem_neighborsIn G x v X).mp hv).1

theorem neighborsIn_card_le (x : V) (X : Finset V) :
    (neighborsIn G x X).card ≤ (G.edgesTo x X).card := Finset.card_image_le

theorem edgesTo_sdiff (x : V) (X Y : Finset V) :
    G.edgesTo x (X \ Y) = G.edgesTo x X \ G.edgesTo x Y := by
  ext e
  simp only [Multigraph.mem_edgesTo, Finset.mem_sdiff]
  tauto

theorem neighborsIn_sdiff (x : V) (X Y : Finset V) :
    neighborsIn G x (X \ Y) = neighborsIn G x X \ neighborsIn G x Y := by
  ext v
  simp only [mem_neighborsIn, Finset.mem_sdiff]
  tauto

theorem neighborsIn_mono (x : V) {X Y : Finset V} (hXY : X ⊆ Y) :
    neighborsIn G x X ⊆ neighborsIn G x Y := by
  intro v hv
  obtain ⟨hvX, he⟩ := (mem_neighborsIn G x v X).mp hv
  exact (mem_neighborsIn G x v Y).mpr ⟨hXY hvX, he⟩

theorem edgesTo_mono (x : V) {X Y : Finset V} (hXY : X ⊆ Y) :
    G.edgesTo x X ⊆ G.edgesTo x Y := by
  intro e he
  obtain ⟨hx, hX⟩ := (G.mem_edgesTo x X e).mp he
  exact (G.mem_edgesTo x Y e).mpr ⟨hx, hXY hX⟩

/-- Removing vertices loses at most one distinct neighbor per removed vertex. -/
theorem neighborsIn_loss (x : V) (X Y : Finset V) :
    (neighborsIn G x X).card ≤ (neighborsIn G x (X \ Y)).card + Y.card := by
  rw [neighborsIn_sdiff]
  have h := Finset.card_sdiff_add_card_inter
    (neighborsIn G x X) (neighborsIn G x Y)
  have hsub : neighborsIn G x X ∩ neighborsIn G x Y ⊆ Y :=
    fun _ hv => neighborsIn_subset G x Y (Finset.mem_inter.mp hv).2
  have hc := Finset.card_le_card hsub
  omega

/-- The number of repeated incidences cannot increase when the target set shrinks. -/
theorem repeated_incidence_mono (x : V) {X Y : Finset V} (hXY : X ⊆ Y) :
    (G.edgesTo x X).card - (neighborsIn G x X).card ≤
      (G.edgesTo x Y).card - (neighborsIn G x Y).card := by
  have he := Finset.card_sdiff_add_card_eq_card (edgesTo_mono G x hXY)
  have hn := Finset.card_sdiff_add_card_eq_card (neighborsIn_mono G x hXY)
  rw [← edgesTo_sdiff] at he
  rw [← neighborsIn_sdiff] at hn
  have hdiff := neighborsIn_card_le G x (Y \ X)
  have hX := neighborsIn_card_le G x X
  have hY := neighborsIn_card_le G x Y
  omega

theorem repeated_incidence_real_mono (x : V) {X Y : Finset V} (hXY : X ⊆ Y) :
    ((G.edgesTo x X).card : ℝ) - (neighborsIn G x X).card ≤
      ((G.edgesTo x Y).card : ℝ) - (neighborsIn G x Y).card := by
  have h := repeated_incidence_mono G x hXY
  have hX := neighborsIn_card_le G x X
  have hY := neighborsIn_card_le G x Y
  have h' : ((G.edgesTo x X).card - (neighborsIn G x X).card : ℕ) ≤
      (G.edgesTo x Y).card - (neighborsIn G x Y).card := h
  have hr : (((G.edgesTo x X).card - (neighborsIn G x X).card : ℕ) : ℝ) ≤
      (((G.edgesTo x Y).card - (neighborsIn G x Y).card : ℕ) : ℝ) := by
    exact_mod_cast h'
  rw [Nat.cast_sub hX, Nat.cast_sub hY] at hr
  exact hr

/-- A pointwise bound on parallel copies gives the actual total loss bound. -/
theorem edgesTo_card_le_of_parallel (x : V) (Y : Finset V) (a : ℝ)
    (hparallel : ∀ y ∈ Y, ((G.parallelEdges x y).card : ℝ) ≤ a) :
    ((G.edgesTo x Y).card : ℝ) ≤ a * Y.card := by
  have hsum : (G.edgesTo x Y).card =
      ∑ y ∈ Y, ((G.edgesTo x Y).filter (fun e => G.otherEnd x e = y)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun e he => ((G.mem_edgesTo x Y e).mp he).2)
  have hf (y : V) (hy : y ∈ Y) :
      (G.edgesTo x Y).filter (fun e => G.otherEnd x e = y) = G.parallelEdges x y := by
    ext e
    simp only [Finset.mem_filter, Multigraph.mem_edgesTo, Multigraph.mem_parallelEdges]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.symm ▸ hy⟩, h.2⟩
  have hreal : ((G.edgesTo x Y).card : ℝ) =
      ∑ y ∈ Y, (((G.edgesTo x Y).filter (fun e => G.otherEnd x e = y)).card : ℝ) := by
    exact_mod_cast hsum
  rw [hreal]
  calc
    _ ≤ ∑ _y ∈ Y, a := by
      apply Finset.sum_le_sum
      intro y hy
      rw [hf y hy]
      exact hparallel y hy
    _ = a * Y.card := by simp [mul_comm]

/-- A deleted set with bounded pair multiplicities loses at most `a * |Y|` copies. -/
theorem edgesTo_loss (x : V) (U Y : Finset V) (a : ℝ)
    (hparallel : ∀ y ∈ Y, ((G.parallelEdges x y).card : ℝ) ≤ a) :
    ((G.edgesTo x U).card : ℝ) - a * Y.card ≤ (G.edgesTo x (U \ Y)).card := by
  have hsplit := Finset.card_sdiff_add_card_inter (G.edgesTo x U) (G.edgesTo x Y)
  have hinter := Finset.card_le_card
    (Finset.inter_subset_right : G.edgesTo x U ∩ G.edgesTo x Y ⊆ G.edgesTo x Y)
  have hnat : (G.edgesTo x U).card ≤
      (G.edgesTo x (U \ Y)).card + (G.edgesTo x Y).card := by
    rw [edgesTo_sdiff]
    omega
  have hr : ((G.edgesTo x U).card : ℝ) ≤
      (G.edgesTo x (U \ Y)).card + (G.edgesTo x Y).card := by exact_mod_cast hnat
  have hp := edgesTo_card_le_of_parallel G x Y a hparallel
  linarith

variable {G}

/-- An edge from outside the core is a complementary copy, even if parallel. -/
theorem outside_parallel_le_complement (U : Finset V) (H : Finset E)
    (hsupport : H ⊆ G.internalEdges U) (x : V) (hx : x ∉ U) (y : V) :
    (G.parallelEdges x y).card ≤ (G.restrictEdges Hᶜ).degree y := by
  rw [Multigraph.restrictEdges_degree]
  apply Finset.card_le_card
  intro e he
  obtain ⟨hxe, hother⟩ := (G.mem_parallelEdges x y e).mp he
  have heq : G.edge e = s(x,y) := by rw [G.edge_eq_otherEnd x e hxe, hother]
  refine Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩
  · intro heH
    exact hx ((G.internalEdges_iff_of_edge e x y heq U).mp (hsupport heH)).1
  · rw [G.mem_incidenceEdges, heq]
    simp

/-- A simple embedded core accounts for distinct neighbors; all repeated
incidences are charged to actual complementary copies. -/
theorem repeated_incidence_le_complement (H : Finset E)
    (hsimple : Set.InjOn G.edge H) (x : V) (X : Finset V) :
    (G.edgesTo x X).card ≤
      (neighborsIn G x X).card + (G.restrictEdges Hᶜ).degree x := by
  have hcore : (H ∩ G.edgesTo x X).card ≤ (neighborsIn G x X).card := by
    apply Finset.card_le_card_of_injOn (G.otherEnd x)
    · intro e he
      exact Finset.mem_image.mpr ⟨e, (Finset.mem_inter.mp he).2, rfl⟩
    · intro e he f hf hef
      have hex := ((G.mem_edgesTo x X e).mp (Finset.mem_inter.mp he).2).1
      have hfx := ((G.mem_edgesTo x X f).mp (Finset.mem_inter.mp hf).2).1
      apply hsimple (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hf).1
      rw [G.edge_eq_otherEnd x e hex, G.edge_eq_otherEnd x f hfx, hef]
  have hcomp : (G.edgesTo x X \ H).card ≤ (G.restrictEdges Hᶜ).degree x := by
    rw [Multigraph.restrictEdges_degree]
    apply Finset.card_le_card
    intro e he
    obtain ⟨heX, heH⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr heH,
      (G.mem_incidenceEdges x e).mpr ((G.mem_edgesTo x X e).mp heX).1⟩
  have hsplit := Finset.card_sdiff_add_card_inter (G.edgesTo x X) H
  rw [Finset.inter_comm] at hsplit
  omega

/-- The two ordinary-vertex alternatives, expressed on actual incidences
and distinct neighbors in the two sides. -/
def OrdinaryPorts (A B Z₀ : Finset V) (k : ℕ) (a β : ℝ) : Prop :=
  ∀ x, x ∉ A ∪ B → x ∉ Z₀ →
    β * k ≤ ((G.edgesTo x (A ∪ B)).card : ℝ) ∧
      (((G.edgesTo x (A ∪ B)).card : ℝ) ≤ (neighborsIn G x (A ∪ B)).card + a ∨
        (β * k ≤ (neighborsIn G x A).card ∧ β * k ≤ (neighborsIn G x B).card))

variable [Fintype V]

omit [Fintype E] in
/-- The new exceptional set contains precisely the old exceptions and
the moved core vertices, with no overlap. -/
theorem moved_exceptional_card (U Y : Finset V) (hY : Y ⊆ U) :
    (U \ Y)ᶜ.card = Uᶜ.card + Y.card := by
  have heq : (U \ Y)ᶜ = Uᶜ ∪ Y := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hd : Disjoint Uᶜ Y := by
    apply Finset.disjoint_left.mpr
    intro v hv hy
    exact (Finset.mem_compl.mp hv) (hY hy)
  rw [heq, Finset.card_union_of_disjoint hd]

omit [Fintype V] [Fintype E] in
/-- Equal deletions from equal actual sides preserve their equality of order. -/
theorem moved_sides_balance (A B Y : Finset V)
    (hAB : A.card = B.card) (hY : (A ∩ Y).card = (B ∩ Y).card) :
    (A \ Y).card = (B \ Y).card := by
  have hA := Finset.card_sdiff_add_card_inter A Y
  have hB := Finset.card_sdiff_add_card_inter B Y
  omega

/-- Moving core vertices preserves the ordinary-vertex alternatives.
The numerical hypotheses are explicit finite budgets, later supplied by
the small-error and large-order parameter choices. -/
theorem ordinaryPorts_after_move
    (A B Z₀ Y : Finset V) (H : Finset E) (k : ℕ) (a β : ℝ)
    (hsupport : H ⊆ G.internalEdges (A ∪ B)) (hsimple : Set.InjOn G.edge H)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v ∈ A ∪ B, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hY : Y ⊆ A ∪ B) (hβ : β ≤ 1)
    (hbudget : 3 * (a + Y.card) < k)
    (hloss : 2 * a * Y.card ≤ β * k)
    (hneighborloss : 2 * (Y.card : ℝ) ≤ β * k)
    (hports : OrdinaryPorts (G := G) A B Z₀ k a β) :
    OrdinaryPorts (G := G) (A \ Y) (B \ Y) Z₀ k (a + Y.card) (β / 2) := by
  have hunion : (A \ Y) ∪ (B \ Y) = (A ∪ B) \ Y := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  intro x hx hxZ
  rw [hunion] at hx ⊢
  by_cases hxU : x ∈ A ∪ B
  · have houtside := G.core_outside_degree_le H (A ∪ B) Y hsupport hsimple x
    have hsplit := G.edgesTo_compl_card_add x ((A ∪ B) \ Y)
    rw [hregular x] at hsplit
    have hsplit' : ((G.edgesTo x ((A ∪ B) \ Y)ᶜ).card : ℝ) +
        (G.edgesTo x ((A ∪ B) \ Y)).card = k := by exact_mod_cast hsplit
    have houtside' : ((G.edgesTo x ((A ∪ B) \ Y)ᶜ).card : ℝ) ≤
        (G.restrictEdges Hᶜ).degree x + Y.card := by exact_mod_cast houtside
    have hcorex := hcore x hxU
    have hβk : β * k ≤ (k : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg k)
    refine ⟨by nlinarith, Or.inl ?_⟩
    have hr := repeated_incidence_le_complement H hsimple x ((A ∪ B) \ Y)
    have hr' : ((G.edgesTo x ((A ∪ B) \ Y)).card : ℝ) ≤
        (neighborsIn G x ((A ∪ B) \ Y)).card + (G.restrictEdges Hᶜ).degree x := by
      exact_mod_cast hr
    have ht : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    linarith
  · obtain ⟨hc, halt⟩ := hports x hxU hxZ
    have hparallel (y : V) (hy : y ∈ Y) : ((G.parallelEdges x y).card : ℝ) ≤ a := by
      have hp := outside_parallel_le_complement (A ∪ B) H hsupport x hxU y
      have hp' : ((G.parallelEdges x y).card : ℝ) ≤
          (G.restrictEdges Hᶜ).degree y := by exact_mod_cast hp
      exact hp'.trans (hcore y (hY hy))
    have hleft := edgesTo_loss G x (A ∪ B) Y a hparallel
    refine ⟨by nlinarith, ?_⟩
    rcases halt with hr | ⟨hA, hB⟩
    · apply Or.inl
      have hm := repeated_incidence_real_mono G x
        (Finset.sdiff_subset : (A ∪ B) \ Y ⊆ A ∪ B)
      have ht : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
      linarith
    · apply Or.inr
      have hAloss := neighborsIn_loss G x A Y
      have hBloss := neighborsIn_loss G x B Y
      have hAloss' : ((neighborsIn G x A).card : ℝ) ≤
          (neighborsIn G x (A \ Y)).card + Y.card := by exact_mod_cast hAloss
      have hBloss' : ((neighborsIn G x B).card : ℝ) ≤
          (neighborsIn G x (B \ Y)).card + Y.card := by exact_mod_cast hBloss
      constructor <;> nlinarith

/-- The actual bounded move supplies a coloring of the new complement,
its core load bound, and the new ordinary-vertex neighborhood conditions. -/
theorem bounded_move_with_ports
    (A B Z₀ Y : Finset V) (H : Finset E) (k : ℕ) (a β : ℝ)
    (hsupport : H ⊆ G.internalEdges (A ∪ B)) (hsimple : Set.InjOn G.edge H)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v ∈ A ∪ B, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hY : Y ⊆ A ∪ B) (hβ : β ≤ 1)
    (hbudget : 3 * (a + Y.card) < k)
    (hloss : 2 * a * Y.card ≤ β * k)
    (hneighborloss : 2 * (Y.card : ℝ) ≤ β * k)
    (hports : OrdinaryPorts (G := G) A B Z₀ k a β)
    (hcolor : Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k)) :
    Nonempty ((G.restrictEdges (H ∩ G.internalEdges ((A ∪ B) \ Y))ᶜ).EdgeColoring k) ∧
      (∀ v ∈ (A ∪ B) \ Y,
        ((G.restrictEdges (H ∩ G.internalEdges ((A ∪ B) \ Y))ᶜ).degree v : ℝ) ≤
          a + Y.card) ∧
      OrdinaryPorts (G := G) (A \ Y) (B \ Y) Z₀ k (a + Y.card) (β / 2) := by
  obtain ⟨c, hc⟩ := G.bounded_core_move_full k a (A ∪ B) Y H
    hregular hsupport hsimple hcore hcolor hbudget
  exact ⟨c, hc, ordinaryPorts_after_move A B Z₀ Y H k a β
    hsupport hsimple hregular hcore hY hβ hbudget hloss hneighborloss hports⟩

/-- The move applies to the actual embedded simple core, deriving its
complementary degree bound from the core degree error. -/
theorem core_move_with_ports
    (A B Z₀ Y : Finset V) (C : Core G (A ∪ B)) (k : ℕ) (a β : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (hY : Y ⊆ A ∪ B) (hβ : β ≤ 1)
    (hbudget : 3 * (a + Y.card) < k)
    (hloss : 2 * a * Y.card ≤ β * k)
    (hneighborloss : 2 * (Y.card : ℝ) ≤ β * k)
    (hports : OrdinaryPorts (G := G) A B Z₀ k a β)
    (hcolor : Nonempty ((G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)) :
    Nonempty ((G.restrictEdges
      (OneCore.coreEdges C ∩ G.internalEdges ((A ∪ B) \ Y))ᶜ).EdgeColoring k) ∧
      (∀ v ∈ (A ∪ B) \ Y,
        ((G.restrictEdges
          (OneCore.coreEdges C ∩ G.internalEdges ((A ∪ B) \ Y))ᶜ).degree v : ℝ) ≤
          a + Y.card) ∧
      OrdinaryPorts (G := G) (A \ Y) (B \ Y) Z₀ k (a + Y.card) (β / 2) := by
  apply bounded_move_with_ports A B Z₀ Y (OneCore.coreEdges C) k a β
    (OneCore.coreEdges_subset_internal C) (OneCore.coreEdges_simple C)
    hregular ?_ hY hβ hbudget hloss hneighborloss hports hcolor
  intro v hv
  exact OneCore.complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩

omit [Fintype V] [Fintype E] in
/-- For any fixed density, port reserve, and bound on the moved set,
the three numerical move budgets hold uniformly at sufficiently large order. -/
theorem exists_move_budgets (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (L : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (m k t : ℕ) (a : ℝ),
      n₀ ≤ m → α * m ≤ k → 0 ≤ a → a ≤ ε * m → t ≤ L →
      3 * (a + t) < k ∧ 2 * a * t ≤ β * k ∧ 2 * (t : ℝ) ≤ β * k := by
  let ε : ℝ := min (α / 12) (α * β / (2 * ((L : ℝ) + 1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (12 * (L : ℝ) / α)
    (4 * (L : ℝ) / (α * β)) + 1)
  refine ⟨ε, hε, n₀, ?_⟩
  intro m k t a hm hk ha hae ht
  have hnm : (n₀ : ℝ) ≤ m := by exact_mod_cast hm
  have htL : (t : ℝ) ≤ L := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hab : 0 < α * β := mul_pos hα hβ
  have hmfirst : 12 * (L : ℝ) / α < m := by
    have hh := le_max_left (12 * (L : ℝ) / α) (4 * (L : ℝ) / (α * β))
    linarith
  have hmsecond : 4 * (L : ℝ) / (α * β) < m := by
    have hh := le_max_right (12 * (L : ℝ) / α) (4 * (L : ℝ) / (α * β))
    linarith
  have hbig : 12 * (L : ℝ) < m * α := (div_lt_iff₀ hα).mp hmfirst
  have hbigβ : 4 * (L : ℝ) < m * (α * β) := (div_lt_iff₀ hab).mp hmsecond
  have hεα : ε ≤ α / 12 := min_le_left _ _
  have hεαm := mul_le_mul_of_nonneg_right hεα hm0
  have hβk := mul_le_mul_of_nonneg_left hk hβ.le
  have hεL : ε * (2 * ((L : ℝ) + 1)) ≤ α * β := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((L : ℝ) + 1))).mp
    exact min_le_right _ _
  have hεt : 2 * ε * (t : ℝ) ≤ α * β := by
    have hh := mul_le_mul_of_nonneg_left htL (show 0 ≤ 2 * ε by positivity)
    nlinarith
  have hεtm := mul_le_mul_of_nonneg_right hεt hm0
  have hat := mul_le_mul_of_nonneg_right hae ht0
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  nlinarith

end Overfull.BipartiteFactorization
