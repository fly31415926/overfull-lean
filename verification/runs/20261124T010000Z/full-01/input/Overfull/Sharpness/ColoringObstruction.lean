import Overfull.CliqueColors
import Overfull.CutCounting
import Overfull.Sharpness.Family
import Overfull.Sharpness.DeletedPetersen

/-!
# Contracting the four odd cliques

Every surviving weighted Petersen edge copy is represented by a distinct
actual edge of the sharpness graph. The inverse images of contracted vertices
are odd cliques or single vertices. Saturation forces the colors on each such
boundary to be distinct, producing the forbidden coloring of the deleted
weighted Petersen multigraph.
-/

namespace Overfull.Sharpness.ColoringObstruction

open Finset

abbrev DeletedEdge (Δ : ℕ) :=
  Deletion.OldEdge (DeletedPetersen.graph (Δ - 2)) (Sum.inl 0)

def contracted {Δ : ℕ} : Family.Vertex Δ → WeightedVertex
  | .inl (i, _) => .inl (Family.spoke i)
  | .inr w => .inr w

def fiber (Δ : ℕ) (v : WeightedVertex) : Finset (Family.Vertex Δ) :=
  Finset.univ.filter (fun x => contracted x = v)

@[simp] theorem mem_fiber (Δ : ℕ) (v : WeightedVertex) (x : Family.Vertex Δ) :
    x ∈ fiber Δ v ↔ contracted x = v := by
  simp [fiber]

theorem fiber_outer_card (Δ : ℕ) (i : Fin 4) :
    (fiber Δ (.inl (Family.spoke i))).card = Δ := by
  have heq : fiber Δ (.inl (Family.spoke i)) =
      Finset.univ.image (fun a : Fin Δ => (Sum.inl (i, a) : Family.Vertex Δ)) := by
    ext x
    cases x with
    | inl x =>
      rcases x with ⟨j, a⟩
      simp [fiber, contracted, Family.spoke, Fin.ext_iff, eq_comm]
    | inr w => simp [fiber, contracted]
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (Prod.mk.inj (Sum.inl.inj h)).2

theorem fiber_inner_card (Δ : ℕ) (w : Fin 5) :
    (fiber Δ (.inr w)).card = 1 := by
  have heq : fiber Δ (.inr w) = {Sum.inr w} := by
    ext x
    cases x <;> simp [fiber, contracted]
  rw [heq]
  simp

theorem fiber_isClique (Δ : ℕ) (v : WeightedVertex) :
    ∀ x ∈ fiber Δ v, ∀ y ∈ fiber Δ v, x ≠ y → (Family.graph Δ).Adj x y := by
  intro x hx y hy hne
  have hxy : contracted x = contracted y :=
    (mem_fiber Δ v x).mp hx |>.trans ((mem_fiber Δ v y).mp hy).symm
  cases x with
  | inl x =>
    rcases x with ⟨i, a⟩
    cases y with
    | inl y =>
      rcases y with ⟨j, b⟩
      have hij : i = j := by
        apply Fin.ext
        have h := congrArg Fin.val (Sum.inl.inj hxy)
        dsimp [Family.spoke] at h
        omega
      have hab : a ≠ b := by
        intro hab
        apply hne
        cases hij
        cases hab
        rfl
      exact Or.inl ⟨hij, hab⟩
    | inr w => cases hxy
  | inr w =>
    cases y with
    | inl y => cases hxy
    | inr z => exact False.elim (hne (congrArg Sum.inr (Sum.inr.inj hxy)))

def precedingClique (i : Fin 5) : Fin 4 := ⟨(i.val + 3) % 4, by omega⟩
def followingClique (i : Fin 5) : Fin 4 := ⟨i.val % 4, by omega⟩

def spokeLabel {Δ : ℕ} (hΔ : 3 ≤ Δ) (j : Fin (Δ - 2)) : Fin Δ :=
  ⟨j.val + 2, by have h := j.isLt; omega⟩

def expandedLeft {Δ : ℕ} (hΔ : 3 ≤ Δ) : WeightedEdge (Δ - 2) → Family.Vertex Δ
  | .outer i => .inl (precedingClique i, Family.v hΔ)
  | .inner i => .inr i
  | .spoke i j => .inl (precedingClique i, spokeLabel hΔ j)

def expandedRight {Δ : ℕ} (hΔ : 3 ≤ Δ) : WeightedEdge (Δ - 2) → Family.Vertex Δ
  | .outer i => .inl (followingClique i, Family.u hΔ)
  | .inner i => .inr (nextInner i)
  | .spoke i _ => .inr i

theorem outer_old_iff (s : ℕ) (i : Fin 5) :
    (Sum.inl 0 : WeightedVertex) ∉ Deletion.ends (DeletedPetersen.graph s) (.outer i) ↔
      i.val ≠ 0 ∧ i.val ≠ 4 := by
  rw [DeletedPetersen.mem_ends_iff]
  fin_cases i <;> simp [Incident, firstEnd, secondEnd, nextOuter]

theorem spoke_old_iff (s : ℕ) (i : Fin 5) (j : Fin s) :
    (Sum.inl 0 : WeightedVertex) ∉ Deletion.ends (DeletedPetersen.graph s) (.spoke i j) ↔
      i.val ≠ 0 := by
  rw [DeletedPetersen.mem_ends_iff]
  change (¬ ((Sum.inl i : WeightedVertex) = Sum.inl 0 ∨
    (Sum.inr i : WeightedVertex) = Sum.inl 0)) ↔ i.val ≠ 0
  simp only [Sum.inl.injEq, Sum.inr_ne_inl, or_false, Fin.ext_iff, Fin.val_zero]

theorem expanded_adj {Δ : ℕ} (hΔ : 3 ≤ Δ) (e : DeletedEdge Δ) :
    (Family.graph Δ).Adj (expandedLeft hΔ e.val) (expandedRight hΔ e.val) := by
  rcases e with ⟨e, he⟩
  cases e with
  | outer i =>
    have hi := (outer_old_iff (Δ - 2) i).mp he
    fin_cases i <;>
      simp_all [expandedLeft, expandedRight, precedingClique, followingClique,
        Family.graph, Family.Adjacent, Family.u, Family.v]
  | inner i => exact Or.inl rfl
  | spoke i j =>
    have hi := (spoke_old_iff (Δ - 2) i j).mp he
    fin_cases i <;>
      simp_all [expandedLeft, expandedRight, precedingClique, spokeLabel,
        Family.graph, Family.Adjacent]

def liftedEdge {Δ : ℕ} (hΔ : 3 ≤ Δ) (e : DeletedEdge Δ) : (Family.graph Δ).edgeSet :=
  ⟨s(expandedLeft hΔ e.val, expandedRight hΔ e.val), expanded_adj hΔ e⟩

theorem contracted_expandedLeft {Δ : ℕ} (hΔ : 3 ≤ Δ) (e : DeletedEdge Δ) :
    contracted (expandedLeft hΔ e.val) = firstEnd e.val := by
  rcases e with ⟨e, he⟩
  cases e with
  | outer i =>
    have hi := (outer_old_iff (Δ - 2) i).mp he
    fin_cases i <;> simp_all [contracted, expandedLeft, firstEnd, precedingClique, Family.spoke]
  | inner i => rfl
  | spoke i j =>
    have hi := (spoke_old_iff (Δ - 2) i j).mp he
    fin_cases i <;> simp_all [contracted, expandedLeft, firstEnd, precedingClique, Family.spoke]

theorem contracted_expandedRight {Δ : ℕ} (hΔ : 3 ≤ Δ) (e : DeletedEdge Δ) :
    contracted (expandedRight hΔ e.val) = secondEnd e.val := by
  rcases e with ⟨e, he⟩
  cases e with
  | outer i =>
    have hi := (outer_old_iff (Δ - 2) i).mp he
    fin_cases i <;>
      simp_all [contracted, expandedRight, secondEnd, followingClique, Family.spoke, nextOuter]
  | inner i => rfl
  | spoke i j => rfl

theorem liftedEdge_injective {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    Function.Injective (liftedEdge hΔ) := by
  intro e f hef
  have hval := congrArg Subtype.val hef
  apply Subtype.ext
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  change s(expandedLeft hΔ e, expandedRight hΔ e) =
    s(expandedLeft hΔ f, expandedRight hΔ f) at hval
  cases e with
  | outer i =>
    cases f with
    | outer j =>
      have hi := (outer_old_iff (Δ - 2) i).mp he
      have hj := (outer_old_iff (Δ - 2) j).mp hf
      simp only [expandedLeft, expandedRight] at hval
      rcases Sym2.eq_iff.mp hval with ⟨_, hright⟩ | ⟨hflip, _⟩
      · have hidx := congrArg Fin.val ((Prod.mk.inj (Sum.inl.inj hright)).1)
        dsimp [followingClique] at hidx
        have hbi := i.isLt
        have hbj := j.isLt
        have hij : i = j := Fin.ext (by omega)
        exact congrArg WeightedEdge.outer hij
      · have hlabel := congrArg Fin.val ((Prod.mk.inj (Sum.inl.inj hflip)).2)
        simp [Family.u, Family.v] at hlabel
    | inner j =>
      simp [expandedLeft, expandedRight] at hval
    | spoke j b =>
      simp [expandedLeft, expandedRight] at hval
  | inner i =>
    cases f with
    | outer j =>
      simp [expandedLeft, expandedRight] at hval
    | inner j =>
      fin_cases i <;> fin_cases j <;>
        simp_all [expandedLeft, expandedRight, nextInner]
    | spoke j b =>
      simp [expandedLeft, expandedRight] at hval
  | spoke i a =>
    cases f with
    | outer j =>
      simp [expandedLeft, expandedRight] at hval
    | inner j =>
      simp [expandedLeft, expandedRight] at hval
    | spoke j b =>
      simp only [expandedLeft, expandedRight] at hval
      rcases Sym2.eq_iff.mp hval with ⟨hleft, hright⟩ | ⟨hflip, _⟩
      · have hij : i = j := Sum.inr.inj hright
        have hlabel := congrArg Fin.val ((Prod.mk.inj (Sum.inl.inj hleft)).2)
        dsimp [spokeLabel] at hlabel
        have hab : a = b := Fin.ext (by omega)
        cases hij
        cases hab
        rfl
      · cases hflip

theorem fiber_odd_and_saturated {Δ : ℕ} (hodd : Δ % 2 = 1)
    (v : WeightedVertex) (hv : v ≠ Sum.inl 0) :
    (fiber Δ v).card % 2 = 1 ∧
      (internalEdges (Family.graph Δ) (fiber Δ v)).card =
        Δ * ((fiber Δ v).card / 2) := by
  cases v with
  | inl i =>
    have hi : i.val ≠ 0 := by
      intro hi
      exact hv (congrArg Sum.inl (Fin.ext hi))
    have hindex : Family.spoke (precedingClique i) = i := by
      fin_cases i <;> simp_all [Family.spoke, precedingClique]
    have hcard : (fiber Δ (.inl i)).card = Δ := by
      rw [← hindex]
      exact fiber_outer_card Δ (precedingClique i)
    refine ⟨by rw [hcard]; exact hodd, ?_⟩
    exact saturated_odd_clique (Family.graph Δ) (fiber Δ (.inl i)) Δ hcard hodd
      (fiber_isClique Δ (.inl i))
  | inr w =>
    have hcard := fiber_inner_card Δ w
    have hcount := clique_internal_edge_count (Family.graph Δ) (fiber Δ (.inr w))
      (fiber_isClique Δ (.inr w))
    rw [hcard] at hcount ⊢
    norm_num at hcount ⊢
    omega

theorem liftedEdge_crosses_fiber {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (e : DeletedEdge Δ) (v : WeightedVertex) (hv : Incident v e.val) :
    EdgeCrosses (fiber Δ v) (liftedEdge hΔ e) := by
  have hleft := contracted_expandedLeft hΔ e
  have hright := contracted_expandedRight hΔ e
  rcases hv with hv | hv
  · refine ⟨⟨expandedLeft hΔ e.val, ?_, by simp [liftedEdge]⟩,
      ⟨expandedRight hΔ e.val, ?_, by simp [liftedEdge]⟩⟩
    · exact (mem_fiber Δ v _).mpr (hleft.trans hv)
    · intro hmem
      have h := (mem_fiber Δ v _).mp hmem
      exact loopless e.val (hv.trans (hright.symm.trans h).symm)
  · refine ⟨⟨expandedRight hΔ e.val, ?_, by simp [liftedEdge]⟩,
      ⟨expandedLeft hΔ e.val, ?_, by simp [liftedEdge]⟩⟩
    · exact (mem_fiber Δ v _).mpr (hright.trans hv)
    · intro hmem
      have h := (mem_fiber Δ v _).mp hmem
      exact loopless e.val ((hleft.symm.trans h).trans hv.symm)

/-- A hypothetical coloring of the sharpness graph descends to a proper
coloring of the actual deleted weighted Petersen multigraph. -/
def contractedColoring {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1)
    (c : EdgeColoring (Family.graph Δ) Δ) :
    Deletion.DeletedColoring (DeletedPetersen.graph (Δ - 2)) (.inl 0) Δ where
  color e := c.color (liftedEdge hΔ e)
  proper := by
    intro e f v he hf hcolor
    have hv : v ≠ Sum.inl 0 := by
      intro hv
      subst v
      exact e.property he
    obtain ⟨hoddFiber, hfull⟩ := fiber_odd_and_saturated hodd v hv
    have heInc : Incident v e.val := (DeletedPetersen.mem_ends_iff _ _ _).mp he
    have hfInc : Incident v f.val := (DeletedPetersen.mem_ends_iff _ _ _).mp hf
    have hef : liftedEdge hΔ e = liftedEdge hΔ f :=
      c.crossing_edges_eq_of_color_eq (fiber Δ v) hoddFiber hfull
        (liftedEdge_crosses_fiber hΔ e v heInc)
        (liftedEdge_crosses_fiber hΔ f v hfInc) hcolor
    exact liftedEdge_injective hΔ hef

end Overfull.Sharpness.ColoringObstruction

namespace Overfull.Sharpness.Family

/-- For every odd `Δ ≥ 3`, the actual graph of the sharpness family has no
proper edge coloring with `Δ` colors. -/
theorem not_edge_colorable {Δ : ℕ} (hΔ : 3 ≤ Δ) (hodd : Δ % 2 = 1) :
    ¬ Nonempty (EdgeColoring (graph Δ) Δ) := by
  rintro ⟨c⟩
  exact DeletedPetersen.not_Delta_edge_colorable Δ hΔ
    ⟨ColoringObstruction.contractedColoring hΔ hodd c⟩

end Overfull.Sharpness.Family
