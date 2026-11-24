import Overfull.WeightedPalette.StarWeights

/-!
# Actual colored-star copies and sequential resource accounting

Each color receives the original copies in its color fiber. An injective
star coloring adds at most one copy per color. Away from its exceptional
center, the new color load is bounded by the actual parallel multiplicity.
For a second star's old-core pool, each color adds at most one old-core
endpoint, and hence at most one multiplicity bound to its blocked-copy weight.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical WeightedPalette

variable {V E : Type*} {h : ℕ}

/-- Actual original copies in one color fiber of a finite star-copy set. -/
def coloredStarCopies (A : Finset E) (c : ↥A → Fin h) (j : Fin h) : Finset E :=
  (univ.filter (fun e => c e = j)).image Subtype.val

@[simp] theorem mem_coloredStarCopies (A : Finset E) (c : ↥A → Fin h)
    (j : Fin h) (e : E) :
    e ∈ coloredStarCopies A c j ↔ ∃ q : ↥A, c q = j ∧ q.val = e := by
  simp only [coloredStarCopies, mem_image, mem_filter, mem_univ, true_and]

theorem coloredStarCopies_subset (A : Finset E) (c : ↥A → Fin h) (j : Fin h) :
    coloredStarCopies A c j ⊆ A := by
  intro e he
  obtain ⟨q,_,rfl⟩ := (mem_coloredStarCopies A c j e).mp he
  exact q.property

/-- An injective assignment places at most one actual copy in each color. -/
theorem coloredStarCopies_card_le_one (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (j : Fin h) :
    (coloredStarCopies A c j).card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨q,hq,rfl⟩ := (mem_coloredStarCopies A c j e).mp he
  obtain ⟨q',hq',rfl⟩ := (mem_coloredStarCopies A c j f).mp hf
  exact congrArg Subtype.val (hc (hq.trans hq'.symm))

/-- Distinct colors retain disjoint sets of original copies. -/
theorem coloredStarCopies_disjoint (A : Finset E) (c : ↥A → Fin h) :
    Pairwise (fun i j => Disjoint (coloredStarCopies A c i) (coloredStarCopies A c j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨q,hq,hqe⟩ := (mem_coloredStarCopies A c i e).mp he
  obtain ⟨q',hq',hq'e⟩ := (mem_coloredStarCopies A c j e).mp hf
  have hqq : q = q' := Subtype.ext (hqe.trans hq'e.symm)
  exact hij (hq.symm.trans (hqq ▸ hq'))

/-- The color classes cover exactly the supplied original copy set. -/
theorem coloredStarCopies_cover (A : Finset E) (c : ↥A → Fin h) :
    univ.biUnion (coloredStarCopies A c) = A := by
  ext e
  constructor
  · intro he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    exact coloredStarCopies_subset A c j hj
  · intro he
    let q : ↥A := ⟨e,he⟩
    exact mem_biUnion.mpr ⟨c q,mem_univ _,
      (mem_coloredStarCopies A c (c q) e).mpr ⟨q,rfl,rfl⟩⟩

/-- Every prescribed copy belongs to its own exact color. -/
theorem coloredStarCopies_contains (A : Finset E) (c : ↥A → Fin h) (e : ↥A) :
    e.val ∈ coloredStarCopies A c (c e) :=
  (mem_coloredStarCopies A c (c e) e.val).mpr ⟨e,rfl,rfl⟩

/-- An injective assignment makes the used color class exactly that original copy. -/
theorem coloredStarCopies_eq_singleton (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (e : ↥A) :
    coloredStarCopies A c (c e) = {e.val} := by
  ext f
  constructor
  · intro hf
    exact mem_singleton.mpr (card_le_one.mp (coloredStarCopies_card_le_one A c hc (c e))
      f hf e.val (coloredStarCopies_contains A c e))
  · intro hf
    rw [mem_singleton.mp hf]
    exact coloredStarCopies_contains A c e

variable (G : Multigraph V E)

/-- Each injectively colored star class is an actual matching. -/
theorem coloredStarCopies_isMatching (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (j : Fin h) :
    G.IsMatching (coloredStarCopies A c j) := by
  intro e he f hf _ _ _
  exact card_le_one.mp (coloredStarCopies_card_le_one A c hc j) e he f hf

/-- A color adds at most two actual support vertices. -/
theorem coloredStarCopies_support_card_le_two (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (j : Fin h) :
    (G.edgeSupport (coloredStarCopies A c j)).card ≤ 2 := by
  exact (G.edgeSupport_card_le _).trans
    (Nat.mul_le_mul_left 2 (coloredStarCopies_card_le_one A c hc j))

/-- Star endpoints are the center and the original other endpoints. -/
theorem coloredStarCopies_support_subset (x : V) (A : Finset E) (c : ↥A → Fin h)
    (hA : ∀ e ∈ A, x ∈ G.edge e) (j : Fin h) :
    G.edgeSupport (coloredStarCopies A c j) ⊆ insert x (A.image (G.otherEnd x)) := by
  intro v hv
  obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
  have heA := coloredStarCopies_subset A c j he
  rw [G.edge_eq_otherEnd x e (hA e heA),Sym2.mem_iff] at hve
  rcases hve with hx | ho
  · exact mem_insert.mpr (Or.inl hx)
  · exact mem_insert.mpr (Or.inr (mem_image.mpr ⟨e,heA,ho.symm⟩))

/-- Across all colors, actual incident copies bound the color-support load. -/
theorem coloredStarCopies_support_load_le_degreeOn (A : Finset E)
    (c : ↥A → Fin h) (v : V) :
    (univ.filter (fun j => v ∈ G.edgeSupport (coloredStarCopies A c j))).card ≤
      G.degreeOn A v :=
  G.family_support_load_le_degreeOn (coloredStarCopies A c) A
    (coloredStarCopies_disjoint A c) (coloredStarCopies_subset A c) v

variable [Fintype E]

/-- Away from a star center, its actual incidence is bounded by the
corresponding original parallel-copy pool. -/
theorem star_degreeOn_le_parallel (x : V) (A : Finset E)
    (hA : ∀ e ∈ A, x ∈ G.edge e) (v : V) (hvx : v ≠ x) :
    G.degreeOn A v ≤ (G.parallelEdges x v).card := by
  apply card_le_card
  intro e he
  obtain ⟨heA,hve⟩ := mem_filter.mp he
  have hxe := hA e heA
  apply (G.mem_parallelEdges x v e).mpr
  refine ⟨hxe,?_⟩
  rw [G.edge_eq_otherEnd x e hxe,Sym2.mem_iff] at hve
  exact (hve.resolve_left hvx).symm

/-- No vertex other than the first exception acquires more colors than
the actual number of first-star parallel copies to that vertex. -/
theorem coloredStarCopies_support_load_le_parallel (x : V) (A : Finset E)
    (c : ↥A → Fin h) (hA : ∀ e ∈ A, x ∈ G.edge e) (v : V) (hvx : v ≠ x) :
    (univ.filter (fun j => v ∈ G.edgeSupport (coloredStarCopies A c j))).card ≤
      (G.parallelEdges x v).card :=
  (coloredStarCopies_support_load_le_degreeOn G A c v).trans
    (star_degreeOn_le_parallel G x A hA v hvx)

omit [Fintype E] in
private theorem support_union (B C : Finset E) :
    G.edgeSupport (B ∪ C) = G.edgeSupport B ∪ G.edgeSupport C := by
  ext v
  simp only [Multigraph.mem_edgeSupport,mem_union]
  aesop

/-- After adjoining the entire first star, old-core color load increases
from at most `D` to at most `D+b`. Injectivity is unnecessary for this bound. -/
theorem coloredStarCopies_union_support_load_le
    (B : Fin h → Finset E) (x : V) (A : Finset E) (c : ↥A → Fin h)
    (hA : ∀ e ∈ A, x ∈ G.edge e) (U : Finset V) (hxU : x ∉ U) (D b : ℕ)
    (hparallel : ∀ v ∈ U, (G.parallelEdges x v).card ≤ b)
    (hbase : ∀ v ∈ U, (univ.filter (fun j => v ∈ G.edgeSupport (B j))).card ≤ D) :
    ∀ v ∈ U, (univ.filter (fun j =>
      v ∈ G.edgeSupport (B j ∪ coloredStarCopies A c j))).card ≤ D+b := by
  intro v hv
  have hvx : v ≠ x := fun hh => hxU (hh ▸ hv)
  have hstar := (coloredStarCopies_support_load_le_parallel G x A c hA v hvx).trans
    (hparallel v hv)
  have heq : (univ.filter (fun j => v ∈ G.edgeSupport (B j ∪ coloredStarCopies A c j))) =
      (univ.filter (fun j => v ∈ G.edgeSupport (B j))) ∪
      (univ.filter (fun j => v ∈ G.edgeSupport (coloredStarCopies A c j))) := by
    ext j
    simp [support_union]
  rw [heq]
  exact (card_union_le _ _).trans (Nat.add_le_add (hbase v hv) hstar)

omit [Fintype E] in
/-- An injective star class occupies at most one vertex of any old-core
set excluding its exceptional center. -/
theorem coloredStarCopies_inter_support_card_le_one
    (x : V) (U : Finset V) (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (hA : ∀ e ∈ A, x ∈ G.edge e)
    (hxU : x ∉ U) (j : Fin h) :
    (U ∩ G.edgeSupport (coloredStarCopies A c j)).card ≤ 1 := by
  apply card_le_one.mpr
  intro v hv w hw
  obtain ⟨hvU,hv⟩ := mem_inter.mp hv
  obtain ⟨hwU,hw⟩ := mem_inter.mp hw
  obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hv
  obtain ⟨f,hf,hwf⟩ := (G.mem_edgeSupport _ w).mp hw
  have hef := card_le_one.mp (coloredStarCopies_card_le_one A c hc j) e he f hf
  subst f
  have hxe := hA e (coloredStarCopies_subset A c j he)
  rw [G.edge_eq_otherEnd x e hxe,Sym2.mem_iff] at hve hwf
  have hvx : v ≠ x := fun hh => hxU (hh ▸ hvU)
  have hwx : w ≠ x := fun hh => hxU (hh ▸ hwU)
  exact (hve.resolve_left hvx).trans (hwf.resolve_left hwx).symm

/-- The first star blocks at most `b` copies of a second assigned star
in any one color, counting actual parallel multiplicities. -/
theorem coloredStarCopies_starWeight_le (z : V) (U : Finset V)
    (x : V) (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (hA : ∀ e ∈ A, x ∈ G.edge e) (hxU : x ∉ U)
    (b : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b) (j : Fin h) :
    starWeight G z U (coloredStarCopies A c j) ≤ b := by
  have hcard := coloredStarCopies_inter_support_card_le_one G x U A c hc hA hxU j
  exact (starWeight_le_inter_support_mul G z U _ b hparallel).trans
    (by simpa using Nat.mul_le_mul_right b hcard)

/-- Whole-star blocked-copy weight is subadditive under actual copy union. -/
theorem starWeight_union_le (z : V) (U : Finset V) (B C : Finset E) :
    starWeight G z U (B ∪ C) ≤ starWeight G z U B + starWeight G z U C := by
  have heq : starBlockedCopies G z U (B ∪ C) =
      starBlockedCopies G z U B ∪ starBlockedCopies G z U C := by
    ext e
    simp only [mem_starBlockedCopies,support_union,mem_union]
    tauto
  change (starBlockedCopies G z U (B ∪ C)).card ≤ _
  rw [heq]
  exact card_union_le _ _

/-- Adjoining the first injectively colored star increases every second-star
whole-color blocked-copy budget from `W` to at most `W+b`. -/
theorem starWeight_union_coloredStarCopies_le (z : V) (U : Finset V)
    (B : Fin h → Finset E) (x : V) (A : Finset E) (c : ↥A → Fin h)
    (hc : Function.Injective c) (hA : ∀ e ∈ A, x ∈ G.edge e) (hxU : x ∉ U)
    (b W : ℕ) (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b)
    (hbase : ∀ j, starWeight G z U (B j) ≤ W) (j : Fin h) :
    starWeight G z U (B j ∪ coloredStarCopies A c j) ≤ W+b :=
  (starWeight_union_le G z U _ _).trans (Nat.add_le_add (hbase j)
    (coloredStarCopies_starWeight_le G z U x A c hc hA hxU b hparallel j))

end Overfull.NativeStar
