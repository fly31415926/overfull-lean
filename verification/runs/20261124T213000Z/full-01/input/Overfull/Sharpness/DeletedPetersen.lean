import Overfull.Sharpness.WeightedPetersen
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Restoring a deleted vertex

This file uses separate edge copies and explicit endpoints, so parallel
edges remain distinct throughout the counting and coloring arguments.
-/

namespace Overfull.Sharpness.Deletion

open Finset

structure Graph (V E : Type) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V E : Type}

noncomputable def ends (G : Graph V E) (e : E) : Finset V := by
  classical
  exact {G.left e, G.right e}

@[simp] theorem ends_card (G : Graph V E) (e : E) : (ends G e).card = 2 := by
  classical
  simp [ends, G.loopless e]

noncomputable def edgesAt [Fintype E] (G : Graph V E) (v : V) : Finset E := by
  classical
  exact univ.filter (fun e => v ∈ ends G e)

noncomputable def degree [Fintype E] (G : Graph V E) (v : V) : Nat := (edgesAt G v).card

def OldEdge (G : Graph V E) (x : V) := {e : E // x ∉ ends G e}

noncomputable instance oldEdgeFintype [Fintype E] (G : Graph V E) (x : V) : Fintype (OldEdge G x) := by
  classical
  unfold OldEdge
  infer_instance

structure DeletedColoring (G : Graph V E) (x : V) (k : Nat) where
  color : OldEdge G x → Fin k
  proper : ∀ {e f : OldEdge G x} {v : V},
    v ∈ ends G e.val → v ∈ ends G f.val → color e = color f → e = f

variable [Fintype V] [Fintype E] {G : Graph V E} {x : V} {k : Nat}

noncomputable def remainingVertices (_G : Graph V E) (x : V) : Finset V := by
  classical
  exact univ.erase x

noncomputable def colorEdges (c : DeletedColoring G x k) (i : Fin k) : Finset (OldEdge G x) := by
  classical
  exact univ.filter (fun e => c.color e = i)

noncomputable def covered (c : DeletedColoring G x k) (i : Fin k) : Finset V := by
  classical
  exact (colorEdges c i).biUnion (fun e => ends G e.val)

omit [Fintype V] in
theorem colorEdges_disjoint (c : DeletedColoring G x k) (i : Fin k) :
    (colorEdges c i).toSet.PairwiseDisjoint (fun e => ends G e.val) := by
  classical
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  apply hne
  exact c.proper hve hvf
    ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)

omit [Fintype V] in
theorem covered_card (c : DeletedColoring G x k) (i : Fin k) :
    (covered c i).card = 2 * (colorEdges c i).card := by
  classical
  rw [covered, Finset.card_biUnion (colorEdges_disjoint c i)]
  simp [Nat.mul_comm]

theorem covered_subset (c : DeletedColoring G x k) (i : Fin k) :
    covered c i ⊆ remainingVertices G x := by
  classical
  intro v hv
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro hvx
  subst v
  exact e.property hve

theorem colorEdges_card_le (c : DeletedColoring G x k) (i : Fin k) :
    (colorEdges c i).card ≤ (remainingVertices G x).card / 2 := by
  have h := Finset.card_le_card (covered_subset c i)
  rw [covered_card] at h
  omega

omit [Fintype V] in
theorem edge_count_by_colors (c : DeletedColoring G x k) :
    Fintype.card (OldEdge G x) = ∑ i : Fin k, (colorEdges c i).card := by
  classical
  simpa [colorEdges] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (OldEdge G x))) (t := (Finset.univ : Finset (Fin k)))
      (fun _ _ => Finset.mem_univ _) (f := c.color))

theorem colorEdges_card_eq (c : DeletedColoring G x k)
    (hfull : Fintype.card (OldEdge G x) = k * ((remainingVertices G x).card / 2))
    (i : Fin k) : (colorEdges c i).card = (remainingVertices G x).card / 2 := by
  classical
  have hsum : ∑ j : Fin k, (colorEdges c j).card =
      ∑ _j : Fin k, (remainingVertices G x).card / 2 := by
    rw [← edge_count_by_colors c, hfull]
    simp
  exact (Finset.sum_eq_sum_iff_of_le
    (fun j _ => colorEdges_card_le c j)).mp hsum i (Finset.mem_univ i)

theorem missing_vertex_unique (c : DeletedColoring G x k)
    (hodd : (remainingVertices G x).card % 2 = 1)
    (hfull : Fintype.card (OldEdge G x) = k * ((remainingVertices G x).card / 2))
    (i : Fin k) :
    ∃! v, v ∈ remainingVertices G x ∧ v ∉ covered c i := by
  classical
  have hcard : ((remainingVertices G x) \ covered c i).card = 1 := by
    rw [Finset.card_sdiff_of_subset (covered_subset c i), covered_card,
      colorEdges_card_eq c hfull i]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, ?_, ?_⟩
  · have hmem : v ∈ (remainingVertices G x) \ covered c i := by rw [hv]; simp
    exact Finset.mem_sdiff.mp hmem
  · intro w hw
    have hmem : w ∈ (remainingVertices G x) \ covered c i := Finset.mem_sdiff.mpr hw
    rw [hv] at hmem
    simpa using hmem

noncomputable def oldAt (_c : DeletedColoring G x k) (v : V) : Finset (OldEdge G x) := by
  classical
  exact univ.filter (fun e => v ∈ ends G e.val)

noncomputable def missingColors (c : DeletedColoring G x k) (v : V) : Finset (Fin k) := by
  classical
  exact univ \ (oldAt c v).image c.color

omit [Fintype V] in
theorem mem_missingColors (c : DeletedColoring G x k) (v : V) (i : Fin k) :
    i ∈ missingColors c v ↔ v ∉ covered c i := by
  classical
  simp only [missingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image, oldAt, Finset.mem_filter, Finset.mem_univ, true_and,
    covered, Finset.mem_biUnion, colorEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    and_comm]

omit [Fintype V] in
theorem missingColors_card (c : DeletedColoring G x k) (v : V) :
    (missingColors c v).card + (oldAt c v).card = k := by
  classical
  have hinj : Set.InjOn c.color (oldAt c v) := by
    intro e he f hf hcol
    exact c.proper (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hcol
  have hcard := Finset.card_image_of_injOn hinj
  have hle : ((oldAt c v).image c.color).card ≤ k := by
    simpa using Finset.card_le_univ ((oldAt c v).image c.color)
  rw [missingColors, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simpa [hcard] using Nat.sub_add_cancel hle

noncomputable def newAt (G : Graph V E) (x v : V) : Finset E := by
  classical
  exact (edgesAt G v).filter (fun e => x ∈ ends G e)

omit [Fintype V] in
theorem oldAt_card (c : DeletedColoring G x k) (v : V) :
    (oldAt c v).card = (by classical exact ((edgesAt G v).filter (fun e => x ∉ ends G e)).card) := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, edgesAt, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_filter.mp he).2, e.property⟩
  · intro e he f hf heq
    exact Subtype.ext heq
  · intro e he
    refine ⟨⟨e, (Finset.mem_filter.mp he).2⟩, ?_, rfl⟩
    simp only [oldAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2

omit [Fintype V] in
theorem newAt_card_eq_missing (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (v : V) :
    (newAt G x v).card = (missingColors c v).card := by
  classical
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := edgesAt G v) (fun e => x ∈ ends G e)
  have hm := missingColors_card c v
  have hd := hregular v
  rw [← oldAt_card c v] at hp
  change (newAt G x v).card + (oldAt c v).card = degree G v at hp
  omega

noncomputable def newMissingEquiv (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (v : V) :
    ↥(newAt G x v) ≃ ↥(missingColors c v) := by
  classical
  apply Fintype.equivOfCardEq
  simpa using newAt_card_eq_missing c hregular v

def NewEdge (G : Graph V E) (x : V) := {e : E // x ∈ ends G e}

noncomputable def otherEnd (e : NewEdge G x) : V := by
  classical
  exact if G.left e.val = x then G.right e.val else G.left e.val

omit [Fintype V] [Fintype E] in
theorem newEdge_ends (e : NewEdge G x) :
    ends G e.val = (by classical exact {x, otherEnd e}) := by
  classical
  have hx := e.property
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hx
  by_cases hleft : G.left e.val = x
  · simp [ends, otherEnd, hleft]
  · have hright : G.right e.val = x := by
      rcases hx with hx | hx
      · exact False.elim (hleft hx.symm)
      · exact hx.symm
    simp [ends, otherEnd, hleft, hright, Finset.pair_comm]

omit [Fintype V] [Fintype E] in
theorem otherEnd_ne (e : NewEdge G x) : otherEnd e ≠ x := by
  classical
  intro h
  have hc := ends_card G e.val
  rw [newEdge_ends, h] at hc
  simp at hc

omit [Fintype V] [Fintype E] in
theorem otherEnd_incident (e : NewEdge G x) : otherEnd e ∈ ends G e.val := by
  classical
  rw [newEdge_ends]
  simp

omit [Fintype V] in
theorem newEdge_mem_newAt (e : NewEdge G x) : e.val ∈ newAt G x (otherEnd e) := by
  classical
  simp only [newAt, edgesAt, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨otherEnd_incident e, e.property⟩

noncomputable def newColor (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (e : NewEdge G x) : Fin k :=
  (newMissingEquiv c hregular (otherEnd e) ⟨e.val, newEdge_mem_newAt e⟩).val

omit [Fintype V] in
theorem newColor_missing (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (e : NewEdge G x) :
    newColor c hregular e ∈ missingColors c (otherEnd e) :=
  (newMissingEquiv c hregular (otherEnd e) ⟨e.val, newEdge_mem_newAt e⟩).property

omit [Fintype V] in
theorem newColor_missing_at (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (e : NewEdge G x) (v : V)
    (hv : v ∈ ends G e.val) (hvx : v ≠ x) :
    newColor c hregular e ∈ missingColors c v := by
  classical
  rw [newEdge_ends] at hv
  have heq : v = otherEnd e :=
    Finset.mem_singleton.mp ((Finset.mem_insert.mp hv).resolve_left hvx)
  rw [heq]
  exact newColor_missing c hregular e

omit [Fintype V] in
theorem newMissingEquiv_val_congr (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) {v w : V} (hvw : v = w) (e : E)
    (hv : e ∈ newAt G x v) (hw : e ∈ newAt G x w) :
    (newMissingEquiv c hregular v ⟨e, hv⟩).val =
      (newMissingEquiv c hregular w ⟨e, hw⟩).val := by
  cases hvw
  rfl

theorem newColor_injective (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k)
    (hodd : (remainingVertices G x).card % 2 = 1)
    (hfull : Fintype.card (OldEdge G x) = k * ((remainingVertices G x).card / 2)) :
    Function.Injective (newColor c hregular) := by
  classical
  intro e f hef
  obtain ⟨v, hv, hu⟩ := missing_vertex_unique c hodd hfull (newColor c hregular e)
  have he : otherEnd e = v := hu _ ⟨by
      simp [remainingVertices, otherEnd_ne e],
    (mem_missingColors c _ _).mp (newColor_missing c hregular e)⟩
  have hf : otherEnd f = v := hu _ ⟨by
      simp [remainingVertices, otherEnd_ne f], by
      rw [hef]
      exact (mem_missingColors c _ _).mp (newColor_missing c hregular f)⟩
  have hother : otherEnd e = otherEnd f := he.trans hf.symm
  have hemem : e.val ∈ newAt G x (otherEnd f) := hother ▸ newEdge_mem_newAt e
  have hecolor : newColor c hregular e =
      (newMissingEquiv c hregular (otherEnd f) ⟨e.val, hemem⟩).val :=
    newMissingEquiv_val_congr c hregular hother e.val (newEdge_mem_newAt e) hemem
  have hvalues :
      (newMissingEquiv c hregular (otherEnd f) ⟨e.val, hemem⟩).val =
      (newMissingEquiv c hregular (otherEnd f) ⟨f.val, newEdge_mem_newAt f⟩).val :=
    hecolor.symm.trans hef
  have heq := (newMissingEquiv c hregular (otherEnd f)).injective (Subtype.ext hvalues)
  exact Subtype.ext (congrArg (fun z : ↥(newAt G x (otherEnd f)) => z.val) heq)

omit [Fintype V] in
theorem missing_ne_old (c : DeletedColoring G x k) (v : V) (i : Fin k)
    (hi : i ∈ missingColors c v) (e : OldEdge G x) (he : v ∈ ends G e.val) :
    i ≠ c.color e := by
  classical
  intro hic
  have hmiss := (mem_missingColors c v i).mp hi
  apply hmiss
  apply Finset.mem_biUnion.mpr
  refine ⟨e, ?_, he⟩
  simp [colorEdges, hic]

noncomputable def extendedColor (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k) (e : E) : Fin k := by
  classical
  exact if h : x ∈ ends G e then newColor c hregular ⟨e, h⟩ else c.color ⟨e, h⟩

theorem extendedColor_proper (c : DeletedColoring G x k)
    (hregular : ∀ v, degree G v = k)
    (hodd : (remainingVertices G x).card % 2 = 1)
    (hfull : Fintype.card (OldEdge G x) = k * ((remainingVertices G x).card / 2))
    {e f : E} {v : V} (he : v ∈ ends G e) (hf : v ∈ ends G f)
    (hcolor : extendedColor c hregular e = extendedColor c hregular f) : e = f := by
  classical
  by_cases hex : x ∈ ends G e <;> by_cases hfx : x ∈ ends G f
  · have hc : newColor c hregular ⟨e, hex⟩ = newColor c hregular ⟨f, hfx⟩ := by
      simpa [extendedColor, hex, hfx] using hcolor
    exact congrArg Subtype.val (newColor_injective c hregular hodd hfull hc)
  · have hvx : v ≠ x := fun hvx => hfx (hvx ▸ hf)
    have hm := newColor_missing_at c hregular ⟨e, hex⟩ v he hvx
    apply False.elim
    apply missing_ne_old c v _ hm ⟨f, hfx⟩ hf
    simpa [extendedColor, hex, hfx] using hcolor
  · have hvx : v ≠ x := fun hvx => hex (hvx ▸ he)
    have hm := newColor_missing_at c hregular ⟨f, hfx⟩ v hf hvx
    apply False.elim
    apply missing_ne_old c v _ hm ⟨e, hex⟩ he
    simpa [extendedColor, hex, hfx] using hcolor.symm
  · have hc : c.color ⟨e, hex⟩ = c.color ⟨f, hfx⟩ := by
      simpa [extendedColor, hex, hfx] using hcolor
    exact congrArg Subtype.val (c.proper he hf hc)

end Deletion

namespace DeletedPetersen

open Deletion

def edgeEquiv (s : Nat) : WeightedEdge s ≃ (Fin 5 ⊕ (Fin 5 ⊕ (Fin 5 × Fin s))) where
  toFun
    | .outer i => .inl i
    | .inner i => .inr (.inl i)
    | .spoke i j => .inr (.inr (i, j))
  invFun
    | .inl i => .outer i
    | .inr (.inl i) => .inner i
    | .inr (.inr (i, j)) => .spoke i j
  left_inv := by intro e; cases e <;> rfl
  right_inv := by
    intro z
    rcases z with i | (i | ⟨i, j⟩) <;> rfl

instance weightedEdgeFintype (s : Nat) : Fintype (WeightedEdge s) :=
  Fintype.ofEquiv _ (edgeEquiv s).symm

def graph (s : Nat) : Deletion.Graph WeightedVertex (WeightedEdge s) where
  left := firstEnd
  right := secondEnd
  loopless := loopless

theorem mem_ends_iff (s : Nat) (v : WeightedVertex) (e : WeightedEdge s) :
    v ∈ ends (graph s) e ↔ Incident v e := by
  classical
  simp [ends, graph, Incident, eq_comm]

theorem regular (s : Nat) (v : WeightedVertex) : degree (graph s) v = s + 2 := by
  classical
  cases v with
  | inl i =>
      have hs : edgesAt (graph s) (.inl i) = Finset.univ.image (outerEdges i) := by
        ext e
        simp only [edgesAt, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, mem_ends_iff]
        constructor
        · intro h
          obtain ⟨j, hj⟩ := outerEdges_cover i e h
          exact ⟨j, hj⟩
        · rintro ⟨j, rfl⟩
          exact outerEdges_incident i j
      rw [degree, hs, Finset.card_image_of_injective _ (outerEdges_injective i)]
      simp
  | inr i =>
      have hs : edgesAt (graph s) (.inr i) = Finset.univ.image (innerEdges i) := by
        ext e
        simp only [edgesAt, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, mem_ends_iff]
        constructor
        · intro h
          obtain ⟨j, hj⟩ := innerEdges_cover i e h
          exact ⟨j, hj⟩
        · rintro ⟨j, rfl⟩
          exact innerEdges_incident i j
      rw [degree, hs, Finset.card_image_of_injective _ (innerEdges_injective i)]
      simp

theorem edge_count (s : Nat) : Fintype.card (WeightedEdge s) = 5 * (s + 2) := by
  rw [Fintype.card_congr (edgeEquiv s)]
  simp [Fintype.card_sum, Fintype.card_prod]
  omega

theorem remaining_vertex_count (s : Nat) :
    (remainingVertices (graph s) (.inl 0)).card = 9 := by
  simp [remainingVertices, WeightedVertex, Fintype.card_sum]

theorem old_edge_count (s : Nat) :
    Fintype.card (OldEdge (graph s) (.inl 0)) = 4 * (s + 2) := by
  classical
  have hold : Fintype.card (OldEdge (graph s) (.inl 0)) =
      (Finset.univ.filter (fun e : WeightedEdge s =>
        (Sum.inl 0 : WeightedVertex) ∉ ends (graph s) e)).card := by
    rw [← Finset.card_univ (α := OldEdge (graph s) (.inl 0))]
    apply Finset.card_bij (fun e _ => e.val)
    · intro e _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property⟩
    · intro e _ f _ heq
      exact Subtype.ext heq
    · intro e he
      exact ⟨⟨e, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, rfl⟩
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (WeightedEdge s)))
    (fun e => (Sum.inl 0 : WeightedVertex) ∈ ends (graph s) e)
  rw [← hold] at hp
  have hnew : (Finset.univ.filter (fun e : WeightedEdge s =>
      (Sum.inl 0 : WeightedVertex) ∈ ends (graph s) e)).card = degree (graph s) (.inl 0) := by
    unfold degree
    congr 1
    ext e
    simp [edgesAt]
  rw [hnew, Finset.card_univ] at hp
  rw [regular, edge_count] at hp
  omega

/-- Removing outer vertex zero does not remove the weighted Petersen coloring
obstruction. All regularity, order, and tight edge-count conditions of the
restoration argument are established for this actual multigraph. -/
theorem not_edge_colorable (s : Nat) :
    ¬ Nonempty (DeletedColoring (graph s) (.inl 0) (s + 2)) := by
  rintro ⟨c⟩
  have hodd : (remainingVertices (graph s) (.inl 0)).card % 2 = 1 := by
    rw [remaining_vertex_count]
  have hfull : Fintype.card (OldEdge (graph s) (.inl 0)) =
      (s + 2) * ((remainingVertices (graph s) (.inl 0)).card / 2) := by
    rw [old_edge_count, remaining_vertex_count]
    omega
  apply weighted_petersen_not_edge_colorable s (extendedColor c (regular s))
  intro v e f he hf hcolor
  exact extendedColor_proper c (regular s) hodd hfull
    ((mem_ends_iff s v e).mpr he) ((mem_ends_iff s v f).mpr hf) hcolor

theorem not_Delta_edge_colorable (Δ : Nat) (hΔ : 3 ≤ Δ) :
    ¬ Nonempty (DeletedColoring (graph (Δ - 2)) (.inl 0) Δ) := by
  rintro ⟨c⟩
  have hk : Δ = (Δ - 2) + 2 := by omega
  apply not_edge_colorable (Δ - 2)
  refine ⟨⟨fun e => Fin.cast hk (c.color e), ?_⟩⟩
  intro e f v he hf hef
  apply c.proper he hf
  apply Fin.ext
  exact congrArg (fun z : Fin ((Δ - 2) + 2) => z.val) hef

end DeletedPetersen

end Overfull.Sharpness
