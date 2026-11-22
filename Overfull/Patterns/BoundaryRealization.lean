import Overfull.Patterns.Boundary
import Overfull.Patterns.Forest
import Overfull.Patterns.Realization

/-!
# Realization of the accepted boundary patterns

The demand slots are the actual quotient edges of each selected pattern.
A slot is realized by a fresh host edge with exactly those quotient
endpoints.  Thus the output is a family of actual edge-disjoint matchings.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open PatternRealization
open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Exceptional labels occurring in one quotient edge. -/
def exceptionalLabels (b : Finset (E ⊕ Fin 4)) : Finset E :=
  univ.filter (fun z => Sum.inl z ∈ b)

/-- A quotient edge uses one core endpoint if it meets the exceptional
set, and at most two otherwise. Accepted patterns have no internal pair. -/
def boundaryArity (b : Finset (E ⊕ Fin 4)) : ℕ :=
  if (exceptionalLabels b).Nonempty then 1 else 2

@[simp] theorem exceptionalLabels_exceptional (z : E) (i : Fin 4) :
    exceptionalLabels {Sum.inl z, Sum.inr i} = {z} := by
  ext w
  simp [exceptionalLabels]

@[simp] theorem boundaryArity_exceptional (z : E) (i : Fin 4) :
    boundaryArity (E := E) {Sum.inl z, Sum.inr i} = 1 := by
  simp [boundaryArity]

@[simp] theorem exceptionalLabels_joining (p : LabelPair) :
    exceptionalLabels (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) = ∅ := by
  ext z
  simp [exceptionalLabels]

@[simp] theorem boundaryArity_joining (p : LabelPair) :
    boundaryArity (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) = 2 := by
  simp [boundaryArity]

theorem boundaryEdges_of_no_internal (P : Pattern E) (hP : P.internalPairs = ∅) :
    P.boundaryEdges =
      univ.image (fun z : E => {Sum.inl z,Sum.inr (P.assignment z)}) ∪
      P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) := by
  simp [Pattern.boundaryEdges,Pattern.Paired,hP]

theorem boundaryEdge_card (P : Pattern E) (hP : P.internalPairs = ∅)
    (b : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) : b.card = 2 := by
  rw [boundaryEdges_of_no_internal P hP] at hb
  rcases mem_union.mp hb with hb | hb
  · obtain ⟨z,_hz,rfl⟩ := mem_image.mp hb
    simp
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
    rw [card_image_of_injective _ Sum.inr_injective,p.property]

/-- Each exceptional label determines its unique edge in an accepted pattern. -/
theorem boundaryEdge_of_exceptional (P : Pattern E) (hP : P.internalPairs = ∅)
    (b : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) (z : E)
    (hz : Sum.inl z ∈ b) : b = {Sum.inl z,Sum.inr (P.assignment z)} := by
  rw [boundaryEdges_of_no_internal P hP] at hb
  rcases mem_union.mp hb with hb | hb
  · obtain ⟨w,_hw,rfl⟩ := mem_image.mp hb
    have hzw : z = w := by simpa using hz
    subst w
    rfl
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
    simp at hz

/-- Every edge of an accepted pattern has a core label. -/
theorem boundaryEdge_core_label (P : Pattern E) (hP : P.internalPairs = ∅)
    (b : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) :
    ∃ i : Fin 4, Sum.inr i ∈ b := by
  rw [boundaryEdges_of_no_internal P hP] at hb
  rcases mem_union.mp hb with hb | hb
  · obtain ⟨z,_hz,rfl⟩ := mem_image.mp hb
    exact ⟨P.assignment z,by simp⟩
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
    have hpnon : p.val.Nonempty := card_pos.mp (by rw [p.property]; omega)
    obtain ⟨i,hi⟩ := hpnon
    exact ⟨i,mem_image.mpr ⟨i,hi,rfl⟩⟩

/-- Distinct quotient edges of an accepted pattern share no exceptional label. -/
theorem exceptionalLabels_disjoint (P : Pattern E) (hP : P.internalPairs = ∅)
    (b c : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) (hc : c ∈ P.boundaryEdges)
    (hne : b ≠ c) : Disjoint (exceptionalLabels b) (exceptionalLabels c) := by
  apply disjoint_left.mpr
  intro z hz hz'
  exact hne ((boundaryEdge_of_exceptional P hP b hb z (mem_filter.mp hz).2).trans
    (boundaryEdge_of_exceptional P hP c hc z (mem_filter.mp hz').2).symm)

/-- Every exceptional label occurs in its assigned boundary edge. -/
theorem assignment_edge_mem (P : Pattern E) (hP : P.internalPairs = ∅) (z : E) :
    {Sum.inl z,Sum.inr (P.assignment z)} ∈ P.boundaryEdges := by
  rw [boundaryEdges_of_no_internal P hP]
  exact mem_union_left _ (mem_image.mpr ⟨z,mem_univ _,rfl⟩)

/-- An accepted pattern has at most one core endpoint per exceptional
vertex and at most six from its joining forest. -/
theorem boundaryArity_sum_le (P : Pattern E) (hP : P.internalPairs = ∅)
    (hforest : LeafForest P.forest) :
    ∑ b ∈ P.boundaryEdges, boundaryArity b ≤ Fintype.card E + 6 := by
  rw [boundaryEdges_of_no_internal P hP]
  let A : Finset (Finset (E ⊕ Fin 4)) :=
    univ.image (fun z : E => {Sum.inl z,Sum.inr (P.assignment z)})
  let B : Finset (Finset (E ⊕ Fin 4)) :=
    P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4))
  have hleft : (∑ b ∈ A, boundaryArity b) ≤ Fintype.card E := by
    calc
      _ = ∑ _b ∈ A, 1 := by
        apply Finset.sum_congr rfl
        intro b hb
        obtain ⟨z,_hz,rfl⟩ := mem_image.mp hb
        exact boundaryArity_exceptional z (P.assignment z)
      _ = A.card := by simp
      _ ≤ Fintype.card E := (card_image_le).trans_eq (card_univ)
  have hright : (∑ b ∈ B, boundaryArity b) ≤ 6 := by
    calc
      _ = ∑ _b ∈ B, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
        exact boundaryArity_joining p
      _ = B.card * 2 := by simp
      _ ≤ P.forest.card * 2 := Nat.mul_le_mul_right 2 card_image_le
      _ ≤ 6 := by have h := label_forest_card P.forest hforest; omega
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro b hb hb'
    obtain ⟨z,_hz,rfl⟩ := mem_image.mp hb
    obtain ⟨p,_hp,heq⟩ := mem_image.mp hb'
    have hh := congrArg (exceptionalLabels (E := E)) heq
    have hc := congrArg Finset.card hh
    simp at hc
  change (∑ b ∈ A ∪ B, boundaryArity b) ≤ _
  rw [Finset.sum_union hdis]
  exact Nat.add_le_add hleft hright


section Actual

variable {V I J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)

/-- All actual host edges with the requested quotient endpoints. -/
def boundaryPool (b : Finset (Z ⊕ Fin 4)) : Finset G.edgeSet :=
  univ.filter (fun e => labelledEdge G U Z code e = b)

/-- The actual exceptional endpoints prescribed by a quotient edge. -/
def boundarySpecial (b : Finset (Z ⊕ Fin 4)) : Finset V :=
  (exceptionalLabels b).image Subtype.val

@[simp] theorem mem_boundaryPool (b : Finset (Z ⊕ Fin 4)) (e : G.edgeSet) :
    e ∈ boundaryPool G U Z code b ↔ labelledEdge G U Z code e = b := by
  simp [boundaryPool]

theorem boundaryPool_disjoint (b c : Finset (Z ⊕ Fin 4)) (h : b ≠ c) :
    Disjoint (boundaryPool G U Z code b) (boundaryPool G U Z code c) := by
  apply disjoint_left.mpr
  intro e he he'
  exact h ((mem_boundaryPool G U Z code b e).mp he |>.symm.trans
    ((mem_boundaryPool G U Z code c e).mp he'))

theorem boundaryPool_special (b : Finset (Z ⊕ Fin 4)) (e : G.edgeSet)
    (he : e ∈ boundaryPool G U Z code b) :
    edgeEnds G e ∩ Z = boundarySpecial Z b := by
  have heq := (mem_boundaryPool G U Z code b e).mp he
  ext v
  constructor
  · intro hv
    obtain ⟨hev,hvZ⟩ := mem_inter.mp hv
    refine mem_image.mpr ⟨⟨v,hvZ⟩,?_,rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [← heq]
    exact (inl_mem_labelledEdge G U Z code e ⟨v,hvZ⟩).mpr ((mem_edgeEnds G e v).mp hev)
  · intro hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    refine mem_inter.mpr ⟨?_,z.property⟩
    apply (mem_edgeEnds G e z.val).mpr
    apply (inl_mem_labelledEdge G U Z code e z).mp
    rw [heq]
    exact (mem_filter.mp hz).2

theorem boundaryPool_arity (b : Finset (Z ⊕ Fin 4)) (e : G.edgeSet)
    (he : e ∈ boundaryPool G U Z code b) :
    (coreEnds G Z e).card ≤ boundaryArity b := by
  have hh := coreEnds_card_add G Z e
  unfold boundaryArity
  split_ifs with hz
  · have hn : (boundarySpecial Z b).Nonempty := by
      obtain ⟨z,hz⟩ := hz
      exact ⟨z.val,mem_image.mpr ⟨z,hz,rfl⟩⟩
    rw [← boundaryPool_special G U Z code b e he] at hn
    have hc := Finset.card_pos.mpr hn
    omega
  · omega

/-- One demand slot for every boundary edge of every copy. -/
abbrev BoundarySlot (P : J → Pattern Z) := (j : J) × {b // b ∈ (P j).boundaryEdges}

def slotKind (P : J → Pattern Z) (s : BoundarySlot Z P) : Finset (Z ⊕ Fin 4) := s.2.val

def slotRound (P : J → Pattern Z) (s : BoundarySlot Z P) : J := s.1

omit [Fintype V] in
/-- The sum of slot arities is the actual arity sum of the specified pattern. -/
theorem slot_arity_sum (P : J → Pattern Z) (j : J) :
    (∑ s ∈ univ.filter (fun s : BoundarySlot Z P => slotRound Z P s = j),
      boundaryArity (slotKind Z P s)) =
      ∑ b ∈ (P j).boundaryEdges, boundaryArity b := by
  rw [Finset.sum_filter,Fintype.sum_sigma]
  simp only [slotKind,slotRound]
  rw [Finset.sum_eq_single j]
  · simpa using (Finset.sum_coe_sort (P j).boundaryEdges (boundaryArity (E := Z)))
  · intro i _ hij
    simp [hij]
  · simp

omit [Fintype V] in
/-- Exact total demand for one quotient edge across all pattern copies. -/
theorem demandCount_slots (P : J → Pattern Z) (b : Finset (Z ⊕ Fin 4)) :
    demandCount (slotKind Z P) b = ∑ j : J, if b ∈ (P j).boundaryEdges then 1 else 0 := by
  unfold demandCount
  rw [Finset.sum_boole]
  apply Finset.card_bij (fun s _ => s.1)
  · intro s hs
    have heq : slotKind Z P s = b := (mem_filter.mp hs).2
    exact mem_filter.mpr ⟨mem_univ _,heq ▸ s.2.property⟩
  · intro s hs t ht hst
    rcases s with ⟨j,c⟩
    rcases t with ⟨j',d⟩
    change j = j' at hst
    subst j'
    have hc : c.val = b := (mem_filter.mp hs).2
    have hd : d.val = b := (mem_filter.mp ht).2
    exact congrArg (fun x => (⟨j,x⟩ : BoundarySlot Z P)) (Subtype.ext (hc.trans hd.symm))
  · intro j hj
    have hb : b ∈ (P j).boundaryEdges := (mem_filter.mp hj).2
    exact ⟨⟨j,⟨b,hb⟩⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩

/-- Each round's chosen edges have exactly the requested quotient image. -/
theorem realized_boundary_image (P : J → Pattern Z)
    (pick : BoundarySlot Z P → G.edgeSet)
    (hpick : ∀ s, pick s ∈ boundaryPool G U Z code (slotKind Z P s)) (j : J) :
    (matchingEdges (roundMatching G pick (slotRound Z P) j)).image
      (labelledEdge G U Z code) = (P j).boundaryEdges := by
  rw [roundMatching_edges]
  ext b
  constructor
  · intro hb
    obtain ⟨e,he,rfl⟩ := mem_image.mp hb
    obtain ⟨s,hs,rfl⟩ := mem_image.mp he
    have hr : s.1 = j := (mem_filter.mp hs).2
    rw [(mem_boundaryPool G U Z code _ _).mp (hpick s)]
    exact hr ▸ s.2.property
  · intro hb
    let s : BoundarySlot Z P := ⟨j,⟨b,hb⟩⟩
    refine mem_image.mpr ⟨pick s,?_,?_⟩
    · exact mem_image.mpr ⟨s,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩
    · exact (mem_boundaryPool G U Z code _ _).mp (hpick s)

/-- Every quotient edge occurs once in the chosen round. -/
theorem realized_boundary_injective (P : J → Pattern Z)
    (pick : BoundarySlot Z P → G.edgeSet)
    (hpick : ∀ s, pick s ∈ boundaryPool G U Z code (slotKind Z P s)) (j : J) :
    Set.InjOn (labelledEdge G U Z code)
      (matchingEdges (roundMatching G pick (slotRound Z P) j)) := by
  rw [roundMatching_edges]
  intro e he f hf heq
  obtain ⟨s,hs,rfl⟩ := mem_image.mp he
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hf
  have hs' : s.1 = j := (mem_filter.mp hs).2
  have ht' : t.1 = j := (mem_filter.mp ht).2
  have hk : slotKind Z P s = slotKind Z P t := by
    rw [← (mem_boundaryPool G U Z code _ _).mp (hpick s),
      ← (mem_boundaryPool G U Z code _ _).mp (hpick t)]
    exact heq
  have hst : s = t := by
    rcases s with ⟨s,b⟩
    rcases t with ⟨t,c⟩
    dsimp only at hs' ht'
    subst s
    subst t
    exact congrArg (fun x => (⟨j,x⟩ : BoundarySlot Z P)) (Subtype.ext hk)
  exact congrArg pick hst

/-- A pool requested by an accepted pattern contains no edge internal to a core. -/
theorem boundaryPool_no_internal (P : Pattern Z) (hP : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges)
    (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b)
    (i : I) (u v : V) (hu : u ∈ U i) (hv : v ∈ U i) : e.val ≠ s(u,v) := by
  intro heq
  have huZ : u ∉ Z := fun hh => disjoint_left.mp (hUZ i) hu hh
  have hvZ : v ∉ Z := fun hh => disjoint_left.mp (hUZ i) hv hh
  have hlabel : labelledEdge G U Z code e = {Sum.inr (code i)} := by
    rw [labelledEdge,heq,Sym2.toFinset_mk_eq]
    simp [boundaryLabel_outside U Z code u huZ,boundaryLabel_outside U Z code v hvZ,
      coreLabel_of_mem U code hdisjoint hu,coreLabel_of_mem U code hdisjoint hv]
  have hc := boundaryEdge_card P hP b hb
  rw [← (mem_boundaryPool G U Z code b e).mp he,hlabel] at hc
  simp at hc

/-- Actual core incidence in a demanded pool is bounded by the original
core error. This premise is derived from graph degrees, including when
the error is a nonintegral real number. -/
theorem boundaryPool_incidence_le (P : Pattern Z) (hP : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ) ≤ (H i).degree v + a)
    (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) (v : V) :
    ((boundaryPool G U Z code b).filter (fun e => v ∈ coreEnds G Z e)).card ≤ ⌊a⌋₊ := by
  classical
  by_cases hvZ : v ∈ Z
  · simp [mem_coreEnds,hvZ]
  · obtain ⟨i,hvi⟩ := (hcover v).resolve_left hvZ
    let A := boundaryPool G U Z code b
    let N := selectedMatching G A
    have hle : N.spanningCoe ≤ G \ Replacement.lift (U i) (H i) := by
      rintro x y ⟨hxy,he⟩
      refine ⟨hxy,?_⟩
      intro hi
      obtain ⟨hx,hy⟩ := Replacement.lift_adj_mem (U i) (H i) hi
      exact boundaryPool_no_internal G U Z code P hP hdisjoint hUZ b hb
        ⟨s(x,y),hxy⟩ he i x y hx hy rfl
    have hc : ((boundaryPool G U Z code b).filter
        (fun e => v ∈ coreEnds G Z e)).card = N.spanningCoe.degree v := by
      rw [← incidentCount_matchingEdges_degree G N v]
      change _ = incidentCount (matchingEdges (selectedMatching G A)) v
      rw [selectedMatching_edges]
      unfold incidentCount
      congr 1
      ext e
      simp [mem_coreEnds,hvZ,incident_iff,A]
    have hledeg := SimpleGraph.degree_le_of_le hle (v := v)
    have hid := BipartitePackingAccounting.degree_sdiff_add_of_le G
      (Replacement.lift (U i) (H i))
      (Replacement.lift_le (U i) (H i) G (hH i)) v
    have hid' : (G \ Replacement.lift (U i) (H i)).degree v +
        (H i).degree ⟨v,hvi⟩ = k := by
      have hid0 : (G \ Replacement.lift (U i) (H i)).degree v +
          (Replacement.lift (U i) (H i)).degree v = G.degree v := by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hid
      rw [hregular] at hid0
      have hlift := Replacement.lift_degree (U i) (H i) ⟨v,hvi⟩
      rw [hlift] at hid0
      exact hid0
    have hnum : ((boundaryPool G U Z code b).filter
        (fun e => v ∈ coreEnds G Z e)).card + (H i).degree ⟨v,hvi⟩ ≤ k := by
      rw [hc]
      omega
    apply Nat.le_floor
    have hnum' : (((boundaryPool G U Z code b).filter
        (fun e => v ∈ coreEnds G Z e)).card : ℝ) + (H i).degree ⟨v,hvi⟩ ≤ k := by
      exact_mod_cast hnum
    have hdeg := hdegree i ⟨v,hvi⟩
    linarith

/-- A demanded boundary pool has an actual core endpoint. -/
theorem boundaryPool_has_core (P : Pattern Z) (hP : P.internalPairs = ∅)
    (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges)
    (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b) :
    (coreEnds G Z e).Nonempty := by
  obtain ⟨i,hi⟩ := boundaryEdge_core_label P hP b hb
  rw [← (mem_boundaryPool G U Z code b e).mp he,labelledEdge] at hi
  obtain ⟨v,hv,hlabel⟩ := mem_image.mp hi
  have hvZ : v ∉ Z := by
    intro hz
    simp [boundaryLabel,hz] at hlabel
  exact ⟨v,(mem_coreEnds G Z e v).mpr ⟨Sym2.mem_toFinset.mp hv,hvZ⟩⟩

/-- Positive demand forces the real core error to be at least one. -/
theorem one_le_error_of_boundary (P : Pattern Z) (hP : P.internalPairs = ∅)
    (M : G.Subgraph) (hM : Encodes G U Z code M P)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ) ≤ (H i).degree v + a)
    (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) : 1 ≤ a := by
  obtain ⟨e,_heM,heq⟩ := hM.boundaryEdge_realized b hb
  have he : e ∈ boundaryPool G U Z code b := (mem_boundaryPool G U Z code b e).mpr heq
  obtain ⟨v,hv⟩ := boundaryPool_has_core G U Z code P hP b hb e he
  have hn : 0 < ((boundaryPool G U Z code b).filter
      (fun f => v ∈ coreEnds G Z f)).card :=
    card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hv⟩⟩
  have hle := boundaryPool_incidence_le G U Z code P hP hdisjoint hUZ hcover H hH
    k a hregular hdegree b hb v
  exact Nat.floor_pos.mp (hn.trans_le hle)

/-- Realize every selected pattern copy by an actual matching, preserving
its exact quotient edges. Numerical pool slack supplies all edge choices. -/
theorem exists_pattern_realization (P : J → Pattern Z)
    (hP : ∀ j, (P j).internalPairs = ∅)
    (hforest : ∀ j, LeafForest (P j).forest)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z) (a : ℕ)
    (hinc : ∀ s : BoundarySlot Z P, ∀ v,
      ((boundaryPool G U Z code (slotKind Z P s)).filter
        (fun e => v ∈ coreEnds G Z e)).card ≤ a)
    (hcap : ∀ s : BoundarySlot Z P,
      demandCount (slotKind Z P) (slotKind Z P s) + (Z.card+6)*a <
        (boundaryPool G U Z code (slotKind Z P s)).card) :
    ∃ F : J → G.Subgraph,
      (∀ j, (F j).IsMatching) ∧
      (∀ j, (Z : Set V) ⊆ (F j).verts) ∧
      (∀ j j', j ≠ j' → Disjoint (F j).spanningCoe (F j').spanningCoe) ∧
      (∀ j i u v, u ∈ U i → v ∈ U i → ¬ (F j).Adj u v) ∧
      (∀ j, (matchingEdges (F j)).image (labelledEdge G U Z code) = (P j).boundaryEdges) ∧
      (∀ j, Set.InjOn (labelledEdge G U Z code) (matchingEdges (F j))) ∧
      (∀ j, ((F j).verts.toFinset \ Z).card ≤ Z.card+6) := by
  have hround (j : J) : (∑ s ∈ univ.filter (fun s : BoundarySlot Z P =>
      slotRound Z P s = j), boundaryArity (slotKind Z P s)) ≤ Z.card+6 := by
    rw [slot_arity_sum]
    simpa using boundaryArity_sum_le (P j) (hP j) (hforest j)
  have hspecialDisj (s t : BoundarySlot Z P) (hst : s ≠ t)
      (hr : slotRound Z P s = slotRound Z P t) :
      Disjoint (boundarySpecial Z (slotKind Z P s))
        (boundarySpecial Z (slotKind Z P t)) := by
    rcases s with ⟨j,b⟩
    rcases t with ⟨j',c⟩
    change j = j' at hr
    subst j'
    have hbc : b.val ≠ c.val := by
      intro hh
      exact hst (congrArg (fun x => (⟨j,x⟩ : BoundarySlot Z P)) (Subtype.ext hh))
    have hd := exceptionalLabels_disjoint (P j) (hP j) b.val c.val b.property c.property hbc
    apply disjoint_left.mpr
    intro v hv hv'
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    obtain ⟨w,hw,hzw⟩ := mem_image.mp hv'
    have hzw' : w = z := Subtype.ext hzw
    exact disjoint_left.mp hd hz (hzw' ▸ hw)
  have hcover (j : J) (v : V) (hv : v ∈ Z) :
      ∃ s : BoundarySlot Z P, slotRound Z P s = j ∧
        v ∈ boundarySpecial Z (slotKind Z P s) := by
    let z : Z := ⟨v,hv⟩
    let b : Finset (Z ⊕ Fin 4) := {Sum.inl z,Sum.inr ((P j).assignment z)}
    have hb : b ∈ (P j).boundaryEdges := assignment_edge_mem (P j) (hP j) z
    refine ⟨⟨j,⟨b,hb⟩⟩,rfl,?_⟩
    exact mem_image.mpr ⟨z,by simp [slotKind,b],rfl⟩
  obtain ⟨pick,hpick,hinj,hmatch,hdisj,hcov,_hcount⟩ :=
    exists_boundary_matchings G Z (boundaryPool G U Z code) (boundarySpecial Z)
      (slotKind Z P) (slotRound Z P) boundaryArity a (Z.card+6)
      (boundaryPool_disjoint G U Z code) (boundaryPool_arity G U Z code) hinc hround hcap
      (boundaryPool_special G U Z code) hspecialDisj hcover
  refine ⟨roundMatching G pick (slotRound Z P),hmatch,hcov,hdisj,?_,?_,?_,?_⟩
  · intro j
    exact roundMatching_no_internal G U (boundaryPool G U Z code) (slotKind Z P)
      (slotRound Z P) pick hpick
      (fun s e he i u v hu hv => boundaryPool_no_internal G U Z code
        (P s.1) (hP s.1) hdisjoint hUZ s.2.val s.2.property e he i u v hu hv) j
  · exact realized_boundary_image G U Z code P pick hpick
  · exact realized_boundary_injective G U Z code P pick hpick
  · intro j
    exact (roundMatching_core_card_le G Z (boundaryPool G U Z code) (slotKind Z P)
      (slotRound Z P) boundaryArity (boundaryPool_arity G U Z code) pick hpick j).trans (hround j)

/-- All graph and parity properties of one actually realized boundary. -/
structure RealizesPattern (P : Pattern Z) (F : G.Subgraph) : Prop where
  matching : F.IsMatching
  covered : (Z : Set V) ⊆ F.verts
  no_core_internal : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v
  boundary_image : (matchingEdges F).image (labelledEdge G U Z code) = P.boundaryEdges
  projection_injective : Set.InjOn (labelledEdge G U Z code) (matchingEdges F)
  core_footprint : (F.verts.toFinset \ Z).card ≤ Z.card+6
  even_uncovered : ∀ i, Even (((U i : Set V) \ F.verts).ncard)

/-- The bound needed by the packing rule is a bound on each actual core
footprint, and follows from the total realized core support. -/
theorem RealizesPattern.coveredCore_card_le {P : Pattern Z} {F : G.Subgraph}
    (hF : RealizesPattern G U Z code P F)
    (hUZ : ∀ i, Disjoint (U i) Z) (i : I) :
    (ForceMatching.coveredCore (U i) G F).card ≤ Z.card+6 := by
  rw [ForceMatching.coveredCore_card]
  apply (Finset.card_le_card ?_).trans hF.core_footprint
  intro v hv
  obtain ⟨hvF,hvU⟩ := mem_inter.mp hv
  exact mem_sdiff.mpr ⟨hvF,fun hvZ => disjoint_left.mp (hUZ i) hvU hvZ⟩

/-- Realize the selected copies from the actual regular host and its core
error. The original compressed witnesses supply pattern parity; every
new edge is chosen by the proved pool construction. -/
theorem realize_patterns (P : J → Pattern Z)
    (hP : ∀ j, (P j).internalPairs = ∅)
    (hsource : ∀ j, ∃ M : G.Subgraph, Encodes G U Z code M (P j) ∧
      ∀ i, Even (((U i : Set V) \ M.verts).ncard))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ) ≤ (H i).degree v + a)
    (hcap : ∀ s : BoundarySlot Z P,
      demandCount (slotKind Z P) (slotKind Z P s) + (Z.card+6)*⌊a⌋₊ <
        (boundaryPool G U Z code (slotKind Z P s)).card) :
    ∃ F : J → G.Subgraph, (∀ j, RealizesPattern G U Z code (P j) (F j)) ∧
      (∀ j j', j ≠ j' → Disjoint (F j).spanningCoe (F j').spanningCoe) := by
  have hforest (j : J) : LeafForest (P j).forest := by
    obtain ⟨M,hM,_hpar⟩ := hsource j
    exact hM.forest
  have hinc (s : BoundarySlot Z P) (v : V) :
      ((boundaryPool G U Z code (slotKind Z P s)).filter
        (fun e => v ∈ coreEnds G Z e)).card ≤ ⌊a⌋₊ :=
    boundaryPool_incidence_le G U Z code (P s.1) (hP s.1) hdisjoint hUZ hcover H hH
      k a hregular hdegree s.2.val s.2.property v
  obtain ⟨F,hmatch,hcov,hdisj,hno,himage,hinj,hfoot⟩ :=
    exists_pattern_realization G U Z code P hP hforest hdisjoint hUZ ⌊a⌋₊ hinc hcap
  refine ⟨F,?_,hdisj⟩
  intro j
  obtain ⟨M,hM,hpar⟩ := hsource j
  exact ⟨hmatch j,hcov j,hno j,himage j,hinj j,hfoot j,
    even_uncovered_of_same_boundary U Z code hdisjoint hUZ hcover M (P j) hM hpar
      (F j) (hmatch j) (hinj j) (himage j)⟩

end Actual

end Overfull.Patterns
