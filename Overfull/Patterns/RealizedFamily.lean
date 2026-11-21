import Overfull.Patterns.Pools

/-!
# Realizing a finite family of boundary patterns

The slots are the quotient edges of the requested patterns themselves.
Their realization supplies the exact quotient, exceptional coverage,
bounded core footprints, and the parity required for completion.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open PatternRealization
open scoped BigOperators

theorem mem_roundEdges {V S T : Type*} [Fintype S] (G : SimpleGraph V)
    (pick : S → G.edgeSet) (round : S → T) (r : T) (e : G.edgeSet) :
    e ∈ roundEdges G pick round r ↔ ∃ s, round s = r ∧ pick s = e := by
  simp [roundEdges]

variable {E R : Type*} [Fintype E] [DecidableEq E] [Fintype R]

/-- One slot for each boundary pair in each requested pattern. -/
abbrev BoundarySlot (P : R → Pattern E) :=
  Σ r : R, {b : BoundaryPair E // boundaryPairLabels b ∈ (P r).boundaryEdges}

def slotPair (P : R → Pattern E) (s : BoundarySlot P) : BoundaryPair E := s.2.val

def slotRound (P : R → Pattern E) (s : BoundarySlot P) : R := s.1

omit [Fintype R] in
theorem slot_eq_of_round_pair (P : R → Pattern E) (s t : BoundarySlot P)
    (hr : slotRound P s = slotRound P t) (hb : slotPair P s = slotPair P t) : s = t := by
  obtain ⟨r,b⟩ := s
  obtain ⟨r',b'⟩ := t
  dsimp [slotRound,slotPair] at hr hb
  subst r'
  exact congrArg (Sigma.mk r) (Subtype.ext hb)

theorem slots_arity_eq (P : R → Pattern E)
    (hP : ∀ r, (P r).internalPairs = ∅) (r : R) :
    (∑ s ∈ univ.filter (fun s : BoundarySlot P => slotRound P s = r),
      boundaryPairArity (slotPair P s)) = ∑ b ∈ (P r).boundaryEdges, boundaryArity b := by
  apply Finset.sum_bij (fun s _ => boundaryPairLabels (slotPair P s))
  · intro s hs
    have hr := (mem_filter.mp hs).2
    simpa only [← hr] using s.2.property
  · intro s hs t ht heq
    exact slot_eq_of_round_pair P s t ((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm)
      (boundaryPairLabels_injective heq)
  · intro b hb
    obtain ⟨p,hp⟩ := boundaryEdge_has_pair (P r) (hP r) b hb
    refine ⟨⟨r,⟨p,hp ▸ hb⟩⟩,?_,hp⟩
    simp [slotRound]
  · intro s _
    exact boundaryPairArity_eq (slotPair P s)

theorem slots_arity_le (P : R → Pattern E)
    (hP : ∀ r, (P r).internalPairs = ∅)
    (hforest : ∀ r, LeafForest (P r).forest) (r : R) :
    (∑ s ∈ univ.filter (fun s : BoundarySlot P => slotRound P s = r),
      boundaryPairArity (slotPair P s)) ≤ Fintype.card E+6 := by
  rw [slots_arity_eq P hP r]
  exact boundaryArity_sum_le (P r) (hP r) (hforest r)

/-- Each round uses a specified pair at most once. -/
theorem slots_demand_eq (P : R → Pattern E) (b : BoundaryPair E) :
    demandCount (slotPair P) b =
      (univ.filter (fun r : R => boundaryPairLabels b ∈ (P r).boundaryEdges)).card := by
  unfold demandCount
  apply Finset.card_bij (fun s _ => slotRound P s)
  · intro s hs
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have hb : slotPair P s = b := by simpa only [mem_filter,mem_univ,true_and] using hs
    rw [← hb]
    exact s.2.property
  · intro s hs t ht hr
    have hs' : slotPair P s = b := by simpa only [mem_filter,mem_univ,true_and] using hs
    have ht' : slotPair P t = b := by simpa only [mem_filter,mem_univ,true_and] using ht
    exact slot_eq_of_round_pair P s t hr (hs'.trans ht'.symm)
  · intro r hr
    refine ⟨⟨r,⟨b,(mem_filter.mp hr).2⟩⟩,?_,rfl⟩
    simp [slotPair]

variable {V I : Type*} [Fintype V] [DecidableEq V]

omit [Fintype R] [Fintype V] in
theorem slot_special_disjoint (Z : Finset V) (P : R → Pattern Z)
    (hP : ∀ r, (P r).internalPairs = ∅)
    (s t : BoundarySlot P) (hne : s ≠ t) (hr : slotRound P s = slotRound P t) :
    Disjoint (boundaryPairSpecial Z (slotPair P s)) (boundaryPairSpecial Z (slotPair P t)) := by
  have hpair : slotPair P s ≠ slotPair P t := fun h => hne (slot_eq_of_round_pair P s t hr h)
  have hs := s.2.property
  have ht : boundaryPairLabels (slotPair P t) ∈ (P (slotRound P s)).boundaryEdges := by
    rw [hr]; exact t.2.property
  have hdis := exceptionalLabels_disjoint (P (slotRound P s)) (hP _)
    (boundaryPairLabels (slotPair P s)) (boundaryPairLabels (slotPair P t)) hs ht
    (fun h => hpair (boundaryPairLabels_injective h))
  rw [boundaryPairSpecial_eq_image,boundaryPairSpecial_eq_image]
  apply disjoint_left.mpr
  intro v hv hv'
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
  obtain ⟨w,hw,heq⟩ := mem_image.mp hv'
  have hzw : w = z := Subtype.ext heq
  subst w
  exact disjoint_left.mp hdis hz hw

omit [Fintype R] [Fintype V] in
theorem slot_covers_exceptional (Z : Finset V) (P : R → Pattern Z)
    (hP : ∀ r, (P r).internalPairs = ∅) (r : R) (v : V) (hv : v ∈ Z) :
    ∃ s : BoundarySlot P, slotRound P s = r ∧
      v ∈ boundaryPairSpecial Z (slotPair P s) := by
  let z : Z := ⟨v,hv⟩
  let b : BoundaryPair Z := Sum.inl (z,(P r).assignment z)
  have hb : boundaryPairLabels b ∈ (P r).boundaryEdges :=
    assignment_edge_mem (P r) (hP r) z
  exact ⟨⟨r,⟨b,hb⟩⟩,rfl,by simp [slotPair,b,boundaryPairSpecial,z]⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual output of the greedy boundary realization. -/
structure RealizedBoundaryFamily (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (P : R → Pattern Z) where
  matching : R → G.Subgraph
  isMatching : ∀ r, (matching r).IsMatching
  disjoint : ∀ r s, r ≠ s → Disjoint (matching r).spanningCoe (matching s).spanningCoe
  covered : ∀ r, (Z : Set V) ⊆ (matching r).verts
  no_internal : ∀ r i u v, u ∈ U i → v ∈ U i → ¬ (matching r).Adj u v
  boundary_injective : ∀ r, Set.InjOn (labelledEdge G U Z code) (matchingEdges (matching r))
  boundary_image : ∀ r,
    (matchingEdges (matching r)).image (labelledEdge G U Z code) = (P r).boundaryEdges
  footprint : ∀ r i, ((matching r).verts.toFinset ∩ U i).card ≤ Z.card+6

set_option maxHeartbeats 1000000 in
/-- The numerical pool slack constructs every actual boundary matching;
matching, coverage and quotient correctness are conclusions. -/
theorem exists_realized_boundary_family
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (P : R → Pattern Z) (hP : ∀ r, (P r).internalPairs = ∅)
    (hforest : ∀ r, LeafForest (P r).forest)
    (hcap : ∀ s : BoundarySlot P,
      demandCount (slotPair P) (slotPair P s) + (Z.card+6)*⌊a⌋₊ <
        (boundaryPool G U Z code (slotPair P s)).card) :
    Nonempty (RealizedBoundaryFamily G U Z code P) := by
  obtain ⟨pick,hpick,hinj,hmatching,hpairwise,hcovered,_hcounts⟩ :=
    exists_boundary_matchings G Z (boundaryPool G U Z code) (boundaryPairSpecial Z)
      (slotPair P) (slotRound P) boundaryPairArity ⌊a⌋₊ (Z.card+6)
      (boundaryPools_disjoint G U Z code)
      (boundaryPool_arity G U Z code)
      (fun b v => by
        convert boundaryPool_incidence_le_floor G U Z code hdisjoint hUZ hcover
          H hH k a ha hregular hdegree b v using 1
        congr 1
        ext e
        simp)
      (fun r => by simpa using slots_arity_le P hP hforest r)
      hcap (fun b e he => by
        convert boundaryPool_special G U Z code b e he using 1
        ext v
        simp)
      (slot_special_disjoint Z P hP) (slot_covers_exceptional Z P hP)
  let N := roundMatching G pick (slotRound P)
  have hlabels (s : BoundarySlot P) :
      labelledEdge G U Z code (pick s) = boundaryPairLabels (slotPair P s) :=
    (mem_boundaryPool G U Z code _ _).mp (hpick s)
  have hquotient (r : R) :
      Set.InjOn (labelledEdge G U Z code) (matchingEdges (N r)) := by
    rw [roundMatching_edges]
    intro e he f hf hef
    obtain ⟨s,hs,rfl⟩ := (mem_roundEdges G pick (slotRound P) r e).mp he
    obtain ⟨t,ht,rfl⟩ := (mem_roundEdges G pick (slotRound P) r f).mp hf
    rw [hlabels,hlabels] at hef
    have hst := slot_eq_of_round_pair P s t
      (hs.trans ht.symm)
      (boundaryPairLabels_injective hef)
    exact congrArg pick hst
  have himage (r : R) :
      (matchingEdges (N r)).image (labelledEdge G U Z code) = (P r).boundaryEdges := by
    rw [roundMatching_edges]
    ext b
    simp only [mem_image,roundEdges,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨e,⟨s,hs,rfl⟩,rfl⟩
      rw [hlabels]
      rw [← hs]
      exact s.2.property
    · intro hb
      obtain ⟨p,hp⟩ := boundaryEdge_has_pair (P r) (hP r) b hb
      let s : BoundarySlot P := ⟨r,⟨p,hp ▸ hb⟩⟩
      exact ⟨pick s,⟨s,rfl,rfl⟩,(hlabels s).trans hp⟩
  refine ⟨⟨N,hmatching,hpairwise,hcovered,?_,hquotient,himage,?_⟩⟩
  · intro r
    exact roundMatching_no_internal G U (boundaryPool G U Z code) (slotPair P) (slotRound P)
      pick hpick (fun s => boundaryPool_no_internal G U Z code hdisjoint hUZ (slotPair P s)) r
  · intro r i
    have hsub : (N r).verts.toFinset ∩ U i ⊆ (N r).verts.toFinset \ Z := by
      intro v hv
      obtain ⟨hNv,hvU⟩ := mem_inter.mp hv
      exact mem_sdiff.mpr ⟨hNv,fun hz => disjoint_left.mp (hUZ i) hvU hz⟩
    have hc := roundMatching_core_card_le G Z (boundaryPool G U Z code) (slotPair P)
      (slotRound P) boundaryPairArity (boundaryPool_arity G U Z code) pick hpick r
    have hc' : ((N r).verts.toFinset \ Z).card ≤
        ∑ s ∈ univ.filter (fun s : BoundarySlot P => slotRound P s = r),
          boundaryPairArity (slotPair P s) := by
      convert hc using 1
      congr 1
      ext v
      simp [N]
    exact (Finset.card_le_card hsub).trans
      (hc'.trans (by simpa using slots_arity_le P hP hforest r))

omit [Fintype R] in
/-- A supporting compressed matching supplies the core parity of every
newly realized copy, via equality of the actual quotient boundaries. -/
theorem RealizedBoundaryFamily.even_uncovered
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {P : R → Pattern Z}
    (D : RealizedBoundaryFamily G U Z code P)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hsource : ∀ r, ∃ F : G.Subgraph, Encodes G U Z code F (P r) ∧
      ∀ i, Even (((U i : Set V) \ F.verts).ncard)) :
    ∀ r i, Even (((U i : Set V) \ (D.matching r).verts).ncard) := by
  intro r
  obtain ⟨F,henc,hpar⟩ := hsource r
  exact even_uncovered_of_same_boundary U Z code hdisjoint hUZ hcover F (P r) henc hpar
    (D.matching r) (D.isMatching r) (D.boundary_injective r) (D.boundary_image r)

/-- Real slack from the rounded and filtered demands suffices. The zero
error case requires no separate assumption: any demanded edge would
itself force positive exterior error. -/
theorem exists_realized_boundary_family_of_slack
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k t : ℕ) (a η : ℝ) (ha : 0 ≤ a) (hη : 0 < η) (hZ : Z.card ≤ t)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (P : R → Pattern Z) (hP : ∀ r, (P r).internalPairs = ∅)
    (hforest : ∀ r, LeafForest (P r).forest)
    (hdemand : ∀ b : BoundaryPair Z,
      ((univ.filter (fun r : R => boundaryPairLabels b ∈ (P r).boundaryEdges)).card : ℝ) ≤
        (1-η)*(boundaryPool G U Z code b).card)
    (hsparse : ∀ r b, boundaryPairLabels b ∈ (P r).boundaryEdges →
      ((t : ℝ)+8)*a/η ≤ (boundaryPool G U Z code b).card) :
    Nonempty (RealizedBoundaryFamily G U Z code P) := by
  apply exists_realized_boundary_family G U Z code hdisjoint hUZ hcover H hH k a ha
    hregular hdegree P hP hforest
  intro s
  have hd := hdemand (slotPair P s)
  rw [← slots_demand_eq] at hd
  have hpos : 0 < demandCount (slotPair P) (slotPair P s) := by
    unfold demandCount
    apply card_pos.mpr
    exact ⟨s,by simp⟩
  have hpool : (boundaryPool G U Z code (slotPair P s)).Nonempty := by
    apply card_pos.mp
    by_contra hn
    have heq : (boundaryPool G U Z code (slotPair P s)).card = 0 := by omega
    rw [heq] at hd
    simp only [Nat.cast_zero,mul_zero,Nat.cast_nonpos] at hd
    omega
  have hapos := boundaryPool_nonempty_error_pos G U Z code hdisjoint hUZ hcover
    H hH k a ha hregular hdegree (slotPair P s) hpool
  have hs := (div_le_iff₀ hη).mp (hsparse (slotRound P s) (slotPair P s) s.2.property)
  have hZr : (Z.card : ℝ) ≤ t := by exact_mod_cast hZ
  apply capacity_of_real_slack _ _ (Z.card+6) a η hapos hd
  have hmul := mul_le_mul_of_nonneg_right hZr ha
  push_cast
  nlinarith

end Overfull.Patterns
