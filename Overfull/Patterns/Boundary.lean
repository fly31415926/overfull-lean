import Overfull.Patterns.Encoding

/-!
# Boundary edges determined by a finite pattern

The quotient keeps every exceptional vertex and collapses each core to
its fixed label. On compressed matchings this quotient is injective on
edges. Consequently a pattern determines all whole-union cut counts.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open scoped BigOperators

variable {E V I : Type*}

/-- Quotient edges prescribed by a pattern. -/
def Pattern.boundaryEdges [Fintype E] [DecidableEq E] (P : Pattern E) : Finset (Finset (E ⊕ Fin 4)) :=
  P.internalPairs.image (fun p => p.val.image Sum.inl) ∪
    (univ.filter (fun z => ¬ P.Paired z)).image
      (fun z => {Sum.inl z,Sum.inr (P.assignment z)}) ∪
    P.forest.image (fun p => p.val.image Sum.inr)

variable [DecidableEq V]

def boundaryLabel (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (v : V) : Z ⊕ Fin 4 :=
  if hz : v ∈ Z then Sum.inl ⟨v,hz⟩ else Sum.inr (coreLabel U code v)

@[simp] theorem boundaryLabel_exceptional (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (z : Z) : boundaryLabel U Z code z.val = Sum.inl z := by
  simp [boundaryLabel,z.property]

@[simp] theorem boundaryLabel_inl_iff (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (v : V) (z : Z) :
    boundaryLabel U Z code v = Sum.inl z ↔ v = z.val := by
  by_cases hv : v ∈ Z
  · simp [boundaryLabel,hv,Subtype.ext_iff]
  · simp only [boundaryLabel,dif_neg hv,Sum.inr_ne_inl,false_iff]
    exact fun h => hv (h ▸ z.property)

theorem boundaryLabel_outside (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (v : V) (hv : v ∉ Z) :
    boundaryLabel U Z code v = Sum.inr (coreLabel U code v) := by
  simp [boundaryLabel,hv]

def labelledEdge (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (e : G.edgeSet) : Finset (Z ⊕ Fin 4) :=
  e.val.toFinset.image (boundaryLabel U Z code)

theorem labelledEdge_eq_pair (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (e : G.edgeSet) :
    labelledEdge G U Z code e =
      {boundaryLabel U Z code (firstEnd e),boundaryLabel U Z code (secondEnd e)} := by
  rw [labelledEdge,← edge_eq e,Sym2.toFinset_mk_eq]
  simp

@[simp] theorem inl_mem_labelledEdge (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (e : G.edgeSet) (z : Z) :
    Sum.inl z ∈ labelledEdge G U Z code e ↔ z.val ∈ e.val := by
  simp [labelledEdge,Sym2.mem_toFinset]

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem matchingEdges_edge {F : G.Subgraph} {e : G.edgeSet}
    (he : e ∈ matchingEdges F) : e.val ∈ F.edgeSet := (mem_filter.mp he).2

omit [DecidableEq V] in
theorem matchingEdges_of_adj {F : G.Subgraph} {u v : V} (h : F.Adj u v) :
    (⟨s(u,v),F.adj_sub h⟩ : G.edgeSet) ∈ matchingEdges F := by
  simp only [matchingEdges,mem_filter,mem_univ,true_and]
  exact h

omit [DecidableEq V] in
/-- In an actual matching, an incident vertex uniquely identifies its edge. -/
theorem matchingEdges_eq_of_common {F : G.Subgraph} (hF : F.IsMatching)
    {e f : G.edgeSet} (he : e ∈ matchingEdges F) (hf : f ∈ matchingEdges F)
    {v : V} (hev : v ∈ e.val) (hfv : v ∈ f.val) : e = f := by
  obtain ⟨x,hx⟩ := Sym2.mem_iff_exists.mp hev
  obtain ⟨y,hy⟩ := Sym2.mem_iff_exists.mp hfv
  have hxe : F.Adj v x := by simpa only [hx] using matchingEdges_edge he
  have hye : F.Adj v y := by simpa only [hy] using matchingEdges_edge hf
  have hxy := hF.eq_of_adj_left hxe hye
  apply Subtype.ext
  rw [hx,hy,hxy]

/-- The quotient of a compressed matching has no parallel edge copies. -/
theorem Encodes.labelledEdge_injective
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P) :
    Set.InjOn (labelledEdge G U Z code) (matchingEdges F) := by
  intro e he f hf heq
  by_cases hz : ∃ z : Z, z.val ∈ e.val
  · obtain ⟨z,hz⟩ := hz
    have hz' : Sum.inl z ∈ labelledEdge G U Z code f := by
      rw [← heq]
      exact (inl_mem_labelledEdge G U Z code e z).mpr hz
    exact matchingEdges_eq_of_common hP.matching he hf hz
      ((inl_mem_labelledEdge G U Z code f z).mp hz')
  · have heZ (v : V) (hv : v ∈ e.val) : v ∉ Z := fun hvZ => hz ⟨⟨v,hvZ⟩,hv⟩
    have hfZ (v : V) (hv : v ∈ f.val) : v ∉ Z := by
      intro hvZ
      have hvl := (inl_mem_labelledEdge G U Z code f ⟨v,hvZ⟩).mpr hv
      rw [← heq] at hvl
      exact hz ⟨⟨v,hvZ⟩,(inl_mem_labelledEdge G U Z code e ⟨v,hvZ⟩).mp hvl⟩
    have he₁ : firstEnd e ∉ Z := heZ _ ((incident_iff e _).mpr (Or.inl rfl))
    have he₂ : secondEnd e ∉ Z := heZ _ ((incident_iff e _).mpr (Or.inr rfl))
    have hf₁ : firstEnd f ∉ Z := hfZ _ ((incident_iff f _).mpr (Or.inl rfl))
    have hf₂ : secondEnd f ∉ Z := hfZ _ ((incident_iff f _).mpr (Or.inr rfl))
    have heN : e ∈ nonexceptionalEdges G F Z := mem_filter.mpr ⟨he,he₁,he₂⟩
    have hfN : f ∈ nonexceptionalEdges G F Z := mem_filter.mpr ⟨hf,hf₁,hf₂⟩
    obtain ⟨label,hlabel,hinj,_heq⟩ := hP.projection
    apply hinj heN hfN
    apply Subtype.ext
    rw [hlabel e heN,hlabel f hfN]
    apply Finset.image_injective (f := (Sum.inr : Fin 4 → Z ⊕ Fin 4)) Sum.inr_injective
    simpa only [labelledEdge_eq_pair,boundaryLabel_outside U Z code _ he₁,
      boundaryLabel_outside U Z code _ he₂,boundaryLabel_outside U Z code _ hf₁,
      boundaryLabel_outside U Z code _ hf₂,Finset.image_insert,Finset.image_singleton] using heq

theorem Encodes.not_paired_of_adj_outside
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (z : Z) (v : V) (hv : F.Adj z.val v) (hvZ : v ∉ Z) : ¬ P.Paired z := by
  intro hp
  obtain ⟨w,hw⟩ := (hP.paired_iff z).mp hp
  have heq : w.val = v := hP.matching.eq_of_adj_left hw hv
  exact hvZ (heq ▸ w.property)

theorem Encodes.labelledEdge_mem_boundary
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (e : G.edgeSet) (he : e ∈ matchingEdges F) :
    labelledEdge G U Z code e ∈ P.boundaryEdges := by
  have hadj : F.Adj (firstEnd e) (secondEnd e) := by
    have hh := matchingEdges_edge he
    rw [← edge_eq e] at hh
    exact hh
  by_cases ha : firstEnd e ∈ Z
  · let z : Z := ⟨firstEnd e,ha⟩
    by_cases hb : secondEnd e ∈ Z
    · let w : Z := ⟨secondEnd e,hb⟩
      have hne : z ≠ w := fun h => endpoints_distinct e (congrArg Subtype.val h)
      have hp : exceptionalPair z w hne ∈ P.internalPairs := by
        rw [hP.internal_pairs]
        exact (exceptionalPair_mem_iff G Z F z w hne).mpr hadj
      apply mem_union_left
      apply mem_union_left
      refine mem_image.mpr ⟨exceptionalPair z w hne,hp,?_⟩
      rw [labelledEdge_eq_pair]
      simp [exceptionalPair,boundaryLabel,ha,hb,z,w]
    · have hnpaired : ¬ P.Paired z := hP.not_paired_of_adj_outside z (secondEnd e) hadj hb
      have hn : ¬ ∃ w : Z, F.Adj z.val w.val := by
        simpa only [← hP.paired_iff z] using hnpaired
      have hassigned := hP.assignment_of_adj z hn (secondEnd e) hadj
      apply mem_union_left
      apply mem_union_right
      refine mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,hnpaired⟩,?_⟩
      rw [labelledEdge_eq_pair,hassigned]
      simp [boundaryLabel,ha,hb,z]
  · by_cases hb : secondEnd e ∈ Z
    · let z : Z := ⟨secondEnd e,hb⟩
      have hadj' : F.Adj z.val (firstEnd e) := F.symm hadj
      have hnpaired := hP.not_paired_of_adj_outside z (firstEnd e) hadj' ha
      have hn : ¬ ∃ w : Z, F.Adj z.val w.val := by
        simpa only [← hP.paired_iff z] using hnpaired
      have hassigned := hP.assignment_of_adj z hn (firstEnd e) hadj'
      apply mem_union_left
      apply mem_union_right
      refine mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,hnpaired⟩,?_⟩
      rw [labelledEdge_eq_pair,hassigned]
      simp [boundaryLabel,ha,hb,z,Finset.pair_comm]
    · have heN : e ∈ nonexceptionalEdges G F Z := mem_filter.mpr ⟨he,ha,hb⟩
      obtain ⟨label,hlabel,_hinj,hforest⟩ := hP.projection
      apply mem_union_right
      refine mem_image.mpr ⟨label e,?_,?_⟩
      · rw [hforest]
        exact mem_image.mpr ⟨e,heN,rfl⟩
      · rw [hlabel e heN,labelledEdge_eq_pair]
        simp [boundaryLabel,ha,hb]

/-- Every edge specified by the finite pattern is an actual edge of the
compressed matching after applying the quotient labels. -/
theorem Encodes.boundaryEdge_realized
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (A : Finset (Z ⊕ Fin 4)) (hA : A ∈ P.boundaryEdges) :
    ∃ e ∈ matchingEdges F, labelledEdge G U Z code e = A := by
  rcases mem_union.mp hA with hA | hA
  · rcases mem_union.mp hA with hA | hA
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp hA
      obtain ⟨z,w,hne,hends⟩ := Finset.card_eq_two.mp p.property
      have hadj := hP.internal_pair_adj p hp z w hends
      let e : G.edgeSet := ⟨s(z.val,w.val),F.adj_sub hadj⟩
      refine ⟨e,matchingEdges_of_adj hadj,?_⟩
      simp [labelledEdge,e,Sym2.toFinset_mk_eq,hends]
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hA
      have hnpaired : ¬ P.Paired z := (mem_filter.mp hz).2
      have hn : ¬ ∃ w : Z, F.Adj z.val w.val := by
        simpa only [← hP.paired_iff z] using hnpaired
      obtain ⟨v,hv,_huniq⟩ := hP.matching (hP.covered z.property)
      have hvZ : v ∉ Z := fun h => hn ⟨⟨v,h⟩,hv⟩
      have hassigned := hP.assignment_of_adj z hn v hv
      let e : G.edgeSet := ⟨s(z.val,v),F.adj_sub hv⟩
      refine ⟨e,matchingEdges_of_adj hv,?_⟩
      simp [labelledEdge,e,Sym2.toFinset_mk_eq,boundaryLabel_outside U Z code v hvZ,hassigned]
  · obtain ⟨p,hp,rfl⟩ := mem_image.mp hA
    obtain ⟨label,hlabel,_hinj,hforest⟩ := hP.projection
    rw [hforest] at hp
    obtain ⟨e,he,rfl⟩ := mem_image.mp hp
    obtain ⟨heM,ha,hb⟩ := mem_filter.mp he
    refine ⟨e,heM,?_⟩
    rw [hlabel e he,labelledEdge_eq_pair]
    simp [boundaryLabel,ha,hb]

/-- A pattern identifies exactly the image of the actual compressed edges. -/
theorem Encodes.boundary_edges
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P) :
    (matchingEdges F).image (labelledEdge G U Z code) = P.boundaryEdges := by
  ext A
  constructor
  · intro h
    obtain ⟨e,he,rfl⟩ := mem_image.mp h
    exact hP.labelledEdge_mem_boundary e he
  · intro hA
    exact mem_image.mpr (hP.boundaryEdge_realized A hA)

/-- Every quotient edge of a pattern has two distinct ends. -/
theorem Pattern.boundaryEdge_card [Fintype E] [DecidableEq E]
    (P : Pattern E) (A : Finset (E ⊕ Fin 4)) (hA : A ∈ P.boundaryEdges) : A.card = 2 := by
  rcases mem_union.mp hA with hA | hA
  · rcases mem_union.mp hA with hA | hA
    · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hA
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      exact p.property
    · obtain ⟨z,_hz,rfl⟩ := mem_image.mp hA
      simp
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hA
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    exact p.property

/-- A whole union is the inverse image of quotient vertices. -/
def wholeUnion (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (Q : Finset (Z ⊕ Fin 4)) : Finset V :=
  univ.filter (fun v => boundaryLabel U Z code v ∈ Q)

@[simp] theorem mem_wholeUnion (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (Q : Finset (Z ⊕ Fin 4)) (v : V) :
    v ∈ wholeUnion U Z code Q ↔ boundaryLabel U Z code v ∈ Q := by
  simp [wholeUnion]

/-- The number of pattern edges crossing a set of quotient vertices. -/
def Pattern.cutCount [Fintype E] [DecidableEq E] (P : Pattern E)
    (Q : Finset (E ⊕ Fin 4)) : ℕ :=
  (P.boundaryEdges.filter (fun A => (A.filter (fun v => v ∈ Q)).card = 1)).card

omit [DecidableRel G.Adj] in
theorem labelledEdge_crosses_iff (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (e : G.edgeSet) (Q : Finset (Z ⊕ Fin 4))
    (hcard : (labelledEdge G U Z code e).card = 2) :
    ((labelledEdge G U Z code e).filter (fun v => v ∈ Q)).card = 1 ↔
      ((firstEnd e ∈ wholeUnion U Z code Q) ≠ (secondEnd e ∈ wholeUnion U Z code Q)) := by
  have hne : boundaryLabel U Z code (firstEnd e) ≠ boundaryLabel U Z code (secondEnd e) := by
    intro h
    rw [labelledEdge_eq_pair,h] at hcard
    simp at hcard
  rw [labelledEdge_eq_pair,mem_wholeUnion,mem_wholeUnion]
  by_cases ha : boundaryLabel U Z code (firstEnd e) ∈ Q <;>
    by_cases hb : boundaryLabel U Z code (secondEnd e) ∈ Q <;>
      simp_all [Finset.filter_insert,Finset.filter_singleton]

omit [DecidableRel G.Adj] in
/-- Any actual edge family with the stated injective quotient realizes
exactly the cut counts of the pattern. This also applies to new matchings
constructed by the greedy realization, before an Encodes proof exists. -/
theorem cutCount_eq_pattern_of_boundary (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (A : Finset G.edgeSet) (P : Pattern Z)
    (hinj : Set.InjOn (labelledEdge G U Z code) A)
    (himage : A.image (labelledEdge G U Z code) = P.boundaryEdges)
    (Q : Finset (Z ⊕ Fin 4)) :
    cutCount A (wholeUnion U Z code Q) = P.cutCount Q := by
  unfold Pattern.cutCount
  rw [← himage,Finset.filter_image]
  rw [Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
  unfold cutCount
  apply congrArg Finset.card
  ext e
  simp only [cutEdges,Lovasz.BMatch.cut,Finset.mem_filter]
  apply and_congr_right
  intro he
  have heP : labelledEdge G U Z code e ∈ P.boundaryEdges := by
    rw [← himage]
    exact mem_image.mpr ⟨e,he,rfl⟩
  exact (labelledEdge_crosses_iff U Z code e Q
    (P.boundaryEdge_card _ heP)).symm

/-- All whole-union cut counts of an encoded matching are determined by
its finite pattern. -/
theorem Encodes.whole_cut_count
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (Q : Finset (Z ⊕ Fin 4)) :
    cutCount (matchingEdges F) (wholeUnion U Z code Q) = P.cutCount Q :=
  cutCount_eq_pattern_of_boundary U Z code (matchingEdges F) P
    hP.labelledEdge_injective hP.boundary_edges Q

theorem wholeUnion_single_core (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (i : I) :
    wholeUnion U Z code {Sum.inr (code i)} = U i := by
  ext v
  rw [mem_wholeUnion,mem_singleton]
  by_cases hvZ : v ∈ Z
  · have hvU : v ∉ U i := fun hv => Finset.disjoint_left.mp (hUZ i) hv hvZ
    simp [boundaryLabel,hvZ,hvU]
  · rw [boundaryLabel_outside U Z code v hvZ,Sum.inr.injEq]
    exact coreLabel_eq_iff U Z code hdisjoint hcover hvZ i

/-- The uncovered-order parity is equivalent to the actual cut parity
for every matching, irrespective of its internal edges. -/
theorem matching_uncovered_even_iff_cut_parity (F : G.Subgraph) (hF : F.IsMatching)
    (X : Finset V) :
    Even (((X : Set V) \ F.verts).ncard) ↔
      cutCount (matchingEdges F) X % 2 = X.card % 2 := by
  have hinc (v : V) : incidentCount (matchingEdges F) v = if v ∈ F.verts then 1 else 0 := by
    rw [incidentCount_matchingEdges_degree]
    exact BipartitePackingAccounting.matching_degree G F hF v
  have hcovered := covered_count_of_incident G F (matchingEdges F) hinc X
  have hhandshake := cut_handshake (matchingEdges F) X
  have hcard := Finset.card_sdiff_add_card_inter X F.verts.toFinset
  rw [Finset.inter_comm X F.verts.toFinset] at hcard
  have hdiff : ((X : Set V) \ F.verts).ncard = (X \ F.verts.toFinset).card := by
    have hh : (X : Set V) \ F.verts = ((X \ F.verts.toFinset : Finset V) : Set V) := by
      ext v
      simp
    rw [hh,Set.ncard_coe_finset]
  rw [hdiff,Nat.even_iff]
  omega

/-- Matching realizations with the same pattern retain exactly the core
parities needed for independent perfect completion. -/
theorem even_uncovered_of_same_boundary
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (F : G.Subgraph) (P : Pattern Z) (hP : Encodes G U Z code F P)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (N : G.Subgraph) (hN : N.IsMatching)
    (hinj : Set.InjOn (labelledEdge G U Z code) (matchingEdges N))
    (himage : (matchingEdges N).image (labelledEdge G U Z code) = P.boundaryEdges) :
    ∀ i, Even (((U i : Set V) \ N.verts).ncard) := by
  intro i
  apply (matching_uncovered_even_iff_cut_parity N hN (U i)).mpr
  have hcut := cutCount_eq_pattern_of_boundary U Z code (matchingEdges N) P hinj himage
    {Sum.inr (code i)}
  have hcutF := hP.whole_cut_count {Sum.inr (code i)}
  rw [wholeUnion_single_core U Z code hdisjoint hUZ hcover i] at hcut hcutF
  rw [hcut,hcutF.symm]
  exact (matching_uncovered_even_iff_cut_parity F hP.matching (U i)).mp (hparity i)

end Overfull.Patterns
