import Overfull.ColorCoverage

/-!
# Placing the exterior vertices of a matching on balanced shores

Every edge is an original multigraph copy. A matching that covers the
exterior and has no internal core edge has a bounded core footprint.
If that footprint is balanced on a core cut, the exterior vertices can
be split equally so that the whole matching crosses the augmented cut.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical

variable {V E : Type*}

/-- The original core vertices incident with the given copy set. -/
def coreFootprint (G : Multigraph V E) (U : Finset V) (M : Finset E) : Finset V :=
  U.filter (fun v => ∃ e ∈ M, v ∈ G.edge e)

@[simp] theorem mem_coreFootprint (G : Multigraph V E) (U : Finset V)
    (M : Finset E) (v : V) :
    v ∈ coreFootprint G U M ↔ v ∈ U ∧ ∃ e ∈ M, v ∈ G.edge e := by
  simp only [coreFootprint, mem_filter]

theorem coreFootprint_subset (G : Multigraph V E) (U : Finset V) (M : Finset E) :
    coreFootprint G U M ⊆ U := filter_subset _ _

/-- The same footprint indexed by the actual core subtype. -/
def coreFootprintSubtype (G : Multigraph V E) (U : Finset V) (M : Finset E) : Finset U :=
  univ.filter (fun v => ∃ e ∈ M, v.val ∈ G.edge e)

@[simp] theorem mem_coreFootprintSubtype (G : Multigraph V E) (U : Finset V)
    (M : Finset E) (v : U) :
    v ∈ coreFootprintSubtype G U M ↔ ∃ e ∈ M, v.val ∈ G.edge e := by
  simp only [coreFootprintSubtype, mem_filter, mem_univ, true_and]

theorem coreFootprintSubtype_map (G : Multigraph V E) (U : Finset V) (M : Finset E) :
    (coreFootprintSubtype G U M).map (Function.Embedding.subtype (fun v => v ∈ U)) =
      coreFootprint G U M := by
  ext v
  simp only [mem_map, Function.Embedding.subtype_apply, mem_coreFootprintSubtype,
    mem_coreFootprint]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hh⟩
    exact ⟨⟨v, hv⟩, hh, rfl⟩

theorem coreFootprintSubtype_card (G : Multigraph V E) (U : Finset V) (M : Finset E) :
    (coreFootprintSubtype G U M).card = (coreFootprint G U M).card := by
  rw [← coreFootprintSubtype_map G U M, card_map]

theorem coreFootprintSubtype_inter_card (G : Multigraph V E) (U : Finset V)
    (M : Finset E) (A : Finset U) :
    (coreFootprintSubtype G U M ∩ A).card =
      (coreFootprint G U M ∩
        A.map (Function.Embedding.subtype (fun v => v ∈ U))).card := by
  rw [← coreFootprintSubtype_map G U M, ← map_inter, card_map]

variable [Fintype V] [Fintype E]

/-- Every covered core vertex consumes a distinct exterior endpoint.
The matching handshake also gives its exact even parity. -/
theorem matching_footprint_bounds (G : Multigraph V E) (U : Finset V) (M : Finset E)
    (hM : G.IsMatching M) (houtside : M ⊆ (G.internalEdges U)ᶜ)
    (hcover : ∀ z ∈ Uᶜ, ∃ e ∈ M, z ∈ G.edge e) (heven : Even Uᶜ.card) :
    Even (coreFootprint G U M).card ∧ (coreFootprint G U M).card ≤ Uᶜ.card := by
  let W := M.biUnion (fun e => (G.edge e).toFinset)
  have hdisj : (↑M : Set E).PairwiseDisjoint (fun e => (G.edge e).toFinset) := by
    intro e he f hf hne
    apply disjoint_left.mpr
    intro v hv hv'
    exact hne (hM e he f hf v
      (by simpa only [Sym2.mem_toFinset] using hv)
      (by simpa only [Sym2.mem_toFinset] using hv'))
  have hWcard : W.card = 2 * M.card := by
    rw [show W = M.biUnion (fun e => (G.edge e).toFinset) from rfl,
      card_biUnion hdisj]
    have hh : (∑ e ∈ M, (G.edge e).toFinset.card) = ∑ _e ∈ M, (2 : ℕ) := by
      apply sum_congr rfl
      intro e _
      exact Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)
    rw [hh]
    simp [Nat.mul_comm]
  have hW : coreFootprint G U M ∪ Uᶜ = W := by
    ext v
    simp only [mem_union, mem_coreFootprint, mem_compl, W, mem_biUnion, Sym2.mem_toFinset]
    constructor
    · rintro (⟨_hv, hh⟩ | hv)
      · exact hh
      · exact hcover v (mem_compl.mpr hv)
    · intro hh
      by_cases hv : v ∈ U
      · exact Or.inl ⟨hv, hh⟩
      · exact Or.inr hv
  have hfootdisj : Disjoint (coreFootprint G U M) Uᶜ := by
    apply disjoint_left.mpr
    intro v hv hv'
    exact (mem_compl.mp hv') (coreFootprint_subset G U M hv)
  have hsize : (coreFootprint G U M).card + Uᶜ.card = 2 * M.card := by
    rw [← card_union_of_disjoint hfootdisj, hW, hWcard]
  let out : E → V := fun e => if G.firstEnd e ∈ U then G.secondEnd e else G.firstEnd e
  have houtmem (e : E) : out e ∈ G.edge e := by
    dsimp only [out]
    split_ifs
    · exact (G.incident_iff e _).mpr (Or.inr rfl)
    · exact (G.incident_iff e _).mpr (Or.inl rfl)
  have hout : M.image out ⊆ Uᶜ := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := mem_image.mp hv
    apply mem_compl.mpr
    dsimp only [out]
    split_ifs with hfirst
    · intro hsecond
      exact (mem_compl.mp (houtside he)) ((G.mem_internalEdges U e).mpr ⟨hfirst, hsecond⟩)
    · exact hfirst
  have hinj : Set.InjOn out (↑M : Set E) := by
    intro e he f hf hef
    exact hM e he f hf (out e) (houtmem e) (hef ▸ houtmem f)
  have hMbound : M.card ≤ Uᶜ.card := by
    have hh := card_le_card hout
    rw [card_image_of_injOn hinj] at hh
    exact hh
  constructor
  · rw [Nat.even_iff] at heven ⊢
    omega
  · omega

private def leftEnd (G : Multigraph V E) (A B : Finset V) (e : E) : V :=
  if G.firstEnd e ∈ B ∨ G.secondEnd e ∈ A then G.secondEnd e else G.firstEnd e

private def rightEnd (G : Multigraph V E) (A B : Finset V) (e : E) : V :=
  if G.firstEnd e ∈ B ∨ G.secondEnd e ∈ A then G.firstEnd e else G.secondEnd e

omit [Fintype V] [Fintype E] in
private theorem ends_edge (G : Multigraph V E) (A B : Finset V) (e : E) :
    s(leftEnd G A B e, rightEnd G A B e) = G.edge e := by
  unfold leftEnd rightEnd
  split_ifs
  · exact Sym2.eq_swap.trans (G.edge_eq e)
  · exact G.edge_eq e

omit [Fintype V] [Fintype E] in
private theorem left_incident (G : Multigraph V E) (A B : Finset V) (e : E) :
    leftEnd G A B e ∈ G.edge e := by
  rw [← ends_edge G A B e]
  simp

omit [Fintype V] [Fintype E] in
private theorem right_incident (G : Multigraph V E) (A B : Finset V) (e : E) :
    rightEnd G A B e ∈ G.edge e := by
  rw [← ends_edge G A B e]
  simp

omit [Fintype V] [Fintype E] in
private theorem ends_ne (G : Multigraph V E) (A B : Finset V) (e : E) :
    leftEnd G A B e ≠ rightEnd G A B e := by
  intro h
  apply G.loopless e
  rw [← ends_edge G A B e, h]
  simp

omit [Fintype V] in
private theorem ends_avoid (G : Multigraph V E) (U A B : Finset V)
    (hAB : Disjoint A B) (hunion : A ∪ B = U) (e : E)
    (he : e ∉ G.internalEdges U) :
    leftEnd G A B e ∉ B ∧ rightEnd G A B e ∉ A := by
  have hA : A ⊆ U := hunion ▸ subset_union_left
  have hB : B ⊆ U := hunion ▸ subset_union_right
  have hn : ¬ (G.firstEnd e ∈ U ∧ G.secondEnd e ∈ U) := by
    simpa only [G.mem_internalEdges U e] using he
  have hd (v : V) : ¬ (v ∈ A ∧ v ∈ B) := fun h => (disjoint_left.mp hAB) h.1 h.2
  unfold leftEnd rightEnd
  split_ifs with h
  · constructor
    · intro hb
      rcases h with hf | hs
      · exact hn ⟨hB hf, hB hb⟩
      · exact hd _ ⟨hs, hb⟩
    · intro ha
      rcases h with hf | hs
      · exact hd _ ⟨ha, hf⟩
      · exact hn ⟨hA ha, hA hs⟩
  · exact ⟨fun hb => h (Or.inl hb), fun ha => h (Or.inr ha)⟩

/-- A balanced core footprint permits a balanced exterior split across
which every copy of the actual exterior matching passes. -/
theorem exists_balanced_exterior_split (G : Multigraph V E) (U A B : Finset V)
    (M : Finset E) (hM : G.IsMatching M)
    (houtside : M ⊆ (G.internalEdges U)ᶜ)
    (hcover : ∀ z ∈ Uᶜ, ∃ e ∈ M, z ∈ G.edge e)
    (hAB : Disjoint A B) (hunion : A ∪ B = U)
    (hbalance : (coreFootprint G U M ∩ A).card = (coreFootprint G U M ∩ B).card) :
    ∃ ZA ZB : Finset V, Disjoint ZA ZB ∧ ZA ∪ ZB = Uᶜ ∧ ZA.card = ZB.card ∧
      ∀ e ∈ M, e ∈ G.cutEdges (A ∪ ZA) := by
  let L := M.image (leftEnd G A B)
  let R := M.image (rightEnd G A B)
  have hLcard : L.card = M.card := by
    apply card_image_of_injOn
    intro e he f hf hef
    exact hM e he f hf _ (left_incident G A B e) (hef ▸ left_incident G A B f)
  have hRcard : R.card = M.card := by
    apply card_image_of_injOn
    intro e he f hf hef
    exact hM e he f hf _ (right_incident G A B e) (hef ▸ right_incident G A B f)
  have hLR : Disjoint L R := by
    apply disjoint_left.mpr
    intro v hv hv'
    obtain ⟨e, he, hev⟩ := mem_image.mp hv
    obtain ⟨f, hf, hfv⟩ := mem_image.mp hv'
    have hef : e = f := hM e he f hf v
      (hev ▸ left_incident G A B e) (hfv ▸ right_incident G A B f)
    subst f
    exact ends_ne G A B e (hev.trans hfv.symm)
  have hLcore : L ∩ U = coreFootprint G U M ∩ A := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, rfl⟩ := mem_image.mp (mem_inter.mp hv).1
      have hu := (mem_inter.mp hv).2
      have hn := (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).1
      have ha : leftEnd G A B e ∈ A := by
        have hh : leftEnd G A B e ∈ A ∪ B := hunion.symm ▸ hu
        exact (mem_union.mp hh).resolve_right hn
      exact mem_inter.mpr ⟨(mem_coreFootprint G U M _).mpr
        ⟨hu, e, he, left_incident G A B e⟩, ha⟩
    · intro hv
      obtain ⟨hu, e, he, hve⟩ := (mem_coreFootprint G U M v).mp (mem_inter.mp hv).1
      have ha := (mem_inter.mp hv).2
      have hor : v = leftEnd G A B e ∨ v = rightEnd G A B e := by
        simpa only [← ends_edge G A B e, Sym2.mem_iff] using hve
      have hvL : v = leftEnd G A B e := hor.resolve_right (fun hr =>
        (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).2 (hr ▸ ha))
      exact mem_inter.mpr ⟨mem_image.mpr ⟨e, he, hvL.symm⟩, hu⟩
  have hRcore : R ∩ U = coreFootprint G U M ∩ B := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, rfl⟩ := mem_image.mp (mem_inter.mp hv).1
      have hu := (mem_inter.mp hv).2
      have hn := (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).2
      have hb : rightEnd G A B e ∈ B := by
        have hh : rightEnd G A B e ∈ A ∪ B := hunion.symm ▸ hu
        exact (mem_union.mp hh).resolve_left hn
      exact mem_inter.mpr ⟨(mem_coreFootprint G U M _).mpr
        ⟨hu, e, he, right_incident G A B e⟩, hb⟩
    · intro hv
      obtain ⟨hu, e, he, hve⟩ := (mem_coreFootprint G U M v).mp (mem_inter.mp hv).1
      have hb := (mem_inter.mp hv).2
      have hor : v = leftEnd G A B e ∨ v = rightEnd G A B e := by
        simpa only [← ends_edge G A B e, Sym2.mem_iff] using hve
      have hvR : v = rightEnd G A B e := hor.resolve_left (fun hl =>
        (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).1 (hl ▸ hb))
      exact mem_inter.mpr ⟨mem_image.mpr ⟨e, he, hvR.symm⟩, hu⟩
  have hsplit : L \ U ∪ R \ U = Uᶜ := by
    ext v
    constructor
    · intro hv
      rcases mem_union.mp hv with hv | hv <;> exact mem_compl.mpr (mem_sdiff.mp hv).2
    · intro hv
      obtain ⟨e, he, hve⟩ := hcover v hv
      have hor : v = leftEnd G A B e ∨ v = rightEnd G A B e := by
        simpa only [← ends_edge G A B e, Sym2.mem_iff] using hve
      rcases hor with hl | hr
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_image.mpr ⟨e, he, hl.symm⟩, mem_compl.mp hv⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_image.mpr ⟨e, he, hr.symm⟩, mem_compl.mp hv⟩)
  have hsize : (L \ U).card = (R \ U).card := by
    have hL := card_inter_add_card_sdiff L U
    have hR := card_inter_add_card_sdiff R U
    rw [hLcore, hLcard] at hL
    rw [hRcore, hRcard] at hR
    omega
  refine ⟨L \ U, R \ U, hLR.mono sdiff_subset sdiff_subset, hsplit, hsize, ?_⟩
  intro e he
  apply (G.mem_cutEdges_iff (A ∪ L \ U) e).mpr
  refine ⟨leftEnd G A B e, rightEnd G A B e, (ends_edge G A B e).symm, ?_, ?_⟩
  · by_cases hu : leftEnd G A B e ∈ U
    · apply mem_union_left
      have hh : leftEnd G A B e ∈ A ∪ B := hunion.symm ▸ hu
      exact (mem_union.mp hh).resolve_right
        (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).1
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_image.mpr ⟨e, he, rfl⟩, hu⟩)
  · intro hv
    rcases mem_union.mp hv with ha | hl
    · exact (ends_avoid G U A B hAB hunion e (mem_compl.mp (houtside he))).2 ha
    · exact (disjoint_left.mp hLR) (mem_sdiff.mp hl).1 (mem_image.mpr ⟨e, he, rfl⟩)

/-- The bounded even footprint in the subtype used by the paired-cut
probability construction. -/
theorem matching_footprintSubtype_bounds (G : Multigraph V E) (U : Finset V)
    (M : Finset E) (hM : G.IsMatching M) (houtside : M ⊆ (G.internalEdges U)ᶜ)
    (hcover : ∀ z ∈ Uᶜ, ∃ e ∈ M, z ∈ G.edge e) (heven : Even Uᶜ.card) :
    Even (coreFootprintSubtype G U M).card ∧
      (coreFootprintSubtype G U M).card ≤ Uᶜ.card := by
  simpa only [coreFootprintSubtype_card] using
    matching_footprint_bounds G U M hM houtside hcover heven

/-- Subtype form of the exterior split: the core sides are precisely the
finite sets produced by the paired-cut construction. -/
theorem exists_balanced_exterior_split_subtype (G : Multigraph V E) (U : Finset V)
    (A B : Finset U) (M : Finset E) (hM : G.IsMatching M)
    (houtside : M ⊆ (G.internalEdges U)ᶜ)
    (hcover : ∀ z ∈ Uᶜ, ∃ e ∈ M, z ∈ G.edge e)
    (hAB : Disjoint A B) (hunion : A ∪ B = univ)
    (hbalance : (coreFootprintSubtype G U M ∩ A).card =
      (coreFootprintSubtype G U M ∩ B).card) :
    ∃ ZA ZB : Finset V, Disjoint ZA ZB ∧ ZA ∪ ZB = Uᶜ ∧ ZA.card = ZB.card ∧
      ∀ e ∈ M, e ∈ G.cutEdges
        (A.map (Function.Embedding.subtype (fun v => v ∈ U)) ∪ ZA) := by
  let emb := Function.Embedding.subtype (fun v => v ∈ U)
  have hdisj : Disjoint (A.map emb) (B.map emb) := (disjoint_map emb).mpr hAB
  have hcoverU : A.map emb ∪ B.map emb = U := by
    rw [← map_union, hunion]
    ext v
    simp only [mem_map, mem_univ, true_and, emb, Function.Embedding.subtype_apply]
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hv => ⟨⟨v, hv⟩, rfl⟩⟩
  have hbalance' : (coreFootprint G U M ∩ A.map emb).card =
      (coreFootprint G U M ∩ B.map emb).card := by
    rw [← coreFootprintSubtype_inter_card G U M A,
      ← coreFootprintSubtype_inter_card G U M B]
    exact hbalance
  exact exists_balanced_exterior_split G U (A.map emb) (B.map emb) M
    hM houtside hcover hdisj hcoverU hbalance'

end Overfull.BoundedExterior
