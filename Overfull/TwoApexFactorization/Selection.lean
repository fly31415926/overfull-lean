import Overfull.OneCore.Complement

/-!
# Selecting the exceptional copies at two apices

The selection retains every exceptional copy internal to the core, contains
the prescribed same-shore apex copies, and has the same prescribed degree
at both apices. All sets consist of actual original host copies.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E) (U A B : Finset V)

omit [Fintype V] in
private theorem edgesTo_mono (x : V) {S T : Finset V} (hST : S ⊆ T) :
    G.edgesTo x S ⊆ G.edgesTo x T := by
  intro e he
  exact (G.mem_edgesTo x T e).mpr
    ⟨((G.mem_edgesTo x S e).mp he).1, hST ((G.mem_edgesTo x S e).mp he).2⟩

omit [Fintype V] in
private theorem internal_endpoint {S : Finset V} {e : E}
    (he : e ∈ G.internalEdges S) {v : V} (hv : v ∈ G.edge e) : v ∈ S := by
  obtain ⟨hf, hs⟩ := (G.mem_internalEdges S e).mp he
  rcases (G.incident_iff e v).mp hv with h | h
  · exact h ▸ hf
  · exact h ▸ hs

omit [Fintype V] in
private theorem parallel_symm (x y : V) : G.parallelEdges x y = G.parallelEdges y x := by
  ext e
  constructor
  · intro he
    obtain ⟨hx, hy⟩ := (G.mem_parallelEdges x y e).mp he
    have hedge : G.edge e = s(y, x) := by
      rw [G.edge_eq_otherEnd x e hx, hy]
      exact Sym2.eq_swap
    exact (G.mem_parallelEdges y x e).mpr
      ⟨by simp [hedge], G.otherEnd_eq_of_edge e y x hedge⟩
  · intro he
    obtain ⟨hy, hx⟩ := (G.mem_parallelEdges y x e).mp he
    have hedge : G.edge e = s(x, y) := by
      rw [G.edge_eq_otherEnd y e hy, hx]
      exact Sym2.eq_swap
    exact (G.mem_parallelEdges x y e).mpr
      ⟨by simp [hedge], G.otherEnd_eq_of_edge e x y hedge⟩

private theorem outside_edgesTo (x y : V) (houtside : Uᶜ = {x, y}) :
    G.edgesTo x Uᶜ = G.parallelEdges x y := by
  ext e
  simp only [G.mem_edgesTo, G.mem_parallelEdges]
  constructor
  · rintro ⟨hx, hu⟩
    rw [houtside] at hu
    rcases Finset.mem_insert.mp hu with heq | heq
    · exact (G.otherEnd_ne x e hx heq).elim
    · exact ⟨hx, Finset.mem_singleton.mp heq⟩
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    rw [houtside, heq]
    simp

omit [Fintype V] in
private theorem other_apex_not_incident {x y : V} (hxy : x ≠ y) (hy : y ∉ U)
    {e : E} (he : e ∈ G.edgesTo x U) : y ∉ G.edge e := by
  obtain ⟨hx, hu⟩ := (G.mem_edgesTo x U e).mp he
  rw [G.edge_eq_otherEnd x e hx, Sym2.mem_iff]
  rintro (h | h)
  · exact hxy h.symm
  · exact hy (h ▸ hu)

omit [Fintype V] in
private theorem four_piece_incidence (x y : V) (hxy : x ≠ y) (hx : x ∉ U)
    (R Sx Sy Z : Finset E) (hR : R ⊆ G.internalEdges U)
    (hSx : Sx ⊆ G.edgesTo x U) (hSy : Sy ⊆ G.edgesTo y U)
    (hZ : Z ⊆ G.parallelEdges x y) :
    (R ∪ Sx ∪ Sy ∪ Z) ∩ G.incidenceEdges x = Sx ∪ Z := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_union, G.mem_incidenceEdges]
  constructor
  · rintro ⟨((he | he) | he) | he, hi⟩
    · exact (hx (internal_endpoint G (hR he) hi)).elim
    · exact Or.inl he
    · exact (other_apex_not_incident G U hxy.symm hx (hSy he) hi).elim
    · exact Or.inr he
  · intro he
    refine ⟨?_, ?_⟩
    · tauto
    · rcases he with he | he
      · exact ((G.mem_edgesTo x U e).mp (hSx he)).1
      · exact ((G.mem_parallelEdges x y e).mp (hZ he)).1

omit [Fintype V] in
private theorem four_piece_to_core (x y : V) (hxy : x ≠ y) (hx : x ∉ U)
    (hy : y ∉ U) (R Sx Sy Z : Finset E) (hR : R ⊆ G.internalEdges U)
    (hSx : Sx ⊆ G.edgesTo x U) (hSy : Sy ⊆ G.edgesTo y U)
    (hZ : Z ⊆ G.parallelEdges x y) :
    (R ∪ Sx ∪ Sy ∪ Z) ∩ G.edgesTo x U = Sx := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨((he | he) | he) | he, hi⟩
    · exact (hx (internal_endpoint G (hR he) ((G.mem_edgesTo x U e).mp hi).1)).elim
    · exact he
    · exact (other_apex_not_incident G U hxy.symm hx (hSy he)
        ((G.mem_edgesTo x U e).mp hi).1).elim
    · have hother := ((G.mem_parallelEdges x y e).mp (hZ he)).2
      have hin := ((G.mem_edgesTo x U e).mp hi).2
      exact (hy (hother ▸ hin)).elim
  · intro he
    exact ⟨Or.inl (Or.inl (Or.inr he)), hSx he⟩

omit [Fintype V] in
private theorem internal_insert_subset (x : V) {S : Finset V} (hS : S ⊆ U)
    {e : E} (he : e ∈ G.internalEdges (insert x S)) :
    e ∈ G.internalEdges U ∨ e ∈ G.edgesTo x S := by
  obtain ⟨hf, hs⟩ := (G.mem_internalEdges (insert x S) e).mp he
  rcases Finset.mem_insert.mp hf with hf | hf <;>
    rcases Finset.mem_insert.mp hs with hs | hs
  · exact (G.endpoints_distinct e (hf.trans hs.symm)).elim
  · right
    have hedge : G.edge e = s(x, G.secondEnd e) := by rw [← G.edge_eq e, hf]
    exact (G.mem_edgesTo x S e).mpr
      ⟨by simp [hedge], by rw [G.otherEnd_eq_of_edge e x (G.secondEnd e) hedge]; exact hs⟩
  · right
    have hedge : G.edge e = s(x, G.firstEnd e) := by
      rw [← G.edge_eq e, hs]
      exact Sym2.eq_swap
    exact (G.mem_edgesTo x S e).mpr
      ⟨by simp [hedge], by rw [G.otherEnd_eq_of_edge e x (G.firstEnd e) hedge]; exact hf⟩
  · exact Or.inl ((G.mem_internalEdges U e).mpr ⟨hS hf, hS hs⟩)

theorem augmented_shore_compl (x y : V) (hxy : x ≠ y)
    (houtside : Uᶜ = {x, y}) (hAB : Disjoint A B) (hunion : A ∪ B = U) :
    (insert x A)ᶜ = insert y B := by
  have hx : x ∉ U := by
    have : x ∈ Uᶜ := by rw [houtside]; simp
    exact Finset.mem_compl.mp this
  have hy : y ∉ U := by
    have : y ∈ Uᶜ := by rw [houtside]; simp
    exact Finset.mem_compl.mp this
  have hAU : A ⊆ U := hunion ▸ Finset.subset_union_left
  have hBU : B ⊆ U := hunion ▸ Finset.subset_union_right
  ext v
  simp only [Finset.mem_compl, Finset.mem_insert]
  constructor
  · intro hv
    by_cases hvU : v ∈ U
    · have hvAB : v ∈ A ∨ v ∈ B := by simpa only [← hunion, Finset.mem_union] using hvU
      exact Or.inr (hvAB.resolve_left (fun ha => hv (Or.inr ha)))
    · have hvout : v = x ∨ v = y := by
        have : v ∈ Uᶜ := Finset.mem_compl.mpr hvU
        simpa only [houtside, Finset.mem_insert, Finset.mem_singleton] using this
      exact Or.inl (hvout.resolve_left (fun heq => hv (Or.inl heq)))
  · rintro (rfl | hvB) (heq | hvA)
    · exact hxy heq.symm
    · exact hy (hAU hvA)
    · exact hx (heq ▸ hBU hvB)
    · exact Finset.disjoint_left.mp hAB hvA hvB

/-- The selected original copies and their exact incidence identities. -/
structure Selection (C : Core G U) (x y : V) (q : ℕ) where
  edges : Finset E
  xyCopies : Finset E
  subset_complement : edges ⊆ (OneCore.coreEdges C)ᶜ
  apex_degree_left : (G.restrictEdges edges).degree x = q
  apex_degree_right : (G.restrictEdges edges).degree y = q
  apex_core_left : ((G.restrictEdges edges).edgesTo x U).card =
    min q (G.edgesTo x U).card
  apex_core_right : ((G.restrictEdges edges).edgesTo y U).card =
    min q (G.edgesTo x U).card
  core_complement : G.internalEdges U \ OneCore.coreEdges C ⊆ edges
  same_shore_left : G.edgesTo x A ⊆ edges
  same_shore_right : G.edgesTo y B ⊆ edges
  xy_subset : xyCopies ⊆ G.parallelEdges x y
  xy_card : xyCopies.card = q - (G.edgesTo x U).card
  outside_eq : edges ∩ G.internalEdges Uᶜ = xyCopies
  remaining_exterior_cross : ∀ e, e ∉ edges → e ∉ OneCore.coreEdges C →
    e ∈ G.cutEdges (insert x A)

/-- The two apex-to-core incidence counts agree in a regular host. -/
theorem apex_core_counts_eq (x y : V) (k : ℕ) (houtside : Uᶜ = {x, y})
    (hregular : ∀ v, G.degree v = k) :
    (G.edgesTo x U).card = (G.edgesTo y U).card := by
  have hx := G.edgesTo_compl_card_add x U
  have hy := G.edgesTo_compl_card_add y U
  rw [outside_edgesTo G U x y houtside, hregular] at hx
  rw [outside_edgesTo G U y x (houtside.trans (Finset.pair_comm _ _)),
    ← parallel_symm G x y, hregular] at hy
  omega

/-- Select the actual exceptional copies while retaining every prescribed
same-shore copy. The two apices receive precisely `q` selected incidences. -/
theorem exists_selection (C : Core G U) (x y : V) (k q : ℕ)
    (hxy : x ≠ y) (houtside : Uᶜ = {x, y})
    (hAB : Disjoint A B) (hunion : A ∪ B = U)
    (hregular : ∀ v, G.degree v = k) (hq : q ≤ k)
    (hleft : (G.edgesTo x A).card ≤ q) (hright : (G.edgesTo y B).card ≤ q) :
    Nonempty (Selection G U A B C x y q) := by
  have hx : x ∉ U := by
    have : x ∈ Uᶜ := by rw [houtside]; simp
    exact Finset.mem_compl.mp this
  have hy : y ∉ U := by
    have : y ∈ Uᶜ := by rw [houtside]; simp
    exact Finset.mem_compl.mp this
  have hAU : A ⊆ U := hunion ▸ Finset.subset_union_left
  have hBU : B ⊆ U := hunion ▸ Finset.subset_union_right
  have hbalance := apex_core_counts_eq G U x y k houtside hregular
  let b := (G.edgesTo x U).card
  let u := min q b
  let t := q - b
  have hxsum : (G.parallelEdges x y).card + b = k := by
    simpa only [outside_edgesTo G U x y houtside, hregular] using
      G.edgesTo_compl_card_add x U
  have hleftU := edgesTo_mono G x hAU
  have hrightU := edgesTo_mono G y hBU
  have hleftu : (G.edgesTo x A).card ≤ u :=
    le_min hleft (Finset.card_le_card hleftU)
  have hrightu : (G.edgesTo y B).card ≤ u := by
    apply le_min hright
    exact (Finset.card_le_card hrightU).trans_eq hbalance.symm
  obtain ⟨Sx, hSxA, hSxU, hSxcard⟩ :=
    Finset.exists_subsuperset_card_eq hleftU hleftu (min_le_right q b)
  obtain ⟨Sy, hSyB, hSyU, hSycard⟩ :=
    Finset.exists_subsuperset_card_eq hrightU hrightu
      ((min_le_right q b).trans_eq hbalance)
  obtain ⟨Z, hZ, hZcard⟩ := Finset.exists_subset_card_eq
    (show t ≤ (G.parallelEdges x y).card by dsimp [t]; omega)
  let R := G.internalEdges U \ OneCore.coreEdges C
  let F := R ∪ Sx ∪ Sy ∪ Z
  have hR : R ⊆ G.internalEdges U := Finset.sdiff_subset
  have hZsymm : Z ⊆ G.parallelEdges y x := by rwa [← parallel_symm G x y]
  have hswap : F = R ∪ Sy ∪ Sx ∪ Z := by
    dsimp [F]
    ext e
    simp only [Finset.mem_union]
    tauto
  have hincx : F ∩ G.incidenceEdges x = Sx ∪ Z :=
    four_piece_incidence G U x y hxy hx R Sx Sy Z hR hSxU hSyU hZ
  have hincy : F ∩ G.incidenceEdges y = Sy ∪ Z := by
    rw [hswap]
    exact four_piece_incidence G U y x hxy.symm hy R Sy Sx Z hR hSyU hSxU hZsymm
  have htox : F ∩ G.edgesTo x U = Sx :=
    four_piece_to_core G U x y hxy hx hy R Sx Sy Z hR hSxU hSyU hZ
  have htoy : F ∩ G.edgesTo y U = Sy := by
    rw [hswap]
    exact four_piece_to_core G U y x hxy.symm hy hx R Sy Sx Z hR hSyU hSxU hZsymm
  have hdisjx : Disjoint Sx Z := by
    apply Finset.disjoint_left.mpr
    intro e he hz
    have hu := ((G.mem_edgesTo x U e).mp (hSxU he)).2
    have heq := ((G.mem_parallelEdges x y e).mp (hZ hz)).2
    exact hy (heq ▸ hu)
  have hdisjy : Disjoint Sy Z := by
    apply Finset.disjoint_left.mpr
    intro e he hz
    have hu := ((G.mem_edgesTo y U e).mp (hSyU he)).2
    have heq := ((G.mem_parallelEdges y x e).mp (hZsymm hz)).2
    exact hx (heq ▸ hu)
  have hRF : R ⊆ F := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he))
  have hSxF : Sx ⊆ F := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he))
  have hSyF : Sy ⊆ F := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
  have hZF : Z ⊆ F := Finset.subset_union_right
  refine ⟨{
    edges := F
    xyCopies := Z
    subset_complement := ?_
    apex_degree_left := ?_
    apex_degree_right := ?_
    apex_core_left := ?_
    apex_core_right := ?_
    core_complement := hRF
    same_shore_left := hSxA.trans hSxF
    same_shore_right := hSyB.trans hSyF
    xy_subset := hZ
    xy_card := hZcard
    outside_eq := ?_
    remaining_exterior_cross := ?_
  }⟩
  · intro e he
    apply Finset.mem_compl.mpr
    intro hc
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with he | he
        · exact (Finset.mem_sdiff.mp he).2 hc
        · exact hx (OneCore.coreEdges_endpoint C hc ((G.mem_edgesTo x U e).mp (hSxU he)).1)
      · exact hy (OneCore.coreEdges_endpoint C hc ((G.mem_edgesTo y U e).mp (hSyU he)).1)
    · exact hx (OneCore.coreEdges_endpoint C hc ((G.mem_parallelEdges x y e).mp (hZ he)).1)
  · rw [G.restrictEdges_degree, hincx, Finset.card_union_of_disjoint hdisjx,
      hSxcard, hZcard]
    dsimp [u, t]
    omega
  · rw [G.restrictEdges_degree, hincy, Finset.card_union_of_disjoint hdisjy,
      hSycard, hZcard]
    dsimp [u, t]
    omega
  · rw [G.restrictEdges_edgesTo_card, htox, hSxcard]
  · rw [G.restrictEdges_edgesTo_card, htoy, hSycard]
  · ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨he, hout⟩
      have hno (v : V) (hv : v ∈ G.edge e) : v ∉ U :=
        Finset.mem_compl.mp (internal_endpoint G hout hv)
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with he | he
        · rcases Finset.mem_union.mp he with he | he
          · have hf := ((G.mem_internalEdges U e).mp (hR he)).1
            exact (hno (G.firstEnd e) ((G.incident_iff e _).mpr (Or.inl rfl)) hf).elim
          · obtain ⟨hi, hu⟩ := (G.mem_edgesTo x U e).mp (hSxU he)
            exact (hno (G.otherEnd x e) (by rw [G.edge_eq_otherEnd x e hi]; simp) hu).elim
        · obtain ⟨hi, hu⟩ := (G.mem_edgesTo y U e).mp (hSyU he)
          exact (hno (G.otherEnd y e) (by rw [G.edge_eq_otherEnd y e hi]; simp) hu).elim
      · exact he
    · intro he
      refine ⟨hZF he, ?_⟩
      obtain ⟨hi, heq⟩ := (G.mem_parallelEdges x y e).mp (hZ he)
      have hedge : G.edge e = s(x, y) := by rw [G.edge_eq_otherEnd x e hi, heq]
      exact (G.internalEdges_iff_of_edge e x y hedge Uᶜ).mpr
        ⟨Finset.mem_compl.mpr hx, Finset.mem_compl.mpr hy⟩
  · intro e he hc
    by_contra hcross
    have hsame : (G.firstEnd e ∈ insert x A) = (G.secondEnd e ∈ insert x A) := by
      simpa only [G.mem_cutEdges, not_not] using hcross
    have hhandle {z : V} {S : Finset V} (hSU : S ⊆ U)
        (hselected : G.edgesTo z S ⊆ F)
        (hin : e ∈ G.internalEdges (insert z S)) : False := by
      rcases internal_insert_subset G U z hSU hin with hin | hin
      · exact he (hRF (Finset.mem_sdiff.mpr ⟨hin, hc⟩))
      · exact he (hselected hin)
    by_cases hf : G.firstEnd e ∈ insert x A
    · apply hhandle hAU (hSxA.trans hSxF)
      exact (G.mem_internalEdges (insert x A) e).mpr ⟨hf, hsame ▸ hf⟩
    · apply hhandle hBU (hSyB.trans hSyF)
      rw [← augmented_shore_compl U A B x y hxy houtside hAB hunion]
      exact (G.mem_internalEdges (insert x A)ᶜ e).mpr
        ⟨Finset.mem_compl.mpr hf, Finset.mem_compl.mpr (hsame ▸ hf)⟩

namespace Selection

variable {G U A B} {C : Core G U} {x y : V} {q : ℕ}

/-- Every selected core incidence is an incidence of the original exceptional
complement, so any previously established error bound is inherited. -/
theorem degree_le_complement (S : Selection G U A B C x y q) (v : V) :
    (G.restrictEdges S.edges).degree v ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v :=
  G.restrictEdges_degree_mono S.subset_complement v

/-- The selected copies wholly outside the core are exactly the selected
apex--apex copies, with their original multiplicities. -/
theorem outside_card (S : Selection G U A B C x y q) :
    (S.edges ∩ G.internalEdges Uᶜ).card = q - (G.edgesTo x U).card := by
  rw [S.outside_eq, S.xy_card]

/-- The selected graph uses every exceptional internal core copy and no
specified simple-core copy. -/
theorem internal_eq (S : Selection G U A B C x y q) :
    S.edges ∩ G.internalEdges U = G.internalEdges U \ OneCore.coreEdges C := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hu⟩
    exact ⟨hu, Finset.mem_compl.mp (S.subset_complement he)⟩
  · rintro ⟨hu, hc⟩
    exact ⟨S.core_complement (Finset.mem_sdiff.mpr ⟨hu, hc⟩), hu⟩

/-- Every original simple-core copy survives the selection. -/
theorem core_survives (S : Selection G U A B C x y q) :
    OneCore.coreEdges C ⊆ S.edgesᶜ := by
  intro e he
  apply Finset.mem_compl.mpr
  intro hs
  exact Finset.mem_compl.mp (S.subset_complement hs) he

/-- After selection, the internal graph is exactly the original embedded
simple core, at the level of its actual host copies. -/
theorem remaining_internal_eq (S : Selection G U A B C x y q) :
    S.edgesᶜ ∩ G.internalEdges U = OneCore.coreEdges C := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_compl]
  constructor
  · rintro ⟨he, hu⟩
    by_contra hc
    exact he (S.core_complement (Finset.mem_sdiff.mpr ⟨hu, hc⟩))
  · intro hc
    exact ⟨Finset.mem_compl.mp (S.core_survives hc), OneCore.coreEdges_subset_internal C hc⟩

/-- Every surviving copy crosses the specified augmented shore whenever the
original simple core does. -/
theorem remaining_cross (S : Selection G U A B C x y q)
    (hcore : ∀ e ∈ OneCore.coreEdges C, e ∈ G.cutEdges (insert x A))
    {e : E} (he : e ∉ S.edges) : e ∈ G.cutEdges (insert x A) := by
  by_cases hc : e ∈ OneCore.coreEdges C
  · exact hcore e hc
  · exact S.remaining_exterior_cross e he hc

/-- The actual complementary graph has the explicitly specified bipartition,
not merely an abstract witness that some bipartition exists. -/
theorem remaining_side (S : Selection G U A B C x y q)
    (hcore : ∀ e ∈ OneCore.coreEdges C, e ∈ G.cutEdges (insert x A))
    (e : (S.edgesᶜ : Finset E)) :
    decide ((G.restrictEdges S.edgesᶜ).firstEnd e ∈ insert x A) ≠
      decide ((G.restrictEdges S.edgesᶜ).secondEnd e ∈ insert x A) := by
  have hc := (G.mem_cutEdges (insert x A) e.val).mp
    (S.remaining_cross hcore (Finset.mem_compl.mp e.property))
  change decide (G.firstEnd e.val ∈ insert x A) ≠
    decide (G.secondEnd e.val ∈ insert x A)
  simpa only [ne_eq, decide_eq_decide, eq_iff_iff] using hc

/-- The actual graph of unselected copies is bipartite on the augmented
shore `insert x A`. -/
theorem remaining_bipartite (S : Selection G U A B C x y q)
    (hcore : ∀ e ∈ OneCore.coreEdges C, e ∈ G.cutEdges (insert x A)) :
    (G.restrictEdges S.edgesᶜ).IsBipartite :=
  ⟨fun v => decide (v ∈ insert x A), S.remaining_side hcore⟩

end Selection

end Overfull.TwoApexFactorization
