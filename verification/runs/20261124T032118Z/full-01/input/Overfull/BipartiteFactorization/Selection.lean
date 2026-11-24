import Overfull.BipartiteFactorization.Capacity

/-!
# Filling exceptional demands with actual preferred copies

Every row is selected from the unused copies joining its exceptional
vertex to its preferred core block. Distinct exceptional vertices have
disjoint rows, even when the ambient graph has parallel copies.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.PreferredSelection

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

omit [Fintype V] in
theorem outside_source (U : Finset V) (x y : V) (e : E)
    (hy : y ∉ U) (he : e ∈ G.edgesTo x U) (hye : y ∈ G.edge e) : y = x := by
  obtain ⟨hxe, hxU⟩ := (G.mem_edgesTo x U e).mp he
  rw [G.edge_eq_otherEnd x e hxe] at hye
  rcases Sym2.mem_iff.mp hye with h | h
  · exact h
  · exact False.elim (hy (h.symm ▸ hxU))

omit [Fintype V] in
theorem edgesTo_mono {X Y : Finset V} (hXY : X ⊆ Y) (x : V) :
    G.edgesTo x X ⊆ G.edgesTo x Y := by
  intro e he
  obtain ⟨hx, hX⟩ := (G.mem_edgesTo x X e).mp he
  exact (G.mem_edgesTo x Y e).mpr ⟨hx, hXY hX⟩

omit [Fintype V] in
theorem internal_incident (X : Finset V) (e : E) (x : V)
    (he : e ∈ G.internalEdges X) (hx : x ∈ G.edge e) : x ∈ X :=
  ((G.internalEdges_iff_of_edge e x (G.otherEnd x e)
    (G.edge_eq_otherEnd x e hx) X).mp he).1

omit [Fintype V] in
theorem pool_outside_incidence (U W Z : Finset V) (hWU : W ⊆ U)
    (x : V) (hx : x ∉ U) (e : E)
    (he : e ∈ G.internalEdges W ∪ Z.biUnion (fun y => G.edgesTo y W))
    (hxe : x ∈ G.edge e) : x ∈ Z ∧ e ∈ G.edgesTo x U := by
  rcases Finset.mem_union.mp he with he | he
  · exact False.elim (hx (hWU (internal_incident G W e x he hxe)))
  · obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp he
    have heyU := edgesTo_mono G hWU y hey
    have hxy := outside_source G U y x e hx heyU hxe
    subst x
    exact ⟨hy, heyU⟩

omit [Fintype V] in
theorem pool_core_incidence (U W Z : Finset V) (hUZ : Disjoint U Z)
    (x : V) (hx : x ∈ U) (e : E)
    (he : e ∈ G.internalEdges W ∪ Z.biUnion (fun y => G.edgesTo y W))
    (hxe : x ∈ G.edge e) : x ∈ W := by
  rcases Finset.mem_union.mp he with he | he
  · exact internal_incident G W e x he hxe
  · obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hye, hyW⟩ := (G.mem_edgesTo y W e).mp hey
    rw [G.edge_eq_otherEnd y e hye] at hxe
    rcases Sym2.mem_iff.mp hxe with hxy | hxy
    · exact False.elim ((Finset.disjoint_left.mp hUZ) (hxy ▸ hx) hy)
    · exact hxy.symm ▸ hyW

omit [Fintype V] in
theorem degree_union (F H : Finset E) (hFH : Disjoint F H) (x : V) :
    (G.restrictEdges (F ∪ H)).degree x =
      (G.restrictEdges F).degree x + (G.restrictEdges H).degree x := by
  simp only [G.restrictEdges_degree, Finset.union_inter_distrib_right]
  exact Finset.card_union_of_disjoint
    (hFH.mono Finset.inter_subset_left Finset.inter_subset_left)

omit [Fintype V] in
theorem degree_zero (F : Finset E) (x : V)
    (h : ∀ e ∈ F, x ∉ G.edge e) : (G.restrictEdges F).degree x = 0 := by
  rw [G.restrictEdges_degree, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heF, hex⟩ := Finset.mem_inter.mp he
  exact h e heF ((G.mem_incidenceEdges x e).mp hex)

theorem internal_base_disjoint (U Z W : Finset V) (hWU : W ⊆ U)
    (F C : Finset E) (hF : F ⊆ G.internalEdges Uᶜ)
    (hC : C ⊆ G.internalEdges W ∪ Z.biUnion (fun x => G.edgesTo x W)) :
    Disjoint F C := by
  apply Finset.disjoint_left.mpr
  intro e heF heC
  have hboth := (G.mem_internalEdges Uᶜ e).mp (hF heF)
  rcases Finset.mem_union.mp (hC heC) with he | he
  · exact (Finset.mem_compl.mp hboth.1) (hWU ((G.mem_internalEdges W e).mp he).1)
  · obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hxe, hxW⟩ := (G.mem_edgesTo x W e).mp hex
    have ho := ((G.internalEdges_iff_of_edge e x (G.otherEnd x e)
      (G.edge_eq_otherEnd x e hxe) Uᶜ).mp (hF heF)).2
    exact (Finset.mem_compl.mp ho) (hWU hxW)

omit [Fintype V] in
/-- Simultaneously choose every preferred row. Their distinct outside
ends prove disjointness on actual edge copies. -/
theorem exists_rows (U Z : Finset V) (hUZ : Disjoint U Z)
    (P : Z → Finset V) (hP : ∀ x, P x ⊆ U)
    (D : Finset E) (n : Z → ℕ)
    (hsupply : ∀ x, n x ≤ (G.edgesTo x.val (P x) \ D).card) :
    ∃ M : Z → Finset E,
      (∀ x, M x ⊆ G.edgesTo x.val (P x) \ D) ∧
      (∀ x, (M x).card = n x) ∧
      (∀ x y, x ≠ y → Disjoint (M x) (M y)) := by
  have hex (x : Z) : ∃ M : Finset E,
      M ⊆ G.edgesTo x.val (P x) \ D ∧ M.card = n x :=
    Finset.exists_subset_card_eq (hsupply x)
  choose M hM hcard using hex
  refine ⟨M, hM, hcard, ?_⟩
  intro x y hxy
  apply Finset.disjoint_left.mpr
  intro e hex hey
  have hx := (Finset.mem_sdiff.mp (hM x hex)).1
  have hy := (Finset.mem_sdiff.mp (hM y hey)).1
  have hye := ((G.mem_edgesTo y.val (P y) e).mp hy).1
  have hyU : y.val ∉ U := fun hyU => (Finset.disjoint_left.mp hUZ) hyU y.property
  exact hxy (Subtype.ext (outside_source G U x.val y.val e hyU
    (edgesTo_mono G (hP x) x.val hx) hye).symm)

omit [Fintype V] in
theorem rows_degree (U Z : Finset V) (P : Z → Finset V)
    (hP : ∀ x, P x ⊆ U) (M : Z → Finset E)
    (hM : ∀ x, M x ⊆ G.edgesTo x.val (P x))
    (x : V) (hx : x ∉ U) :
    (G.restrictEdges (univ.biUnion M)).degree x =
      if hxZ : x ∈ Z then (M ⟨x, hxZ⟩).card else 0 := by
  rw [G.restrictEdges_degree]
  split_ifs with hxZ
  · congr 1
    ext e
    constructor
    · intro he
      obtain ⟨heM, hex⟩ := Finset.mem_inter.mp he
      obtain ⟨y, _, hey⟩ := Finset.mem_biUnion.mp heM
      have hxy := outside_source G U y.val x e hx
        (edgesTo_mono G (hP y) y.val (hM y hey))
        ((G.mem_incidenceEdges x e).mp hex)
      have hyx : y = (⟨x, hxZ⟩ : Z) := Subtype.ext hxy.symm
      simpa only [hyx] using hey
    · intro he
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
        ⟨⟨x, hxZ⟩, Finset.mem_univ _, he⟩,
        (G.mem_incidenceEdges x e).mpr
          (((G.mem_edgesTo x (P ⟨x, hxZ⟩) e).mp (hM _ he)).1)⟩
  · rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heM, hex⟩ := Finset.mem_inter.mp he
    obtain ⟨y, _, hey⟩ := Finset.mem_biUnion.mp heM
    have hxy := outside_source G U y.val x e hx
      (edgesTo_mono G (hP y) y.val (hM y hey))
      ((G.mem_incidenceEdges x e).mp hex)
    exact hxZ (hxy.symm ▸ y.property)

/-- Fill every residual exceptional demand from its unused preferred
row, while retaining an arbitrary exceptional-internal base. The
correction copies are supplied separately and need not be independent
of the deleted set. -/
theorem exists_filled_exterior (U W Z : Finset V)
    (hWU : W ⊆ U) (hUZ : Disjoint U Z)
    (P : Z → Finset V) (hP : ∀ x, P x ⊆ U)
    (R₀ C D : Finset E) (r : V → ℕ)
    (hbase : R₀ ⊆ G.internalEdges Uᶜ)
    (hC : C ⊆ G.internalEdges W ∪ Z.biUnion (fun x => G.edgesTo x W))
    (hCD : Disjoint C D)
    (hCP : ∀ x : Z, Disjoint C (G.edgesTo x.val (P x)))
    (hcap : ∀ x : Z, (G.restrictEdges C).degree x.val ≤ r x.val)
    (hzero : ∀ x, x ∉ U → x ∉ Z → r x = 0)
    (hsupply : ∀ x : Z, r x.val - (G.restrictEdges C).degree x.val ≤
      (G.edgesTo x.val (P x) \ D).card) :
    ∃ F : Finset E,
      R₀ ⊆ F ∧ C ⊆ F ∧
      F ⊆ (R₀ ∪ C) ∪ univ.biUnion (fun x : Z => G.edgesTo x.val (P x)) ∧
      Disjoint (F \ R₀) D ∧
      (∀ x, x ∉ U → (G.restrictEdges F).degree x =
        (G.restrictEdges R₀).degree x + r x) ∧
      (∀ x, x ∉ U → (F ∩ G.edgesTo x U).card = r x) ∧
      (∀ x ∈ U, x ∉ W ∪ univ.biUnion P → (G.restrictEdges F).degree x = 0) ∧
      F ∩ G.internalEdges Uᶜ = R₀ := by
  obtain ⟨M, hM, hMcard, _hMpairwise⟩ := exists_rows G U Z hUZ P hP D
    (fun x => r x.val - (G.restrictEdges C).degree x.val) hsupply
  let Mtot := univ.biUnion M
  have hMP (x : Z) : M x ⊆ G.edgesTo x.val (P x) :=
    (hM x).trans Finset.sdiff_subset
  have hMU : Mtot ⊆ Z.biUnion (fun x => G.edgesTo x U) := by
    intro e he
    obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨x.val, x.property,
      edgesTo_mono G (hP x) x.val (hMP x hex)⟩
  have hMC : Disjoint C Mtot := by
    apply Finset.disjoint_left.mpr
    intro e heC heM
    obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp heM
    exact (Finset.disjoint_left.mp (hCP x)) heC (hMP x hex)
  have hMD : Disjoint Mtot D := by
    apply Finset.disjoint_left.mpr
    intro e heM heD
    obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp heM
    exact (Finset.mem_sdiff.mp (hM x hex)).2 heD
  have hCMpool : C ∪ Mtot ⊆
      G.internalEdges U ∪ Z.biUnion (fun x => G.edgesTo x U) := by
    intro e he
    rcases Finset.mem_union.mp he with heC | heM
    · rcases Finset.mem_union.mp (hC heC) with heW | heZ
      · apply Finset.mem_union_left
        exact (G.mem_internalEdges U e).mpr
          ⟨hWU ((G.mem_internalEdges W e).mp heW).1,
            hWU ((G.mem_internalEdges W e).mp heW).2⟩
      · apply Finset.mem_union_right
        obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heZ
        exact Finset.mem_biUnion.mpr ⟨x, hx, edgesTo_mono G hWU x hex⟩
    · exact Finset.mem_union_right _ (hMU heM)
  have hbaseCM : Disjoint R₀ (C ∪ Mtot) :=
    internal_base_disjoint G U Z U (Subset.refl _) R₀ (C ∪ Mtot) hbase hCMpool
  have hinternalCM : Disjoint (G.internalEdges Uᶜ) (C ∪ Mtot) :=
    internal_base_disjoint G U Z U (Subset.refl _) (G.internalEdges Uᶜ)
      (C ∪ Mtot) (Subset.refl _) hCMpool
  have hCMdegree (x : V) (hx : x ∉ U) :
      (G.restrictEdges (C ∪ Mtot)).degree x = r x := by
    rw [degree_union G C Mtot hMC x, rows_degree G U Z P hP M hMP x hx]
    by_cases hxZ : x ∈ Z
    · simp only [dif_pos hxZ, hMcard]
      exact Nat.add_sub_of_le (hcap ⟨x, hxZ⟩)
    · simp only [dif_neg hxZ, add_zero, hzero x hx hxZ]
      apply degree_zero G C x
      intro e he hxe
      exact hxZ (pool_outside_incidence G U W Z hWU x hx e (hC he) hxe).1
  let F := R₀ ∪ (C ∪ Mtot)
  refine ⟨F, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · intro e he
    rcases Finset.mem_union.mp he with he₀ | heCM
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ he₀)
    · rcases Finset.mem_union.mp heCM with heC | heM
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ heC)
      · apply Finset.mem_union_right
        obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heM
        exact Finset.mem_biUnion.mpr ⟨x, hx, hMP x hex⟩
  · apply Finset.disjoint_left.mpr
    intro e he heD
    obtain ⟨heF, he₀⟩ := Finset.mem_sdiff.mp he
    rcases Finset.mem_union.mp heF with heR | heCM
    · exact he₀ heR
    · rcases Finset.mem_union.mp heCM with heC | heM
      · exact (Finset.disjoint_left.mp hCD) heC heD
      · exact (Finset.disjoint_left.mp hMD) heM heD
  · intro x hx
    rw [degree_union G R₀ (C ∪ Mtot) hbaseCM x, hCMdegree x hx]
  · intro x hx
    rw [← hCMdegree x hx, G.restrictEdges_degree]
    congr 1
    ext e
    constructor
    · intro he
      obtain ⟨heF, hex⟩ := Finset.mem_inter.mp he
      obtain ⟨hxe, hoU⟩ := (G.mem_edgesTo x U e).mp hex
      rcases Finset.mem_union.mp heF with he₀ | heCM
      · have ho := ((G.internalEdges_iff_of_edge e x (G.otherEnd x e)
          (G.edge_eq_otherEnd x e hxe) Uᶜ).mp (hbase he₀)).2
        exact False.elim ((Finset.mem_compl.mp ho) hoU)
      · exact Finset.mem_inter.mpr ⟨heCM, (G.mem_incidenceEdges x e).mpr hxe⟩
    · intro he
      obtain ⟨heCM, hex⟩ := Finset.mem_inter.mp he
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ heCM,
        (pool_outside_incidence G U U Z (Subset.refl _) x hx e
          (hCMpool heCM) ((G.mem_incidenceEdges x e).mp hex)).2⟩
  · intro x hx hxW
    apply degree_zero G F x
    intro e he hxe
    rcases Finset.mem_union.mp he with he₀ | heCM
    · exact (Finset.mem_compl.mp (internal_incident G Uᶜ e x (hbase he₀) hxe)) hx
    · rcases Finset.mem_union.mp heCM with heC | heM
      · exact hxW (Finset.mem_union_left _
          (pool_core_incidence G U W Z hUZ x hx e (hC heC) hxe))
      · obtain ⟨y, _, hey⟩ := Finset.mem_biUnion.mp heM
        obtain ⟨hye, hyP⟩ := (G.mem_edgesTo y.val (P y) e).mp (hMP y hey)
        rw [G.edge_eq_otherEnd y.val e hye] at hxe
        rcases Sym2.mem_iff.mp hxe with hxy | hxy
        · exact (Finset.disjoint_left.mp hUZ) (hxy ▸ hx) y.property
        · exact hxW (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hxy.symm ▸ hyP⟩))
  · ext e
    constructor
    · intro he
      obtain ⟨heF, heI⟩ := Finset.mem_inter.mp he
      rcases Finset.mem_union.mp heF with he₀ | heCM
      · exact he₀
      · exact False.elim ((Finset.disjoint_left.mp hinternalCM) heI heCM)
    · exact fun he => Finset.mem_inter.mpr ⟨Finset.mem_union_left _ he, hbase he⟩

omit [Fintype V] in
theorem row_disjoint_pool (U W Z P : Finset V) (hWU : W ⊆ U)
    (x : V) (hx : x ∉ U) (h : x ∉ Z ∨ Disjoint P W) :
    Disjoint (G.edgesTo x P)
      (G.internalEdges W ∪ Z.biUnion (fun y => G.edgesTo y W)) := by
  apply Finset.disjoint_left.mpr
  intro e heP heC
  obtain ⟨hxe, hoP⟩ := (G.mem_edgesTo x P e).mp heP
  obtain ⟨hxZ, heW⟩ := pool_outside_incidence G W W Z (Subset.refl _) x
    (fun hxW => hx (hWU hxW)) e heC hxe
  rcases h with hxZ' | hPW
  · exact hxZ' hxZ
  · exact (Finset.disjoint_left.mp hPW) hoP ((G.mem_edgesTo x W e).mp heW).2

omit [Fintype V] in
theorem pools_disjoint (U W T Z Y : Finset V) (hWU : W ⊆ U)
    (hUY : Disjoint U Y) (hWT : Disjoint W T) :
    Disjoint (G.internalEdges W ∪ Z.biUnion (fun x => G.edgesTo x W))
      (G.internalEdges T ∪ Y.biUnion (fun x => G.edgesTo x T)) := by
  apply Finset.disjoint_left.mpr
  intro e heW heT
  rcases Finset.mem_union.mp heW with heW | heZ
  · have hxW := ((G.mem_internalEdges W e).mp heW).1
    have hxT := pool_core_incidence G U T Y hUY (G.firstEnd e) (hWU hxW) e heT
      (by rw [(G.edge_eq e).symm]; simp)
    exact (Finset.disjoint_left.mp hWT) hxW hxT
  · obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp heZ
    obtain ⟨hxe, hoW⟩ := (G.mem_edgesTo x W e).mp hex
    have hoT := pool_core_incidence G U T Y hUY (G.otherEnd x e) (hWU hoW) e heT
      (by rw [G.edge_eq_otherEnd x e hxe]; simp)
    exact (Finset.disjoint_left.mp hWT) hoW hoT

end Overfull.BipartiteFactorization.PreferredSelection

namespace Overfull.BipartiteFactorization

open Finset Classical PreferredSelection

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The deterministic selection for one palette. Corrections lie in the
positive pool, and each active exceptional vertex receives its remaining
demand from its preferred block. The two correction-pool intersections
record precisely which copies can be charged to later capacity loss. -/
theorem exists_preferred_selected_graph
    (A B ZA ZB Ablock Bblock : Finset V)
    (hAB : Disjoint A B) (hZA : Disjoint ZA (A ∪ B))
    (hZB : Disjoint ZB (A ∪ B)) (hZZ : Disjoint ZA ZB)
    (hAblock : Ablock ⊆ A) (hBblock : Bblock ⊆ B)
    (R₀ C D : Finset E) (r : V → ℕ)
    (hbase : R₀ ⊆ G.internalEdges (A ∪ B)ᶜ)
    (hC : C ⊆ G.internalEdges Bblock ∪ ZA.biUnion (fun x => G.edgesTo x Bblock))
    (hCD : Disjoint C D)
    (hcap : ∀ x ∈ ZA, (G.restrictEdges C).degree x ≤ r x)
    (hzero : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB → r x = 0)
    (hsupplyA : ∀ x ∈ ZA, r x - (G.restrictEdges C).degree x ≤
      (G.edgesTo x Ablock \ D).card)
    (hsupplyB : ∀ x ∈ ZB, r x ≤ (G.edgesTo x Bblock \ D).card) :
    ∃ F : Finset E,
      R₀ ⊆ F ∧ C ⊆ F ∧
      F ⊆ (R₀ ∪ C) ∪
        (ZA.biUnion (fun x => G.edgesTo x Ablock) ∪
          ZB.biUnion (fun x => G.edgesTo x Bblock)) ∧
      Disjoint (F \ R₀) D ∧
      (∀ x, x ∉ A ∪ B → (G.restrictEdges F).degree x =
        (G.restrictEdges R₀).degree x + r x) ∧
      (∀ x, x ∉ A ∪ B → (F ∩ G.edgesTo x (A ∪ B)).card = r x) ∧
      (∀ x ∈ A ∪ B, x ∉ Ablock ∪ Bblock → (G.restrictEdges F).degree x = 0) ∧
      F ∩ G.internalEdges (A ∪ B)ᶜ = R₀ ∧
      F ∩ (G.internalEdges B ∪ ZA.biUnion (fun x => G.edgesTo x B)) = C ∧
      F ∩ (G.internalEdges A ∪ ZB.biUnion (fun x => G.edgesTo x A)) = ∅ := by
  let U := A ∪ B
  let Z := ZA ∪ ZB
  let P : Z → Finset V := fun x => if x.val ∈ ZA then Ablock else Bblock
  have hAU : A ⊆ U := Finset.subset_union_left
  have hBU : B ⊆ U := Finset.subset_union_right
  have hAW : Ablock ⊆ U := hAblock.trans hAU
  have hBW : Bblock ⊆ U := hBblock.trans hBU
  have hUZ : Disjoint U Z := Finset.disjoint_union_right.mpr ⟨hZA.symm, hZB.symm⟩
  have hxU (x : Z) : x.val ∉ U :=
    fun hx => (Finset.disjoint_left.mp hUZ) hx x.property
  have hP (x : Z) : P x ⊆ U := by
    dsimp only [P]
    split_ifs
    · exact hAW
    · exact hBW
  have hCzero (x : V) (hx : x ∉ U) (hxA : x ∉ ZA) :
      (G.restrictEdges C).degree x = 0 := by
    apply degree_zero G C x
    intro e he hxe
    exact hxA (pool_outside_incidence G U Bblock ZA hBW x hx e (hC he) hxe).1
  have hCbig : C ⊆ G.internalEdges Bblock ∪ Z.biUnion (fun x => G.edgesTo x Bblock) := by
    intro e he
    rcases Finset.mem_union.mp (hC he) with heB | heZ
    · exact Finset.mem_union_left _ heB
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heZ
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left _ hx, hex⟩)
  have hCP (x : Z) : Disjoint C (G.edgesTo x.val (P x)) := by
    apply Disjoint.mono hC (Subset.refl _)
    apply Disjoint.symm
    apply row_disjoint_pool G U Bblock ZA (P x) hBW x.val (hxU x)
    by_cases hxA : x.val ∈ ZA
    · right
      simpa only [P, if_pos hxA] using hAB.mono hAblock hBblock
    · exact Or.inl hxA
  have hcaps (x : Z) : (G.restrictEdges C).degree x.val ≤ r x.val := by
    by_cases hxA : x.val ∈ ZA
    · exact hcap x.val hxA
    · rw [hCzero x.val (hxU x) hxA]
      exact Nat.zero_le _
  have hsupply (x : Z) : r x.val - (G.restrictEdges C).degree x.val ≤
      (G.edgesTo x.val (P x) \ D).card := by
    by_cases hxA : x.val ∈ ZA
    · simpa only [P, if_pos hxA] using hsupplyA x.val hxA
    · have hxB : x.val ∈ ZB := (Finset.mem_union.mp x.property).resolve_left hxA
      simpa only [P, if_neg hxA, hCzero x.val (hxU x) hxA, Nat.sub_zero] using
        hsupplyB x.val hxB
  obtain ⟨F, h₀F, hCF, hFsub, hFD, hdegree, hdemand, hsupport, hinternal⟩ :=
    exists_filled_exterior G U Bblock Z hBW hUZ P hP R₀ C D r hbase hCbig hCD
      hCP hcaps hzero hsupply
  let Q := ZA.biUnion (fun x => G.edgesTo x Ablock) ∪
    ZB.biUnion (fun x => G.edgesTo x Bblock)
  have hPQ : univ.biUnion (fun x : Z => G.edgesTo x.val (P x)) ⊆ Q := by
    intro e he
    obtain ⟨x, _, hex⟩ := Finset.mem_biUnion.mp he
    by_cases hxA : x.val ∈ ZA
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨x.val, hxA, by simpa only [P, if_pos hxA] using hex⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x.val,
        (Finset.mem_union.mp x.property).resolve_left hxA,
        by simpa only [P, if_neg hxA] using hex⟩
  have hFQ : F ⊆ (R₀ ∪ C) ∪ Q :=
    hFsub.trans (Finset.union_subset_union (Subset.refl _) hPQ)
  let Plus := G.internalEdges B ∪ ZA.biUnion (fun x => G.edgesTo x B)
  let Minus := G.internalEdges A ∪ ZB.biUnion (fun x => G.edgesTo x A)
  have hCplus : C ⊆ Plus := by
    intro e he
    rcases Finset.mem_union.mp (hC he) with heB | heZ
    · exact Finset.mem_union_left _ ((G.mem_internalEdges B e).mpr
        ⟨hBblock ((G.mem_internalEdges Bblock e).mp heB).1,
          hBblock ((G.mem_internalEdges Bblock e).mp heB).2⟩)
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heZ
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨x, hx, PreferredSelection.edgesTo_mono G hBblock x hex⟩)
  have h₀plus : Disjoint R₀ Plus :=
    internal_base_disjoint G U ZA B hBU R₀ Plus hbase (Subset.refl _)
  have h₀minus : Disjoint R₀ Minus :=
    internal_base_disjoint G U ZB A hAU R₀ Minus hbase (Subset.refl _)
  have hCminus : Disjoint C Minus :=
    (pools_disjoint G U B A ZA ZB hBU hZB.symm hAB.symm).mono hCplus (Subset.refl _)
  have hQplus : Disjoint Q Plus := by
    apply Finset.disjoint_left.mpr
    intro e heQ heP
    rcases Finset.mem_union.mp heQ with heA | heB
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heA
      have hxout : x ∉ U := fun hxU => (Finset.disjoint_left.mp hZA) hx hxU
      exact (Finset.disjoint_left.mp (row_disjoint_pool G U B ZA Ablock hBU x hxout
        (Or.inr (hAB.mono_left hAblock)))) hex heP
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heB
      have hxout : x ∉ U := fun hxU => (Finset.disjoint_left.mp hZB) hx hxU
      have hxA : x ∉ ZA := fun hxA => (Finset.disjoint_left.mp hZZ) hxA hx
      exact (Finset.disjoint_left.mp (row_disjoint_pool G U B ZA Bblock hBU x hxout
        (Or.inl hxA))) hex heP
  have hQminus : Disjoint Q Minus := by
    apply Finset.disjoint_left.mpr
    intro e heQ heP
    rcases Finset.mem_union.mp heQ with heA | heB
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heA
      have hxout : x ∉ U := fun hxU => (Finset.disjoint_left.mp hZA) hx hxU
      have hxB : x ∉ ZB := fun hxB => (Finset.disjoint_left.mp hZZ) hx hxB
      exact (Finset.disjoint_left.mp (row_disjoint_pool G U A ZB Ablock hAU x hxout
        (Or.inl hxB))) hex heP
    · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heB
      have hxout : x ∉ U := fun hxU => (Finset.disjoint_left.mp hZB) hx hxU
      exact (Finset.disjoint_left.mp (row_disjoint_pool G U A ZB Bblock hAU x hxout
        (Or.inr (hAB.symm.mono_left hBblock)))) hex heP
  refine ⟨F, h₀F, hCF, hFQ, hFD, hdegree, hdemand, ?_, hinternal, ?_, ?_⟩
  · intro x hx hxblocks
    apply hsupport x hx
    intro hxW
    rcases Finset.mem_union.mp hxW with hxB | hxP
    · exact hxblocks (Finset.mem_union_right _ hxB)
    · obtain ⟨y, _, hxy⟩ := Finset.mem_biUnion.mp hxP
      dsimp only [P] at hxy
      split_ifs at hxy with hyA
      · exact hxblocks (Finset.mem_union_left _ hxy)
      · exact hxblocks (Finset.mem_union_right _ hxy)
  · ext e
    constructor
    · intro he
      obtain ⟨heF, heP⟩ := Finset.mem_inter.mp he
      rcases Finset.mem_union.mp (hFQ heF) with he₀C | heQ
      · rcases Finset.mem_union.mp he₀C with he₀ | heC
        · exact False.elim ((Finset.disjoint_left.mp h₀plus) he₀ heP)
        · exact heC
      · exact False.elim ((Finset.disjoint_left.mp hQplus) heQ heP)
    · exact fun he => Finset.mem_inter.mpr ⟨hCF he, hCplus he⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heF, heP⟩ := Finset.mem_inter.mp he
    rcases Finset.mem_union.mp (hFQ heF) with he₀C | heQ
    · rcases Finset.mem_union.mp he₀C with he₀ | heC
      · exact (Finset.disjoint_left.mp h₀minus) he₀ heP
      · exact (Finset.disjoint_left.mp hCminus) heC heP
    · exact (Finset.disjoint_left.mp hQminus) heQ heP

end Overfull.BipartiteFactorization
