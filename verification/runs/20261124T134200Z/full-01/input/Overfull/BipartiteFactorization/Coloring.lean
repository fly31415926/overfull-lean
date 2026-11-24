import Overfull.MultigraphFanApplications
import Overfull.BalancedColoring
import Overfull.ColoringExtension.Exterior

/-!
# Coloring selected exterior subgraphs

The low-degree core is an actual vertex set in a finite loopless multigraph.
The initial coloring is needed only on the exceptional-exceptional copies
and on the core copies at inactive exceptional vertices. A minimal
noncolorable restriction cannot contain any of the remaining copies.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- Delete the core-core copies and the copies from active vertices to the
core. The retained copies are precisely those requiring an initial coloring. -/
def inactiveExterior (U Zplus : Finset V) : Finset E :=
  (G.internalEdges U ∪ Zplus.biUnion (fun x => G.edgesTo x U))ᶜ

omit [Fintype V] in
@[simp] theorem mem_inactiveExterior (U Zplus : Finset V) (e : E) :
    e ∈ inactiveExterior G U Zplus ↔
      e ∉ G.internalEdges U ∧ ∀ x ∈ Zplus, e ∉ G.edgesTo x U := by
  simp only [inactiveExterior, Finset.mem_compl, Finset.mem_union,
    Finset.mem_biUnion, not_or, not_exists, not_and]

/-- The retained residue consists exactly of exceptional-exceptional
copies and core copies at inactive exceptional vertices. -/
theorem inactiveExterior_eq (U Zplus : Finset V) :
    inactiveExterior G U Zplus =
      G.internalEdges Uᶜ ∪ (Uᶜ \ Zplus).biUnion (fun x => G.edgesTo x U) := by
  ext e
  rw [mem_inactiveExterior, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro h
    by_cases hx : G.firstEnd e ∈ U
    · have hy : G.secondEnd e ∉ U := fun hy =>
        h.1 ((G.mem_internalEdges U e).mpr ⟨hx, hy⟩)
      have heq : G.edge e = s(G.secondEnd e, G.firstEnd e) :=
        (G.edge_eq e).symm.trans Sym2.eq_swap
      have heU : e ∈ G.edgesTo (G.secondEnd e) U := by
        apply (G.mem_edgesTo _ _ _).mpr
        exact ⟨by simp [heq], (G.otherEnd_eq_of_edge e _ _ heq).symm ▸ hx⟩
      exact Or.inr ⟨G.secondEnd e,
        Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hy, fun hyZ => h.2 _ hyZ heU⟩, heU⟩
    · by_cases hy : G.secondEnd e ∈ U
      · have heq := (G.edge_eq e).symm
        have heU : e ∈ G.edgesTo (G.firstEnd e) U := by
          apply (G.mem_edgesTo _ _ _).mpr
          exact ⟨by simp [heq], (G.otherEnd_eq_of_edge e _ _ heq).symm ▸ hy⟩
        exact Or.inr ⟨G.firstEnd e,
          Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hx, fun hxZ => h.2 _ hxZ heU⟩, heU⟩
      · exact Or.inl ((G.mem_internalEdges Uᶜ e).mpr
          ⟨Finset.mem_compl.mpr hx, Finset.mem_compl.mpr hy⟩)
  · rintro (houtside | ⟨x, hx, heX⟩)
    · obtain ⟨hx, _⟩ := (G.mem_internalEdges Uᶜ e).mp houtside
      refine ⟨fun he => (Finset.mem_compl.mp hx) ((G.mem_internalEdges U e).mp he).1, ?_⟩
      intro x _ heX
      obtain ⟨hxe, hxU⟩ := (G.mem_edgesTo x U e).mp heX
      have hh := (G.internalEdges_iff_of_edge e x _ (G.edge_eq_otherEnd x e hxe) Uᶜ).mp
        houtside
      exact (Finset.mem_compl.mp hh.2) hxU
    · obtain ⟨hxU, hxZ⟩ := Finset.mem_sdiff.mp hx
      have hxU' := Finset.mem_compl.mp hxU
      obtain ⟨hxe, hother⟩ := (G.mem_edgesTo x U e).mp heX
      have heq := G.edge_eq_otherEnd x e hxe
      refine ⟨fun he => hxU' ((G.internalEdges_iff_of_edge e x _ heq U).mp he).1, ?_⟩
      intro y hyZ heY
      obtain ⟨hye, hyU⟩ := (G.mem_edgesTo y U e).mp heY
      have hends : y = x ∨ y = G.otherEnd x e := by
        simpa only [heq, Sym2.mem_iff] using hye
      rcases hends with rfl | rfl
      · exact hxZ hyZ
      · have hh := G.otherEnd_eq_of_edge e (G.otherEnd x e) x (heq.trans Sym2.eq_swap)
        exact hxU' (hh ▸ hyU)

omit [Fintype V] in
/-- A coloring of the restriction retaining every copy gives a coloring
of the original multigraph, preserving its individual edge copies. -/
theorem coloring_of_univ_restriction (k : ℕ)
    (hcolor : Nonempty ((G.restrictEdges univ).EdgeColoring k)) :
    Nonempty (G.EdgeColoring k) := by
  obtain ⟨c⟩ := hcolor
  refine ⟨⟨fun e => c.color ⟨e, Finset.mem_univ e⟩, ?_⟩⟩
  intro e f v hef hev hfv
  exact congrArg Subtype.val (c.proper hef hev hfv)

/-- The finite fan criterion with a natural core degree bound. It does
not require regularity of the selected subgraph. -/
theorem coloring_from_inactive_exterior_nat (U Zplus : Finset V) (k a : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hcore : ∀ v ∈ U, G.degree v ≤ a) (hka : 2 * a < k)
    (hactive : ∀ x ∈ Zplus, 2 * a < (G.edgesTo x U).card)
    (hcolor : Nonempty ((G.restrictEdges (inactiveExterior G U Zplus)).EdgeColoring k)) :
    Nonempty (G.EdgeColoring k) := by
  by_contra hnot
  have huniv : ¬ Nonempty ((G.restrictEdges univ).EdgeColoring k) :=
    fun hc => hnot (coloring_of_univ_restriction G k hc)
  obtain ⟨F, _hF, hmin⟩ := G.exists_kMinimal_subset k hdegree univ huniv
  have hFcore (v : V) (hv : v ∈ U) : (G.restrictEdges F).degree v ≤ a :=
    (G.restrictEdges_degree_le F v).trans (hcore v hv)
  have hnone (x : V) (hx : x ∈ Zplus) :
      (G.restrictEdges F).edgesTo x U = ∅ := by
    apply hmin.no_edgesTo_low_set x U a hFcore hka.le
    intro v hv
    have hsum := G.edgesTo_compl_card_add x U
    have hout := G.restrictEdges_edgesTo_card_le F x Uᶜ
    have hpar := (G.restrictEdges F).parallelEdges_card_le_degree x v
    have hdv := hFcore v hv
    have hdx := hdegree x
    have hmany := hactive x hx
    omega
  have hsub : F ⊆ inactiveExterior G U Zplus := by
    intro e he
    apply (mem_inactiveExterior G U Zplus e).mpr
    constructor
    · intro hinside
      obtain ⟨hx, hy⟩ := (G.mem_internalEdges U e).mp hinside
      have hsum := hmin.endpoint_degree_sum ⟨e, he⟩
        (G.firstEnd e) (G.secondEnd e) (G.edge_eq e).symm
      have hdx := hFcore (G.firstEnd e) hx
      have hdy := hFcore (G.secondEnd e) hy
      omega
    · intro x hx hxe
      have hxe' : (⟨e, he⟩ : F) ∈ (G.restrictEdges F).edgesTo x U := by
        apply ((G.restrictEdges F).mem_edgesTo x U ⟨e, he⟩).mpr
        change x ∈ G.edge e ∧ G.otherEnd x e ∈ U
        exact (G.mem_edgesTo x U e).mp hxe
      rw [hnone x hx] at hxe'
      exact Finset.notMem_empty _ hxe'
  obtain ⟨c⟩ := hcolor
  exact hmin.2.1 ⟨c.restrictEdgesSubset hsub⟩

/-- Color a selected exterior graph from its actual inactive residue.
Only the exceptional degree upper bound, the small core degrees, and
the actual active-to-core incidence lower bounds are supplied. -/
theorem coloring_from_inactive_exterior (U Zplus : Finset V) (k : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hcore : ∀ v ∈ U, (G.degree v : ℝ) ≤ a)
    (houtside : ∀ v ∉ U, G.degree v ≤ k) (hka : 2 * a < k)
    (hactive : ∀ x ∈ Zplus, 2 * a < ((G.edgesTo x U).card : ℝ))
    (hcolor : Nonempty ((G.restrictEdges (inactiveExterior G U Zplus)).EdgeColoring k)) :
    Nonempty (G.EdgeColoring k) := by
  have hfloor := Nat.floor_le ha
  have hdegree (v : V) : G.degree v ≤ k := by
    by_cases hv : v ∈ U
    · have hh := hcore v hv
      have hh' : (G.degree v : ℝ) ≤ k := by linarith
      exact_mod_cast hh'
    · exact houtside v hv
  apply coloring_from_inactive_exterior_nat G U Zplus k (Nat.floor a) hdegree
    (fun v hv => Nat.le_floor (hcore v hv))
  · have hh : 2 * (Nat.floor a : ℝ) < k := by linarith
    exact_mod_cast hh
  · intro x hx
    have hh := hactive x hx
    have hh' : 2 * (Nat.floor a : ℝ) < (G.edgesTo x U).card := by linarith
    exact_mod_cast hh'
  · exact hcolor

/-- Color and balance a selected exterior graph whose core incidences
are localized in two equal blocks. The coloring of the entire selected
graph is constructed from its inactive residue by the fan criterion. -/
theorem exists_balanced_localized_coloring
    (A B Ablock Bblock Zplus : Finset V) (k : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hka : 2 * a < k)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card)
    (hZ : ∀ v ∈ (A ∪ B)ᶜ, G.degree v = k)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hdegree : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hactive : ∀ x ∈ Zplus, 2 * a < ((G.edgesTo x (A ∪ B)).card : ℝ))
    (hcolor : Nonempty ((G.restrictEdges
      (inactiveExterior G (A ∪ B) Zplus)).EdgeColoring k))
    (hAblock : Ablock ⊆ A) (hBblock : Bblock ⊆ B)
    (hblockcard : Ablock.card = Bblock.card)
    (hsupport : ∀ v ∈ A ∪ B, v ∉ Ablock ∪ Bblock → G.degree v = 0) :
    ∃ c : G.EdgeColoring k,
      (∀ i, (A ∪ B)ᶜ ⊆ c.coveredVertices i) ∧
      (∀ i, (A ∩ c.coveredVertices i).card = (B ∩ c.coveredVertices i).card) ∧
      (∀ i j, |((A ∩ c.coveredVertices i).card : ℤ) -
        (A ∩ c.coveredVertices j).card| ≤ 2) ∧
      (∀ i, c.exteriorFootprint (A ∪ B) i ⊆ Ablock ∪ Bblock) ∧
      (∀ i, ((c.exteriorFootprint (A ∪ B) i).card : ℝ) ≤
        2 * Ablock.card * a / k + 4) ∧
      (∀ i, Even (c.exteriorFootprint (A ∪ B) i).card) ∧
      (∀ v ∈ A ∪ B,
        (univ.filter (fun i => v ∈ c.exteriorFootprint (A ∪ B) i)).card = G.degree v) ∧
      (∀ v ∈ A ∪ B,
        ((univ.filter (fun i => v ∈ c.exteriorFootprint (A ∪ B) i)).card : ℝ) ≤ a) := by
  have hkR : (0 : ℝ) < k := by linarith
  have hk : 0 < k := by exact_mod_cast hkR
  have hc := coloring_from_inactive_exterior G (A ∪ B) Zplus k a ha hcore
    (fun v hv => (hZ v (Finset.mem_compl.mpr hv)).le) hka hactive hcolor
  obtain ⟨c, hcover, hbalanced, hspread, _hload, hbound, _hbounda⟩ :=
    G.balanced_edgeColoring k hk A B (A ∪ B)ᶜ hAB disjoint_compl_right
      (Finset.union_compl _) hcard hZeven hZ hdegree hc
  have hblocks : Ablock ∪ Bblock ⊆ A ∪ B := Finset.union_subset_union hAblock hBblock
  have hblockdisjoint : Disjoint Ablock Bblock := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    exact (Finset.disjoint_left.mp hAB) (hAblock hvA) (hBblock hvB)
  have hsum : (∑ v ∈ A ∪ B, (G.degree v : ℝ)) ≤ 2 * Ablock.card * a := by
    calc
      _ = ∑ v ∈ Ablock ∪ Bblock, (G.degree v : ℝ) := by
        symm
        apply Finset.sum_subset hblocks
        intro v hv hvblock
        simp only [hsupport v hv hvblock, Nat.cast_zero]
      _ ≤ ∑ _v ∈ Ablock ∪ Bblock, a :=
        Finset.sum_le_sum (fun v hv => hcore v (hblocks hv))
      _ = ((Ablock ∪ Bblock).card : ℝ) * a := by simp
      _ = 2 * Ablock.card * a := by
        rw [Finset.card_union_of_disjoint hblockdisjoint, ← hblockcard]
        push_cast
        ring
  refine ⟨c, hcover, hbalanced, hspread, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hv
    obtain ⟨hvU, e, _hcolor, hve⟩ := (c.mem_exteriorFootprint (A ∪ B) i v).mp hv
    by_contra hvblock
    have hzero := hsupport v hvU hvblock
    have hpos : 0 < G.degree v := by
      exact Finset.card_pos.mpr ⟨e, (G.mem_incidenceEdges v e).mpr hve⟩
    omega
  · intro i
    exact (hbound i).trans (add_le_add_right (div_le_div_of_nonneg_right hsum hkR.le) 4)
  · exact c.exteriorFootprint_even (A ∪ B) hZ hZeven
  · intro v hv
    exact c.exteriorFootprint_incidence (A ∪ B) v hv
  · intro v hv
    rw [c.exteriorFootprint_incidence (A ∪ B) v hv]
    exact hcore v hv

end Overfull.BipartiteFactorization
