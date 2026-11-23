import Overfull.AssignedParts.BoundaryCompression

/-!
# Exact cuts and uncovered parity of the native compressed boundary

The old-core cut splits into its exceptional copies and its copies to the
other old core. Compression changes only the latter set, retaining zero or
one of its original copies with the same parity. Consequently the vertices
left uncovered in each old core have even order. All copy and assignment
identities refer to the originally supplied perfect matching.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

private theorem two_disjoint_cuts_iff (a b c d : Prop)
    (hab : ¬ (a ∧ b)) (hcd : ¬ (c ∧ d)) :
    ((a ≠ c) ∧ (b ≠ d)) ↔ (a ∧ d) ∨ (b ∧ c) := by
  by_cases ha : a <;> by_cases hb : b <;>
    by_cases hc : c <;> by_cases hd : d <;> simp_all

/-- A copy crossing both disjoint old cores has one endpoint in each. -/
theorem mem_coreCrossings_iff (M : Finset E) (U₀ U₁ : Finset V)
    (h01 : Disjoint U₀ U₁) (e : E) :
    e ∈ G.cutOn M U₀ ∩ G.cutOn M U₁ ↔ e ∈ M ∧
      ((G.firstEnd e ∈ U₀ ∧ G.secondEnd e ∈ U₁) ∨
        (G.firstEnd e ∈ U₁ ∧ G.secondEnd e ∈ U₀)) := by
  simp only [mem_inter, Multigraph.mem_cutOn]
  have hiff := two_disjoint_cuts_iff
    (G.firstEnd e ∈ U₀) (G.firstEnd e ∈ U₁)
    (G.secondEnd e ∈ U₀) (G.secondEnd e ∈ U₁)
    (fun h => disjoint_left.mp h01 h.1 h.2)
    (fun h => disjoint_left.mp h01 h.1 h.2)
  tauto

/-- No original old-core crossing copy touches an exceptional vertex. -/
theorem exceptionalCopies_disjoint_coreCrossings (M : Finset E)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) :
    Disjoint (exceptionalCopies G M Z) (G.cutOn M U₀ ∩ G.cutOn M U₁) := by
  apply disjoint_left.mpr
  intro e he hcross
  have heZ := (mem_exceptionalCopies G M Z e).mp he |>.2
  have hends := (mem_coreCrossings_iff G M U₀ U₁ h01 e).mp hcross |>.2
  rcases heZ with hZ | hZ <;> rcases hends with hends | hends
  · exact disjoint_left.mp h0Z hends.1 hZ
  · exact disjoint_left.mp h1Z hends.1 hZ
  · exact disjoint_left.mp h1Z hends.2 hZ
  · exact disjoint_left.mp h0Z hends.2 hZ

private theorem two_core_cut_split_iff (a b z c d w : Prop)
    (hcover₀ : a ∨ b ∨ z) (hcover₁ : c ∨ d ∨ w)
    (hab : ¬ (a ∧ b)) (haz : ¬ (a ∧ z)) (hbz : ¬ (b ∧ z))
    (hcd : ¬ (c ∧ d)) (hcw : ¬ (c ∧ w)) (hdw : ¬ (d ∧ w)) :
    (a ≠ c) ↔ ((z ∨ w) ∧ a ≠ c) ∨ ((a ≠ c) ∧ (b ≠ d)) := by
  rcases hcover₀ with ha | hb | hz <;>
    rcases hcover₁ with hc | hd | hw <;> simp_all

/-- Every old-core cut consists of its exceptional copies and its copies
to the other old core, on the original copy type. -/
theorem core_cut_split (M : Finset E) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    G.cutOn M U₀ = G.cutOn (exceptionalCopies G M Z) U₀ ∪
      (G.cutOn M U₀ ∩ G.cutOn M U₁) := by
  ext e
  by_cases he : e ∈ M
  · simp only [Multigraph.mem_cutOn, mem_union, mem_inter,
      mem_exceptionalCopies, he, true_and]
    exact two_core_cut_split_iff _ _ _ _ _ _
      (hcover (G.firstEnd e)) (hcover (G.secondEnd e))
      (fun h => disjoint_left.mp h01 h.1 h.2)
      (fun h => disjoint_left.mp h0Z h.1 h.2)
      (fun h => disjoint_left.mp h1Z h.1 h.2)
      (fun h => disjoint_left.mp h01 h.1 h.2)
      (fun h => disjoint_left.mp h0Z h.1 h.2)
      (fun h => disjoint_left.mp h1Z h.1 h.2)
  · simp [Multigraph.mem_cutOn, mem_exceptionalCopies, he]

/-- The selected parity copies lie in each old-core cut. -/
theorem cutOn_paritySelection_coreCrossings (M : Finset E) (U₀ U₁ : Finset V) :
    G.cutOn (paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁)) U₀ =
      paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁) := by
  apply filter_eq_self.mpr
  intro e he
  exact (G.mem_cutOn M U₀ e).mp
    (mem_inter.mp (paritySelection_subset _ he)).1 |>.2

/-- Compression retains precisely the exceptional old-core cut and the
chosen parity copies between the old cores. -/
theorem compressedBoundary_cut_split (M : Finset E) (U₀ U₁ Z : Finset V) :
    G.cutOn (compressedBoundary G M U₀ U₁ Z) U₀ =
      G.cutOn (exceptionalCopies G M Z) U₀ ∪
        paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁) := by
  unfold compressedBoundary
  rw [Multigraph.cutOn, filter_union]
  change G.cutOn (exceptionalCopies G M Z) U₀ ∪
      G.cutOn (paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁)) U₀ = _
  rw [cutOn_paritySelection_coreCrossings]

/-- The compressed old-core crossing set is exactly the selected original
parity set; no exceptional copy is misclassified as an old-core crossing. -/
theorem compressedBoundary_core_crossings (M : Finset E)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) :
    G.cutOn (compressedBoundary G M U₀ U₁ Z) U₀ ∩
        G.cutOn (compressedBoundary G M U₀ U₁ Z) U₁ =
      paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁) := by
  ext e
  constructor
  · intro he
    obtain ⟨he₀, he₁⟩ := mem_inter.mp he
    obtain ⟨heF, hcut₀⟩ := (G.mem_cutOn _ _ e).mp he₀
    have hcut₁ := (G.mem_cutOn _ _ e).mp he₁ |>.2
    have heM := compressedBoundary_subset G M U₀ U₁ Z heF
    rcases mem_union.mp heF with heZ | hep
    · have hcross : e ∈ G.cutOn M U₀ ∩ G.cutOn M U₁ :=
        mem_inter.mpr ⟨(G.mem_cutOn _ _ e).mpr ⟨heM, hcut₀⟩,
          (G.mem_cutOn _ _ e).mpr ⟨heM, hcut₁⟩⟩
      exact (disjoint_left.mp
        (exceptionalCopies_disjoint_coreCrossings G M U₀ U₁ Z h01 h0Z h1Z)
        heZ hcross).elim
    · exact hep
  · intro he
    obtain ⟨he₀, he₁⟩ := mem_inter.mp (paritySelection_subset _ he)
    have heF : e ∈ compressedBoundary G M U₀ U₁ Z := mem_union_right _ he
    exact mem_inter.mpr ⟨(G.mem_cutOn _ _ e).mpr
      ⟨heF, (G.mem_cutOn _ _ e).mp he₀ |>.2⟩,
      (G.mem_cutOn _ _ e).mpr ⟨heF, (G.mem_cutOn _ _ e).mp he₁ |>.2⟩⟩

/-- Compression leaves no selected copy internal to the first old core. -/
theorem compressedBoundary_internal_core_empty (M : Finset E)
    (U₀ U₁ Z : Finset V) (h0Z : Disjoint U₀ Z) :
    G.internalOn (compressedBoundary G M U₀ U₁ Z) U₀ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heF, hends⟩ := mem_filter.mp he
  rcases mem_union.mp heF with heZ | hep
  · rcases (mem_exceptionalCopies G M Z e).mp heZ |>.2 with hZ | hZ
    · exact disjoint_left.mp h0Z hends.1 hZ
    · exact disjoint_left.mp h0Z hends.2 hZ
  · have hcut := (G.mem_cutOn M U₀ e).mp
      (mem_inter.mp (paritySelection_subset _ hep)).1 |>.2
    exact hcut (propext ⟨fun _ => hends.2, fun _ => hends.1⟩)

/-- The old-core cut count changes only by an even number of original copies. -/
theorem compressedBoundary_cut_parity (M : Finset E)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    (G.cutOn (compressedBoundary G M U₀ U₁ Z) U₀).card % 2 =
      (G.cutOn M U₀).card % 2 := by
  have hdisj := exceptionalCopies_disjoint_coreCrossings G M U₀ U₁ Z h01 h0Z h1Z
  have hdisjcut : Disjoint (G.cutOn (exceptionalCopies G M Z) U₀)
      (G.cutOn M U₀ ∩ G.cutOn M U₁) :=
    hdisj.mono_left (filter_subset _ _)
  have hdisjpick := hdisjcut.mono_right
    (paritySelection_subset (G.cutOn M U₀ ∩ G.cutOn M U₁))
  have horiginal : (G.cutOn M U₀).card =
      (G.cutOn (exceptionalCopies G M Z) U₀).card +
        (G.cutOn M U₀ ∩ G.cutOn M U₁).card := by
    rw [core_cut_split G M U₀ U₁ Z h01 h0Z h1Z hcover,
      card_union_of_disjoint hdisjcut]
  rw [compressedBoundary_cut_split, card_union_of_disjoint hdisjpick,
    paritySelection_card, horiginal]
  omega

/-- The first old core has even uncovered order in the actual compression. -/
theorem compressedBoundary_uncovered_even_first {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    Even (U₀ \ G.edgeSupport (compressedBoundary G M U₀ U₁ Z)).card := by
  apply ((compressedBoundary_isMatching G (hM.isMatching G) U₀ U₁ Z).
    uncovered_even_iff_cut_parity G U₀).mpr
  rw [compressedBoundary_cut_parity G M U₀ U₁ Z h01 h0Z h1Z hcover]
  exact perfectMatching_shore_card_parity G hM U₀

/-- The compression is symmetric in the two old cores. -/
theorem compressedBoundary_swap (M : Finset E) (U₀ U₁ Z : Finset V) :
    compressedBoundary G M U₀ U₁ Z = compressedBoundary G M U₁ U₀ Z := by
  unfold compressedBoundary
  rw [inter_comm (G.cutOn M U₀) (G.cutOn M U₁)]

/-- Both old cores have even uncovered order, so later independent robust
core completions have the required exact parity. -/
theorem compressedBoundary_uncovered_even {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    Even (U₀ \ G.edgeSupport (compressedBoundary G M U₀ U₁ Z)).card ∧
      Even (U₁ \ G.edgeSupport (compressedBoundary G M U₀ U₁ Z)).card := by
  refine ⟨compressedBoundary_uncovered_even_first G hM U₀ U₁ Z
    h01 h0Z h1Z hcover, ?_⟩
  rw [compressedBoundary_swap G M U₀ U₁ Z]
  apply compressedBoundary_uncovered_even_first G hM U₁ U₀ Z h01.symm h1Z h0Z
  intro v
  rcases hcover v with h0 | h1 | hZ
  · exact Or.inr (Or.inl h0)
  · exact Or.inl h1
  · exact Or.inr (Or.inr hZ)

end Overfull.AssignedParts
