import Overfull.FourOdd.Theorem
import Overfull.ResidualPalette.PaletteParity

/-!
# Original-copy boundary forests for four odd parts

The four-odd decomposition is lifted from the joining-copy subtype without
identifying any original copies. Each primary retains its actual matching
or star profile; surplus parts have even cuts at every part.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd Compression CircuitPatterns

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The exact per-part cut counts of one primary matching come from one
of the three perfect matchings or four stars on the four labels. -/
def PrimaryProfile (G : Multigraph V E) (label : V → Fin 4) (M : Finset E) : Prop :=
  ∃ F : Finset LabelPair, LabelForestShape F ∧
    ∀ i, (G.cutOn M (labelShore label {i})).card = pairDegree F i

omit [Fintype E] in
theorem PrimaryProfile.cut_one_or_three {G : Multigraph V E}
    {label : V → Fin 4} {M : Finset E} (hp : PrimaryProfile G label M) (i : Fin 4) :
    (G.cutOn M (labelShore label {i})).card = 1 ∨
      (G.cutOn M (labelShore label {i})).card = 3 := by
  obtain ⟨F, hF, hcuts⟩ := hp
  rw [hcuts]
  rcases hF with hmatching | ⟨c, rfl⟩
  · exact Or.inl ((labelPerfectMatching_spec F hmatching).2.1 i)
  · rw [(labelStar_spec c).2.1 i]
    split_ifs <;> simp

omit [Fintype E] in
theorem PrimaryProfile.odd_cut {G : Multigraph V E}
    {label : V → Fin 4} {M : Finset E} (hp : PrimaryProfile G label M) (i : Fin 4) :
    Odd (G.cutOn M (labelShore label {i})).card := by
  rcases hp.cut_one_or_three i with h | h <;> rw [h] <;> decide

/-- An actual original-copy decomposition, retaining the forest profile
needed for later singleton/triple boundary extension. -/
structure JoiningDecomposition (G : Multigraph V E) (label : V → Fin 4) (h : ℕ) where
  primary : Finset (Finset E)
  surplus : Finset (Finset E)
  primary_card : primary.card = h
  families_disjoint : Disjoint primary surplus
  nonempty : ∀ M ∈ primary ∪ surplus, M.Nonempty
  matching : ∀ M ∈ primary ∪ surplus, G.IsMatching M
  disjoint : ∀ M ∈ primary ∪ surplus, ∀ N ∈ primary ∪ surplus, M ≠ N → Disjoint M N
  cover : (primary ∪ surplus).biUnion id = joiningCopies G label
  primary_card_le : ∀ M ∈ primary, M.card ≤ 3
  surplus_card_eq : ∀ M ∈ surplus, M.card = 2
  primary_profile : ∀ M ∈ primary, PrimaryProfile G label M
  surplus_even_cut : ∀ M ∈ surplus, ∀ i, Even (G.cutOn M (labelShore label {i})).card

variable (G : Multigraph V E) (label : V → Fin 4) {h : ℕ}

/-- Lift every matching of the constructed four-odd decomposition to the
original copy type, preserving counts, profiles and exact coverage. -/
def liftDecomposition
    (P : Decomposition (joiningGraph G label) (joiningQuotient G label).edgeLabelPair univ h) :
    JoiningDecomposition G label h := by
  let lift : Finset (joiningCopies G label) → Finset E := fun M => M.image Subtype.val
  have hinj : Function.Injective lift := Finset.image_injective Subtype.val_injective
  have hfamilies : P.primary.image lift ∪ (P.parts \ P.primary).image lift =
      P.parts.image lift := by
    rw [← image_union, union_sdiff_of_subset P.primary_subset]
  have hmem {M : Finset E} (hm : M ∈ P.primary.image lift ∪ (P.parts \ P.primary).image lift) :
      ∃ N ∈ P.parts, lift N = M := by
    rw [hfamilies] at hm
    exact mem_image.mp hm
  refine {
    primary := P.primary.image lift
    surplus := (P.parts \ P.primary).image lift
    primary_card := by rw [card_image_of_injective _ hinj, P.primary_card]
    families_disjoint := ?_
    nonempty := ?_
    matching := ?_
    disjoint := ?_
    cover := ?_
    primary_card_le := ?_
    surplus_card_eq := ?_
    primary_profile := ?_
    surplus_even_cut := ?_
  }
  · exact (disjoint_image hinj).mpr disjoint_sdiff_self_right
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := hmem hM
    exact (P.nonempty N hN).image _
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := hmem hM
    exact joiningGraph_isMatching_image G label (P.matching N hN)
  · intro M hM N hN hne
    obtain ⟨A, hA, rfl⟩ := hmem hM
    obtain ⟨B, hB, rfl⟩ := hmem hN
    exact (disjoint_image Subtype.val_injective).mpr
      (P.disjoint A hA B hB (fun heq => hne (congrArg lift heq)))
  · rw [hfamilies, image_biUnion]
    change P.parts.biUnion (fun M => M.image Subtype.val) = joiningCopies G label
    rw [← biUnion_image]
    change (P.parts.biUnion id).image Subtype.val = joiningCopies G label
    have hcover : P.parts.biUnion id = univ := by
      convert P.cover using 1
      congr
      exact Subsingleton.elim _ _
    rw [hcover]
    ext e
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨f, hf⟩ => hf ▸ f.property, fun he => ⟨⟨e,he⟩,rfl⟩⟩
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := mem_image.mp hM
    change (N.image Subtype.val).card ≤ 3
    rw [card_image_of_injective _ Subtype.val_injective]
    have hs := P.primary_shape N hN
    have hc := card_image_iff.mpr hs.1
    rcases hs.2 with hm | ⟨c, heq⟩
    · have hh := (labelPerfectMatching_spec _ hm).1
      omega
    · have hh := (labelStar_spec c).1
      rw [heq] at hc
      omega
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := mem_image.mp hM
    change (N.image Subtype.val).card = 2
    rw [card_image_of_injective _ Subtype.val_injective]
    exact (P.surplus_shape N (mem_sdiff.mp hN).1 (mem_sdiff.mp hN).2).1
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := mem_image.mp hM
    have hs := P.primary_shape N hN
    refine ⟨N.image (joiningQuotient G label).edgeLabelPair, hs.2, ?_⟩
    intro i
    change (G.cutOn (N.image Subtype.val) (labelShore label {i})).card = _
    rw [← joiningQuotient_degreeOn_eq_cut, (joiningQuotient G label).edgeLabelPair_degree hs.1]
  · intro M hM i
    obtain ⟨N, hN, rfl⟩ := mem_image.mp hM
    change Even (G.cutOn (N.image Subtype.val) (labelShore label {i})).card
    rw [← joiningQuotient_degreeOn_eq_cut]
    exact Multigraph.IsCircuit.even_degreeOn _
      ((P.surplus_shape N (mem_sdiff.mp hN).1 (mem_sdiff.mp hN).2).isCircuit _) i

/-- Construct the original-copy decomposition from the actual host and
prescribed forest supply, without assuming any boundary coloring. -/
theorem exists_joining_decomposition (h r₀ : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (hdegree : ∀ v, (G.degreeOn (joiningCopies G label) v : ℝ) ≤ a)
    (F : Finset LabelPair) (hF : LabelForestShape F)
    (hsupply : ∀ p ∈ F, r₀ ≤ (pairPool (joiningQuotient G label) p).card)
    (hsmall : 1000*a ≤ h) (hnearly : 999*h ≤ 1000*r₀) :
    Nonempty (JoiningDecomposition G label h) := by
  obtain ⟨P⟩ := four_odd_decomposition_real G label h r₀ a ha hregular hno hodd
    hdegree F hF hsupply hsmall hnearly
  exact ⟨liftDecomposition G label P⟩

end Overfull.TerminalFourOdd
