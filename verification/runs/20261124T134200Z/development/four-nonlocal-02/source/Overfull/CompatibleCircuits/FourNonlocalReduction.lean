import Overfull.CompatibleCircuits.FourStrictCoarsening

/-!
# Normalizing the remaining tight-shore case on four labels

Every nonlocal shore may be complemented so that it avoids its class
vertex. On four labels the resulting shore is nonempty and has at most
two vertices, exactly the size needed for the two three-label constructions.
Zero cuts are included, so disconnected inputs need no hidden connectivity
assumption.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

theorem fourLabel_nonlocal_shore_card_le_two
    {v : Fin 4} {X : Finset (Fin 4)} (hX : NonlocalShore v X) (hv : v ∉ X) :
    X.Nonempty ∧ X.card ≤ 2 := by
  classical
  obtain ⟨x, hx, _⟩ := hX.1
  obtain ⟨y, hy, hyv⟩ := hX.2
  refine ⟨⟨x, hx⟩, ?_⟩
  have hsub : ({v, y} : Finset (Fin 4)) ⊆ Xᶜ := by
  classical
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_compl.mpr hv
    · exact mem_compl.mpr (mem_singleton.mp hz ▸ hy)
  have hcard := card_le_card hsub
  rw [card_pair hyv.symm] at hcard
  have hc := card_compl X
  have hXcard : X.card ≤ 4 := by simpa using card_le_univ X
  simp only [Fintype.card_fin] at hc
  omega

/-- A tight nonlocal class cut can always be placed on a nonempty shore
of at most two vertices disjoint from its class vertex. -/
theorem fourLabel_tight_shore_normalization
    (classOf : Fin 4 → E → K) (C : Finset E)
    (v : Fin 4) (k : K) (X : Finset (Fin 4))
    (hX : NonlocalShore v X)
    (htight : 2 * (Q.classCutOn classOf C v k X).card = (Q.cutOn C X).card) :
    ∃ T : Finset (Fin 4), T.Nonempty ∧ T.card ≤ 2 ∧ v ∉ T ∧
      2 * (Q.classCutOn classOf C v k T).card = (Q.cutOn C T).card := by
  classical
  by_cases hv : v ∈ X
  · have hT := (nonlocalShore_compl_iff v X).mpr hX
    have hvT : v ∉ Xᶜ := by simpa using hv
    obtain ⟨hne, hsmall⟩ := fourLabel_nonlocal_shore_card_le_two hT hvT
    exact ⟨Xᶜ, hne, hsmall, hvT,
      by simpa only [Q.classCutOn_compl, Q.cutOn_compl] using htight⟩
  · obtain ⟨hne, hsmall⟩ := fourLabel_nonlocal_shore_card_le_two hX hv
    exact ⟨X, hne, hsmall, hv, htight⟩

/-- The complement of the strict branch supplies exactly the original
tight cut required by the inside and outside constructions. -/
theorem exists_small_tight_shore_of_not_four_strictNonlocal
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hnot : ¬ Q.StrictNonlocalOn classOf C) :
    ∃ v k T, T.Nonempty ∧ T.card ≤ 2 ∧ v ∉ T ∧
      2 * (Q.classCutOn classOf C v k T).card = (Q.cutOn C T).card := by
  classical
  have hex : ∃ v k X, NonlocalShore v X ∧
      2 * (Q.classCutOn classOf C v k X).card = (Q.cutOn C X).card := by
  classical
    by_contra h
    exact hnot ((Q.strictNonlocalOn_iff_no_tight_nonlocal classOf hadmissible).mpr h)
  obtain ⟨v, k, X, hX, ht⟩ := hex
  obtain ⟨T, hT, hsmall, hv, hbound⟩ :=
    Q.fourLabel_tight_shore_normalization classOf C v k X hX ht
  exact ⟨v, k, T, hT, hsmall, hv, hbound⟩

end Overfull.Multigraph
