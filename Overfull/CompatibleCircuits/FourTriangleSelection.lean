import Overfull.CompatibleCircuits.LocalCoarsening

/-!
# Choosing actual copies from three endpoint-class bundles

If no two copies of a bundle differ at both endpoints, that bundle is
monochromatic at one endpoint.  For three nonempty bundles with this
property, failure to choose a compatible triangle forces one whole
corner to have a common class.  This is an elementary finite selection
result; it does not assert existence of a general circuit partition.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K L : Type*}

def MonochromaticOn (S : Finset E) (f : E → K) : Prop :=
  ∃ k, ∀ e ∈ S, f e = k

def CommonClassOn (S T : Finset E) (f : E → K) : Prop :=
  ∃ k, ∀ e ∈ S ∪ T, f e = k

theorem CommonClassOn.symm {S T : Finset E} {f : E → K}
    (h : CommonClassOn S T f) : CommonClassOn T S f := by
  simpa only [CommonClassOn,union_comm] using h

theorem not_commonClassOn_symm {S T : Finset E} {f : E → K}
    (h : ¬ CommonClassOn S T f) : ¬ CommonClassOn T S f :=
  fun ht => h ht.symm

theorem exists_distinct_of_not_monochromatic (S : Finset E) (f : E → K)
    (hS : S.Nonempty) (h : ¬ MonochromaticOn S f) :
    ∃ e ∈ S, ∃ g ∈ S, f e ≠ f g := by
  obtain ⟨a,ha⟩ := hS
  by_contra! heq
  exact h ⟨f a,fun e he => heq e he a ha⟩

/-- Absence of a compatible pair forces a constant endpoint coordinate. -/
theorem monochromatic_coordinate_of_no_pair
    (S : Finset E) (f : E → K) (g : E → L) (hS : S.Nonempty)
    (hnone : ¬ ∃ e ∈ S, ∃ h ∈ S, f e ≠ f h ∧ g e ≠ g h) :
    MonochromaticOn S f ∨ MonochromaticOn S g := by
  by_cases hf : MonochromaticOn S f
  · exact Or.inl hf
  by_cases hg : MonochromaticOn S g
  · exact Or.inr hg
  obtain ⟨e,he,h,hh,_,hd1,hd2⟩ := exists_pair_distinct_both_coordinates S f g
    (exists_distinct_of_not_monochromatic S f hS hf)
    (exists_distinct_of_not_monochromatic S g hS hg)
  exact False.elim (hnone ⟨e,he,h,hh,hd1,hd2⟩)

theorem exists_different_from_constant_of_no_common_class
    (S T : Finset E) (f : E → K) (k : K)
    (hS : ∀ e ∈ S, f e = k) (hnone : ¬ CommonClassOn S T f) :
    ∃ e ∈ T, f e ≠ k := by
  by_contra! hT
  apply hnone
  refine ⟨k,?_⟩
  intro e he
  exact (mem_union.mp he).elim (hS e) (hT e)

theorem exists_distinct_between_of_no_common_class
    (S T : Finset E) (f : E → K) (hS : S.Nonempty) (hT : T.Nonempty)
    (hnone : ¬ CommonClassOn S T f) :
    ∃ e ∈ S, ∃ g ∈ T, f e ≠ f g := by
  obtain ⟨a,ha⟩ := hS
  obtain ⟨b,hb⟩ := hT
  by_contra! heq
  apply hnone
  refine ⟨f a,?_⟩
  intro e he
  rcases mem_union.mp he with he | he
  · exact (heq e he b hb).trans (heq a ha b hb).symm
  · exact (heq a ha e he).symm

/-- The three endpoint choices are independent in a cyclic orientation. -/
theorem exists_compatible_triple_of_cyclic_monochromatic_bundles
    (AB AC BC : Finset E) (a b c : E → K)
    (hAB : MonochromaticOn AB a) (hAC : MonochromaticOn AC c)
    (hBC : MonochromaticOn BC b)
    (hA : ¬ CommonClassOn AB AC a) (hB : ¬ CommonClassOn AB BC b)
    (hC : ¬ CommonClassOn AC BC c) :
    ∃ e ∈ AB, ∃ f ∈ AC, ∃ g ∈ BC,
      a e ≠ a f ∧ b e ≠ b g ∧ c f ≠ c g := by
  obtain ⟨kA,hAB⟩ := hAB
  obtain ⟨kC,hAC⟩ := hAC
  obtain ⟨kB,hBC⟩ := hBC
  obtain ⟨f,hf,hfa⟩ :=
    exists_different_from_constant_of_no_common_class AB AC a kA hAB hA
  obtain ⟨e,he,heb⟩ :=
    exists_different_from_constant_of_no_common_class BC AB b kB hBC
      (not_commonClassOn_symm hB)
  obtain ⟨g,hg,hgc⟩ :=
    exists_different_from_constant_of_no_common_class AC BC c kC hAC hC
  refine ⟨e,he,f,hf,g,hg,?_,?_,?_⟩
  · rw [hAB e he]
    exact hfa.symm
  · rw [hBC g hg]
    exact heb
  · rw [hAC f hf]
    exact hgc.symm

/-- In a transitive orientation, the two remaining endpoint choices separate. -/
theorem exists_compatible_triple_of_transitive_monochromatic_bundles
    (AB AC BC : Finset E) (a b c : E → K)
    (hACne : AC.Nonempty) (hBCne : BC.Nonempty)
    (hAB : MonochromaticOn AB a) (hAC : MonochromaticOn AC a)
    (hBC : MonochromaticOn BC b)
    (hA : ¬ CommonClassOn AB AC a) (hB : ¬ CommonClassOn AB BC b)
    (hC : ¬ CommonClassOn AC BC c) :
    ∃ e ∈ AB, ∃ f ∈ AC, ∃ g ∈ BC,
      a e ≠ a f ∧ b e ≠ b g ∧ c f ≠ c g := by
  obtain ⟨kAB,hAB⟩ := hAB
  obtain ⟨kAC,hAC⟩ := hAC
  obtain ⟨kBC,hBC⟩ := hBC
  have hdiff : kAB ≠ kAC := by
    intro heq
    apply hA
    refine ⟨kAB,?_⟩
    intro e he
    rcases mem_union.mp he with he | he
    · exact hAB e he
    · exact (hAC e he).trans heq.symm
  obtain ⟨e,he,heb⟩ :=
    exists_different_from_constant_of_no_common_class BC AB b kBC hBC
      (not_commonClassOn_symm hB)
  obtain ⟨f,hf,g,hg,hcg⟩ :=
    exists_distinct_between_of_no_common_class AC BC c hACne hBCne hC
  refine ⟨e,he,f,hf,g,hg,?_,?_,hcg⟩
  · rw [hAB e he,hAC f hf]
    exact hdiff
  · rw [hBC g hg]
    exact heb

/-- A compatible actual-copy triangle exists unless one entire corner has
one common class. No bound on the number of available class values is needed. -/
theorem exists_compatible_triple_of_no_monochromatic_corner
    (AB AC BC : Finset E) (a b c : E → K)
    (hABne : AB.Nonempty) (hACne : AC.Nonempty) (hBCne : BC.Nonempty)
    (hAB : MonochromaticOn AB a ∨ MonochromaticOn AB b)
    (hAC : MonochromaticOn AC a ∨ MonochromaticOn AC c)
    (hBC : MonochromaticOn BC b ∨ MonochromaticOn BC c)
    (hA : ¬ CommonClassOn AB AC a) (hB : ¬ CommonClassOn AB BC b)
    (hC : ¬ CommonClassOn AC BC c) :
    ∃ e ∈ AB, ∃ f ∈ AC, ∃ g ∈ BC,
      a e ≠ a f ∧ b e ≠ b g ∧ c f ≠ c g := by
  rcases hAB with hAB | hAB <;>
    rcases hAC with hAC | hAC <;> rcases hBC with hBC | hBC
  · exact exists_compatible_triple_of_transitive_monochromatic_bundles
      AB AC BC a b c hACne hBCne hAB hAC hBC hA hB hC
  · obtain ⟨f,hf,e,he,g,hg,hfae,hfcg,hebg⟩ :=
      exists_compatible_triple_of_transitive_monochromatic_bundles
        AC AB BC a c b hABne hBCne hAC hAB hBC
        (not_commonClassOn_symm hA) hC hB
    exact ⟨e,he,f,hf,g,hg,hfae.symm,hebg,hfcg⟩
  · exact exists_compatible_triple_of_cyclic_monochromatic_bundles
      AB AC BC a b c hAB hAC hBC hA hB hC
  · obtain ⟨f,hf,g,hg,e,he,hcfg,hfae,hgbe⟩ :=
      exists_compatible_triple_of_transitive_monochromatic_bundles
        AC BC AB c a b hBCne hABne hAC hBC hAB
        hC (not_commonClassOn_symm hA) (not_commonClassOn_symm hB)
    exact ⟨e,he,f,hf,g,hg,hfae.symm,hgbe.symm,hcfg⟩
  · obtain ⟨e,he,g,hg,f,hf,hbeg,haef,hcgf⟩ :=
      exists_compatible_triple_of_transitive_monochromatic_bundles
        AB BC AC b a c hBCne hACne hAB hBC hAC
        hB hA (not_commonClassOn_symm hC)
    exact ⟨e,he,f,hf,g,hg,haef,hbeg,hcgf.symm⟩
  · obtain ⟨e,he,g,hg,f,hf,hbeg,haef,hcgf⟩ :=
      exists_compatible_triple_of_cyclic_monochromatic_bundles
        AB BC AC b a c hAB hBC hAC hB hA (not_commonClassOn_symm hC)
    exact ⟨e,he,f,hf,g,hg,haef,hbeg,hcgf.symm⟩
  · obtain ⟨g,hg,e,he,f,hf,hbge,hcgf,haef⟩ :=
      exists_compatible_triple_of_transitive_monochromatic_bundles
        BC AB AC b c a hABne hACne hBC hAB hAC
        (not_commonClassOn_symm hB) (not_commonClassOn_symm hC) hA
    exact ⟨e,he,f,hf,g,hg,haef,hbge.symm,hcgf.symm⟩
  · obtain ⟨g,hg,f,hf,e,he,hcgf,hbge,hafe⟩ :=
      exists_compatible_triple_of_transitive_monochromatic_bundles
        BC AC AB c b a hACne hABne hBC hAC hAB
        (not_commonClassOn_symm hC) (not_commonClassOn_symm hB)
        (not_commonClassOn_symm hA)
    exact ⟨e,he,f,hf,g,hg,hafe.symm,hbge.symm,hcgf.symm⟩

/-- The obstruction is a genuinely monochromatic whole corner, not just a
failure of one independently chosen pair of endpoint labels. -/
theorem monochromatic_corner_of_no_compatible_triple
    (AB AC BC : Finset E) (a b c : E → K)
    (hABne : AB.Nonempty) (hACne : AC.Nonempty) (hBCne : BC.Nonempty)
    (hAB : MonochromaticOn AB a ∨ MonochromaticOn AB b)
    (hAC : MonochromaticOn AC a ∨ MonochromaticOn AC c)
    (hBC : MonochromaticOn BC b ∨ MonochromaticOn BC c)
    (hnone : ¬ ∃ e ∈ AB, ∃ f ∈ AC, ∃ g ∈ BC,
      a e ≠ a f ∧ b e ≠ b g ∧ c f ≠ c g) :
    CommonClassOn AB AC a ∨ CommonClassOn AB BC b ∨ CommonClassOn AC BC c := by
  by_contra h
  have hA : ¬ CommonClassOn AB AC a := fun ha => h (Or.inl ha)
  have hB : ¬ CommonClassOn AB BC b := fun hb => h (Or.inr (Or.inl hb))
  have hC : ¬ CommonClassOn AC BC c := fun hc => h (Or.inr (Or.inr hc))
  exact hnone (exists_compatible_triple_of_no_monochromatic_corner AB AC BC a b c
    hABne hACne hBCne hAB hAC hBC hA hB hC)

end Overfull.CompatibleCircuits
