import Overfull.PairedCut.Lifting

/-!
# A prescribed-pair cut from actual regular clusters

The actual random pair orientations and deterministic lifting are combined
here. The only remaining input for the full paired-cut lemma is existence
of the specified regular clusters and their robust reduced graph.
-/

namespace Overfull.PairedCut

open Finset Classical

/-- Uniformly construct the balanced bipartite robust cut once an actual
lower-regular cluster system has been obtained. -/
theorem exists_prescribed_pair_cut_from_clusters
    (α ε β d γ τ : ℝ) (K : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hεγ : ε ≤ γ / 100) (hβ : 0 < β)
    (hd : 0 < d) (hd1 : d ≤ 1) (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ n₀ : ℕ, ∀ (V I J : Type*) [Fintype V] [Fintype I] [Fintype J]
      [DecidableEq V] [DecidableEq J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
      (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V) (w : ℕ),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card V →
      (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card V ≤ ((C j).card : ℝ)) →
      0 < w → 1 ≤ γ * Fintype.card J → IsRobustExpander R (2 * γ) (2 * τ) →
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) → (∀ i, (C i).card = w) →
      (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V →
      LowerRegularPairs G R C ε d w →
      ∃ A B : Finset V,
        Disjoint A B ∧ A ∪ B = univ ∧ A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
        (∀ i, (e (i,false) ∈ A ∧ e (i,true) ∈ B) ∨
          (e (i,true) ∈ A ∧ e (i,false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        IsBipartiteRobustExpander (cutSidesGraph G A B) (d * γ ^ 2 / 100) (4 * τ) := by
  have hε1 : ε ≤ 1 / 2 := by linarith
  obtain ⟨n₀,hn₀⟩ := exists_prescribed_pair_cut α ε β K hα hε hε1 hβ
  refine ⟨n₀,?_⟩
  intro V I J _ _ _ _ _ G _ e R _ C w hK hn hdegree hlarge hw ht hR
    hdisjoint hsize hexception hregular
  obtain ⟨A,B,hAB,hunion,hAcard,hBcard,hpair,hcut,hcluster⟩ :=
    hn₀ V I J G e C hK hn hdegree hlarge
  have hunion' : A ∪ B = univ := by
    ext v
    have h := Finset.ext_iff.mp hunion v
    simpa only [Finset.mem_union,Finset.mem_univ] using h
  have hinter (X Y : Finset V) :
      (letI : DecidableEq V := Classical.decEq V; X ∩ Y) = X ∩ Y := by
    ext v
    simp only [Finset.mem_inter]
  simp only [hinter] at hcluster
  refine ⟨A,B,hAB,hunion',hAcard,hBcard,hpair,hcut,?_⟩
  apply balanced_cluster_cut_expands G R C ε d γ τ w hd hd1 hγ hγτ hτ hε.le hεγ
    hw ht hR hdisjoint hsize hexception hregular A B hAB hunion' (hAcard.trans hBcard.symm)
  · intro j
    have h := (abs_lt.mp (hcluster j).1).2
    rw [hsize j,Finset.inter_comm] at h
    linarith
  · intro j
    have h := (abs_lt.mp (hcluster j).2).1
    rw [hsize j,Finset.inter_comm] at h
    linarith

end Overfull.PairedCut
