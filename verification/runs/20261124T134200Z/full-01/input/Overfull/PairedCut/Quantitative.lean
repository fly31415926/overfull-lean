import Overfull.PairedCut.QuantitativeSampling
import Overfull.PairedCut.Full

/-!
# A robust prescribed-pair cut with arbitrarily accurate degree balance

The crossing robust parameter is fixed before the requested degree error.
The graph, prescribed pairing, and regularity clusters are all quantified
after the order threshold. The same actual cut satisfies robust expansion,
the prescribed pairing, and both neighborhood estimates.
-/

namespace Overfull.PairedCut

open Finset Classical

/-- Transport simultaneous degree and cluster balance to arbitrary vertex
labels while retaining the exact prescribed pairing. -/
theorem exists_prescribed_pair_cut_quantitative (α δ ε β : ℝ) (K : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (V I J : Type*) [Fintype V] [Fintype I] [Fintype J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
      (C : J → Finset V),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card V →
      (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card V ≤ ((C j).card : ℝ)) →
      ∃ A B : Finset V,
        Disjoint A B ∧ A ∪ B = univ ∧
        A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
        (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
          (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
          |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
        ∀ j,
          |(((C j) ∩ A).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ B).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  obtain ⟨n₀, hn₀⟩ := exists_orientation_quantitative α δ ε β K hα hδ hε hε1 hβ
  refine ⟨n₀, ?_⟩
  intro V I J _ _ _ G _ e C hK hn hdegree hsize
  let C' := fun j => (C j).map e.symm.toEmbedding
  have hcard : Fintype.card (I × Bool) = Fintype.card V := Fintype.card_congr e
  have hdegree' (v : I × Bool) :
      α * Fintype.card (I × Bool) ≤ ((G.comap e).degree v : ℝ) := by
    have hd := Overfull.iso_degree_eq (SimpleGraph.Iso.comap e G) v
    change (G.comap e).degree v = G.degree (e v) at hd
    rw [hcard, hd]
    exact hdegree (e v)
  have hsize' (j : J) : β * Fintype.card (I × Bool) ≤ ((C' j).card : ℝ) := by
    simpa only [C', Finset.card_map, hcard] using hsize j
  obtain ⟨ω, hcut, hprecision, hbalance⟩ := hn₀ I J (G.comap e) C' hK
    (by simpa [hcard] using hn) hdegree' hsize'
  let A := (leftVertices ω).map e.toEmbedding
  let B := (rightVertices ω).map e.toEmbedding
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvA hvB
    change v ∈ (leftVertices ω).map e.toEmbedding at hvA
    change v ∈ (rightVertices ω).map e.toEmbedding at hvB
    rw [Finset.mem_map_equiv] at hvA hvB
    exact Finset.disjoint_left.mp (sides_disjoint ω) hvA hvB
  · ext v
    change (v ∈ (leftVertices ω).map e.toEmbedding ∪
      (rightVertices ω).map e.toEmbedding) ↔ v ∈ univ
    simp only [Finset.mem_union, Finset.mem_map_equiv, Finset.mem_univ, iff_true]
    have h : e.symm v ∈ leftVertices ω ∪ rightVertices ω := by rw [sides_union]; simp
    exact Finset.mem_union.mp h
  · simp only [A, Finset.card_map, leftVertices_card]
  · simp only [B, Finset.card_map, rightVertices_card]
  · intro i
    cases hω : ω i <;>
      simp [A, B, Finset.mem_map_equiv, mem_leftVertices, mem_rightVertices, hω]
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have h := hcut u
    rw [hcard, Overfull.iso_degree_eq (pairCutIso G e ω)] at h
    exact h
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have h := hprecision u
    have hneighbor : (G.comap e).neighborFinset u =
        (G.neighborFinset (e u)).map e.symm.toEmbedding := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.comap_adj,
        Finset.mem_map_equiv, Equiv.symm_symm]
    have hd := Overfull.iso_degree_eq (SimpleGraph.Iso.comap e G) u
    change (G.comap e).degree u = G.degree (e u) at hd
    rw [hneighbor, inverse_inter_card e (G.neighborFinset (e u)) (leftVertices ω),
      inverse_inter_card e (G.neighborFinset (e u)) (rightVertices ω), hd, hcard] at h
    exact h
  · intro j
    have h := hbalance j
    dsimp only [C'] at h
    rw [inverse_inter_card e (C j) (leftVertices ω),
      inverse_inter_card e (C j) (rightVertices ω), Finset.card_map] at h
    exact h

/-- Lifting uses the fixed cluster tolerance, so the robust parameter does
not change when the neighborhood error is made smaller. -/
theorem exists_prescribed_pair_cut_from_clusters_quantitative
    (α δ ε β d γ τ : ℝ) (K : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hεγ : ε ≤ γ / 100) (hβ : 0 < β)
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
        (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
          (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
          |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
        IsBipartiteRobustExpander (cutSidesGraph G A B) (d * γ ^ 2 / 100) (4 * τ) := by
  have hε1 : ε ≤ 1 / 2 := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_prescribed_pair_cut_quantitative α δ ε β K hα hδ hε hε1 hβ
  refine ⟨n₀, ?_⟩
  intro V I J _ _ _ _ _ G _ e R _ C w hK hn hdegree hlarge hw ht hR
    hdisjoint hsize hexception hregular
  obtain ⟨A, B, hAB, hunion, hAcard, hBcard, hpair, hcut, hprecision, hcluster⟩ :=
    hn₀ V I J G e C hK hn hdegree hlarge
  have hunion' : A ∪ B = univ := by
    ext v
    have h := Finset.ext_iff.mp hunion v
    simpa only [Finset.mem_union, Finset.mem_univ] using h
  have hinter (X Y : Finset V) :
      (letI : DecidableEq V := Classical.decEq V; X ∩ Y) = X ∩ Y := by
    ext v
    simp only [Finset.mem_inter]
  simp only [hinter] at hcluster hprecision
  refine ⟨A, B, hAB, hunion', hAcard, hBcard, hpair, hcut, hprecision, ?_⟩
  apply balanced_cluster_cut_expands G R C ε d γ τ w hd hd1 hγ hγτ hτ hε.le hεγ
    hw ht hR hdisjoint hsize hexception hregular A B hAB hunion' (hAcard.trans hBcard.symm)
  · intro j
    have h := (abs_lt.mp (hcluster j).1).2
    rw [hsize j, Finset.inter_comm] at h
    linarith
  · intro j
    have h := (abs_lt.mp (hcluster j).2).1
    rw [hsize j, Finset.inter_comm] at h
    linarith

/-- A robust prescribed-pair cut whose degrees into both sides are within
`δ * |V|` of half the original degree. The positive robust crossing constant
is chosen before `δ`, and only the order threshold subsequently depends
on that requested tolerance. -/
theorem paired_cut_quantitative (α ν τ : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        ∃ A B : Finset V,
          Disjoint A B ∧ A ∪ B = univ ∧ A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
          (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
            (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
          (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
          (∀ v,
            |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
            |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
          IsBipartiteRobustExpander (cutSidesGraph G A B) ξ (4 * τ) := by
  let γ := ν / 4
  let ε := γ / 200
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεγ : ε ≤ γ / 100 := by dsimp [ε]; linarith
  have hγτ : γ ≤ τ := by dsimp [γ]; linarith
  have hν1 : ν ≤ 1 := by linarith
  have hτ0 : 0 ≤ τ := hν.le.trans hντ
  obtain ⟨K, hK, d, hd, hd1, nReg, hReg⟩ :=
    exists_robust_regular_clusters ν τ ε hν hν1 hτ0 hε
  let β := 1 / (2 * (K : ℝ))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨d * γ ^ 2 / 100, by positivity, ?_⟩
  intro δ hδ
  obtain ⟨nCut, hCut⟩ := exists_prescribed_pair_cut_from_clusters_quantitative α δ ε β d γ τ K
    hα hδ hε hεγ hβ hd hd1 hγ hγτ hτ
  refine ⟨max nReg nCut, ?_⟩
  intro V I _ _ _ G _ e hn hdegree hG
  obtain ⟨P, w, C, R, hK', ht, hw, hsize, hdisjoint, hexception, hlarge, hR, hregular⟩ :=
    hReg V G ((le_max_left nReg nCut).trans hn) hG
  apply hCut V I P.parts G e R C w
  · simpa only [Fintype.card_coe] using hK'
  · exact (le_max_right nReg nCut).trans hn
  · exact hdegree
  · intro j
    rw [hsize j]
    exact hlarge
  · exact hw
  · simpa only [γ, Fintype.card_coe] using ht
  · have heq : 2 * γ = ν / 2 := by dsimp [γ]; ring
    simpa only [heq] using hR
  · exact hdisjoint
  · exact hsize
  · simpa only [Finset.compl_eq_univ_sdiff] using hexception
  · exact hregular

end Overfull.PairedCut
