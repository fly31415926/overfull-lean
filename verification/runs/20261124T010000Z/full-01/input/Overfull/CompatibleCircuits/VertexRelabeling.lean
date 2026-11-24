import Overfull.CompatibleCircuits.ThreeLabelBundles

/-!
# Relabeling vertices while preserving actual edge copies

Vertex equivalences preserve every incidence, cut, compatibility condition,
and circuit.  The edge-copy type and each selected finite set stay fixed.
This permits sorting the three bundle sizes without losing copy identities.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V W E K : Type*} (G : Multigraph V E)

/-- Rename the endpoints; retain the same actual edge-copy type. -/
def renameVertices (φ : V ≃ W) : Multigraph W E where
  edge e := Sym2.map φ (G.edge e)
  loopless e := by
    rw [Sym2.isDiag_map φ.injective]
    exact G.loopless e

@[simp] theorem renameVertices_incident (φ : V ≃ W) (e : E) (w : W) :
    w ∈ (G.renameVertices φ).edge e ↔ φ.symm w ∈ G.edge e := by
  change w ∈ Sym2.map φ (G.edge e) ↔ _
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hw
    exact ⟨φ.symm w, hw, φ.apply_symm_apply w⟩

theorem renameVertices_degreeOn (φ : V ≃ W) (C : Finset E) (w : W) :
    (G.renameVertices φ).degreeOn C w = G.degreeOn C (φ.symm w) := by
  simp only [degreeOn, G.renameVertices_incident]

theorem renameVertices_edgeSupport (φ : V ≃ W) (C : Finset E) :
    (G.renameVertices φ).edgeSupport C = (G.edgeSupport C).map φ.toEmbedding := by
  ext w
  simp only [mem_edgeSupport, G.renameVertices_incident, mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨φ.symm w, ⟨e, he, hw⟩, φ.apply_symm_apply w⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, by simpa using hv⟩

theorem renameVertices_cutOn (φ : V ≃ W) (C : Finset E) (X : Finset W) :
    (G.renameVertices φ).cutOn C X = G.cutOn C (X.map φ.symm.toEmbedding) := by
  ext e
  have hedge : s((G.renameVertices φ).firstEnd e, (G.renameVertices φ).secondEnd e) =
      s(φ (G.firstEnd e), φ (G.secondEnd e)) := by
    rw [(G.renameVertices φ).edge_eq]
    change Sym2.map φ (G.edge e) = _
    rw [← G.edge_eq e, Sym2.map_pair_eq]
  rcases Sym2.eq_iff.mp hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [mem_cutOn, ha, hb]
  · simp [mem_cutOn, ha, hb]
    tauto

theorem renameVertices_classCutOn (φ : V ≃ W) (classOf : V → E → K)
    (C : Finset E) (w : W) (k : K) (X : Finset W) :
    (G.renameVertices φ).classCutOn (fun w e => classOf (φ.symm w) e) C w k X =
      G.classCutOn classOf C (φ.symm w) k (X.map φ.symm.toEmbedding) := by
  simp only [classCutOn, G.renameVertices_cutOn, G.renameVertices_incident]

theorem renameVertices_admissibleOn (φ : V ≃ W) (classOf : V → E → K)
    (C : Finset E) :
    (G.renameVertices φ).AdmissibleOn (fun w e => classOf (φ.symm w) e) C ↔
      G.AdmissibleOn classOf C := by
  constructor
  · intro h v k X
    have hh := h (φ v) k (X.map φ.toEmbedding)
    simpa [G.renameVertices_classCutOn, G.renameVertices_cutOn, map_map] using hh
  · intro h w k X
    simpa only [G.renameVertices_classCutOn, G.renameVertices_cutOn] using
      h (φ.symm w) k (X.map φ.symm.toEmbedding)

theorem renameVertices_compatible (φ : V ≃ W) (classOf : V → E → K)
    (C : Finset E) :
    (G.renameVertices φ).Compatible (fun w e => classOf (φ.symm w) e) C ↔
      G.Compatible classOf C := by
  constructor
  · intro h v e he hve f hf hvf heq
    exact h (φ v) e he (by simpa using hve) f hf (by simpa using hvf)
      (by simpa using heq)
  · intro h w e he hwe f hf hwf heq
    exact h (φ.symm w) e he ((G.renameVertices_incident φ e w).mp hwe)
      f hf ((G.renameVertices_incident φ f w).mp hwf) heq

/-- A renamed circuit has exactly the same original copies. -/
theorem IsCircuit.renameVertices (φ : V ≃ W) {C : Finset E} (hC : G.IsCircuit C) :
    (G.renameVertices φ).IsCircuit C := by
  refine ⟨hC.1, ?_, ?_⟩
  · intro w hw
    rw [G.renameVertices_degreeOn]
    apply hC.2.1
    obtain ⟨e, he, hwe⟩ := (mem_edgeSupport _ _ _).mp hw
    exact (G.mem_edgeSupport C _).mpr
      ⟨e, he, (G.renameVertices_incident φ e w).mp hwe⟩
  · intro X hX hnonempty hproper
    rw [G.renameVertices_cutOn]
    apply hC.2.2
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
      obtain ⟨e, he, hwe⟩ := (mem_edgeSupport _ _ _).mp (hX hw)
      exact (G.mem_edgeSupport C _).mpr
        ⟨e, he, (G.renameVertices_incident φ e w).mp hwe⟩
    · exact hnonempty.map
    · intro heq
      apply hproper
      rw [G.renameVertices_edgeSupport, ← heq]
      simp [map_map]

theorem renameVertices_isCircuit (φ : V ≃ W) (C : Finset E) :
    (G.renameVertices φ).IsCircuit C ↔ G.IsCircuit C := by
  constructor
  · intro h
    have hh := h.renameVertices (G.renameVertices φ) φ.symm
    have hgraph : (G.renameVertices φ).renameVertices φ.symm = G := by
      cases G
      simp [renameVertices, Sym2.map_map]
    simpa only [hgraph] using hh
  · exact fun h => h.renameVertices G φ

theorem renameVertices_edgeBundleOn (φ : V ≃ W) (C : Finset E) (u v : V) :
    (G.renameVertices φ).edgeBundleOn C (φ u) (φ v) = G.edgeBundleOn C u v := by
  ext e
  simp only [mem_edgeBundleOn, renameVertices, ← Sym2.map_pair_eq,
    (Sym2.map.injective φ.injective).eq_iff]

theorem renameVertices_edgeBundleOn_symm (φ : V ≃ W) (C : Finset E) (u v : W) :
    (G.renameVertices φ).edgeBundleOn C u v =
      G.edgeBundleOn C (φ.symm u) (φ.symm v) := by
  simpa using G.renameVertices_edgeBundleOn φ C (φ.symm u) (φ.symm v)

/-- Sort the three actual bundle sizes by a permutation of the vertices. -/
theorem exists_threeLabel_sorted_renaming (Q : Multigraph (Fin 3) E) (C : Finset E) :
    ∃ φ : Equiv.Perm (Fin 3),
      ((Q.renameVertices φ).edgeBundleOn C 0 2).card ≤
        ((Q.renameVertices φ).edgeBundleOn C 0 1).card ∧
      ((Q.renameVertices φ).edgeBundleOn C 1 2).card ≤
        ((Q.renameVertices φ).edgeBundleOn C 0 2).card := by
  let x := (Q.edgeBundleOn C 0 1).card
  let y := (Q.edgeBundleOn C 0 2).card
  let z := (Q.edgeBundleOn C 1 2).card
  have h10 := Q.edgeBundleOn_swap C 1 0
  have h20 := Q.edgeBundleOn_swap C 2 0
  have h21 := Q.edgeBundleOn_swap C 2 1
  by_cases hxy : y ≤ x
  · by_cases hyz : z ≤ y
    · refine ⟨Equiv.refl _, ?_⟩
      simpa [renameVertices_edgeBundleOn_symm, x, y, z] using And.intro hxy hyz
    · by_cases hxz : z ≤ x
      · refine ⟨Equiv.swap 0 1, ?_⟩
        simpa [renameVertices_edgeBundleOn_symm, Equiv.swap_apply_def,
          h10, h20, h21, x, y, z] using And.intro hxz (le_of_not_ge hyz)
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_⟩
        simpa [renameVertices_edgeBundleOn_symm, Equiv.swap_apply_def,
          h10, h20, h21, x, y, z] using And.intro (le_of_not_ge hxz) hxy
  · by_cases hxz : z ≤ x
    · refine ⟨Equiv.swap 1 2, ?_⟩
      simpa [renameVertices_edgeBundleOn_symm, Equiv.swap_apply_def,
        h10, h20, h21, x, y, z] using And.intro (le_of_not_ge hxy) hxz
    · by_cases hyz : z ≤ y
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
        simpa [renameVertices_edgeBundleOn_symm, Equiv.swap_apply_def,
          h10, h20, h21, x, y, z] using And.intro hyz (le_of_not_ge hxz)
      · refine ⟨Equiv.swap 0 2, ?_⟩
        simpa [renameVertices_edgeBundleOn_symm, Equiv.swap_apply_def,
          h10, h20, h21, x, y, z] using
            And.intro (le_of_not_ge hyz) (le_of_not_ge hxy)

end Overfull.Multigraph
