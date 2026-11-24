import Overfull.CompatibleCircuits.ThreeLabelBundles

/-!
# Padding vertex sets while retaining actual edge copies

An injective vertex map embeds a loopless multigraph into a larger vertex
type. The additional vertices are isolated. Incidence classes use `Option`
so the construction does not assume that the original class type is
inhabited. Cuts, admissibility and compatible circuit partitions transfer
without changing any actual edge copy or selected finite set.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V W E K : Type*} (G : Multigraph V E)

/-- Embed endpoints injectively and leave all actual copies unchanged. -/
def embedVertices (φ : V ↪ W) : Multigraph W E where
  edge e := Sym2.map φ (G.edge e)
  loopless e := by
    rw [Sym2.isDiag_map φ.injective]
    exact G.loopless e

@[simp] theorem embedVertices_incident (φ : V ↪ W) (e : E) (w : W) :
    w ∈ (G.embedVertices φ).edge e ↔ ∃ v, v ∈ G.edge e ∧ φ v = w := by
  exact Sym2.mem_map

@[simp] theorem embedVertices_incident_image (φ : V ↪ W) (e : E) (v : V) :
    φ v ∈ (G.embedVertices φ).edge e ↔ v ∈ G.edge e := by
  rw [G.embedVertices_incident]
  constructor
  · rintro ⟨u, hu, huv⟩
    simpa [φ.injective huv] using hu
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem embedVertices_not_incident (φ : V ↪ W) {w : W}
    (hw : ¬ ∃ v, φ v = w) (e : E) : w ∉ (G.embedVertices φ).edge e := by
  rintro h
  obtain ⟨v, _, hv⟩ := (G.embedVertices_incident φ e w).mp h
  exact hw ⟨v, hv⟩

/-- Original classes on image vertices; a dummy value on isolated padding
vertices. No inhabitant of the original class type is chosen. -/
noncomputable def embedIncidenceClasses (φ : V ↪ W) (classOf : V → E → K)
    (w : W) (e : E) : Option K :=
  if hw : ∃ v, φ v = w then some (classOf (Classical.choose hw) e) else none

@[simp] theorem embedIncidenceClasses_image (φ : V ↪ W)
    (classOf : V → E → K) (v : V) (e : E) :
    embedIncidenceClasses φ classOf (φ v) e = some (classOf v e) := by
  have hv : ∃ u, φ u = φ v := ⟨v, rfl⟩
  rw [embedIncidenceClasses, dif_pos hv]
  have hchoice : Classical.choose hv = v := φ.injective (Classical.choose_spec hv)
  rw [hchoice]

theorem embedVertices_degreeOn (φ : V ↪ W) (C : Finset E) (v : V) :
    (G.embedVertices φ).degreeOn C (φ v) = G.degreeOn C v := by
  simp only [degreeOn, G.embedVertices_incident_image]

theorem embedVertices_degreeOn_zero (φ : V ↪ W) (C : Finset E) {w : W}
    (hw : ¬ ∃ v, φ v = w) : (G.embedVertices φ).degreeOn C w = 0 := by
  simp [degreeOn, G.embedVertices_not_incident φ hw]

theorem embedVertices_even_degrees (φ : V ↪ W) {C : Finset E}
    (heven : ∀ v, Even (G.degreeOn C v)) :
    ∀ w, Even ((G.embedVertices φ).degreeOn C w) := by
  intro w
  by_cases hw : ∃ v, φ v = w
  · obtain ⟨v, rfl⟩ := hw
    simpa only [G.embedVertices_degreeOn] using heven v
  · simp [G.embedVertices_degreeOn_zero φ C hw]

theorem embedVertices_edgeSupport (φ : V ↪ W) (C : Finset E) :
    (G.embedVertices φ).edgeSupport C = (G.edgeSupport C).map φ := by
  ext w
  simp only [mem_edgeSupport, G.embedVertices_incident, mem_map]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩
    exact ⟨v, ⟨e, he, hv⟩, rfl⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, v, hv, rfl⟩

/-- A shore on the larger type pulls back to its original vertices. -/
theorem embedVertices_cutOn [Fintype V] (φ : V ↪ W) (C : Finset E) (X : Finset W) :
    (G.embedVertices φ).cutOn C X =
      G.cutOn C (univ.filter (fun v => φ v ∈ X)) := by
  ext e
  have hedge : s((G.embedVertices φ).firstEnd e, (G.embedVertices φ).secondEnd e) =
      s(φ (G.firstEnd e), φ (G.secondEnd e)) := by
    rw [(G.embedVertices φ).edge_eq]
    change Sym2.map φ (G.edge e) = _
    rw [← G.edge_eq e, Sym2.map_pair_eq]
  rcases Sym2.eq_iff.mp hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [mem_cutOn, ha, hb]
  · simp [mem_cutOn, ha, hb]
    tauto

theorem embedVertices_cutOn_map [Fintype V] (φ : V ↪ W)
    (C : Finset E) (X : Finset V) :
    (G.embedVertices φ).cutOn C (X.map φ) = G.cutOn C X := by
  rw [G.embedVertices_cutOn]
  congr 1
  ext v
  simp

theorem embedVertices_classCutOn_image [Fintype V] (φ : V ↪ W)
    (classOf : V → E → K) (C : Finset E) (v : V) (k : K) (X : Finset W) :
    (G.embedVertices φ).classCutOn (embedIncidenceClasses φ classOf) C (φ v) (some k) X =
      G.classCutOn classOf C v k (univ.filter (fun u => φ u ∈ X)) := by
  simp only [classCutOn, G.embedVertices_cutOn, G.embedVertices_incident_image,
    embedIncidenceClasses_image, Option.some.injEq]

theorem embedVertices_classCutOn_image_map [Fintype V] (φ : V ↪ W)
    (classOf : V → E → K) (C : Finset E) (v : V) (k : K) (X : Finset V) :
    (G.embedVertices φ).classCutOn (embedIncidenceClasses φ classOf)
      C (φ v) (some k) (X.map φ) = G.classCutOn classOf C v k X := by
  rw [G.embedVertices_classCutOn_image]
  congr 1
  ext u
  simp

/-- Padding isolated vertices preserves all original half-cut inequalities. -/
theorem embedVertices_admissibleOn [Fintype V] (φ : V ↪ W)
    (classOf : V → E → K) (C : Finset E) :
    (G.embedVertices φ).AdmissibleOn (embedIncidenceClasses φ classOf) C ↔
      G.AdmissibleOn classOf C := by
  constructor
  · intro h v k X
    have hh := h (φ v) (some k) (X.map φ)
    simpa only [G.embedVertices_classCutOn_image_map, G.embedVertices_cutOn_map] using hh
  · intro h w q X
    by_cases hw : ∃ v, φ v = w
    · obtain ⟨v, rfl⟩ := hw
      cases q with
      | none => simp [classCutOn, embedIncidenceClasses_image]
      | some k =>
          simpa only [G.embedVertices_classCutOn_image, G.embedVertices_cutOn] using
            h v k (univ.filter (fun u => φ u ∈ X))
    · have hempty : (G.embedVertices φ).classCutOn (embedIncidenceClasses φ classOf)
          C w q X = ∅ := by
        simp [classCutOn, G.embedVertices_not_incident φ hw]
      rw [hempty, card_empty, Nat.mul_zero]
      exact Nat.zero_le _

theorem embedVertices_compatible (φ : V ↪ W) (classOf : V → E → K) (C : Finset E) :
    (G.embedVertices φ).Compatible (embedIncidenceClasses φ classOf) C ↔
      G.Compatible classOf C := by
  constructor
  · intro h v e he hve f hf hvf heq
    apply h (φ v) e he ((G.embedVertices_incident_image φ e v).mpr hve)
      f hf ((G.embedVertices_incident_image φ f v).mpr hvf)
    simpa only [embedIncidenceClasses_image] using congrArg some heq
  · intro h w e he hwe f hf hwf heq
    obtain ⟨v, hve, rfl⟩ := (G.embedVertices_incident φ e w).mp hwe
    apply h v e he hve f hf ((G.embedVertices_incident_image φ f v).mp hwf)
    simpa only [embedIncidenceClasses_image, Option.some.injEq] using heq

/-- Pull an embedded circuit back without changing its actual copies. -/
theorem IsCircuit.of_embedVertices [Fintype V] (φ : V ↪ W) {C : Finset E}
    (hC : (G.embedVertices φ).IsCircuit C) : G.IsCircuit C := by
  refine ⟨hC.1, ?_, ?_⟩
  · intro v hv
    rw [← G.embedVertices_degreeOn φ]
    apply hC.2.1
    rw [G.embedVertices_edgeSupport]
    exact mem_map.mpr ⟨v, hv, rfl⟩
  · intro X hX hnonempty hproper
    have hsub : X.map φ ⊆ (G.embedVertices φ).edgeSupport C := by
      rw [G.embedVertices_edgeSupport]
      exact map_subset_map.mpr hX
    have hproper' : X.map φ ≠ (G.embedVertices φ).edgeSupport C := by
      rw [G.embedVertices_edgeSupport]
      intro heq
      exact hproper (map_injective φ heq)
    have hcross := hC.2.2 (X.map φ) hsub hnonempty.map hproper'
    simpa only [G.embedVertices_cutOn_map] using hcross

/-- Pull back an exact compatible circuit partition. The parts, their
disjointness, and their union are unchanged edge-copy finite sets. -/
def CompatibleCircuitPartition.of_embedVertices [Fintype V] (φ : V ↪ W)
    {classOf : V → E → K} {C : Finset E}
    (P : (G.embedVertices φ).CompatibleCircuitPartition
      (embedIncidenceClasses φ classOf) C) : G.CompatibleCircuitPartition classOf C where
  parts := P.parts
  circuit D hD := (P.circuit D hD).of_embedVertices G φ
  compatible D hD := (G.embedVertices_compatible φ classOf D).mp (P.compatible D hD)
  disjoint := P.disjoint
  cover := P.cover

end Overfull.Multigraph
