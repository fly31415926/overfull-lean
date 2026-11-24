import Overfull.CompatibleCircuits.FourAdmissibleClassification

/-!
# Four-regular compatible circuit partitions on four labels

The graph template, original-copy bijection, and balanced pair classes are
all constructed. The public result assumes only degree four and the original
half-cut inequalities. This is a regular special case, not the unrestricted
four-label existence theorem.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits CompatibleCircuits.FourRegular

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

theorem exists_compatibleCircuitPartition_of_four_regular_local
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hregular : ∀ v, Q.degreeOn C v = 4)
    (hlocal : ∀ v k, (C.filter (fun e => v ∈ Q.edge e ∧ classOf v e=k)).card ≤ 2) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  obtain ⟨t,r,φ,hφ⟩ := exists_template_copy_equiv Q C hregular
  let σ := permutation r
  let ψ : Fin 8 ↪ E := φ.toEmbedding.trans (Function.Embedding.subtype (fun e => e ∈ C))
  have hψ (e : Fin 8) : Q.edge (ψ e) = Sym2.map σ ((graph t).edge e) := hφ e
  have hmem (e : Fin 8) : ψ e ∈ C := (φ e).property
  let f : Fin 4 → Fin 4 → K := fun v i => classOf (σ v) (ψ (port t v i))
  have hf (v : Fin 4) (k : K) : (univ.filter (fun i => f v i=k)).card ≤ 2 := by
    let S := univ.filter (fun i => f v i=k)
    let χ : Fin 4 ↪ E := ⟨fun i => ψ (port t v i),ψ.injective.comp (port_injective t v)⟩
    have hsub : S.map χ ⊆ C.filter (fun e => σ v ∈ Q.edge e ∧ classOf (σ v) e=k) := by
      intro e he
      obtain ⟨i,hi,rfl⟩ := mem_map.mp he
      have hv : v ∈ (graph t).edge (port t v i) := by
        simpa only [graph,Sym2.mem_iff] using port_incident t v i
      refine mem_filter.mpr ⟨hmem _,?_,(mem_filter.mp hi).2⟩
      change σ v ∈ Q.edge (ψ (port t v i))
      rw [hψ]
      exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩
    have hh := (card_le_card hsub).trans (hlocal (σ v) k)
    simpa only [card_map] using hh
  choose choice hchoice using (fun v => four_incidence_pair_coarsening (f v) (hf v))
  obtain ⟨P⟩ := exists_template_partition t choice
  let classes' : Fin 4 → Fin 8 → K := fun v e => classOf (σ v) (ψ e)
  have hcomp (D : Finset (Fin 8)) (hD : D ∈ P.parts) :
      (graph t).Compatible classes' D := by
    intro v e he hve e' he' hve' hclasses
    obtain ⟨i,hi⟩ := port_surjective t v e (by
      simpa only [graph,Sym2.mem_iff] using hve)
    obtain ⟨j,hj⟩ := port_surjective t v e' (by
      simpa only [graph,Sym2.mem_iff] using hve')
    have hpair := hchoice v i j (show f v i=f v j by
      simpa only [f,hi,hj,classes'] using hclasses)
    apply P.compatible D hD v e he hve e' he' hve'
    rw [← hi,← hj]
    simpa only [classes,rank_port] using hpair
  let P' : (graph t).CompatibleCircuitPartition classes' univ := {
    parts := P.parts
    circuit := P.circuit
    compatible := hcomp
    disjoint := P.disjoint
    cover := P.cover }
  let A := (graph t).renameVertices σ
  let P'' : A.CompatibleCircuitPartition (fun v e => classOf v (ψ e)) univ := {
    parts := P'.parts
    circuit := fun D hD => (P'.circuit D hD).renameVertices (graph t) σ
    compatible := by
      intro D hD v e he hve e' he' hve' hclasses
      apply P'.compatible D hD (σ.symm v) e he
        (((graph t).renameVertices_incident σ e v).mp hve)
        e' he' (((graph t).renameVertices_incident σ e' v).mp hve')
      simpa only [classes',Equiv.apply_symm_apply] using hclasses
    disjoint := P'.disjoint
    cover := P'.cover }
  let R := P''.map_copies A Q ψ hψ classOf
  have hcover : univ.map ψ = C := by
    ext e
    constructor
    · intro he
      obtain ⟨i,_,rfl⟩ := mem_map.mp he
      exact hmem i
    · intro he
      obtain ⟨i,hi⟩ := φ.surjective ⟨e,he⟩
      exact mem_map.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩
  exact ⟨hcover ▸ R⟩

/-- Exact actual-copy decomposition for four-regular graphs on four labels.
No template, class pairing, or circuit partition is supplied as a hypothesis. -/
theorem exists_compatibleCircuitPartition_of_four_regular
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hregular : ∀ v, Q.degreeOn C v = 4)
    (hadmissible : Q.AdmissibleOn classOf C) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  apply exists_compatibleCircuitPartition_of_four_regular_local Q classOf C hregular
  intro v k
  have hh := hadmissible.local_class_bound Q v k
  rw [hregular] at hh
  have hh' : 2 * (C.filter (fun e => v ∈ Q.edge e ∧ classOf v e=k)).card ≤ 4 := by
    convert hh using 1
    congr 2
    ext e
    simp only [mem_filter]
  omega

end Overfull.Multigraph
