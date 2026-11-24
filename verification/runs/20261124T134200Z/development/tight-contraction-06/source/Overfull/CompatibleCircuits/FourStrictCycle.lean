import Overfull.CompatibleCircuits.FourUniformCycle
import Overfull.CompatibleCircuits.FourStrictSupport

/-!
# The square-support branch under strict nonlocal singleton cuts

If all four square bundles are nonempty and no compatible parallel pair
exists, the original half-cut inequalities force equal bundle sizes and
constant, different classes at every square corner. The uniform actual-copy
construction then partitions the entire graph, at arbitrary multiplicity.
-/

namespace Overfull.CompatibleCircuits.UniformCycle

open Finset Classical

def previous : Fin 4 → Fin 4 := ![3,0,1,2]

def next : Fin 4 → Fin 4 := ![1,2,3,0]

theorem previous_ne : ∀ v, v ≠ previous v := by decide
theorem next_ne : ∀ v, v ≠ next v := by decide
theorem previous_ne_next : ∀ v, previous v ≠ next v := by decide

theorem pair_previous : ∀ v, pairs (previous v) = s(v, previous v) := by decide
theorem pair_next : ∀ v, pairs v = s(v, next v) := by decide

theorem incident_pair_iff : ∀ v i, v ∈ pairs i ↔ i = previous v ∨ i = v := by decide

end Overfull.CompatibleCircuits.UniformCycle

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits UniformCycle

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- A square corner has exactly its two neighboring bundles. -/
theorem fourCycle_incident_copies (C : Finset E)
    (hcover : ∀ e ∈ C, ∃ i, Q.edge e = pairs i) (v : Fin 4) :
    C.filter (fun e => v ∈ Q.edge e) =
      Q.edgeBundleOn C v (previous v) ∪ Q.edgeBundleOn C v (next v) := by
  ext e
  simp only [mem_filter, mem_union, mem_edgeBundleOn]
  constructor
  · rintro ⟨he, hv⟩
    obtain ⟨i, hi⟩ := hcover e he
    rw [hi, incident_pair_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inl ⟨he, hi.trans (pair_previous v)⟩
    · exact Or.inr ⟨he, hi.trans (pair_next v)⟩
  · rintro (⟨he, hi⟩ | ⟨he, hi⟩) <;> exact ⟨he, by simp [hi]⟩

/-- The final square-support case is fully decomposable. Original
admissibility and strict nonlocal singleton inequalities are the cut
hypotheses; no class coarsening, selector or partition is assumed. -/
theorem exists_compatibleCircuitPartition_of_strict_four_cycle
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hcover : ∀ e ∈ C, ∃ i, Q.edge e = pairs i)
    (hpositive : ∀ i, (C.filter (fun e => Q.edge e = pairs i)).Nonempty)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2)
    (hstrict : ∀ v w, v ≠ w → ∀ k,
      2 * (Q.classCutOn classOf C w k {v}).card < Q.degreeOn C v) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let B (i : Fin 4) := C.filter (fun e => Q.edge e = pairs i)
  have hprevious (v : Fin 4) : Q.edgeBundleOn C v (previous v) = B (previous v) := by
    ext e
    simp only [mem_edgeBundleOn, B, mem_filter, pair_previous]
  have hnext (v : Fin 4) : Q.edgeBundleOn C v (next v) = B v := by
    ext e
    simp only [mem_edgeBundleOn, B, mem_filter, pair_next]
  have hstructure (v : Fin 4) : (B (previous v)).card = (B v).card ∧
      ∃ k l : K, k ≠ l ∧
        (∀ e ∈ B (previous v), classOf v e = k) ∧
        (∀ e ∈ B v, classOf v e = l) := by
    have h := Q.two_neighbor_bundle_structure classOf C hadmissible hnone
      (previous_ne v) (next_ne v) (previous_ne_next v)
      (by rw [hprevious]; exact hpositive (previous v))
      (by rw [hnext]; exact hpositive v)
      (Q.fourCycle_incident_copies C hcover v)
      (hstrict v (previous v) (previous_ne v))
      (hstrict v (next v) (next_ne v))
    simpa only [hprevious, hnext] using h
  have hequal (i : Fin 4) : (B i).card = (B 0).card := by
    have h1 := (hstructure 1).1
    have h2 := (hstructure 2).1
    have h3 := (hstructure 3).1
    change (B 0).card = (B 1).card at h1
    change (B 1).card = (B 2).card at h2
    change (B 2).card = (B 3).card at h3
    fin_cases i
    · rfl
    · exact h1.symm
    · exact h2.symm.trans h1.symm
    · exact h3.symm.trans (h2.symm.trans h1.symm)
  apply Q.exists_compatibleCircuitPartition_of_uniform_four_cycle
    classOf C (B 0).card hcover hequal
  intro v i j hij hvi hvj e he hei f hf hfj
  obtain ⟨k, l, hkl, hk, hl⟩ := (hstructure v).2
  have heB : e ∈ B i := mem_filter.mpr ⟨he, hei⟩
  have hfB : f ∈ B j := mem_filter.mpr ⟨hf, hfj⟩
  rcases (incident_pair_iff v i).mp hvi with rfl | rfl <;>
    rcases (incident_pair_iff v j).mp hvj with rfl | rfl
  · exact False.elim (hij rfl)
  · rw [hk e heB, hl f hfB]
    exact hkl
  · rw [hl e heB, hk f hfB]
    exact hkl.symm
  · exact False.elim (hij rfl)

end Overfull.Multigraph
