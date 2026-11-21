import Overfull.Multigraph

/-!
# Circuits with forbidden incidence classes

All finite sets below consist of actual edge copies.  In particular, a
two-edge circuit may contain two distinct parallel copies.  Connectivity is
expressed by the nonempty proper cuts of the incident vertex set.

This file defines the compatible-circuit problem and proves elementary
consequences of its definitions.  It does not assume or assert the existence
theorem of Fan and Zhang.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*} (G : Multigraph V E)

/-- The vertices incident with the selected actual edge copies. -/
noncomputable def edgeSupport (C : Finset E) : Finset V :=
  C.biUnion (fun e => (G.edge e).toFinset)

/-- Degree within a finite edge-copy set, including parallel multiplicity. -/
noncomputable def degreeOn (C : Finset E) (v : V) : ℕ :=
  (C.filter (fun e => v ∈ G.edge e)).card

/-- The selected edge copies crossing a shore. -/
noncomputable def cutOn (C : Finset E) (X : Finset V) : Finset E :=
  C.filter (fun e => (G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X))

@[simp] theorem mem_edgeSupport (C : Finset E) (v : V) :
    v ∈ G.edgeSupport C ↔ ∃ e ∈ C, v ∈ G.edge e := by
  simp [edgeSupport, Sym2.mem_toFinset]

@[simp] theorem mem_cutOn (C : Finset E) (X : Finset V) (e : E) :
    e ∈ G.cutOn C X ↔ e ∈ C ∧
      (G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X) := by
  simp [cutOn]

theorem degreeOn_pos_iff (C : Finset E) (v : V) :
    0 < G.degreeOn C v ↔ v ∈ G.edgeSupport C := by
  simp [degreeOn, Finset.card_pos, Finset.Nonempty, mem_edgeSupport]

theorem degreeOn_eq_zero_of_not_mem {C : Finset E} {v : V}
    (hv : v ∉ G.edgeSupport C) : G.degreeOn C v = 0 := by
  have := (G.degreeOn_pos_iff C v).not.mpr hv
  omega

/-- A nonempty connected 2-regular edge-copy subgraph. -/
def IsCircuit (C : Finset E) : Prop :=
  C.Nonempty ∧
  (∀ v ∈ G.edgeSupport C, G.degreeOn C v = 2) ∧
  ∀ X : Finset V, X ⊆ G.edgeSupport C → X.Nonempty →
    X ≠ G.edgeSupport C → (G.cutOn C X).Nonempty

/-- No incidence class occurs twice in the selected edge set at a vertex.
Values of `classOf` on nonincident pairs are irrelevant. -/
def Compatible (classOf : V → E → K) (C : Finset E) : Prop :=
  ∀ v e, e ∈ C → v ∈ G.edge e →
    ∀ f, f ∈ C → v ∈ G.edge f → classOf v e = classOf v f → e = f

theorem Compatible.mono {classOf : V → E → K} {C D : Finset E}
    (h : G.Compatible classOf C) (hDC : D ⊆ C) :
    G.Compatible classOf D := by
  intro v e he hve f hf hvf hclass
  exact h v e (hDC he) hve f (hDC hf) hvf hclass

/-- The portion of one incidence class crossing a shore. -/
noncomputable def classCutOn (classOf : V → E → K)
    (C : Finset E) (v : V) (k : K) (X : Finset V) : Finset E :=
  (G.cutOn C X).filter (fun e => v ∈ G.edge e ∧ classOf v e = k)

/-- The exact half-cut condition for the selected edge-copy graph. -/
def AdmissibleOn (classOf : V → E → K) (C : Finset E) : Prop :=
  ∀ v k X, 2 * (G.classCutOn classOf C v k X).card ≤ (G.cutOn C X).card

/-- A genuine partition of the selected copies into compatible circuits. -/
structure CompatibleCircuitPartition (classOf : V → E → K) (C : Finset E) where
  parts : Finset (Finset E)
  circuit : ∀ D ∈ parts, G.IsCircuit D
  compatible : ∀ D ∈ parts, G.Compatible classOf D
  disjoint : ∀ D ∈ parts, ∀ D' ∈ parts, D ≠ D' → Disjoint D D'
  cover : parts.biUnion id = C

/-- The handshake identity for an arbitrary finite set of edge copies. -/
theorem degreeOn_sum (C : Finset E) :
    (∑ v ∈ G.edgeSupport C, G.degreeOn C v) = 2 * C.card := by
  have hswap : (∑ v ∈ G.edgeSupport C, G.degreeOn C v) =
      ∑ e ∈ C, ((G.edgeSupport C).filter (fun v => v ∈ G.edge e)).card := by
    simp only [degreeOn, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  have hfilter (e : E) (he : e ∈ C) :
      (G.edgeSupport C).filter (fun v => v ∈ G.edge e) = (G.edge e).toFinset := by
    ext v
    simp only [Finset.mem_filter, mem_edgeSupport, Sym2.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨⟨e, he, h⟩, h⟩⟩
  calc
    (∑ e ∈ C, ((G.edgeSupport C).filter (fun v => v ∈ G.edge e)).card) =
        ∑ _e ∈ C, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hfilter e he, Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)]
    _ = 2 * C.card := by simp [Nat.mul_comm]

/-- A circuit has as many actual edge copies as incident vertices. -/
theorem IsCircuit.card_eq_support_card {C : Finset E} (hC : G.IsCircuit C) :
    C.card = (G.edgeSupport C).card := by
  have hsum := G.degreeOn_sum C
  have hdegrees : (∑ v ∈ G.edgeSupport C, G.degreeOn C v) =
      2 * (G.edgeSupport C).card := by
    calc
      _ = ∑ _v ∈ G.edgeSupport C, 2 :=
        Finset.sum_congr rfl (fun v hv => hC.2.1 v hv)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- In a quotient on four vertices, every circuit has at most four copies. -/
theorem IsCircuit.card_le [Fintype V] {C : Finset E} (hC : G.IsCircuit C) :
    C.card ≤ Fintype.card V := by
  rw [hC.card_eq_support_card]
  exact Finset.card_le_univ _

theorem Compatible.classCutOn_card_le_one {classOf : V → E → K}
    {C : Finset E} (h : G.Compatible classOf C) (v : V) (k : K) (X : Finset V) :
    (G.classCutOn classOf C v k X).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he, hve, heclass⟩ := Finset.mem_filter.mp he
  obtain ⟨hf, hvf, hfclass⟩ := Finset.mem_filter.mp hf
  exact h v e (G.mem_cutOn C X e |>.mp he).1 hve
    f (G.mem_cutOn C X f |>.mp hf).1 hvf (heclass.trans hfclass.symm)

end Overfull.Multigraph
