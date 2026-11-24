import Overfull.ColorClasses

/-!
# Colors on the boundary of a saturated odd vertex set

If an odd vertex set attains the internal-edge bound for a proper edge coloring,
each color covers all but one of its vertices internally. Consequently, two
boundary edges of the same color must meet the same vertex inside the set;
properness then makes them the same edge. In particular, this applies to the
odd cliques in the sharpness construction once their edge count is established.
-/

namespace Overfull

open Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- An edge crosses `X` when it has an endpoint in `X` and an endpoint outside `X`. -/
def EdgeCrosses (X : Finset V) (e : G.edgeSet) : Prop :=
  (∃ v, v ∈ X ∧ v ∈ e.val) ∧ (∃ w, w ∉ X ∧ w ∈ e.val)

/-- Vertices covered by the internal edges of one color. -/
noncomputable def EdgeColoring.coveredVertices (c : EdgeColoring G k)
    (X : Finset V) (i : Fin k) : Finset V := by
  classical
  exact ((internalEdges G X).filter (fun e => c.color e = i)).biUnion
    (fun e => e.val.toFinset)

/-- Internally covered vertices belong to the prescribed vertex set. -/
theorem EdgeColoring.coveredVertices_subset (c : EdgeColoring G k)
    (X : Finset V) (i : Fin k) :
    c.coveredVertices X i ⊆ X := by
  classical
  intro v hv
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have heX := (Finset.mem_filter.mp he).1
  have hend : e.val.toFinset ⊆ X := (Finset.mem_filter.mp heX).2
  exact hend hve

/-- Properness makes the internal edges of one color pairwise disjoint,
so they cover exactly twice as many vertices as edges. -/
theorem EdgeColoring.coveredVertices_card (c : EdgeColoring G k)
    (X : Finset V) (i : Fin k) :
    (c.coveredVertices X i).card =
      2 * ((internalEdges G X).filter (fun e => c.color e = i)).card := by
  classical
  let S := (internalEdges G X).filter (fun e => c.color e = i)
  have htwo (e : G.edgeSet) : e.val.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeSet e.property)
  have hdisj : S.toSet.PairwiseDisjoint (fun e => e.val.toFinset) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    apply hne
    exact c.proper (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf)
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  change (S.biUnion (fun e => e.val.toFinset)).card = 2 * S.card
  rw [Finset.card_biUnion hdisj]
  simp [htwo, Nat.mul_comm]

/-- Every color misses exactly one vertex of a saturated odd set. -/
theorem EdgeColoring.uncoveredVertices_card_eq_one [DecidableEq V] (c : EdgeColoring G k)
    (X : Finset V) (hodd : X.card % 2 = 1)
    (hfull : (internalEdges G X).card = k * (X.card / 2)) (i : Fin k) :
    (X \ c.coveredVertices X i).card = 1 := by
  classical
  have htotal := Finset.card_sdiff_add_card_eq_card
    (c.coveredVertices_subset X i)
  rw [c.coveredVertices_card X i,
    c.colorClass_card_eq_of_internalEdges_card_eq X hfull i] at htotal
  omega

/-- An edge outside the internal-edge set cannot meet an internal edge of
its own color. -/
theorem EdgeColoring.not_mem_coveredVertices_of_not_internal
    (c : EdgeColoring G k) (X : Finset V) (e : G.edgeSet)
    (he : e ∉ internalEdges G X) (v : V) (hv : v ∈ e.val) :
    v ∉ c.coveredVertices X (c.color e) := by
  classical
  intro hcovered
  obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hcovered
  have hfX := (Finset.mem_filter.mp hf).1
  have hfcolor := (Finset.mem_filter.mp hf).2
  have hef : e = f := c.proper hv (Sym2.mem_toFinset.mp hvf) hfcolor.symm
  rw [hef] at he
  exact he hfX

/-- On the boundary of a saturated odd vertex set, equal colors force equal
edges. There is no additional bound on the number of external edges at an
individual vertex: properness already treats that case. -/
theorem EdgeColoring.crossing_edges_eq_of_color_eq (c : EdgeColoring G k)
    (X : Finset V) (hodd : X.card % 2 = 1)
    (hfull : (internalEdges G X).card = k * (X.card / 2))
    {e f : G.edgeSet} (he : EdgeCrosses X e) (hf : EdgeCrosses X f)
    (hcolor : c.color e = c.color f) : e = f := by
  classical
  obtain ⟨⟨u, hu, hue⟩, ⟨w, hw, hwe⟩⟩ := he
  obtain ⟨⟨v, hv, hvf⟩, ⟨z, hz, hzf⟩⟩ := hf
  have heout : e ∉ internalEdges G X := by
    intro heX
    have hend : e.val.toFinset ⊆ X := (Finset.mem_filter.mp heX).2
    exact hw (hend (Sym2.mem_toFinset.mpr hwe))
  have hfout : f ∉ internalEdges G X := by
    intro hfX
    have hend : f.val.toFinset ⊆ X := (Finset.mem_filter.mp hfX).2
    exact hz (hend (Sym2.mem_toFinset.mpr hzf))
  have humiss : u ∈ X \ c.coveredVertices X (c.color e) :=
    Finset.mem_sdiff.mpr ⟨hu, c.not_mem_coveredVertices_of_not_internal X e heout u hue⟩
  have hvmiss : v ∈ X \ c.coveredVertices X (c.color e) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hv, ?_⟩
    simpa only [hcolor] using
      c.not_mem_coveredVertices_of_not_internal X f hfout v hvf
  have hsmall : (X \ c.coveredVertices X (c.color e)).card ≤ 1 :=
    (c.uncoveredVertices_card_eq_one X hodd hfull (c.color e)).le
  have huv : u = v := Finset.card_le_one.mp hsmall u humiss v hvmiss
  have huf : u ∈ f.val := by simpa only [huv] using hvf
  exact c.proper hue huf hcolor

/-- The color map is injective on the actual crossing edges of a saturated
odd vertex set. -/
theorem EdgeColoring.boundary_color_injective (c : EdgeColoring G k)
    (X : Finset V) (hodd : X.card % 2 = 1)
    (hfull : (internalEdges G X).card = k * (X.card / 2)) :
    Set.InjOn c.color {e | EdgeCrosses X e} := by
  intro e he f hf hcolor
  exact c.crossing_edges_eq_of_color_eq X hodd hfull he hf hcolor

end Overfull
