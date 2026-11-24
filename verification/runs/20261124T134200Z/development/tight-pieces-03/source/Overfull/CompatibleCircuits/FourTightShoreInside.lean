import Overfull.CompatibleCircuits.FourTightShoreContraction

/-!
# The inside graph of a tight nonlocal shore

All vertices outside the shore are collapsed to one apex. Every original
copy touching the shore is retained separately. At the apex the prescribed
tight class and its complement are the two classes. For a shore with at
most two vertices, the verified three-label theorem constructs the inside
partition directly from original admissibility and even degrees.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open Overfull.Multigraph

variable {V E K : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)

/-- Keep each shore vertex and collapse every exterior vertex to the apex. -/
def shoreCollapseLabel (X : Finset V) (v : V) : Option X :=
  if hv : v ∈ X then some ⟨v,hv⟩ else none

omit [Fintype V] [Fintype E] in
@[simp] theorem shoreCollapseLabel_eq_none (X : Finset V) (v : V) :
    shoreCollapseLabel X v = none ↔ v ∉ X := by
  classical
  by_cases hv : v ∈ X <;> simp [shoreCollapseLabel,hv]

omit [Fintype V] [Fintype E] in
@[simp] theorem shoreCollapseLabel_eq_some (X : Finset V) (v : V) (x : X) :
    shoreCollapseLabel X v = some x ↔ v = x.val := by
  classical
  by_cases hv : v ∈ X
  · simp [shoreCollapseLabel,hv,Subtype.ext_iff]
  · have hne : v ≠ x.val := fun h => hv (h ▸ x.property)
    simp [shoreCollapseLabel,hv,hne]

omit [Fintype E] in
theorem labelShore_shoreCollapseLabel_apex (X : Finset V) :
    labelShore (shoreCollapseLabel X) {none} = Xᶜ := by
  classical
  ext v
  simp

omit [Fintype E] in
theorem labelShore_shoreCollapseLabel_inside (X : Finset V) (x : X) :
    labelShore (shoreCollapseLabel X) {some x} = {x.val} := by
  classical
  ext v
  simp

omit [Fintype V] in
/-- Exactly the original copies touching the shore survive the collapse. -/
theorem joiningCopies_shoreCollapseLabel (X : Finset V) :
    joiningCopies G (shoreCollapseLabel X) =
      univ.filter (fun e => G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X) := by
  classical
  ext e
  simp only [mem_joiningCopies,mem_filter,mem_univ,true_and]
  have hne := G.endpoints_distinct e
  by_cases ha : G.firstEnd e ∈ X <;> by_cases hb : G.secondEnd e ∈ X <;>
    simp [shoreCollapseLabel,ha,hb,Subtype.ext_iff,hne]

/-- The inside graph retains all actual copies touching the shore. -/
def tightShoreInsideGraph (X : Finset V) :
    Multigraph (Option X) (joiningCopies G (shoreCollapseLabel X)) :=
  joiningQuotient G (shoreCollapseLabel X)

/-- Original incidence classes inside; the chosen tight class versus its
complement at the apex. -/
def tightShoreInsideClass (X : Finset V) (w : V) (k : K) :
    Option X → joiningCopies G (shoreCollapseLabel X) → (V × K) ⊕ Bool :=
  coarsenTightClassAt (joiningIncidenceClass G (shoreCollapseLabel X) classOf)
    none (w,k)

/-- The original nonlocal tight cut becomes a local tight class at the apex. -/
theorem tightShoreInsideClass_local_tight (X : Finset V) (w : V) (k : K)
    (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    2 * (univ.filter (fun e => none ∈ (tightShoreInsideGraph G X).edge e ∧
      joiningIncidenceClass G (shoreCollapseLabel X) classOf none e = (w,k))).card =
      (tightShoreInsideGraph G X).degreeOn univ none := by
  classical
  let H := tightShoreInsideGraph G X
  let c := joiningIncidenceClass G (shoreCollapseLabel X) classOf
  have hclass := congrArg Finset.card
    (joiningIncidenceClass_classCutOn_image G (shoreCollapseLabel X) classOf
      none w k {none})
  rw [card_image_of_injective _ Subtype.val_injective,
    if_pos ((shoreCollapseLabel_eq_none X w).mpr hw),
    labelShore_shoreCollapseLabel_apex,G.classCutOn_compl,
    (joiningQuotient G (shoreCollapseLabel X)).classCutOn_singleton_self] at hclass
  have hdegree : H.degreeOn univ none = (G.cutOn univ X).card := by
    change (joiningQuotient G (shoreCollapseLabel X)).degree none = _
    rw [joiningQuotient_degree_eq_cut,labelShore_shoreCollapseLabel_apex,G.cutOn_compl]
  have h := (congrArg (fun n : ℕ => 2 * n) hclass).trans htight
  convert h.trans hdegree.symm using 1
  congr 2
  ext e
  simp only [mem_filter]
  rfl

/-- Global admissibility of the constructed inside graph, including both
apex classes, follows from the original tight nonlocal class cut. -/
theorem tightShoreInside_admissible (X : Finset V) (w : V) (k : K)
    (hadmissible : G.AdmissibleOn classOf univ) (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    (tightShoreInsideGraph G X).AdmissibleOn (tightShoreInsideClass G classOf X w k)
      univ := by
  classical
  apply (tightShoreInsideGraph G X).admissibleOn_coarsenTightClassAt
    (joiningIncidenceClass G (shoreCollapseLabel X) classOf)
    (joiningIncidenceClass_admissible G (shoreCollapseLabel X) classOf hadmissible)
  convert tightShoreInsideClass_local_tight G classOf X w k hw htight using 1
  congr 2
  ext e
  simp only [mem_filter]

/-- The contraction has even degrees; the apex degree is the original cut. -/
theorem tightShoreInside_even_degrees (X : Finset V)
    (heven : ∀ v, Even (G.degreeOn univ v)) (x : Option X) :
    Even ((tightShoreInsideGraph G X).degreeOn univ x) :=
  joiningQuotient_even_degrees_of_even_degrees G (shoreCollapseLabel X) heven x

/-- Construct the first partition of the tight-shore reduction. No
partition or path-pairing hypothesis is assumed. -/
theorem exists_tightShoreInside_partition (X : Finset V) (hX : X.card ≤ 2)
    (w : V) (k : K) (hadmissible : G.AdmissibleOn classOf univ)
    (heven : ∀ v, Even (G.degreeOn univ v)) (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    Nonempty ((tightShoreInsideGraph G X).CompatibleCircuitPartition
      (tightShoreInsideClass G classOf X w k) univ) := by
  apply (tightShoreInsideGraph G X).exists_compatibleCircuitPartition_of_card_le_three
    (by simpa using Nat.add_le_add_right hX 1)
    (tightShoreInsideClass G classOf X w k) univ
  · exact tightShoreInside_admissible G classOf X w k hadmissible hw htight
  · exact tightShoreInside_even_degrees G X heven

end Overfull.FourOdd
