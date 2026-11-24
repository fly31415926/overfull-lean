import Overfull.CompatibleCircuits.FourStrictSelection

/-!
# Safe short-circuit selection from strict nonlocal inequalities

Local tight-class coarsening preserves all global inequalities, including
strict nonlocal ones. The complete support selector therefore finds a
coarse-compatible pair or triangle. It meets every original local tight
class, so its deletion preserves original admissibility and even degrees.
-/

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- Every nonempty admissible Eulerian input with strict nonlocal bounds
has a safely removable actual pair or triangle. Neither a selector nor a
partition is an assumption; residual strictness is not asserted. -/
theorem exists_safe_short_circuit_of_four_strictNonlocal
    (classOf : Fin 4 → E → K) (C : Finset E) (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hstrict : Q.StrictNonlocalOn classOf C) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      D.card ≤ 3 ∧ Q.AdmissibleOn classOf (C \ D) ∧
      (∀ v, Even (Q.degreeOn (C \ D) v)) ∧ (C \ D).card < C.card := by
  obtain ⟨e, _⟩ := hC
  letI : Nonempty K := ⟨classOf 0 e⟩
  obtain ⟨L, hLadmissible, hLstrict⟩ :=
    Q.exists_strict_globally_admissible_localCoarsening classOf C hadmissible hstrict
  obtain ⟨D, hDC, hD, hcomp, hsmall⟩ :=
    Q.exists_short_compatible_circuit_of_four_strictNonlocal
      (fun v e => (L v).coarse e) C hC hLadmissible hLstrict
  refine ⟨D, hDC, hD, hcomp.of_localCoarsening Q classOf C L, hsmall,
    Q.admissibleOn_sdiff_of_strict_nonlocal_small_coarse_circuit classOf
      hDC hD hsmall hadmissible heven hstrict L hcomp,
    Q.even_degreeOn_sdiff hDC heven hD.even_degreeOn, ?_⟩
  have hsplit := card_sdiff_add_card_eq_card hDC
  have hpos := card_pos.mpr hD.1
  omega

end Overfull.Multigraph
