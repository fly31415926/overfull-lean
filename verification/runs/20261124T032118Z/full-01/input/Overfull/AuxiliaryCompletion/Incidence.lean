import Overfull.Basic

/-! # Incidences between original and auxiliary vertices -/

namespace Overfull.AuxiliaryCompletion

open Finset

noncomputable def rightLoad {V U : Type*} [Fintype V]
    (N : V → Finset U) (u : U) : ℕ := by
  classical
  exact (univ.filter (fun v => u ∈ N v)).card

end Overfull.AuxiliaryCompletion
