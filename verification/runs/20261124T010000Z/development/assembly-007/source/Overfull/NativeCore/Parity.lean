import Overfull.ResidualPalette.JoiningGrouping
import Overfull.NativeStar.StarExtension

/-!
# Passing from assigned fibers back to the original cores

After every exceptional vertex is covered, the uncovered vertices of an
assigned core part are exactly the uncovered vertices of its original core.
Thus preserved assigned-fiber cut parity gives the parity needed by the
actual core matching construction, even though the representative matching
and the current matching live in different edge-copy types.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E F : Type*}

/-- Covering the exceptions removes every added assigned vertex from the
uncovered set; no parity assumption is needed for this set identity. -/
theorem uncovered_corePart_eq (G : Multigraph V E) (H : Multigraph V F)
    (M : Finset E) (U Z : Finset V) (B : Finset F)
    (hZ : Z ⊆ H.edgeSupport B) :
    corePart G M Z U \ H.edgeSupport B = U \ H.edgeSupport B := by
  ext v
  simp only [mem_sdiff, mem_corePart]
  constructor
  · rintro ⟨hv | ⟨hvZ, _⟩, hn⟩
    · exact ⟨hv, hn⟩
    · exact (hn (hZ hvZ)).elim
  · rintro ⟨hv, hn⟩
    exact ⟨Or.inl hv, hn⟩

variable [Fintype V]

/-- For an actual source assignment, complete exceptional coverage and
the correct assigned-fiber cuts imply even uncovered original cores. -/
theorem uncovered_old_cores_even (G : Multigraph V E) (H : Multigraph V F)
    {M : Finset E} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (B : Finset F) (hB : H.IsMatching B) (hZ : Z ⊆ H.edgeSupport B)
    (hparity : ∀ i : Fin 3,
      (H.cutOn B (labelShore (assignedLabel G M U₀ U₁ Z) {i})).card % 2 =
        (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2) :
    Even (U₀ \ H.edgeSupport B).card ∧ Even (U₁ \ H.edgeSupport B).card := by
  have hfibers := assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover
  have heven (i : Fin 3) :
      Even ((univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)) \
        H.edgeSupport B).card := by
    have hshore : labelShore (assignedLabel G M U₀ U₁ Z) {i} =
        univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i) := by
      ext v
      simp only [mem_labelShore, mem_singleton, mem_filter, mem_univ, true_and]
    apply (hB.uncovered_even_iff_cut_parity H _).mpr
    rw [← hshore]
    simpa only [hshore] using (hparity i).symm
  have h₀ := heven 0
  have h₁ := heven 1
  rw [hfibers.1, uncovered_corePart_eq G H M U₀ Z B hZ] at h₀
  rw [hfibers.2.1, uncovered_corePart_eq G H M U₁ Z B hZ] at h₁
  exact ⟨h₀, h₁⟩

variable [Fintype F]

/-- Every completed exceptional matching inherits the original core parity
from the actual joining palette if its assigned-fiber cuts are unchanged. -/
theorem old_core_parity_of_joining_cuts
    (G : Multigraph V E) (H : Multigraph V F)
    {M : Finset E} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette H (assignedLabel G M U₀ U₁ Z) h D L p)
    (hfibers : ∀ i, (univ.filter (fun v =>
      assignedLabel G M U₀ U₁ Z v = i)).card % 2 = p i)
    (B : Fin h → Finset F) (hB : ∀ j, H.IsMatching (B j))
    (hZ : ∀ j, Z ⊆ H.edgeSupport (B j))
    (hcuts : ∀ j i, H.cutOn (B j) (labelShore (assignedLabel G M U₀ U₁ Z) {i}) =
      H.cutOn (C.classes j) (labelShore (assignedLabel G M U₀ U₁ Z) {i})) :
    ∀ j, Even (U₀ \ H.edgeSupport (B j)).card ∧
      Even (U₁ \ H.edgeSupport (B j)).card := by
  intro j
  apply uncovered_old_cores_even G H hM U₀ U₁ Z h01 h0Z h1Z hcover
    (B j) (hB j) (hZ j)
  intro i
  rw [hcuts j i, C.cut_parity j i, hfibers i]

end Overfull.NativeCore
