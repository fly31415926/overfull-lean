import Overfull.BipartiteFactorization.Assembly
import Overfull.OneCore.Complement

/-!
# The actual remaining exterior and its coloring

Deleting selected original copies gives exact residual degrees and balanced
side degree sums. Only the inactive residual is colored by the unused
original palette. The fan criterion constructs a coloring of all remaining
copies, and balancing then gives the residual footprint bounds.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

omit [Fintype V] in
/-- Exact exceptional degree after deleting a prescribed total number of
incidences. The proof uses the actual complementary edge restriction. -/
theorem remaining_exceptional_degree (T : Finset E) (U : Finset V) (k s : ℕ)
    (hfull : ∀ x, x ∉ U → G.degree x = k)
    (hselected : ∀ x, x ∉ U → (G.restrictEdges T).degree x = s)
    (x : V) (hx : x ∉ U) :
    (G.restrictEdges Tᶜ).degree x = k - s := by
  have h := OneCore.complement_degree_add G T x
  rw [hfull x hx, hselected x hx] at h
  omega

omit [Fintype V] in
/-- Removing a balanced actual edge set preserves the equality of core
side degree sums. -/
theorem remaining_side_degree_eq (T : Finset E) (A B : Finset V)
    (hfull : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hselected : (∑ v ∈ A, (G.restrictEdges T).degree v) =
      ∑ v ∈ B, (G.restrictEdges T).degree v) :
    (∑ v ∈ A, (G.restrictEdges Tᶜ).degree v) =
      ∑ v ∈ B, (G.restrictEdges Tᶜ).degree v := by
  have hsum (X : Finset V) :
      (∑ v ∈ X, (G.restrictEdges Tᶜ).degree v) +
        (∑ v ∈ X, (G.restrictEdges T).degree v) = ∑ v ∈ X, G.degree v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => OneCore.complement_degree_add G T v)
  have hA := hsum A
  have hB := hsum B
  omega

omit [Fintype V] in
/-- Selected and remaining original copies partition every core row. -/
theorem remaining_core_row_add (T : Finset E) (x : V) (U : Finset V) :
    ((G.restrictEdges Tᶜ).edgesTo x U).card +
      (T ∩ G.edgesTo x U).card = (G.edgesTo x U).card := by
  rw [G.restrictEdges_edgesTo_card]
  have hset : Tᶜ ∩ G.edgesTo x U = G.edgesTo x U \ T := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, and_comm]
  rw [hset, Finset.inter_comm T]
  exact Finset.card_sdiff_add_card_inter (G.edgesTo x U) T

omit [Fintype V] in
/-- A selected degree bound controls every actual row loss, without
assuming that the selected copies retain their original colors. -/
theorem remaining_core_row_lower (T : Finset E) (x : V) (U : Finset V) :
    ((G.edgesTo x U).card : ℝ) - (G.restrictEdges T).degree x ≤
      ((G.restrictEdges Tᶜ).edgesTo x U).card := by
  have hrow := remaining_core_row_add G T x U
  have hcap : (T ∩ G.edgesTo x U).card ≤ (G.restrictEdges T).degree x := by
    rw [G.restrictEdges_degree]
    apply Finset.card_le_card
    intro e he
    obtain ⟨heT, hex⟩ := Finset.mem_inter.mp he
    exact Finset.mem_inter.mpr ⟨heT,
      (G.mem_incidenceEdges x e).mpr ((G.mem_edgesTo x U e).mp hex).1⟩
  have hrowR : (((G.restrictEdges Tᶜ).edgesTo x U).card : ℝ) +
      (T ∩ G.edgesTo x U).card = (G.edgesTo x U).card := by
    exact_mod_cast hrow
  have hcapR : ((T ∩ G.edgesTo x U).card : ℝ) ≤ (G.restrictEdges T).degree x := by
    exact_mod_cast hcap
  linarith

/-- Every inactive remaining copy has an unused original color. This
claim is confined to the inactive residue; active remaining copies may
still carry original labels from the selected palette. -/
theorem remaining_inactive_color_mem {k : ℕ} (c : G.EdgeColoring k)
    (U Zplus : Finset V) (T : Finset E) (J : Finset (Fin k))
    (hbase : paletteBase c U J ⊆ T)
    (hlow : ∀ x, x ∉ U → x ∉ Zplus →
      paletteEdges c J ∩ G.edgesTo x U = ∅)
    (e : inactiveExterior (G.restrictEdges Tᶜ) U Zplus) :
    c.color e.val.val ∈ Jᶜ := by
  apply Finset.mem_compl.mpr
  intro heJ
  have hePalette : e.val.val ∈ paletteEdges c J :=
    (mem_paletteEdges c J e.val.val).mpr heJ
  have horig : e.val.val ∈ inactiveExterior G U Zplus := by
    apply (mem_inactiveExterior G U Zplus e.val.val).mpr
    have he := (mem_inactiveExterior (G.restrictEdges Tᶜ) U Zplus e.val).mp e.property
    simpa only [Multigraph.mem_internalEdges, Multigraph.mem_edgesTo] using he
  rw [inactiveExterior_eq] at horig
  rcases Finset.mem_union.mp horig with heInternal | heLow
  · have heBase : e.val.val ∈ paletteBase c U J :=
      Finset.mem_inter.mpr ⟨hePalette, heInternal⟩
    exact (Finset.mem_compl.mp e.val.property) (hbase heBase)
  · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heLow
    obtain ⟨hxU, hxZ⟩ := Finset.mem_sdiff.mp hx
    have he' : e.val.val ∈ paletteEdges c J ∩ G.edgesTo x U :=
      Finset.mem_inter.mpr ⟨hePalette, hex⟩
    rw [hlow x (Finset.mem_compl.mp hxU) hxZ] at he'
    exact Finset.notMem_empty _ he'

/-- Compress the inherited original coloring on the actual inactive
residual into exactly the unused number of colors. -/
theorem remaining_inactive_colorable {k : ℕ} (c : G.EdgeColoring k)
    (U Zplus : Finset V) (T : Finset E) (J : Finset (Fin k))
    (hbase : paletteBase c U J ⊆ T)
    (hlow : ∀ x, x ∉ U → x ∉ Zplus →
      paletteEdges c J ∩ G.edgesTo x U = ∅) :
    Nonempty (((G.restrictEdges Tᶜ).restrictEdges
      (inactiveExterior (G.restrictEdges Tᶜ) U Zplus)).EdgeColoring (k - J.card)) := by
  let color : inactiveExterior (G.restrictEdges Tᶜ) U Zplus → Fin Jᶜ.card :=
    fun e => paletteEquiv Jᶜ
      ⟨c.color e.val.val, remaining_inactive_color_mem G c U Zplus T J hbase hlow e⟩
  have hproper : ∀ {e f : inactiveExterior (G.restrictEdges Tᶜ) U Zplus} {v : V},
      color e = color f → v ∈ G.edge e.val.val → v ∈ G.edge f.val.val → e = f := by
    intro e f v hef hev hfv
    have hc : c.color e.val.val = c.color f.val.val :=
      congrArg Subtype.val ((paletteEquiv Jᶜ).injective hef)
    exact Subtype.ext (Subtype.ext (c.proper hc hev hfv))
  let d : ((G.restrictEdges Tᶜ).restrictEdges
      (inactiveExterior (G.restrictEdges Tᶜ) U Zplus)).EdgeColoring Jᶜ.card :=
    ⟨color, hproper⟩
  simpa only [Finset.card_compl, Fintype.card_fin] using Nonempty.intro d

/-- Construct a balanced coloring of the actual remaining graph. Its
inactive coloring is derived from the unused original palette, rather
than supplied as an assumption. -/
theorem exists_balanced_remaining_coloring {k : ℕ} (c : G.EdgeColoring k)
    (A B Zplus : Finset V) (T : Finset E) (J : Finset (Fin k)) (a : ℝ)
    (ha : 0 ≤ a) (hka : 2 * a < (k - J.card : ℕ))
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card) (hactiveOutside : Disjoint Zplus (A ∪ B))
    (hfull : ∀ x, x ∉ A ∪ B → G.degree x = k)
    (hselected : ∀ x, x ∉ A ∪ B → (G.restrictEdges T).degree x = J.card)
    (hbase : T ∩ G.internalEdges (A ∪ B)ᶜ = paletteBase c (A ∪ B) J)
    (hlow : ∀ x, x ∉ A ∪ B → x ∉ Zplus →
      paletteEdges c J ∩ G.edgesTo x (A ∪ B) = ∅)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hfullBalanced : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hselectedBalanced : (∑ v ∈ A, (G.restrictEdges T).degree v) =
      ∑ v ∈ B, (G.restrictEdges T).degree v)
    (hactive : ∀ x ∈ Zplus,
      2 * a < ((G.edgesTo x (A ∪ B)).card : ℝ) - J.card) :
    ∃ d : (G.restrictEdges Tᶜ).EdgeColoring (k - J.card),
      (∀ i, (A ∪ B)ᶜ ⊆ d.coveredVertices i) ∧
      (∀ i, (A ∩ d.coveredVertices i).card = (B ∩ d.coveredVertices i).card) ∧
      (∀ i j, |((A ∩ d.coveredVertices i).card : ℤ) -
        (A ∩ d.coveredVertices j).card| ≤ 2) ∧
      (∀ i, d.exteriorFootprint (A ∪ B) i ⊆ A ∪ B) ∧
      (∀ i, ((d.exteriorFootprint (A ∪ B) i).card : ℝ) ≤
        2 * A.card * a / (k - J.card : ℕ) + 4) ∧
      (∀ i, Even (d.exteriorFootprint (A ∪ B) i).card) ∧
      (∀ v ∈ A ∪ B,
        (univ.filter (fun i => v ∈ d.exteriorFootprint (A ∪ B) i)).card =
          (G.restrictEdges Tᶜ).degree v) ∧
      (∀ v ∈ A ∪ B,
        ((univ.filter (fun i => v ∈ d.exteriorFootprint (A ∪ B) i)).card : ℝ) ≤ a) := by
  have hbaseSub : paletteBase c (A ∪ B) J ⊆ T := by
    rw [← hbase]
    exact Finset.inter_subset_left
  have hinit := remaining_inactive_colorable G c (A ∪ B) Zplus T J hbaseSub hlow
  apply exists_balanced_localized_coloring (G.restrictEdges Tᶜ)
    A B A B Zplus (k - J.card) a ha hka hAB hcard hZeven
    (fun x hx => remaining_exceptional_degree G T (A ∪ B) k J.card hfull hselected x
      (Finset.mem_compl.mp hx))
    (fun v hv => (Nat.cast_le.mpr (G.restrictEdges_degree_le Tᶜ v)).trans (hcore v hv))
    (remaining_side_degree_eq G T A B hfullBalanced hselectedBalanced)
    _ hinit (Subset.refl _) (Subset.refl _) hcard
    (fun _ hx hxnot => False.elim (hxnot hx))
  intro x hx
  have hxU : x ∉ A ∪ B := fun hxU => Finset.disjoint_left.mp hactiveOutside hx hxU
  have hrow := remaining_core_row_lower G T x (A ∪ B)
  rw [hselected x hxU] at hrow
  exact (hactive x hx).trans_le hrow

end Overfull.BipartiteFactorization
