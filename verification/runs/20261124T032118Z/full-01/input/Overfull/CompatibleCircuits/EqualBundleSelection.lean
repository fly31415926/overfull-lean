import Overfull.CompatibleCircuits.Basic

/-!
# Selecting actual copies from three equal bundles

The counting step for the equal-bundle case of the three-label compatible
circuit construction. If one bundle is monochromatic at one endpoint,
the local half-degree bounds produce a compatible triangle of actual copies.
This does not by itself prove that deleting the triangle is admissible;
that requires the separate tight-class coarsening and deletion arguments.
-/

namespace Overfull.CompatibleCircuits

open Finset Classical

variable {E K : Type*}

/-- A fiber of size at most `S.card` cannot contain every copy of `S`
and one additional copy from a disjoint set. -/
theorem exists_mem_ne_of_union_fiber_bound
    (S T : Finset E) (f : E → K) (hST : Disjoint S T)
    (hbound : ∀ k, ((S ∪ T).filter (fun e => f e = k)).card ≤ S.card)
    {g : E} (hg : g ∈ T) : ∃ e ∈ S, f e ≠ f g := by
  by_contra h
  push_neg at h
  have hgS : g ∉ S := fun hgs => Finset.disjoint_left.mp hST hgs hg
  have hsub : insert g S ⊆ (S ∪ T).filter (fun e => f e = f g) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_filter.mpr ⟨Finset.mem_union_right S hg, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_union_left T he, h e he⟩
  have hcard := (Finset.card_le_card hsub).trans (hbound (f g))
  rw [Finset.card_insert_of_notMem hgS] at hcard
  omega

/-- A monochromatic bundle saturating a local fiber bound is separated
from every copy of the other incident bundle. -/
theorem ne_of_monochromatic_union_fiber_bound
    (S T : Finset E) (f : E → K) (hST : Disjoint S T)
    (hbound : ∀ k, ((S ∪ T).filter (fun e => f e = k)).card ≤ S.card)
    {k : K} (hmono : ∀ e ∈ S, f e = k)
    {e g : E} (he : e ∈ S) (hg : g ∈ T) : f e ≠ f g := by
  obtain ⟨h, hh, hne⟩ := exists_mem_ne_of_union_fiber_bound S T f hST hbound hg
  simpa only [hmono h hh, hmono e he] using hne

/-- From three disjoint equal positive bundles and the three local
half-degree bounds, a monochromatic bundle at the first endpoint yields
one copy in every bundle with different classes at every endpoint. -/
theorem exists_compatible_triple_of_equal_bundles
    (AB AC BC : Finset E) (a b c : E → K)
    (hABAC : Disjoint AB AC) (hABBC : Disjoint AB BC) (hACBC : Disjoint AC BC)
    (hAC : AC.card = AB.card) (hBC : BC.card = AB.card) (hpos : 0 < AB.card)
    (hA : ∀ k, 2 * ((AB ∪ AC).filter (fun e => a e = k)).card ≤ (AB ∪ AC).card)
    (hB : ∀ k, 2 * ((AB ∪ BC).filter (fun e => b e = k)).card ≤ (AB ∪ BC).card)
    (hC : ∀ k, 2 * ((AC ∪ BC).filter (fun e => c e = k)).card ≤ (AC ∪ BC).card)
    (hmono : ∃ k, ∀ e ∈ AB, a e = k) :
    ∃ e ∈ AB, ∃ h ∈ AC, ∃ g ∈ BC,
      a e ≠ a h ∧ b e ≠ b g ∧ c h ≠ c g := by
  have hbA (k : K) : ((AB ∪ AC).filter (fun e => a e = k)).card ≤ AB.card := by
    have hk := hA k
    rw [Finset.card_union_of_disjoint hABAC, hAC] at hk
    omega
  have hbB (k : K) : ((AB ∪ BC).filter (fun e => b e = k)).card ≤ AB.card := by
    have hk := hB k
    rw [Finset.card_union_of_disjoint hABBC, hBC] at hk
    omega
  have hbC (k : K) : ((AC ∪ BC).filter (fun e => c e = k)).card ≤ AC.card := by
    have hk := hC k
    rw [Finset.card_union_of_disjoint hACBC, hBC, hAC] at hk
    omega
  obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < BC.card by omega)
  obtain ⟨e, he, heB⟩ := exists_mem_ne_of_union_fiber_bound AB BC b hABBC hbB hg
  obtain ⟨h, hh, hhC⟩ := exists_mem_ne_of_union_fiber_bound AC BC c hACBC hbC hg
  obtain ⟨k, hk⟩ := hmono
  exact ⟨e, he, h, hh, g, hg,
    ne_of_monochromatic_union_fiber_bound AB AC a hABAC hbA hk he hh, heB, hhC⟩

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical

variable {E K : Type*} (Q : Multigraph (Fin 3) E)

/-- Three copies on the three distinct endpoint pairs form a genuine
triangle circuit, with parallel-copy identities kept distinct. -/
theorem isCircuit_triangle {e h g : E}
    (he : Q.edge e = s(0, 1)) (hh : Q.edge h = s(0, 2))
    (hg : Q.edge g = s(1, 2)) : Q.IsCircuit {e, h, g} := by
  have heh : e ≠ h := by
    intro hEq
    have hh' := hEq ▸ he
    rw [hh] at hh'
    norm_num [Sym2.eq_iff, Fin.ext_iff] at hh'
  have heg : e ≠ g := by
    intro hEq
    have hg' := hEq ▸ he
    rw [hg] at hg'
    norm_num [Sym2.eq_iff, Fin.ext_iff] at hg'
  have hhg : h ≠ g := by
    intro hEq
    have hg' := hEq ▸ hh
    rw [hg] at hg'
    norm_num [Sym2.eq_iff, Fin.ext_iff] at hg'
  have hs : Q.edgeSupport {e, h, g} = Finset.univ := by
    ext v
    fin_cases v <;> simp [mem_edgeSupport, he, hh, hg]
  refine ⟨by simp, ?_, ?_⟩
  · intro v _
    fin_cases v <;>
      simp [degreeOn, Finset.filter_insert, Finset.filter_singleton, he, hh, hg,
        heh, heg, hhg]
  · intro X _ hnonempty hproper
    have hcross (d : E) (a b : Fin 3) (hd : d ∈ ({e, h, g} : Finset E))
        (hedge : Q.edge d = s(a, b)) (hab : (a ∈ X) ≠ (b ∈ X)) :
        (Q.cutOn {e, h, g} X).Nonempty := by
      refine ⟨d, (Q.mem_cutOn {e, h, g} X d).mpr ⟨hd, ?_⟩⟩
      have ends := (Q.edge_eq d).trans hedge
      rcases Sym2.eq_iff.mp ends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · simpa [h₁, h₂] using hab
      · simpa only [h₁, h₂] using hab.symm
    have hsome : (0 : Fin 3) ∈ X ∨ (1 : Fin 3) ∈ X ∨ (2 : Fin 3) ∈ X := by
      obtain ⟨v, hv⟩ := hnonempty
      fin_cases v <;> tauto
    have hnotall : ¬ ((0 : Fin 3) ∈ X ∧ (1 : Fin 3) ∈ X ∧ (2 : Fin 3) ∈ X) := by
      intro h
      apply hproper
      rw [hs]
      ext v
      fin_cases v <;> simp_all
    by_cases h0 : (0 : Fin 3) ∈ X
    · by_cases h1 : (1 : Fin 3) ∈ X
      · have h2 : (2 : Fin 3) ∉ X := by tauto
        exact hcross h 0 2 (by simp) hh (by simp [h0, h2])
      · exact hcross e 0 1 (by simp) he (by simp [h0, h1])
    · by_cases h1 : (1 : Fin 3) ∈ X
      · exact hcross e 0 1 (by simp) he (by simp [h0, h1])
      · have h2 : (2 : Fin 3) ∈ X := by tauto
        exact hcross h 0 2 (by simp) hh (by simp [h0, h2])

/-- A triangle is compatible when the two selected incidences have
unequal class labels at each of its three vertices. -/
theorem compatible_triangle (classOf : Fin 3 → E → K) {e h g : E}
    (he : Q.edge e = s(0, 1)) (hh : Q.edge h = s(0, 2))
    (hg : Q.edge g = s(1, 2))
    (h0 : classOf 0 e ≠ classOf 0 h) (h1 : classOf 1 e ≠ classOf 1 g)
    (h2 : classOf 2 h ≠ classOf 2 g) : Q.Compatible classOf {e, h, g} := by
  intro v d hd hvd f hf hvf hclass
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd hf
  rcases hd with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl
  all_goals try rfl
  all_goals fin_cases v <;> simp_all

/-- The equal-bundle counting selector yields an actual compatible
triangle contained in the original multigraph copies. -/
theorem exists_compatible_triangle_of_equal_bundles
    (classOf : Fin 3 → E → K) (AB AC BC : Finset E)
    (hABAC : Disjoint AB AC) (hABBC : Disjoint AB BC) (hACBC : Disjoint AC BC)
    (hABedge : ∀ e ∈ AB, Q.edge e = s(0, 1))
    (hACedge : ∀ e ∈ AC, Q.edge e = s(0, 2))
    (hBCedge : ∀ e ∈ BC, Q.edge e = s(1, 2))
    (hAC : AC.card = AB.card) (hBC : BC.card = AB.card) (hpos : 0 < AB.card)
    (hA : ∀ k, 2 * ((AB ∪ AC).filter (fun e => classOf 0 e = k)).card ≤
      (AB ∪ AC).card)
    (hB : ∀ k, 2 * ((AB ∪ BC).filter (fun e => classOf 1 e = k)).card ≤
      (AB ∪ BC).card)
    (hC : ∀ k, 2 * ((AC ∪ BC).filter (fun e => classOf 2 e = k)).card ≤
      (AC ∪ BC).card)
    (hmono : ∃ k, ∀ e ∈ AB, classOf 0 e = k) :
    ∃ D : Finset E, D ⊆ AB ∪ AC ∪ BC ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 3 := by
  obtain ⟨e, he, h, hh, g, hg, h0, h1, h2⟩ :=
    CompatibleCircuits.exists_compatible_triple_of_equal_bundles AB AC BC
      (classOf 0) (classOf 1) (classOf 2) hABAC hABBC hACBC hAC hBC hpos
      hA hB hC hmono
  have heh : e ≠ h := fun hEq => Finset.disjoint_left.mp hABAC he (hEq ▸ hh)
  have heg : e ≠ g := fun hEq => Finset.disjoint_left.mp hABBC he (hEq ▸ hg)
  have hhg : h ≠ g := fun hEq => Finset.disjoint_left.mp hACBC hh (hEq ▸ hg)
  refine ⟨{e, h, g}, ?_, Q.isCircuit_triangle (hABedge e he) (hACedge h hh)
    (hBCedge g hg), Q.compatible_triangle classOf (hABedge e he) (hACedge h hh)
      (hBCedge g hg) h0 h1 h2, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Finset.mem_union_left BC (Finset.mem_union_left AC he)
    · exact Finset.mem_union_left BC (Finset.mem_union_right AB hh)
    · exact Finset.mem_union_right (AB ∪ AC) hg
  · simp [heh, heg, hhg]

end Overfull.Multigraph
