import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# The Tutte–Berge formula

The deficiency is computed from the actual odd connected components after
vertex deletion. Matchings are mathlib subgraphs with their actual covered
vertices and edges. The proof uses the proved Tutte theorem.
-/

namespace Overfull.TutteBerge

open Finset Classical SimpleGraph

variable {V W D : Type*}

/-- The graph obtained by adding mutually adjacent universal vertices. -/
def augmented (G : SimpleGraph V) (D : Type*) : SimpleGraph (V ⊕ D) where
  Adj x y := match x, y with
    | .inl v, .inl w => G.Adj v w
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr d, .inr e => d ≠ e
  symm := by
    rintro (v | d) (w | e) h
    · exact h.symm
    · trivial
    · trivial
    · exact h.symm
  loopless := by rintro (v | d) <;> simp

/-- Count odd connected components of the actual vertex-deleted graph. -/
noncomputable def oddCount (G : SimpleGraph V) (X : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard

theorem oddComponents_ncard_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    G.oddComponents.ncard = H.oddComponents.ncard := by
  have hcard (C : G.ConnectedComponent) :
      C.supp.ncard = (e.connectedComponentEquiv C).supp.ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_congr (ConnectedComponent.isoEquivSupp e C)
  let f : G.oddComponents ≃ H.oddComponents :=
    Equiv.subtypeEquiv e.connectedComponentEquiv (fun C => by
      change Odd C.supp.ncard ↔ Odd (e.connectedComponentEquiv C).supp.ncard
      rw [hcard C])
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr f

theorem oddComponents_le_one_of_preconnected [Finite V] (G : SimpleGraph V)
    (hG : G.Preconnected) : G.oddComponents.ncard ≤ 1 := by
  letI := hG.subsingleton_connectedComponent
  exact (Set.ncard_le_one (Set.toFinite G.oddComponents)).mpr (fun _ _ _ _ => Subsingleton.elim _ _)

variable [Fintype V]

theorem deleted_order_add (G : SimpleGraph V) (X : Set V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts X).verts + X.ncard = Nat.card V := by
  have h := Set.ncard_add_ncard_compl X
  simpa only [Nat.card_coe_set_eq, SimpleGraph.Subgraph.deleteVerts_verts,
    SimpleGraph.Subgraph.verts_top, ← Set.compl_eq_univ_diff, add_comm] using h

/-- The nonnegative maximum of the Tutte deficiencies. The empty deletion
set ensures that this is also the maximum of the integer differences. -/
noncomputable def deficiency (G : SimpleGraph V) : ℕ :=
  (univ : Finset (Set V)).sup (fun X => oddCount G X - X.ncard)

theorem oddCount_le_add_deficiency (G : SimpleGraph V) (X : Set V) :
    oddCount G X ≤ X.ncard + deficiency G := by
  have h : oddCount G X - X.ncard ≤ deficiency G := Finset.le_sup (f := fun X => oddCount G X - X.ncard) (Finset.mem_univ X)
  omega

theorem deficiency_attained (G : SimpleGraph V) :
    ∃ X : Set V, oddCount G X = X.ncard + deficiency G := by
  obtain ⟨X, _, hX⟩ := Finset.exists_mem_eq_sup (univ : Finset (Set V))
    ⟨∅, Finset.mem_univ _⟩ (fun X => oddCount G X - X.ncard)
  change deficiency G = oddCount G X - X.ncard at hX
  by_cases h : deficiency G = 0
  · refine ⟨∅, ?_⟩
    have hh := oddCount_le_add_deficiency G ∅
    simp only [Set.ncard_empty, h, add_zero] at hh ⊢
    omega
  · exact ⟨X, by omega⟩

theorem deficiency_order_even (G : SimpleGraph V) :
    Even (Nat.card V + deficiency G) := by
  obtain ⟨X, hX⟩ := deficiency_attained G
  have horder := deleted_order_add G X
  have hodd := SimpleGraph.odd_ncard_oddComponents ((⊤ : G.Subgraph).deleteVerts X).coe
  change Odd (oddCount G X) ↔ Odd (Nat.card ((⊤ : G.Subgraph).deleteVerts X).verts) at hodd
  rw [Nat.odd_iff, Nat.odd_iff] at hodd
  rw [Nat.even_iff]
  omega


/-- Delete a set of original vertices together with every added vertex. -/
def deletionSet (D : Type*) (X : Set V) : Set (V ⊕ D) :=
  Sum.inl '' X ∪ Set.range Sum.inr

theorem deletionSet_ncard [Fintype D] (X : Set V) :
    (deletionSet D X).ncard = X.ncard + Nat.card D := by
  have hdisj : Disjoint (Sum.inl '' X : Set (V ⊕ D)) (Set.range Sum.inr) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, _, rfl⟩ ⟨d, hd⟩
    cases hd
  rw [deletionSet, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective X Sum.inl_injective,
    Set.ncard_range_of_injective Sum.inr_injective]

omit [Fintype V] in
theorem eq_deletionSet_of_all_added (S : Set (V ⊕ D))
    (hS : ∀ d, Sum.inr d ∈ S) :
    S = deletionSet D (Sum.inl ⁻¹' S) := by
  ext z
  cases z <;> simp [deletionSet, hS]

/-- When all added vertices are removed, the remaining graph is exactly
the corresponding vertex-deleted original graph, up to the natural isomorphism. -/
noncomputable def deletionIso (G : SimpleGraph V) (D : Type*) (X : Set V) :
    ((⊤ : G.Subgraph).deleteVerts X).coe ≃g
      ((⊤ : (augmented G D).Subgraph).deleteVerts (deletionSet D X)).coe := by
  let f : ((⊤ : G.Subgraph).deleteVerts X).verts →
      ((⊤ : (augmented G D).Subgraph).deleteVerts (deletionSet D X)).verts :=
    fun v => ⟨Sum.inl v.val, by
      have hv : v.val ∉ X := v.property.2
      simpa [deletionSet] using hv⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      exact Sum.inl_injective (congrArg Subtype.val h)
    · rintro ⟨z, hz⟩
      cases z with
      | inl v =>
          refine ⟨⟨v, ?_⟩, rfl⟩
          simpa [deletionSet] using hz
      | inr d => simp [deletionSet] at hz
  refine { toEquiv := Equiv.ofBijective f hf, map_rel_iff' := ?_ }
  intro v w
  have hv : v.val ∉ X := v.property.2
  have hw : w.val ∉ X := w.property.2
  simp [f, Subgraph.coe_adj, augmented, deletionSet, hv, hw]

omit [Fintype V] in
theorem oddCount_deletionSet (G : SimpleGraph V) (X : Set V) :
    oddCount (augmented G D) (deletionSet D X) = oddCount G X :=
  (oddComponents_ncard_iso (deletionIso G D X)).symm

omit [Fintype V] in
/-- Any added vertex that survives deletion connects all the remaining vertices. -/
theorem deleted_preconnected_of_added (G : SimpleGraph V) (S : Set (V ⊕ D))
    (d : D) (hd : Sum.inr d ∉ S) :
    ((⊤ : (augmented G D).Subgraph).deleteVerts S).coe.Preconnected := by
  let z : ((⊤ : (augmented G D).Subgraph).deleteVerts S).verts :=
    ⟨Sum.inr d, by simpa using hd⟩
  have hreach (x : ((⊤ : (augmented G D).Subgraph).deleteVerts S).verts) :
      ((⊤ : (augmented G D).Subgraph).deleteVerts S).coe.Reachable x z := by
    by_cases hx : x = z
    · subst x
      exact .rfl
    · apply SimpleGraph.Adj.reachable
      have hxS := x.property
      have hneq : x.val ≠ Sum.inr d := fun h => hx (Subtype.ext h)
      change x.val ∈ Set.univ \ S ∧ Sum.inr d ∈ Set.univ \ S ∧
        (augmented G D).Adj x.val (Sum.inr d)
      refine ⟨hxS, z.property, ?_⟩
      cases hxv : x.val with
      | inl v => trivial
      | inr e => exact fun he => hneq (by rw [hxv, he])
  intro x y
  exact (hreach x).trans (hreach y).symm

/-- The two cases of Tutte's condition for the augmented graph. -/
theorem augmented_has_perfectMatching [Fintype D] (G : SimpleGraph V)
    (hparity : Even (Nat.card V + Nat.card D))
    (hbound : ∀ X : Set V, oddCount G X ≤ X.ncard + Nat.card D) :
    ∃ M : (augmented G D).Subgraph, M.IsPerfectMatching := by
  apply SimpleGraph.tutte.mpr
  intro S
  change ¬ S.ncard < oddCount (augmented G D) S
  apply not_lt_of_ge
  by_cases hS : ∀ d, Sum.inr d ∈ S
  · rw [eq_deletionSet_of_all_added S hS, oddCount_deletionSet, deletionSet_ncard]
    exact hbound _
  · push_neg at hS
    obtain ⟨d, hd⟩ := hS
    have hconn := deleted_preconnected_of_added G S d hd
    have hone := oddComponents_le_one_of_preconnected
      ((⊤ : (augmented G D).Subgraph).deleteVerts S).coe hconn
    change oddCount (augmented G D) S ≤ 1 at hone
    by_cases hs : S.ncard = 0
    · have horder := deleted_order_add (augmented G D) S
      have hodd := SimpleGraph.odd_ncard_oddComponents
        ((⊤ : (augmented G D).Subgraph).deleteVerts S).coe
      change Odd (oddCount (augmented G D) S) ↔
        Odd (Nat.card ((⊤ : (augmented G D).Subgraph).deleteVerts S).verts) at hodd
      rw [Nat.odd_iff, Nat.odd_iff] at hodd
      rw [Nat.even_iff] at hparity
      rw [Nat.card_sum] at horder
      omega
    · omega


theorem deficiency_le_of_bounds (G : SimpleGraph V) (d : ℕ)
    (h : ∀ X : Set V, oddCount G X ≤ X.ncard + d) : deficiency G ≤ d := by
  apply Finset.sup_le
  intro X _
  have hX := h X
  omega

/-- The natural-number deficiency is an upper bound for the untruncated
integer difference appearing in the Tutte–Berge formula. -/
theorem deficiency_integer_bound (G : SimpleGraph V) (X : Set V) :
    (oddCount G X : ℤ) - X.ncard ≤ (deficiency G : ℤ) := by
  have h := oddCount_le_add_deficiency G X
  omega

/-- The upper bound for integer deficiencies is attained by an actual
vertex set; truncation in the natural-number definition changes no maximum. -/
theorem deficiency_integer_attained (G : SimpleGraph V) :
    ∃ X : Set V, (oddCount G X : ℤ) - X.ncard = (deficiency G : ℤ) := by
  obtain ⟨X, hX⟩ := deficiency_attained G
  exact ⟨X, by omega⟩

end Overfull.TutteBerge



