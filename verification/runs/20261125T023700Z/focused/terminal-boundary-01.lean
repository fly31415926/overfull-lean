import Overfull.NativeAssembly.Paired

/-!
# Exact native boundaries with two separate exceptional pair copies

Both pair copies of one reserved boundary use its same protected color.
The original joining trace is free on all four pair vertices, so the two
independent internal-pair completions can retain the whole boundary.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- A matching boundary containing the two actual pair copies consists
exactly of its joining trace and those copies.  The trace is free on both
pairs, and the two selected copies are distinct. -/
theorem reserved_two_pair_class
    (C : JoiningPalette G label h D L p) (k₀ k₁ : K)
    (x₀ y₀ x₁ y₁ : V)
    (hfiber₀ : labelShore label {k₀} = {x₀,y₀})
    (hfiber₁ : labelShore label {k₁} = {x₁,y₁})
    (hdisjoint : Disjoint ({x₀,y₀} : Finset V) {x₁,y₁})
    (R : Finset E) (hR : G.IsMatching R)
    (e₀ : pairFiberCopies G x₀ y₀) (e₁ : pairFiberCopies G x₁ y₁)
    (he₀ : e₀.val ∈ R) (he₁ : e₁.val ∈ R)
    (hsubset : R ⊆ joiningCopies G label ∪
      exceptionalCopies G univ ({x₀,y₀} ∪ {x₁,y₁}))
    (j : Fin h) (htrace : R ∩ joiningCopies G label = C.classes j) :
    R = C.classes j ∪ {e₀.val,e₁.val} ∧
      (∀ v ∈ ({x₀,y₀} ∪ {x₁,y₁} : Finset V),
        v ∉ G.edgeSupport (C.classes j)) ∧ e₀.val ≠ e₁.val := by
  have hCsub : C.classes j ⊆ R := by
    rw [← htrace]
    exact inter_subset_left
  have henot₀ : e₀.val ∉ joiningCopies G label :=
    fun he => disjoint_left.mp
      (pairFiberCopies_disjoint_joining G label k₀ x₀ y₀ hfiber₀) e₀.property he
  have henot₁ : e₁.val ∉ joiningCopies G label :=
    fun he => disjoint_left.mp
      (pairFiberCopies_disjoint_joining G label k₁ x₁ y₁ hfiber₁) e₁.property he
  have hincident₀ (v : V) (hv : v ∈ ({x₀,y₀} : Finset V)) :
      v ∈ G.edge e₀.val := by
    apply (pairFiberCopies_incident G e₀.property v).mpr
    simpa only [mem_insert, mem_singleton] using hv
  have hincident₁ (v : V) (hv : v ∈ ({x₁,y₁} : Finset V)) :
      v ∈ G.edge e₁.val := by
    apply (pairFiberCopies_incident G e₁.property v).mpr
    simpa only [mem_insert, mem_singleton] using hv
  have hsame (a : E) (ha : a ∈ R) (v : V) (hav : v ∈ G.edge a)
      (hv : v ∈ ({x₀,y₀} ∪ {x₁,y₁} : Finset V)) :
      a = e₀.val ∨ a = e₁.val := by
    rcases mem_union.mp hv with hv | hv
    · exact Or.inl (hR a ha e₀.val he₀ v hav (hincident₀ v hv))
    · exact Or.inr (hR a ha e₁.val he₁ v hav (hincident₁ v hv))
  refine ⟨?_, ?_, ?_⟩
  · apply subset_antisymm
    · intro a ha
      rcases mem_union.mp (hsubset ha) with haJ | haZ
      · exact mem_union_left _ (htrace ▸ mem_inter.mpr ⟨ha,haJ⟩)
      · obtain ⟨_, hv | hv⟩ := (mem_exceptionalCopies G univ _ a).mp haZ
        · exact mem_union_right _ (by
            simpa only [mem_insert, mem_singleton] using
              hsame a ha (G.firstEnd a) ((G.incident_iff a _).mpr (Or.inl rfl)) hv)
        · exact mem_union_right _ (by
            simpa only [mem_insert, mem_singleton] using
              hsame a ha (G.secondEnd a) ((G.incident_iff a _).mpr (Or.inr rfl)) hv)
    · intro a ha
      rcases mem_union.mp ha with ha | ha
      · exact hCsub ha
      · rcases mem_insert.mp ha with rfl | ha
        · exact he₀
        · exact (mem_singleton.mp ha).symm ▸ he₁
  · intro v hv hvc
    obtain ⟨a,ha,hva⟩ := (G.mem_edgeSupport _ v).mp hvc
    rcases hsame a (hCsub ha) v hva hv with heq | heq
    · exact henot₀ (heq ▸ C.classes_subset_joining j ha)
    · exact henot₁ (heq ▸ C.classes_subset_joining j ha)
  · intro heq
    have hx := hincident₀ x₀ (mem_insert_self _ _)
    rw [heq] at hx
    have hx₁ : x₀ ∈ ({x₁,y₁} : Finset V) := by
      simpa only [mem_insert, mem_singleton] using
        (pairFiberCopies_incident G e₁.property x₀).mp hx
    exact disjoint_left.mp hdisjoint (mem_insert_self _ _) hx₁

/-- The same exact whole-boundary statement for two unordered size-two
fibers.  No ordering of their endpoints enters the conclusion. -/
theorem reserved_two_pairFiber_class
    (C : JoiningPalette G label h D L p) (k₀ k₁ : K)
    (U₀ U₁ : Finset V) (hcard₀ : U₀.card = 2) (hcard₁ : U₁.card = 2)
    (hfiber₀ : labelShore label {k₀} = U₀)
    (hfiber₁ : labelShore label {k₁} = U₁) (hdisjoint : Disjoint U₀ U₁)
    (R : Finset E) (hR : G.IsMatching R)
    (e₀ : G.internalOn univ U₀) (e₁ : G.internalOn univ U₁)
    (he₀ : e₀.val ∈ R) (he₁ : e₁.val ∈ R)
    (hsubset : R ⊆ joiningCopies G label ∪ exceptionalCopies G univ (U₀ ∪ U₁))
    (j : Fin h) (htrace : R ∩ joiningCopies G label = C.classes j) :
    R = C.classes j ∪ {e₀.val,e₁.val} ∧
      (∀ v ∈ U₀ ∪ U₁, v ∉ G.edgeSupport (C.classes j)) ∧ e₀.val ≠ e₁.val := by
  obtain ⟨x₀,y₀,_hxy₀,rfl⟩ := card_eq_two.mp hcard₀
  obtain ⟨x₁,y₁,_hxy₁,rfl⟩ := card_eq_two.mp hcard₁
  exact reserved_two_pair_class C k₀ k₁ x₀ y₀ x₁ y₁ hfiber₀ hfiber₁ hdisjoint
    R hR e₀ e₁ he₀ he₁ hsubset j htrace

end Overfull.NativeAssembly
