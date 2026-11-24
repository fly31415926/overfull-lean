import Overfull.NativeStar.StarExtension

/-!
# Sequential extension by two actual exceptional stars

The second star is colored only after the first has been inserted. Its
available-color vertex loads increase by at most the first-star parallel
multiplicity, and its whole-class blocked-copy weights increase by at most
the second-star multiplicity. All load assumptions are restricted to the
relevant remaining palettes; protected colors may have larger global loads.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical AssignedParts WeightedPalette

variable {V E : Type*} [Fintype E] {h : ℕ}
variable (G : Multigraph V E)

/-- A star to an old-core set avoids any distinct center outside that set. -/
theorem star_pool_avoids_other_center (x y : V) (U : Finset V) (A : Finset E)
    (hA : A ⊆ exceptionCorePool G x U) (hxy : x ≠ y) (hyU : y ∉ U) :
    ∀ e ∈ A, y ∉ G.edge e := by
  intro e he hye
  obtain ⟨hxe,hoU⟩ := (mem_filter.mp (hA he)).2
  rw [G.edge_eq_otherEnd x e hxe,Sym2.mem_iff] at hye
  rcases hye with hyx | hyo
  · exact hxy hyx.symm
  · apply hyU
    rw [hyo]
    exact hoU

/-- The two actual star-copy pools are disjoint when the second center
is distinct from the first and outside its old-core set. -/
theorem star_pools_disjoint (x y : V) (U₀ U₁ : Finset V) (A₀ A₁ : Finset E)
    (hA₀ : A₀ ⊆ exceptionCorePool G x U₀)
    (hA₁ : A₁ ⊆ exceptionCorePool G y U₁) (hxy : x ≠ y) (hyU₀ : y ∉ U₀) :
    Disjoint A₀ A₁ := by
  apply disjoint_left.mpr
  intro e he₀ he₁
  exact star_pool_avoids_other_center G x y U₀ A₀ hA₀ hxy hyU₀ e he₀
    (mem_filter.mp (hA₁ he₁)).2.1

/-- Inserting the first star never occupies the distinct second center. -/
theorem coloredStarCopies_avoids_other_center (x y : V) (U : Finset V)
    (A : Finset E) (c : A → Fin h) (hA : A ⊆ exceptionCorePool G x U)
    (hxy : x ≠ y) (hyU : y ∉ U) (j : Fin h) :
    y ∉ G.edgeSupport (coloredStarCopies A c j) := by
  intro hy
  obtain ⟨e,he,hye⟩ := (G.mem_edgeSupport _ y).mp hy
  exact star_pool_avoids_other_center G x y U A hA hxy hyU e
    (coloredStarCopies_subset A c j he) hye

/-- Available-color loads, rather than global loads including protected
classes, suffice after the first star has been inserted. -/
theorem starExtended_available_support_load_le
    (C : Fin h → Finset E) (F : Finset (Fin h)) (x : V) (U : Finset V)
    (A : Finset E) (c : A → Fin h) (hA : ∀ e ∈ A, x ∈ G.edge e)
    (hxU : x ∉ U) (D b : ℕ)
    (hparallel : ∀ v ∈ U, (G.parallelEdges x v).card ≤ b)
    (hbase : ∀ v ∈ U, (F.filter (fun j => v ∈ G.edgeSupport (C j))).card ≤ D) :
    ∀ v ∈ U, (F.filter (fun j =>
      v ∈ G.edgeSupport (starExtendedClasses C A c j))).card ≤ D+b := by
  intro v hv
  have hvx : v ≠ x := fun hh => hxU (hh ▸ hv)
  have hstar := (coloredStarCopies_support_load_le_parallel G x A c hA v hvx).trans
    (hparallel v hv)
  have hsub : F.filter (fun j => v ∈ G.edgeSupport (starExtendedClasses C A c j)) ⊆
      F.filter (fun j => v ∈ G.edgeSupport (C j)) ∪
      univ.filter (fun j => v ∈ G.edgeSupport (coloredStarCopies A c j)) := by
    intro j hj
    obtain ⟨hjF,hvj⟩ := mem_filter.mp hj
    obtain ⟨e,he,hve⟩ := (G.mem_edgeSupport _ v).mp hvj
    rcases mem_union.mp he with heC | heS
    · exact mem_union_left _ (mem_filter.mpr ⟨hjF,
        (G.mem_edgeSupport _ v).mpr ⟨e,heC,hve⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,
        (G.mem_edgeSupport _ v).mpr ⟨e,heS,hve⟩⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add (hbase v hv) hstar))

/-- The second resource bound is needed only in its own remaining palette. -/
theorem starExtended_available_starWeight_le
    (C : Fin h → Finset E) (F : Finset (Fin h)) (x z : V) (U : Finset V)
    (A : Finset E) (c : A → Fin h) (hc : Function.Injective c)
    (hA : ∀ e ∈ A, x ∈ G.edge e) (hxU : x ∉ U) (W b : ℕ)
    (hparallel : ∀ v ∈ U, (G.parallelEdges z v).card ≤ b)
    (hbase : ∀ j ∈ F, starWeight G z U (C j) ≤ W) :
    ∀ j ∈ F, starWeight G z U (starExtendedClasses C A c j) ≤ W+b := by
  intro j hj
  exact (starWeight_union_le G z U _ _).trans (Nat.add_le_add (hbase j hj)
    (coloredStarCopies_starWeight_le G z U x A c hc hA hxU b hparallel j))

/-- Construct two compatible actual star extensions sequentially. The
initial load and weight assumptions are restricted to each available
palette, so no global joining-degree bound is imposed on protected colors.
The actual copy/free-palette cardinalities remain explicit inputs. -/
theorem exists_two_star_extension_on_available
    (C : Fin h → Finset E) (x y : V) (U₀ U₁ : Finset V)
    (A₀ A₁ : Finset E) (F₀ F₁ : Finset (Fin h)) (D b s : ℕ)
    (hA₀ : A₀ ⊆ exceptionCorePool G x U₀)
    (hA₁ : A₁ ⊆ exceptionCorePool G y U₁)
    (hxy : x ≠ y) (hyU₀ : y ∉ U₀) (hxU₁ : x ∉ U₁)
    (hcard₀ : A₀.card = F₀.card) (hcard₁ : A₁.card = F₁.card)
    (hlower₀ : h-s-D ≤ A₀.card) (hlower₁ : h-s-D ≤ A₁.card)
    (hb : b ≤ D) (hD : 128*D ≤ h) (hs : 2*s ≤ h)
    (hmatching : ∀ j, G.IsMatching (C j))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hAC₀ : ∀ j, Disjoint A₀ (C j)) (hAC₁ : ∀ j, Disjoint A₁ (C j))
    (hfree₀ : ∀ j ∈ F₀, x ∉ G.edgeSupport (C j))
    (hfree₁ : ∀ j ∈ F₁, y ∉ G.edgeSupport (C j))
    (hload₀ : ∀ v ∈ U₀, (F₀.filter (fun j => v ∈ G.edgeSupport (C j))).card ≤ D)
    (hload₁ : ∀ v ∈ U₁, (F₁.filter (fun j => v ∈ G.edgeSupport (C j))).card ≤ D)
    (hweight₀ : ∀ j ∈ F₀, starWeight G x U₀ (C j) ≤ h/8)
    (hweight₁ : ∀ j ∈ F₁, starWeight G y U₁ (C j) ≤ h/8)
    (hparallel₀ : ∀ v ∈ U₁, (G.parallelEdges x v).card ≤ b)
    (hparallel₁ : ∀ v ∈ U₁, (G.parallelEdges y v).card ≤ b) :
    ∃ (f₀ : A₀ ≃ F₀) (f₁ : A₁ ≃ F₁),
      let C₁ := starExtendedClasses C A₀ (fun e => (f₀ e).val)
      let C₂ := starExtendedClasses C₁ A₁ (fun e => (f₁ e).val)
      (∀ j, G.IsMatching (C₂ j)) ∧
      Pairwise (fun i j => Disjoint (C₂ i) (C₂ j)) ∧
      univ.biUnion C₂ = univ.biUnion C ∪ A₀ ∪ A₁ ∧
      (∀ j, C j ⊆ C₂ j) ∧
      (∀ j, (C₂ j).card ≤ (C j).card+2) ∧
      (∀ j, (G.edgeSupport (C₂ j)).card ≤ (G.edgeSupport (C j)).card+4) ∧
      (∀ j ∉ F₀ ∪ F₁, C₂ j = C j) ∧
      (∀ j ∈ F₀, x ∈ G.edgeSupport (C₂ j)) ∧
      (∀ j ∈ F₁, y ∈ G.edgeSupport (C₂ j)) ∧
      (∀ e : A₀, e.val ∈ C₂ (f₀ e).val) ∧
      (∀ e : A₁, e.val ∈ C₂ (f₁ e).val) := by
  have hinc₀ : ∀ e ∈ A₀, x ∈ G.edge e := fun e he => (mem_filter.mp (hA₀ he)).2.1
  have hinc₁ : ∀ e ∈ A₁, y ∈ G.edge e := fun e he => (mem_filter.mp (hA₁ he)).2.1
  have hAA : Disjoint A₀ A₁ := star_pools_disjoint G x y U₀ U₁ A₀ A₁ hA₀ hA₁ hxy hyU₀
  obtain ⟨f₀,hm₀,hd₀,hcover₀,hsub₀,hsize₀,hsupport₀,houtside₀⟩ :=
    exists_star_extension_on_available G C x U₀ A₀ F₀ D b s hA₀ hcard₀ hlower₀ hb hD hs
      hmatching hdisjoint hAC₀ hfree₀
      (fun v hv => (hload₀ v hv).trans (Nat.le_add_right D b))
      (fun j hj => (hweight₀ j hj).trans (Nat.le_add_right (h/8) b))
  let c₀ : A₀ → Fin h := fun e => (f₀ e).val
  let C₁ := starExtendedClasses C A₀ c₀
  have hc₀ : Function.Injective c₀ := Subtype.val_injective.comp f₀.injective
  have hAC₁' : ∀ j, Disjoint A₁ (C₁ j) := by
    intro j
    exact disjoint_union_right.mpr ⟨hAC₁ j,
      hAA.symm.mono_right (coloredStarCopies_subset A₀ c₀ j)⟩
  have hfree₁' : ∀ j ∈ F₁, y ∉ G.edgeSupport (C₁ j) := by
    intro j hj hy
    obtain ⟨e,he,hye⟩ := (G.mem_edgeSupport _ y).mp hy
    rcases mem_union.mp he with heC | heS
    · exact hfree₁ j hj ((G.mem_edgeSupport _ y).mpr ⟨e,heC,hye⟩)
    · exact coloredStarCopies_avoids_other_center G x y U₀ A₀ c₀ hA₀ hxy hyU₀ j
        ((G.mem_edgeSupport _ y).mpr ⟨e,heS,hye⟩)
  have hload₁' : ∀ v ∈ U₁, (F₁.filter (fun j => v ∈ G.edgeSupport (C₁ j))).card ≤ D+b :=
    starExtended_available_support_load_le G C F₁ x U₁ A₀ c₀ hinc₀ hxU₁ D b
      hparallel₀ hload₁
  have hweight₁' : ∀ j ∈ F₁, starWeight G y U₁ (C₁ j) ≤ h/8+b :=
    starExtended_available_starWeight_le G C F₁ x y U₁ A₀ c₀ hc₀ hinc₀ hxU₁ (h/8) b
      hparallel₁ hweight₁
  obtain ⟨f₁,hm₁,hd₁,hcover₁,hsub₁,hsize₁,hsupport₁,houtside₁⟩ :=
    exists_star_extension_on_available G C₁ y U₁ A₁ F₁ D b s hA₁ hcard₁ hlower₁ hb hD hs
      hm₀ hd₀ hAC₁' hfree₁' hload₁' hweight₁'
  refine ⟨f₀,f₁,hm₁,hd₁,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hcover₀] at hcover₁
    exact hcover₁
  · intro j
    exact (hsub₀ j).trans (hsub₁ j)
  · intro j
    have h₀ := hsize₀ j
    have h₁ := hsize₁ j
    omega
  · intro j
    have h₀ := hsupport₀ j
    have h₁ := hsupport₁ j
    omega
  · intro j hj
    have hj₀ := (notMem_union.mp hj).1
    have hj₁ := (notMem_union.mp hj).2
    exact (houtside₁ j hj₁).trans (houtside₀ j hj₀)
  · intro j hj
    have hx := starExtended_covers_available G C A₀ F₀ f₀ x hinc₀ j hj
    obtain ⟨e,he,hxe⟩ := (G.mem_edgeSupport _ x).mp hx
    exact (G.mem_edgeSupport _ x).mpr ⟨e,hsub₁ j he,hxe⟩
  · exact starExtended_covers_available G C₁ A₁ F₁ f₁ y hinc₁
  · intro e
    exact hsub₁ _ (starExtended_contains_assigned_copy C A₀ (fun q => (f₀ q).val) e)
  · exact starExtended_contains_assigned_copy C₁ A₁ (fun q => (f₁ q).val)

end Overfull.NativeStar
