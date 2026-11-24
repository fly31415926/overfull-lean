import Overfull.BoundaryExtension.Residual
import Overfull.RobustRealization.Relabeling
import Overfull.RobustStability

/-!
# The actual core after reserving original host copies

The reserved set is an explicit set of original copies. Its existence and
its degree specifications are not assumed to follow from an absorber. This
file constructs the surviving core and complementary graph, identifies their
copies exactly, and proves the degree and robustness consequences used in
Section 6's final packing stage.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.ReservedCore

open Finset Classical SmallCuts SimpleGraph BoundaryExtension
open BipartitePackingAccounting

variable {V E : Type*}
variable {G : Multigraph V E} {U : Finset V}

/-- The simple core edges whose specified original copies are reserved. -/
def reservedGraph (C : Core G U) (T : Finset E) : SimpleGraph U where
  Adj u v := ∃ h : C.graph.Adj u v,
    C.edgeMap (⟨s(u, v), h⟩ : C.graph.edgeSet) ∈ T
  symm := by
    intro u v h
    obtain ⟨huv, ht⟩ := h
    refine ⟨huv.symm, ?_⟩
    have he : (⟨s(v, u), huv.symm⟩ : C.graph.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext Sym2.eq_swap
    rwa [he]
  loopless := by
    intro v h
    exact C.graph.loopless v h.choose

theorem reservedGraph_le (C : Core G U) (T : Finset E) : reservedGraph C T ≤ C.graph := by
  intro u v h
  exact h.choose

/-- Every actual simple core edge is reserved exactly when its original
embedded copy belongs to the reserved set. -/
theorem coreCopy_reserved_iff (C : Core G U) (T : Finset E) (e : C.graph.edgeSet) :
    e.val ∈ (reservedGraph C T).edgeSet ↔ C.edgeMap e ∈ T := by
  rcases e with ⟨⟨u, v⟩, he⟩
  change (∃ h : C.graph.Adj u v, C.edgeMap ⟨s(u, v), h⟩ ∈ T) ↔
    C.edgeMap ⟨s(u, v), he⟩ ∈ T
  exact ⟨fun h => h.choose_spec, fun h => ⟨he, h⟩⟩

/-- All unreserved original core edges, including unused reserve edges. -/
def remainingGraph (C : Core G U) (T : Finset E) : SimpleGraph U :=
  C.graph \ reservedGraph C T

theorem remainingGraph_le (C : Core G U) (T : Finset E) :
    remainingGraph C T ≤ C.graph := sdiff_le

/-- Core-edge survival is decided by original-copy identity. -/
theorem coreCopy_survives_iff (C : Core G U) (T : Finset E) (e : C.graph.edgeSet) :
    e.val ∈ (remainingGraph C T).edgeSet ↔ C.edgeMap e ∉ T := by
  rcases e with ⟨⟨u, v⟩, he⟩
  change (C.graph.Adj u v ∧ ¬ (reservedGraph C T).Adj u v) ↔ _
  have hadj : C.graph.Adj u v := he
  rw [and_iff_right hadj]
  exact not_congr (coreCopy_reserved_iff C T ⟨s(u, v), he⟩)

variable [Fintype E]

/-- The ambient remainder retains exactly the unreserved original copies. -/
def remainingHost (G : Multigraph V E) (T : Finset E) : Multigraph V ↥(Tᶜ) :=
  G.restrictEdges Tᶜ

/-- The surviving simple graph, embedded by the same original host copies. -/
def core (C : Core G U) (T : Finset E) : Core (remainingHost G T) U :=
  subcoreInRestriction C (remainingGraph C T) (remainingGraph_le C T) T
    (fun e => (coreCopy_survives_iff C T
      ⟨e.val, SimpleGraph.edgeSet_mono (remainingGraph_le C T) e.property⟩).mp e.property)

@[simp] theorem core_graph (C : Core G U) (T : Finset E) :
    (core C T).graph = remainingGraph C T := rfl

@[simp] theorem core_edgeMap_val (C : Core G U) (T : Finset E)
    (e : (remainingGraph C T).edgeSet) :
    ((core C T).edgeMap e).val =
      C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono (remainingGraph_le C T) e.property⟩ := rfl

/-- Among surviving copies, the new core consists of exactly the original
core copies. No endpoint-based identification of parallel edges is used. -/
theorem mem_coreEdges_iff (C : Core G U) (T : Finset E) (e : ↥(Tᶜ)) :
    e ∈ OneCore.coreEdges (core C T) ↔ e.val ∈ OneCore.coreEdges C := by
  constructor
  · intro he
    obtain ⟨f, hf⟩ := (OneCore.mem_coreEdges (core C T) e).mp he
    refine (OneCore.mem_coreEdges C e.val).mpr ⟨
      ⟨f.val, SimpleGraph.edgeSet_mono (remainingGraph_le C T) f.property⟩, ?_⟩
    exact congrArg Subtype.val hf
  · intro he
    obtain ⟨f, hf⟩ := (OneCore.mem_coreEdges C e.val).mp he
    have hsurvive : C.edgeMap f ∉ T := by
      rw [hf]
      exact mem_compl.mp e.property
    have hrem := (coreCopy_survives_iff C T f).mpr hsurvive
    refine (OneCore.mem_coreEdges (core C T) e).mpr ⟨⟨f.val, hrem⟩, ?_⟩
    exact Subtype.ext hf

/-- The complementary copies of the actual surviving core. -/
def exterior (C : Core G U) (T : Finset E) :
    Multigraph V ↥((OneCore.coreEdges (core C T))ᶜ) :=
  (remainingHost G T).restrictEdges (OneCore.coreEdges (core C T))ᶜ

/-- The residual exterior contains exactly the surviving original exterior. -/
theorem mem_exterior_iff (C : Core G U) (T : Finset E) (e : ↥(Tᶜ)) :
    e ∈ (OneCore.coreEdges (core C T))ᶜ ↔ e.val ∉ OneCore.coreEdges C := by
  rw [mem_compl, mem_coreEdges_iff]

/-- Forget the two surviving-copy subtypes, preserving the original exterior
copy and its endpoints. -/
def exteriorOriginal (C : Core G U) (T : Finset E) :
    ↥((OneCore.coreEdges (core C T))ᶜ) ↪ ↥((OneCore.coreEdges C)ᶜ) where
  toFun e := ⟨e.val.val, mem_compl.mpr ((mem_exterior_iff C T e.val).mp e.property)⟩
  inj' := by
    intro e f h
    have hh := congrArg (fun a : ↥((OneCore.coreEdges C)ᶜ) => a.val) h
    exact Subtype.ext (Subtype.ext hh)

@[simp] theorem exteriorOriginal_val (C : Core G U) (T : Finset E)
    (e : ↥((OneCore.coreEdges (core C T))ᶜ)) :
    (exteriorOriginal C T e).val = e.val.val := rfl

/-- Every original complementary copy not reserved is present in the new
complement, still as that same original copy. -/
theorem exteriorOriginal_survives (C : Core G U) (T : Finset E)
    (e : ↥((OneCore.coreEdges C)ᶜ)) (he : e.val ∉ T) :
    ∃ f, exteriorOriginal C T f = e := by
  let t : ↥(Tᶜ) := ⟨e.val, mem_compl.mpr he⟩
  let f : ↥((OneCore.coreEdges (core C T))ᶜ) :=
    ⟨t, (mem_exterior_iff C T t).mpr (mem_compl.mp e.property)⟩
  exact ⟨f, Subtype.ext rfl⟩

/-- Restrict any original exterior coloring to exactly its surviving copies. -/
def exteriorColoring (C : Core G U) (T : Finset E) {k : ℕ}
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k) :
    (exterior C T).EdgeColoring k where
  color e := c.color (exteriorOriginal C T e)
  proper := by
    intro e f v hef hev hfv
    apply (exteriorOriginal C T).injective
    exact c.proper hef hev hfv

/-- Each deleted core edge is a distinct reserved original incidence. -/
theorem reservedGraph_degree_le (C : Core G U) (T : Finset E) (v : U) :
    (reservedGraph C T).degree v ≤ (G.restrictEdges T).degree v.val := by
  let D := subcoreInRestriction C (reservedGraph C T) (reservedGraph_le C T) Tᶜ
    (fun e => by
      have h := (coreCopy_reserved_iff C T
        ⟨e.val, SimpleGraph.edgeSet_mono (reservedGraph_le C T) e.property⟩).mp e.property
      simpa only [mem_compl, not_not] using h)
  have h := OneCore.core_degree_le D v
  change (reservedGraph C T).degree v ≤ (G.restrictEdges Tᶜᶜ).degree v.val at h
  rw [Multigraph.restrictEdges_degree] at h ⊢
  simpa only [compl_compl] using h

omit [Fintype E] in
/-- Exact simple-core accounting for the reserved and unreserved edges. -/
theorem core_degree_partition (C : Core G U) (T : Finset E) (v : U) :
    (remainingGraph C T).degree v + (reservedGraph C T).degree v = C.graph.degree v := by
  have h := degree_sdiff_add_of_le C.graph (reservedGraph C T) (reservedGraph_le C T) v
  simpa only [remainingGraph, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using h

/-- Reserving copies removes at most their actual degree from the core. -/
theorem core_degree_loss (C : Core G U) (T : Finset E) (v : U) :
    C.graph.degree v ≤ (remainingGraph C T).degree v + (G.restrictEdges T).degree v.val := by
  have h := core_degree_partition C T v
  have hle := reservedGraph_degree_le C T v
  omega

/-- Exact ambient incidence loss for an arbitrary explicit reserved set. -/
theorem remainingHost_degree_add (G : Multigraph V E) (T : Finset E) (v : V) :
    (remainingHost G T).degree v + (G.restrictEdges T).degree v = G.degree v :=
  OneCore.complement_degree_add G T v

/-- The actual residual core and exterior partition every residual incidence. -/
theorem core_exterior_degree_add (C : Core G U) (T : Finset E) (v : U) :
    (remainingGraph C T).degree v + (exterior C T).degree v.val =
      (remainingHost G T).degree v.val := by
  have h := OneCore.complement_degree_add_core (core C T) v
  rw [Nat.add_comm]
  convert h using 1
  congr 1
  unfold exterior
  rw [Multigraph.restrictEdges_degree, Multigraph.restrictEdges_degree]
  congr 1
  ext e
  simp

/-- The precise core degree after reserving `2*(s-r)` incidences per core vertex. -/
theorem remainingHost_degree_core (T : Finset E) (k s r : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (v : U) : (remainingHost G T).degree v.val = k - 2 * (s - r) := by
  have h := remainingHost_degree_add G T v.val
  rw [hregular, hreserved] at h
  omega

/-- The outside vertices retain exactly `k-2*s` incidences. -/
theorem remainingHost_degree_outside (T : Finset E) (k s : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v, v ∉ U → (G.restrictEdges T).degree v = 2 * s)
    (v : V) (hv : v ∉ U) : (remainingHost G T).degree v = k - 2 * s := by
  have h := remainingHost_degree_add G T v
  rw [hregular, hreserved v hv] at h
  omega

/-- The exact identity in Section 6, on the actual surviving core and exterior. -/
theorem core_exterior_identity (C : Core G U) (T : Finset E) (k s r : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (v : U) : (remainingGraph C T).degree v + (exterior C T).degree v.val =
      k - 2 * (s - r) := by
  rw [core_exterior_degree_add, remainingHost_degree_core T k s r hregular hreserved]

/-- The resulting core degree is the final palette size plus the even reserve. -/
theorem remainingHost_degree_core_eq_palette_add (T : Finset E)
    (k s r : ℕ) (hrs : r ≤ s) (hsk : 2 * s ≤ k)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (v : U) : (remainingHost G T).degree v.val = (k - 2 * s) + 2 * r := by
  rw [remainingHost_degree_core T k s r hregular hreserved]
  omega


/-- Reservation cannot increase the exterior degree at a retained core vertex. -/
theorem exterior_degree_le_original (C : Core G U) (T : Finset E) (v : U) :
    (exterior C T).degree v.val ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
  have hold := OneCore.complement_degree_add_core C v
  have hnew := core_exterior_degree_add C T v
  have hamb := remainingHost_degree_add G T v.val
  have hloss := core_degree_loss C T v
  omega

/-- The original complement error remains valid after reserving arbitrary
copies, and bounds the exact deficit from the residual nominal degree. -/
theorem core_degree_bounds (C : Core G U) (T : Finset E) (k s r : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) (v : U) :
    ((k - 2 * (s - r) : ℕ) : ℝ) - a ≤ (remainingGraph C T).degree v ∧
      (remainingGraph C T).degree v ≤ k - 2 * (s - r) ∧
      ((exterior C T).degree v.val : ℝ) ≤ a := by
  have hext := OneCore.complement_degree_le_error C k a hregular hcore v
  have hle : ((exterior C T).degree v.val : ℝ) ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
    exact_mod_cast exterior_degree_le_original C T v
  have hext' := hle.trans hext
  have hi := core_exterior_identity C T k s r hregular hreserved v
  have hiR : ((remainingGraph C T).degree v : ℝ) + (exterior C T).degree v.val =
      (k - 2 * (s - r) : ℕ) := by exact_mod_cast hi
  refine ⟨by linarith, ?_, hext'⟩
  omega

/-- The degree error required by the final robust packing is measured on
this actual surviving core. -/
theorem core_almost_regular (C : Core G U) (T : Finset E) (k s r : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) (v : U) :
    |((remainingGraph C T).degree v : ℝ) - (k - 2 * (s - r) : ℕ)| ≤ a := by
  obtain ⟨hlo, hhi, hext⟩ := core_degree_bounds C T k s r a hregular hreserved hcore v
  have hhiR : ((remainingGraph C T).degree v : ℝ) ≤ (k - 2 * (s - r) : ℕ) := by
    exact_mod_cast hhi
  have ha : 0 ≤ a := (Nat.cast_nonneg ((exterior C T).degree v.val)).trans hext
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype E] in
/-- The surviving actual core retains the original specified bipartition. -/
theorem remainingGraph_bipartite (C : Core G U) (T : Finset E) (L R : Set U)
    (hbip : C.graph.IsBipartiteWith L R) :
    (remainingGraph C T).IsBipartiteWith L R :=
  ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj h.1⟩

/-- A bounded degree of reserved copies preserves forward bipartite robust
expansion of the actual surviving core. The equivalence only names its two
sides; all graph degrees are transported exactly. -/
theorem bipartite_robust_of_degree_budget
    {A B : Type*} [Fintype A] [Fintype B]
    (C : Core G U) (T : Finset E) (e : (A ⊕ B) ≃ U) (ν τ μ : ℝ)
    (hrob : IsBipartiteRobustExpander (C.graph.comap e) ν τ)
    (hbip : (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ)
    (hbudget : ∀ v : U, ((G.restrictEdges T).degree v.val : ℝ) ≤ μ * Fintype.card A) :
    IsBipartiteRobustExpander ((remainingGraph C T).comap e) (ν - μ) τ := by
  apply IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound
    (C.graph.comap e) ((remainingGraph C T).comap e) hrob
    (fun _ _ h => h.1) hμ
  · intro b b' h
    have ht := hbip.symm.mem_of_mem_adj
      (show (.inr b : A ⊕ B) ∈ Set.range Sum.inr from ⟨b, rfl⟩) h
    rcases ht with ⟨a, ha⟩
    cases ha
  · intro b
    rw [RobustRealization.comap_equiv_degree, RobustRealization.comap_equiv_degree]
    have hloss : (C.graph.degree (e (.inr b)) : ℝ) ≤
        (remainingGraph C T).degree (e (.inr b)) +
          (G.restrictEdges T).degree (e (.inr b)).val := by
      exact_mod_cast core_degree_loss C T (e (.inr b))
    linarith [hbudget (e (.inr b))]

/-- The degree specification `2*(s-r)` discharges the robust-deletion budget
whenever that explicit reserved degree is small relative to the side order. -/
theorem bipartite_robust_of_reserved_degrees
    {A B : Type*} [Fintype A] [Fintype B]
    (C : Core G U) (T : Finset E) (e : (A ⊕ B) ≃ U) (s r : ℕ) (ν τ μ : ℝ)
    (hrob : IsBipartiteRobustExpander (C.graph.comap e) ν τ)
    (hbip : (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ)
    (hreserved : ∀ v : U, (G.restrictEdges T).degree v.val = 2 * (s - r))
    (hsmall : ((2 * (s - r) : ℕ) : ℝ) ≤ μ * Fintype.card A) :
    IsBipartiteRobustExpander ((remainingGraph C T).comap e) (ν - μ) τ := by
  apply bipartite_robust_of_degree_budget C T e ν τ μ hrob hbip hμ
  intro v
  rw [hreserved]
  exact hsmall

end Overfull.BipartiteFactorization.ReservedCore
