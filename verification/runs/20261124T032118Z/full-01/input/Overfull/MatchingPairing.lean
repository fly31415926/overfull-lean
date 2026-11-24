import Overfull.MatchingExtension
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set

/-!
# Extending the edges of a matching to a pairing

The uncovered vertices are paired arbitrarily. Every actual matching edge
is retained as one of the resulting prescribed pairs.
-/

namespace Overfull.MatchingPairing

open Finset Classical SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

noncomputable def endpoint {M : G.Subgraph} (e : M.edgeSet) : Bool → V
  | false => e.val.out.1
  | true => e.val.out.2

theorem endpoint_pair {M : G.Subgraph} (e : M.edgeSet) :
    s(endpoint e false, endpoint e true) = e.val := e.val.out_eq

theorem endpoint_mem {M : G.Subgraph} (e : M.edgeSet) (b : Bool) :
    endpoint e b ∈ e.val := by
  rw [← endpoint_pair e]
  cases b <;> simp

theorem endpoint_covered {M : G.Subgraph} (e : M.edgeSet) (b : Bool) :
    endpoint e b ∈ M.verts :=
  Subgraph.mem_verts_of_mem_edge e.property (endpoint_mem e b)

theorem endpoint_injective {M : G.Subgraph} (e : M.edgeSet) :
    Function.Injective (endpoint e) := by
  have hne : endpoint e false ≠ endpoint e true := by
    intro h
    have hdiag : e.val.IsDiag := by rw [← endpoint_pair e, h]; simp
    exact G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset e.property) hdiag
  intro b c h
  cases b <;> cases c <;> simp_all

theorem endpoint_exists {M : G.Subgraph} (e : M.edgeSet) (v : V)
    (hv : v ∈ e.val) : ∃ b, endpoint e b = v := by
  rw [← endpoint_pair e, Sym2.mem_iff] at hv
  rcases hv with hv | hv
  · exact ⟨false, hv.symm⟩
  · exact ⟨true, hv.symm⟩

noncomputable def edgePairEquiv (M : G.Subgraph) (hM : M.IsMatching) :
    M.edgeSet × Bool ≃ M.verts :=
  Equiv.ofBijective (fun x => ⟨endpoint x.1 x.2, endpoint_covered x.1 x.2⟩) (by
    constructor
    · rintro ⟨e, b⟩ ⟨f, c⟩ h
      have hval : endpoint e b = endpoint f c := congrArg Subtype.val h
      have hef : e = f := MatchingExtension.matching_edge_eq G hM e f
        (endpoint_mem e b) (hval.symm ▸ endpoint_mem f c)
      subst f
      have hbc : b = c := endpoint_injective e hval
      subst c
      rfl
    · intro v
      obtain ⟨w, hvw, _⟩ := hM v.property
      let e : M.edgeSet := ⟨s(v.val, w), hvw⟩
      obtain ⟨b, hb⟩ := endpoint_exists e v.val (by simp [e])
      exact ⟨(e, b), Subtype.ext hb⟩)

variable [Fintype V]

/-- An actual pairing extending all edges of the given matching. -/
theorem exists_pairing_of_even_uncovered (M : G.Subgraph) (hM : M.IsMatching)
    (heven : Even (Fintype.card (M.vertsᶜ : Set V))) :
    ∃ e : (M.edgeSet ⊕ Fin (Fintype.card (M.vertsᶜ : Set V) / 2)) × Bool ≃ V,
      ∀ v w, M.Adj v w → ∃ i, s(e (i, false), e (i, true)) = s(v, w) := by
  classical
  let r := Fintype.card (M.vertsᶜ : Set V) / 2
  have hcard : Fintype.card (Fin r × Bool) = Fintype.card (M.vertsᶜ : Set V) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    obtain ⟨a, ha⟩ := heven
    dsimp [r]
    omega
  let eU : Fin r × Bool ≃ (M.vertsᶜ : Set V) := Fintype.equivOfCardEq hcard
  let e : (M.edgeSet ⊕ Fin r) × Bool ≃ V :=
    (Equiv.sumProdDistrib M.edgeSet (Fin r) Bool).trans
      ((Equiv.sumCongr (edgePairEquiv M hM) eU).trans (Equiv.Set.sumCompl M.verts))
  have hleft (a : M.edgeSet) (b : Bool) : e (Sum.inl a, b) = endpoint a b := rfl
  refine ⟨e, ?_⟩
  intro v w hvw
  let a : M.edgeSet := ⟨s(v, w), hvw⟩
  refine ⟨Sum.inl a, ?_⟩
  rw [hleft, hleft, endpoint_pair]

/-- In even order every matching extends to a partition into pairs. -/
theorem exists_pairing (M : G.Subgraph) (hM : M.IsMatching)
    (heven : Even (Fintype.card V)) :
    ∃ e : (M.edgeSet ⊕ Fin (Fintype.card (M.vertsᶜ : Set V) / 2)) × Bool ≃ V,
      ∀ v w, M.Adj v w → ∃ i, s(e (i, false), e (i, true)) = s(v, w) := by
  have hcount : Fintype.card (M.vertsᶜ : Set V) +
      2 * M.spanningCoe.edgeFinset.card = Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      TutteBerge.matching_uncovered_add_twice_edges G M hM
  have hfree : Even (Fintype.card (M.vertsᶜ : Set V)) := by
    obtain ⟨a, ha⟩ := heven
    refine ⟨Fintype.card (M.vertsᶜ : Set V) / 2, ?_⟩
    omega
  exact exists_pairing_of_even_uncovered M hM hfree

end Overfull.MatchingPairing
