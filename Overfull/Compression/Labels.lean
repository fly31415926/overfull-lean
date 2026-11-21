import Overfull.Compression.Parity
import Overfull.MatchingProbability

namespace Overfull.Compression

open Finset Classical FractionalMatching MatchingProbability
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- A parity-preserving choice from an arbitrary finite family of actual
joining edges, with their two distinct core labels. -/
theorem exists_endpoint_parity_forest (E : Finset α) (left right : α → Fin 4)
    (hne : ∀ e ∈ E, left e ≠ right e) :
    ∃ T : Finset α, ∃ label : α → LabelPair, T ⊆ E ∧ T.card ≤ 3 ∧
      (∀ i : Fin 4,
        (T.filter (fun e => left e = i ∨ right e = i)).card % 2 =
          (E.filter (fun e => left e = i ∨ right e = i)).card % 2) ∧
      (∀ e ∈ E, (label e).val = {left e, right e}) ∧
      Set.InjOn label T ∧ LeafForest (T.image label) := by
  let label : α → LabelPair := fun e =>
    if h : left e = right e then ⟨{0, 1}, by decide⟩
    else ⟨{left e, right e}, by simp [h]⟩
  have hlabel (e : α) (he : e ∈ E) (i : Fin 4) :
      i ∈ (label e).val ↔ left e = i ∨ right e = i := by
    simp [label, hne e he, eq_comm]
  obtain ⟨T, hTE, hTcard, hpar, hinj, hforest⟩ := exists_parity_subset E label
  refine ⟨T, label, hTE, hTcard, ?_, ?_, hinj, hforest⟩
  · intro i
    have hT : copyDegree T label i = (T.filter (fun e => left e = i ∨ right e = i)).card := by
      unfold copyDegree
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact and_congr_right (fun he => hlabel e (hTE he) i)
    have hE : copyDegree E label i = (E.filter (fun e => left e = i ∨ right e = i)).card := by
      unfold copyDegree
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact and_congr_right (fun he => hlabel e he i)
    simpa only [hT, hE] using hpar i
  · intro e he
    simp [label, hne e he]

variable {V I : Type*}

/-- The core label of a vertex in a core; the arbitrary value outside the
cores is never used for a joining edge. -/
noncomputable def coreLabel (U : I → Finset V) (code : I ↪ Fin 4) (v : V) : Fin 4 :=
  if h : ∃ i, v ∈ U i then code h.choose else 0

theorem coreLabel_of_mem (U : I → Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    {v : V} {i : I} (hv : v ∈ U i) : coreLabel U code v = code i := by
  have hex : ∃ j, v ∈ U j := ⟨i, hv⟩
  have heq : hex.choose = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint _ _ hne) hex.choose_spec hv
  simp only [coreLabel, dif_pos hex, heq]

theorem coreLabel_eq_iff (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    {v : V} (hv : v ∉ Z) (i : I) : coreLabel U code v = code i ↔ v ∈ U i := by
  obtain ⟨j, hj⟩ := (hcover v).resolve_left hv
  rw [coreLabel_of_mem U code hdisjoint hj]
  constructor
  · intro h
    exact code.injective h ▸ hj
  · intro hi
    exact (coreLabel_of_mem U code hdisjoint hj).symm.trans
      (coreLabel_of_mem U code hdisjoint hi)

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def exceptionalEdges (M : G.Subgraph) (Z : Finset V) : Finset G.edgeSet :=
  (matchingEdges M).filter (fun e => firstEnd e ∈ Z ∨ secondEnd e ∈ Z)

noncomputable def joiningEdges (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) : Finset G.edgeSet :=
  (matchingEdges M).filter (fun e => firstEnd e ∉ Z ∧ secondEnd e ∉ Z ∧
    coreLabel U code (firstEnd e) ≠ coreLabel U code (secondEnd e))

/-- All actual matching edges with both endpoints outside the exceptional set. -/
noncomputable def nonexceptionalEdges (F : G.Subgraph) (Z : Finset V) : Finset G.edgeSet :=
  (matchingEdges F).filter (fun e => firstEnd e ∉ Z ∧ secondEnd e ∉ Z)

/-- The actual joining edges project injectively to a forest on at most four
core labels. The equality of label pairs includes every nonexceptional edge. -/
noncomputable def JoiningForest (U : I → Finset V) (Z : Finset V) (F : G.Subgraph) : Prop :=
  ∃ code : I ↪ Fin 4, ∃ label : G.edgeSet → LabelPair,
    (nonexceptionalEdges G F Z).card ≤ 3 ∧
    (∀ e ∈ nonexceptionalEdges G F Z,
      (label e).val = {coreLabel U code (firstEnd e), coreLabel U code (secondEnd e)}) ∧
    Set.InjOn label (nonexceptionalEdges G F Z) ∧
    LeafForest ((nonexceptionalEdges G F Z).image label)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crosses_core_iff (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (e : G.edgeSet) (ha : firstEnd e ∉ Z) (hb : secondEnd e ∉ Z) (i : I) :
    ((firstEnd e ∈ U i) ≠ (secondEnd e ∈ U i)) ↔
      coreLabel U code (firstEnd e) ≠ coreLabel U code (secondEnd e) ∧
      (coreLabel U code (firstEnd e) = code i ∨
        coreLabel U code (secondEnd e) = code i) := by
  rw [← coreLabel_eq_iff U Z code hdisjoint hcover ha i,
    ← coreLabel_eq_iff U Z code hdisjoint hcover hb i]
  by_cases h₁ : coreLabel U code (firstEnd e) = code i <;>
    by_cases h₂ : coreLabel U code (secondEnd e) = code i <;> simp_all [eq_comm]

/-- A core cut consists of its exceptional matching edges and exactly the
joining edges incident with its core label. -/
theorem matching_core_cut_partition (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (i : I) :
    cutCount (matchingEdges M) (U i) =
      cutCount (exceptionalEdges G M Z) (U i) +
        ((joiningEdges G M U Z code).filter (fun e =>
          coreLabel U code (firstEnd e) = code i ∨
            coreLabel U code (secondEnd e) = code i)).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := cutEdges (matchingEdges M) (U i))
    (fun e : G.edgeSet => firstEnd e ∈ Z ∨ secondEnd e ∈ Z)
  have h₁ : (cutEdges (matchingEdges M) (U i)).filter
      (fun e => firstEnd e ∈ Z ∨ secondEnd e ∈ Z) =
      cutEdges (exceptionalEdges G M Z) (U i) := by
    ext e
    simp [cutEdges, exceptionalEdges, Lovasz.BMatch.cut, and_comm, and_left_comm]
  have h₂ : (cutEdges (matchingEdges M) (U i)).filter
      (fun e => ¬(firstEnd e ∈ Z ∨ secondEnd e ∈ Z)) =
      (joiningEdges G M U Z code).filter (fun e =>
        coreLabel U code (firstEnd e) = code i ∨
          coreLabel U code (secondEnd e) = code i) := by
    ext e
    simp only [cutEdges, joiningEdges, Lovasz.BMatch.cut, Finset.mem_filter]
    by_cases ha : firstEnd e ∈ Z
    · simp [ha]
    by_cases hb : secondEnd e ∈ Z
    · simp [hb]
    simp only [ha, hb, false_or, not_false_eq_true, and_true, true_and]
    rw [crosses_core_iff G U Z code hdisjoint hcover e ha hb i]
    tauto
  rw [h₁, h₂] at h
  exact h.symm

/-- Joining edges selected from the projection have no endpoint in the
exceptional set, so they are disjoint from the retained exceptional edges. -/
theorem exceptional_disjoint_joining (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) :
    Disjoint (exceptionalEdges G M Z) (joiningEdges G M U Z code) := by
  apply Finset.disjoint_left.mpr
  intro e he hj
  have he' := (Finset.mem_filter.mp he).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact he'.elim hj'.1 hj'.2.1

/-- The core cut of the retained matching has the same exceptional part. -/
theorem selected_core_cut_partition (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (T : Finset G.edgeSet) (hT : T ⊆ joiningEdges G M U Z code) (i : I) :
    cutCount (exceptionalEdges G M Z ∪ T) (U i) =
      cutCount (exceptionalEdges G M Z) (U i) +
        (T.filter (fun e => coreLabel U code (firstEnd e) = code i ∨
          coreLabel U code (secondEnd e) = code i)).card := by
  have hdis : Disjoint (exceptionalEdges G M Z) T :=
    (exceptional_disjoint_joining G M U Z code).mono_right hT
  have hcut : cutEdges T (U i) = T.filter (fun e =>
      coreLabel U code (firstEnd e) = code i ∨
        coreLabel U code (secondEnd e) = code i) := by
    ext e
    simp only [cutEdges, Lovasz.BMatch.cut, Finset.mem_filter]
    apply and_congr_right
    intro he
    have hj := (Finset.mem_filter.mp (hT he)).2
    rw [crosses_core_iff G U Z code hdisjoint hcover e hj.1 hj.2.1 i]
    exact and_iff_right hj.2.2
  have hcutdis : Disjoint (cutEdges (exceptionalEdges G M Z) (U i)) (cutEdges T (U i)) := by
    apply hdis.mono
    · intro e he
      have he' : e ∈ exceptionalEdges G M Z ∧ ((firstEnd e ∈ U i) ≠ (secondEnd e ∈ U i)) := by
        simpa only [cutEdges, Lovasz.BMatch.cut, Finset.mem_filter] using he
      exact he'.1
    · intro e he
      have he' : e ∈ T ∧ ((firstEnd e ∈ U i) ≠ (secondEnd e ∈ U i)) := by
        simpa only [cutEdges, Lovasz.BMatch.cut, Finset.mem_filter] using he
      exact he'.1
  unfold cutCount cutEdges Lovasz.BMatch.cut
  rw [Finset.filter_union]
  change (cutEdges (exceptionalEdges G M Z) (U i) ∪ cutEdges T (U i)).card = _
  rw [Finset.card_union_of_disjoint hcutdis, hcut]
  rfl

/-- Retaining exceptional edges and joining edges keeps no edge internal
to any one core. -/
theorem selected_edge_not_internal (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (T : Finset G.edgeSet) (hT : T ⊆ joiningEdges G M U Z code)
    (e : G.edgeSet) (he : e ∈ exceptionalEdges G M Z ∪ T) (i : I) :
    ¬(firstEnd e ∈ U i ∧ secondEnd e ∈ U i) := by
  rintro ⟨ha, hb⟩
  rcases Finset.mem_union.mp he with he | he
  · rcases (Finset.mem_filter.mp he).2 with hz | hz
    · exact Finset.disjoint_left.mp (hUZ i) ha hz
    · exact Finset.disjoint_left.mp (hUZ i) hb hz
  · have hne := (Finset.mem_filter.mp (hT he)).2.2.2
    exact hne ((coreLabel_of_mem U code hdisjoint ha).trans
      (coreLabel_of_mem U code hdisjoint hb).symm)

theorem selected_insideCount_eq_zero (M : G.Subgraph) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (T : Finset G.edgeSet) (hT : T ⊆ joiningEdges G M U Z code) (i : I) :
    insideCount (exceptionalEdges G M Z ∪ T) (U i) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' : e ∈ exceptionalEdges G M Z ∪ T ∧
      firstEnd e ∈ U i ∧ secondEnd e ∈ U i := by
    simpa only [Lovasz.BMatch.inside, Finset.mem_filter] using he
  exact selected_edge_not_internal G M U Z code hdisjoint hUZ T hT e he'.1 i he'.2

/-- Actual core cut parity is retained by the finite projected selection. -/
theorem selected_core_cut_parity (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (T : Finset G.edgeSet) (hT : T ⊆ joiningEdges G M U Z code)
    (hpar : ∀ j : Fin 4,
      (T.filter (fun e => coreLabel U code (firstEnd e) = j ∨
        coreLabel U code (secondEnd e) = j)).card % 2 =
      ((joiningEdges G M U Z code).filter (fun e =>
        coreLabel U code (firstEnd e) = j ∨
          coreLabel U code (secondEnd e) = j)).card % 2) (i : I) :
    cutCount (exceptionalEdges G M Z ∪ T) (U i) % 2 = (U i).card % 2 := by
  have h₁ := matching_core_cut_partition G M U Z code hdisjoint hcover i
  have h₂ := selected_core_cut_partition G M U Z code hdisjoint hcover T hT i
  have h₃ := matching_cut_handshake M hM (U i)
  have h₄ := hpar (code i)
  omega

end Overfull.Compression
