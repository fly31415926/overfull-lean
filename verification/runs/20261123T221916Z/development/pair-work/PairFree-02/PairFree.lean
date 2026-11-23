import Overfull.ResidualPalette.JoiningGrouping
import Overfull.NativeReserve.Residual

/-!
# Exact free palettes on an exceptional pair fiber

Every edge is an actual multigraph copy. The equality of the two free
palettes follows from the already constructed whole-class cut parity;
regularity then identifies their cardinality with the parallel-copy pool.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical FourOdd
open scoped BigOperators

variable {V E K : Type*} [Fintype E] [DecidableEq K]

/-- All actual copies whose two endpoints are the specified pair. -/
def pairFiberCopies (G : Multigraph V E) (x y : V) : Finset E :=
  G.internalOn univ {x,y}

theorem mem_pairFiberCopies_iff (G : Multigraph V E) (x y : V) (e : E) :
    e ∈ pairFiberCopies G x y ↔ G.edge e = s(x,y) := by
  constructor
  · intro he
    have hh := (mem_filter.mp he).2
    simp only [mem_insert, mem_singleton] at hh
    rcases hh with ⟨hx | hy, hx' | hy'⟩
    · exact (G.endpoints_distinct e (hx.trans hx'.symm)).elim
    · rw [← G.edge_eq e, hx, hy']
    · rw [← G.edge_eq e, hy, hx']
      exact Sym2.eq_swap
    · exact (G.endpoints_distinct e (hy.trans hy'.symm)).elim
  · intro he
    have hh := (G.edge_eq e).trans he
    rcases Sym2.eq_iff.mp hh with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · simp [pairFiberCopies, Multigraph.internalOn, hx, hy]
    · simp [pairFiberCopies, Multigraph.internalOn, hx, hy]

theorem pairFiberCopies_incident (G : Multigraph V E) {x y : V} {e : E}
    (he : e ∈ pairFiberCopies G x y) (v : V) :
    v ∈ G.edge e ↔ v = x ∨ v = y := by
  rw [(mem_pairFiberCopies_iff G x y e).mp he, Sym2.mem_iff]

variable [Fintype V]
variable {G : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- Colors not yet incident at the indicated vertex. -/
def JoiningPalette.freeColors (C : JoiningPalette G label h D L p) (v : V) :
    Finset (Fin h) := univ.filter (fun j => v ∉ G.edgeSupport (C.classes j))

@[simp] theorem JoiningPalette.mem_freeColors (C : JoiningPalette G label h D L p)
    (v : V) (j : Fin h) :
    j ∈ C.freeColors v ↔ v ∉ G.edgeSupport (C.classes j) := by
  simp [JoiningPalette.freeColors]

/-- Every used color contributes exactly one distinct joining incidence. -/
theorem JoiningPalette.usedColors_card (C : JoiningPalette G label h D L p) (v : V) :
    (univ.filter (fun j => v ∈ G.edgeSupport (C.classes j))).card =
      G.degreeOn (joiningCopies G label) v := by
  have hd (j : Fin h) : G.degreeOn (C.classes j) v =
      if v ∈ G.edgeSupport (C.classes j) then 1 else 0 := by
    split_ifs with hv
    · have hlo := (G.degreeOn_pos_iff (C.classes j) v).mpr hv
      have hhi := (G.isMatching_iff_incident_card_le_one _).mp (C.matching j) v
      change G.degreeOn (C.classes j) v ≤ 1 at hhi
      omega
    · exact G.degreeOn_eq_zero_of_not_mem hv
  have hsum := removed_degreeOn G C.classes univ
    (fun _ _ _ _ hij => C.disjoint hij) v
  change G.degreeOn (univ.biUnion C.classes) v = _ at hsum
  rw [C.cover] at hsum
  simp only [hd, sum_boole] at hsum
  exact hsum.symm

/-- The common palette size splits into free colors and actual joining degree. -/
theorem JoiningPalette.freeColors_card_add_degree
    (C : JoiningPalette G label h D L p) (v : V) :
    (C.freeColors v).card + G.degreeOn (joiningCopies G label) v = h := by
  rw [← C.usedColors_card v]
  have hc := filter_card_add_filter_neg_card_eq_card
    (fun j => v ∈ G.edgeSupport (C.classes j)) (univ : Finset (Fin h))
  simpa only [card_univ, Fintype.card_fin, JoiningPalette.freeColors, add_comm] using hc

/-- In a two-vertex fiber of even cut parity, each whole class covers both
vertices or neither. -/
theorem JoiningPalette.pair_support_iff (C : JoiningPalette G label h D L p)
    (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0) (j : Fin h) :
    x ∈ G.edgeSupport (C.classes j) ↔ y ∈ G.edgeSupport (C.classes j) := by
  have hcut : (G.cutOn (C.classes j) {x,y}).card % 2 = 0 := by
    rw [← hfiber, C.cut_parity j i, hp]
  have heven : Even (({x,y} : Finset V) \ G.edgeSupport (C.classes j)).card := by
    apply ((C.matching j).uncovered_even_iff_cut_parity G {x,y}).mpr
    rw [hcut]
    simp [hxy]
  by_cases hx : x ∈ G.edgeSupport (C.classes j) <;>
    by_cases hy : y ∈ G.edgeSupport (C.classes j)
  · exact iff_of_true hx hy
  · have hh := Nat.even_iff.mp heven
    have hs : ({x,y} : Finset V) \ G.edgeSupport (C.classes j) = {y} := by
      ext v
      simp only [mem_sdiff, mem_insert, mem_singleton]
      aesop
    rw [hs, card_singleton] at hh
    omega
  · have hh := Nat.even_iff.mp heven
    have hs : ({x,y} : Finset V) \ G.edgeSupport (C.classes j) = {x} := by
      ext v
      simp only [mem_sdiff, mem_insert, mem_singleton]
      aesop
    rw [hs, card_singleton] at hh
    omega
  · exact iff_of_false hx hy

/-- The two exceptional vertices have exactly the same missing colors. -/
theorem JoiningPalette.pair_freeColors_eq (C : JoiningPalette G label h D L p)
    (i : K) (x y : V) (hxy : x ≠ y)
    (hfiber : labelShore label {i} = {x,y}) (hp : p i = 0) :
    C.freeColors x = C.freeColors y := by
  ext j
  simp only [JoiningPalette.mem_freeColors]
  exact not_congr (C.pair_support_iff i x y hxy hfiber hp j)

/-- Nonjoining incidences at a vertex of the pair fiber are exactly its
actual internal parallel copies. -/
theorem pairFiberCopies_eq_nonjoining_incidence (G : Multigraph V E)
    (label : V → K) (i : K) (x y : V)
    (hfiber : labelShore label {i} = {x,y}) :
    pairFiberCopies G x y = G.incidenceEdges x \ joiningCopies G label := by
  have hx : label x = i := by
    have hxmem : x ∈ labelShore label {i} := hfiber ▸ mem_insert_self x {y}
    simpa only [mem_labelShore, mem_singleton] using hxmem
  have hy : label y = i := by
    have hymem : y ∈ labelShore label {i} := hfiber ▸ mem_insert_of_mem (mem_singleton_self y)
    simpa only [mem_labelShore, mem_singleton] using hymem
  ext e
  constructor
  · intro he
    refine mem_sdiff.mpr ⟨(G.mem_incidenceEdges x e).mpr
      ((pairFiberCopies_incident G he x).mpr (Or.inl rfl)), ?_⟩
    intro hj
    have heq := (mem_pairFiberCopies_iff G x y e).mp he
    have hends := (G.edge_eq e).trans heq
    rcases Sym2.eq_iff.mp hends with ⟨hf,hs⟩ | ⟨hf,hs⟩
    · exact (mem_joiningCopies G label e).mp hj (by rw [hf,hs,hx,hy])
    · exact (mem_joiningCopies G label e).mp hj (by rw [hf,hs,hx,hy])
  · intro he
    obtain ⟨hinc,hnot⟩ := mem_sdiff.mp he
    have hsame : label (G.firstEnd e) = label (G.secondEnd e) := by
      by_contra hn
      exact hnot ((mem_joiningCopies G label e).mpr hn)
    have hfirst : label (G.firstEnd e) = i := by
      rcases (G.incident_iff e x).mp ((G.mem_incidenceEdges x e).mp hinc) with hf | hs
      · exact hf ▸ hx
      · rw [hs] at hsame
        exact hsame.trans hx
    have hsecond : label (G.secondEnd e) = i := hsame.symm.trans hfirst
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · rw [← hfiber]
      simpa only [mem_labelShore, mem_singleton] using hfirst
    · rw [← hfiber]
      simpa only [mem_labelShore, mem_singleton] using hsecond

/-- The size of the actual parallel-copy pool is precisely the number of
free colors; this equality is derived from regularity and exact coverage. -/
theorem JoiningPalette.pair_freeColors_card (C : JoiningPalette G label h D L p)
    (i : K) (x y : V) (hfiber : labelShore label {i} = {x,y})
    (hdegree : G.degree x = h) :
    (pairFiberCopies G x y).card = (C.freeColors x).card := by
  have hsplit := card_sdiff_add_card_inter (G.incidenceEdges x) (joiningCopies G label)
  have hinter : (G.incidenceEdges x ∩ joiningCopies G label).card =
      G.degreeOn (joiningCopies G label) x := by
    congr 1
    ext e
    simp only [mem_inter, Multigraph.mem_incidenceEdges, mem_filter]
    exact and_comm
  rw [← pairFiberCopies_eq_nonjoining_incidence G label i x y hfiber, hinter] at hsplit
  change (pairFiberCopies G x y).card + G.degreeOn (joiningCopies G label) x =
    G.degree x at hsplit
  rw [hdegree] at hsplit
  have hfree := C.freeColors_card_add_degree x
  omega

/-- Pair copies are disjoint from all joining copies, independently of
their multiplicities. -/
theorem pairFiberCopies_disjoint_joining (G : Multigraph V E) (label : V → K)
    (i : K) (x y : V) (hfiber : labelShore label {i} = {x,y}) :
    Disjoint (pairFiberCopies G x y) (joiningCopies G label) := by
  rw [pairFiberCopies_eq_nonjoining_incidence G label i x y hfiber]
  exact sdiff_disjoint

end Overfull.NativeReserve
