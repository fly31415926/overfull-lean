import Overfull.BipartiteMatching
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Short augmenting paths in a bipartite robust expander

The matching is a subgraph of the complete ambient graph. Its edges are not
assumed to be edges of the robust expander.
-/

namespace Overfull

open Finset

private theorem simple_chain {α : Type*} {R : α → α → Prop}
    {L : List α} (hL : L.IsChain R) :
    ∃ K : List α, K.IsChain R ∧ K.Nodup ∧ K.head? = L.head? ∧
      K.getLast? = L.getLast? ∧ K.length ≤ L.length ∧
      ∀ v ∈ K, v ∈ L := by
  classical
  induction L with
  | nil => exact ⟨[], by simp⟩
  | cons a L ih =>
    obtain ⟨K, hK, hnodup, hhead, hlast, hlen, hmem⟩ := ih hL.tail
    by_cases ha : a ∈ K
    · obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp ha
      have hsplit : K = P ++ a :: Q := hPQ
      refine ⟨a :: Q, ?_, ?_, by simp, ?_, ?_, ?_⟩
      · rw [hsplit] at hK
        exact hK.right_of_append
      · rw [hsplit] at hnodup
        exact hnodup.of_append_right
      · calc
          (a :: Q).getLast? = K.getLast? := by
            rw [hsplit, List.getLast?_append_cons]
          _ = (a :: L).getLast? := by
            rw [hlast]
            cases L with
            | nil =>
              have : K = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
              simp [this] at ha
            | cons b L => simp
      · rw [hsplit, List.length_append, List.length_cons] at hlen
        simp only [List.length_cons]
        omega
      · intro v hv
        exact List.mem_cons_of_mem a (hmem v (by rw [hsplit]; simp [hv]))
    · refine ⟨a :: K, ?_, by simp [ha, hnodup], by simp, ?_, by simpa using hlen, ?_⟩
      · apply hK.cons'
        intro b hb
        have hb' : b ∈ L.head? := by rwa [hhead] at hb
        exact hL.rel_head? hb'
      · cases L with
        | nil =>
          have : K = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
          simp [this]
        | cons b L =>
          have hKne : K ≠ [] := by intro h; simp [h] at hhead
          cases K with
          | nil => exact (hKne rfl).elim
          | cons c K => simpa using hlast
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (hmem v hv)

/-- Vertices reached in at most `n` directed steps of the specified relation. -/
private noncomputable def boundedReach {α : Type*} [Fintype α]
    (R : α → α → Prop) (x : α) (n : ℕ) : Finset α := by
  classical
  exact univ.filter (fun u => ∃ L : List α,
    L.head? = some x ∧ L.getLast? = some u ∧ L.IsChain R ∧ L.length ≤ n + 1)

private theorem start_mem_boundedReach {α : Type*} [Fintype α]
    (R : α → α → Prop) (x : α) (n : ℕ) : x ∈ boundedReach R x n := by
  classical
  simp only [boundedReach, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨[x], by simp⟩

private theorem boundedReach_mono {α : Type*} [Fintype α]
    (R : α → α → Prop) (x : α) {n k : ℕ} (hnk : n ≤ k) :
    boundedReach R x n ⊆ boundedReach R x k := by
  classical
  intro u hu
  simp only [boundedReach, Finset.mem_filter, Finset.mem_univ, true_and] at *
  obtain ⟨L, hh, hl, hc, hn⟩ := hu
  exact ⟨L, hh, hl, hc, by omega⟩

private theorem step_mem_boundedReach {α : Type*} [Fintype α]
    (R : α → α → Prop) (x : α) {n : ℕ} {u v : α}
    (hu : u ∈ boundedReach R x n) (huv : R u v) :
    v ∈ boundedReach R x (n + 1) := by
  classical
  simp only [boundedReach, Finset.mem_filter, Finset.mem_univ, true_and] at *
  obtain ⟨L, hh, hl, hc, hn⟩ := hu
  have hne : L ≠ [] := by intro h; simp [h] at hh
  refine ⟨L ++ [v], ?_, by simp, ?_, by simpa using Nat.add_le_add_right hn 1⟩
  · simpa [List.head?_append_of_ne_nil _ hne] using hh
  · apply hc.append (by simp)
    intro a ha b hb
    simp only [hl, Option.mem_some_iff] at ha
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    simpa [ha, hb] using huv

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Every matching edge has its endpoints in different vertex classes. -/
def IsCrossingMatching (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) : Prop :=
  M.IsMatching ∧
    (∀ a a' : A, ¬M.Adj (.inl a) (.inl a')) ∧
    (∀ b b' : B, ¬M.Adj (.inr b) (.inr b'))

/-- One graph edge followed by one matching edge, with the latter outside `W`. -/
def alternatingStep (G : SimpleGraph (A ⊕ B))
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (W : Finset (A ⊕ B))
    (a a' : A) : Prop :=
  ∃ b : B, G.Adj (.inl a) (.inr b) ∧ M.Adj (.inl a') (.inr b) ∧
    (.inl a' : A ⊕ B) ∉ W ∧ (.inr b : A ⊕ B) ∉ W

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem matching_partner_outside
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hM : IsCrossingMatching M) (W : Finset (A ⊕ B)) (x : A) (y : B)
    (hcovered : ∀ v : A ⊕ B, v ∉ W → v ≠ .inl x → v ≠ .inr y → v ∈ M.verts)
    (hclosed : ∀ v w : A ⊕ B, v ∈ W → M.Adj v w → w ∈ W)
    {b : B} (hbW : (.inr b : A ⊕ B) ∉ W) (hby : b ≠ y) :
    ∃ a : A, M.Adj (.inl a) (.inr b) ∧ (.inl a : A ⊕ B) ∉ W := by
  have hbM : (.inr b : A ⊕ B) ∈ M.verts :=
    hcovered (.inr b) hbW (by simp) (by simpa using hby)
  obtain ⟨v, hv, _⟩ := hM.1 hbM
  cases v with
  | inl a =>
    refine ⟨a, M.symm hv, ?_⟩
    intro haW
    exact hbW (hclosed (.inl a) (.inr b) haW (M.symm hv))
  | inr b' => exact (hM.2.2 b b' hv).elim

omit [Fintype A] [Fintype B] in
private theorem card_allowed_neighbors (W : Finset (A ⊕ B)) (y : B)
    (N : Finset B) :
    N.card ≤ (N.filter (fun b => (.inr b : A ⊕ B) ∉ W ∧ b ≠ y)).card +
      W.card + 1 := by
  classical
  let P : B → Prop := fun b => (.inr b : A ⊕ B) ∉ W ∧ b ≠ y
  have hbad : (N.filter (fun b => ¬P b)).card ≤ (insert (.inr y) W).card := by
    apply Finset.card_le_card_of_injOn (Sum.inr : B → A ⊕ B)
    · intro b hb
      have hb' : ¬P b := (Finset.mem_filter.mp hb).2
      by_cases hbW : (.inr b : A ⊕ B) ∈ W
      · exact Finset.mem_insert_of_mem hbW
      · have hby : b = y := by by_contra h; exact hb' ⟨hbW, h⟩
        simp [hby]
    · intro b _ b' _ h
      exact Sum.inr.inj h
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card (s := N) P
  have hinsert := Finset.card_insert_le (.inr y) W
  change N.card ≤ (N.filter P).card + W.card + 1
  omega

private theorem card_neighbors_le_reached
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hM : IsCrossingMatching M) (W : Finset (A ⊕ B)) (x : A) (y : B)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hcovered : ∀ v : A ⊕ B, v ∉ W → v ≠ .inl x → v ≠ .inr y → v ∈ M.verts)
    (hclosed : ∀ v w : A ⊕ B, v ∈ W → M.Adj v w → w ∈ W)
    (n : ℕ) (S : Finset A)
    (hS : S ⊆ boundedReach (alternatingStep G M W) x n) :
    (S.biUnion (rightNeighbors G)).card ≤
      (boundedReach (alternatingStep G M W) x (n + 1)).card + W.card := by
  classical
  let N := S.biUnion (rightNeighbors G)
  let T := N.filter (fun b => (.inr b : A ⊕ B) ∉ W ∧ b ≠ y)
  let U := (boundedReach (alternatingStep G M W) x (n + 1)).erase x
  have hpartner : ∀ b : T, ∃ a : U, M.Adj (.inl (a : A)) (.inr (b : B)) := by
    intro b
    obtain ⟨hbN, hbW, hby⟩ := Finset.mem_filter.mp b.property
    obtain ⟨a, hab, haW⟩ := matching_partner_outside M hM W x y hcovered hclosed hbW hby
    obtain ⟨a₀, ha₀, ha₀b⟩ := Finset.mem_biUnion.mp hbN
    have ha₀b' : G.Adj (.inl a₀) (.inr (b : B)) := by
      simpa [rightNeighbors] using ha₀b
    have hareach : a ∈ boundedReach (alternatingStep G M W) x (n + 1) :=
      step_mem_boundedReach _ x (hS ha₀) ⟨b, ha₀b', hab, haW, hbW⟩
    have hax : a ≠ x := by
      intro h
      exact hxM (h ▸ M.edge_vert hab)
    exact ⟨⟨a, Finset.mem_erase.mpr ⟨hax, hareach⟩⟩, hab⟩
  choose f hf using hpartner
  have hf_inj : Function.Injective f := by
    intro b b' h
    apply Subtype.ext
    have hab' : M.Adj (.inl (f b : A)) (.inr (b' : B)) := by
      rw [h]
      exact hf b'
    exact Sum.inr.inj (hM.1.eq_of_adj_left (hf b) hab')
  have hTU : T.card ≤ U.card := Finset.card_le_card_of_injective hf_inj
  have hcount := card_allowed_neighbors W y N
  have hx : x ∈ boundedReach (alternatingStep G M W) x (n + 1) :=
    start_mem_boundedReach _ x _
  have herase : U.card + 1 = (boundedReach (alternatingStep G M W) x (n + 1)).card := by
    exact Finset.card_erase_add_one hx
  change N.card ≤ (boundedReach (alternatingStep G M W) x (n + 1)).card + W.card
  change N.card ≤ T.card + W.card + 1 at hcount
  omega

private theorem robust_neighbors_subset_neighbors
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (θ : ℝ) (hθ : 0 < θ) (hm : 0 < Fintype.card A) (S : Finset A) :
    bipartiteRobustNeighbors G θ S ⊆ S.biUnion (rightNeighbors G) := by
  classical
  intro b hb
  have hcount : θ * Fintype.card A ≤ ((S ∩ leftNeighbors G b).card : ℝ) := by
    simpa [bipartiteRobustNeighbors] using hb
  have hm' : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm
  have hpos : 0 < (S ∩ leftNeighbors G b).card := by
    exact_mod_cast lt_of_lt_of_le (mul_pos hθ hm') hcount
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_inter.mp ha with ⟨haS, haG⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a, haS, ?_⟩
  simpa [leftNeighbors, rightNeighbors] using haG

private theorem reached_neighbor
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hM : IsCrossingMatching M) (W : Finset (A ⊕ B)) (x : A) (y : B)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hcovered : ∀ v : A ⊕ B, v ∉ W → v ≠ .inl x → v ≠ .inr y → v ∈ M.verts)
    (hclosed : ∀ v w : A ⊕ B, v ∈ W → M.Adj v w → w ∈ W)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hW : (W.card : ℝ) ≤ min θ δ * Fintype.card A / 2 - 1)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G θ τ) :
    ∃ u ∈ boundedReach (alternatingStep G M W) x (Nat.ceil (2 / θ) + 1),
      G.Adj (.inl u) (.inr y) := by
  classical
  let X := boundedReach (alternatingStep G M W) x
  let t := Nat.ceil (2 / θ)
  have hm : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨x⟩
  have hmR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm
  have hWθ : (W.card : ℝ) ≤ θ * Fintype.card A / 2 - 1 := by
    refine hW.trans ?_
    gcongr
    exact min_le_left θ δ
  have hWδ : (W.card : ℝ) ≤ δ * Fintype.card A / 2 - 1 := by
    refine hW.trans ?_
    gcongr
    exact min_le_right θ δ
  have hδm := mul_le_mul_of_nonneg_right hδ hmR.le
  have hfirstCount : (rightNeighbors G x).card ≤ (X 1).card + W.card := by
    simpa [X] using card_neighbors_le_reached G M hM W x y hxM hcovered hclosed
      0 {x} (by simpa using start_mem_boundedReach (alternatingStep G M W) x 0)
  have hfirstCountR : ((rightNeighbors G x).card : ℝ) ≤ (X 1).card + W.card := by
    exact_mod_cast hfirstCount
  have hfirst : τ * Fintype.card A < ((X 1).card : ℝ) := by
    have hdeg := hleft x
    linarith
  have hlarge : (1 - τ) * Fintype.card A < ((X (t + 1)).card : ℝ) := by
    by_contra! hsmall
    have hmiddle : ∀ n, 1 ≤ n → n ≤ t + 1 →
        τ * Fintype.card A ≤ ((X n).card : ℝ) ∧
        ((X n).card : ℝ) ≤ (1 - τ) * Fintype.card A := by
      intro n hn hnt
      have hlow : (X 1).card ≤ (X n).card :=
        Finset.card_le_card (boundedReach_mono _ x hn)
      have hhigh : (X n).card ≤ (X (t + 1)).card :=
        Finset.card_le_card (boundedReach_mono _ x hnt)
      have hlowR : ((X 1).card : ℝ) ≤ (X n).card := by exact_mod_cast hlow
      have hhighR : ((X n).card : ℝ) ≤ (X (t + 1)).card := by exact_mod_cast hhigh
      exact ⟨hfirst.le.trans hlowR, hhighR.trans hsmall⟩
    have hgrow : ∀ n, 1 ≤ n → n ≤ t + 1 →
        ((X n).card : ℝ) + θ * Fintype.card A / 2 ≤ (X (n + 1)).card := by
      intro n hn hnt
      obtain ⟨hlo, hhi⟩ := hmiddle n hn hnt
      have hex := hexpand (X n) hlo hhi
      have hsub := Finset.card_le_card (robust_neighbors_subset_neighbors G θ hθ hm (X n))
      have hsubR : ((bipartiteRobustNeighbors G θ (X n)).card : ℝ) ≤
          ((X n).biUnion (rightNeighbors G)).card := by exact_mod_cast hsub
      have hcount := card_neighbors_le_reached G M hM W x y hxM hcovered hclosed n (X n)
        (Finset.Subset.refl _)
      have hcountR : (((X n).biUnion (rightNeighbors G)).card : ℝ) ≤
          (X (n + 1)).card + W.card := by exact_mod_cast hcount
      linarith
    have hlinear : ∀ k, k ≤ t →
        ((X 1).card : ℝ) + k * (θ * Fintype.card A / 2) ≤ (X (k + 1)).card := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hi := ih (by omega)
        have hg := hgrow (k + 1) (by omega) (by omega)
        push_cast
        nlinarith
    have hceil : (2 : ℝ) ≤ (t : ℝ) * θ :=
      (div_le_iff₀ hθ).mp (Nat.le_ceil (2 / θ))
    have htm := mul_le_mul_of_nonneg_right hceil (by positivity : (0 : ℝ) ≤ Fintype.card A / 2)
    have hlin := hlinear t le_rfl
    have hcard : ((X (t + 1)).card : ℝ) ≤ Fintype.card A := by
      exact_mod_cast Finset.card_le_univ (X (t + 1))
    have hfirstpos : (0 : ℝ) < (X 1).card := lt_trans (mul_pos hτ hmR) hfirst
    nlinarith
  by_contra! hno
  have hsub : leftNeighbors G y ⊆ Finset.univ \ X (t + 1) := by
    intro a ha
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
    intro haX
    exact hno a haX (by simpa [leftNeighbors] using ha)
  have hcard := Finset.card_le_card hsub
  have hsum : (Finset.univ \ X (t + 1)).card + (X (t + 1)).card = Fintype.card A := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (X (t + 1)))
  have hboth : (leftNeighbors G y).card + (X (t + 1)).card ≤ Fintype.card A := by omega
  have hbothR : ((leftNeighbors G y).card : ℝ) + (X (t + 1)).card ≤ Fintype.card A := by
    exact_mod_cast hboth
  have hdeg := hright y
  have hτm : (0 : ℝ) < τ * Fintype.card A := mul_pos hτ hmR
  nlinarith

/-- A simple alternating path from `x` to `y`, recorded in order.

The `length` counts matching edges; the path has `2 * length + 1` edges in
all. The edge from `left i` to `right i` belongs to `G`, and each intervening
edge from `right i` to `left (i + 1)` belongs to `M`. Both vertex lists are
injective, and all vertices avoid `W`.
-/
structure BipartiteAugmentingPath (G : SimpleGraph (A ⊕ B))
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (W : Finset (A ⊕ B)) (x : A) (y : B) where
  length : ℕ
  left : Fin (length + 1) → A
  right : Fin (length + 1) → B
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  start : left 0 = x
  finish : right (Fin.last length) = y
  graph_edges : ∀ i, G.Adj (.inl (left i)) (.inr (right i))
  matching_edges : ∀ i : Fin length,
    M.Adj (.inl (left i.succ)) (.inr (right i.castSucc))
  left_avoids : ∀ i, (.inl (left i) : A ⊕ B) ∉ W
  right_avoids : ∀ i, (.inr (right i) : A ⊕ B) ∉ W

namespace BipartiteAugmentingPath

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- The intervening matching edges are distinct as unordered graph edges. -/
theorem matching_edges_injective
    {G : SimpleGraph (A ⊕ B)} {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
    {W : Finset (A ⊕ B)} {x : A} {y : B}
    (p : BipartiteAugmentingPath G M W x y) :
    Function.Injective (fun i : Fin p.length =>
      s((.inl (p.left i.succ) : A ⊕ B), .inr (p.right i.castSucc))) := by
  intro i k hik
  have hleft : p.left i.succ = p.left k.succ := by
    rcases Sym2.eq_iff.mp hik with h | h
    · exact Sum.inl.inj h.1
    · exact (Sum.noConfusion h.1)
  exact Fin.succ_inj.mp (p.left_injective hleft)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- The graph edges along the path are not matching edges. -/
theorem graph_edges_not_matching
    {G : SimpleGraph (A ⊕ B)} {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
    {W : Finset (A ⊕ B)} {x : A} {y : B}
    (p : BipartiteAugmentingPath G M W x y) (hM : M.IsMatching)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts) :
    ∀ i, ¬M.Adj (.inl (p.left i)) (.inr (p.right i)) := by
  intro i
  induction i using Fin.cases with
  | zero =>
    intro h
    exact hxM (p.start ▸ M.edge_vert h)
  | succ i =>
    intro h
    have heq := Sum.inr.inj (hM.eq_of_adj_left h (p.matching_edges i))
    have hind := congrArg Fin.val (p.right_injective heq)
    simp only [Fin.val_succ, Fin.coe_castSucc] at hind
    omega

end BipartiteAugmentingPath

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem path_of_simple_chain
    (G : SimpleGraph (A ⊕ B))
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hM : M.IsMatching) (W : Finset (A ⊕ B)) (x : A) (y : B)
    (hyM : (.inr y : A ⊕ B) ∉ M.verts)
    (hxW : (.inl x : A ⊕ B) ∉ W) (hyW : (.inr y : A ⊕ B) ∉ W)
    (L : List A) (hhead : L.head? = some x) (u : A)
    (hlast : L.getLast? = some u) (hu : G.Adj (.inl u) (.inr y))
    (hchain : L.IsChain (alternatingStep G M W)) (hnodup : L.Nodup) :
    ∃ p : BipartiteAugmentingPath G M W x y, p.length + 1 = L.length := by
  classical
  obtain ⟨K, rfl⟩ := List.head?_eq_some_iff.mp hhead
  let a : Fin (K.length + 1) → A := (x :: K).get
  have hai : Function.Injective a := List.nodup_iff_injective_get.mp hnodup
  have hstep : ∀ i : Fin K.length, alternatingStep G M W (a i.castSucc) (a i.succ) := by
    intro i
    exact (List.isChain_iff_get.mp hchain) i.val (by simp)
  choose b hG hMedge haW hbW using hstep
  have hbi : Function.Injective b := by
    intro i k hik
    have hadj : M.Adj (.inl (a k.succ)) (.inr (b i)) := by
      rw [hik]
      exact hMedge k
    have haik := Sum.inl.inj (hM.eq_of_adj_right (hMedge i) hadj)
    exact Fin.succ_inj.mp (hai haik)
  have hbne : ∀ i, b i ≠ y := by
    intro i h
    exact hyM (h ▸ M.edge_vert (M.symm (hMedge i)))
  let r : Fin (K.length + 1) → B := Fin.lastCases y b
  have hri : Function.Injective r := by
    intro i k hik
    induction i using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
        have : y = b k := by simpa [r] using hik
        exact (hbne k this.symm).elim
    | cast i =>
      induction k using Fin.lastCases with
      | last =>
        have : b i = y := by simpa [r] using hik
        exact (hbne i this).elim
      | cast k =>
        have : b i = b k := by simpa [r] using hik
        exact congrArg Fin.castSucc (hbi this)
  have hlastA : a (Fin.last K.length) = u := by
    rw [List.getLast?_eq_getElem?] at hlast
    simpa [a, List.get_eq_getElem] using hlast
  refine ⟨{
    length := K.length
    left := a
    right := r
    left_injective := hai
    right_injective := hri
    start := by simp [a]
    finish := by simp [r]
    graph_edges := ?_
    matching_edges := ?_
    left_avoids := ?_
    right_avoids := ?_
  }, rfl⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [r, hlastA] using hu
    | cast i => simpa [r] using hG i
  · intro i
    simpa [r] using hMedge i
  · intro i
    induction i using Fin.cases with
    | zero => simpa [a] using hxW
    | succ i => exact haW i
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [r] using hyW
    | cast i => simpa [r] using hbW i

/-- Lemma 2.15: the matching has a short augmenting path avoiding `W`.

The conclusion has the manuscript's bound on the number of matching edges.
The assumptions only refer to actual graph neighborhoods and to the given
crossing matching, which need not be contained in `G`.
-/
theorem bipartite_robust_augmenting_path
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hM : IsCrossingMatching M) (W : Finset (A ⊕ B)) (x : A) (y : B)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts) (hyM : (.inr y : A ⊕ B) ∉ M.verts)
    (hxW : (.inl x : A ⊕ B) ∉ W) (hyW : (.inr y : A ⊕ B) ∉ W)
    (hcovered : ∀ v : A ⊕ B, v ∉ W → v ≠ .inl x → v ≠ .inr y → v ∈ M.verts)
    (hclosed : ∀ v w : A ⊕ B, v ∈ W → M.Adj v w → w ∈ W)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hW : (W.card : ℝ) ≤ min θ δ * Fintype.card A / 2 - 1)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G θ τ) :
    ∃ p : BipartiteAugmentingPath G M W x y, p.length ≤ Nat.ceil (2 / θ) + 1 := by
  classical
  obtain ⟨u, hu, hGu⟩ := reached_neighbor G M hM W x y hxM hcovered hclosed
    θ τ δ hθ hτ hδ hW hleft hright hexpand
  simp only [boundedReach, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨L, hhead, hlast, hchain, hlen⟩ := hu
  obtain ⟨K, hK, hnodup, hKh, hKl, hKlen, _⟩ := simple_chain hchain
  obtain ⟨p, hp⟩ := path_of_simple_chain G M hM.1 W x y hyM hxW hyW K
    (hKh.trans hhead) u (hKl.trans hlast) hGu hK hnodup
  exact ⟨p, by omega⟩

end Overfull
