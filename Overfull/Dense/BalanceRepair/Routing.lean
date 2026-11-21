import Overfull.Dense.BalanceRepair.Model

namespace Overfull.Dense.BalanceRepair

open Finset Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
  [DecidableEq A] [DecidableEq B] [DecidableEq W]

set_option maxHeartbeats 1000000 in
/-- All ordered endpoint-part cases admit actual short routes. The internal
vertices avoid the supplied set, including when the endpoints lie in it. -/
theorem exists_routing_path (G : TripartiteGraph A B W) (q k : ℝ)
    (hG : RoutingConditions G q k) (F : Finset (Vertex A B W))
    (hF : (F.card : ℝ) ≤ k) (u v : Vertex A B W) (hne : u ≠ v) :
    ∃ P : RoutingPath (arcSet G) u v, Disjoint P.internal F := by
  let T := F ∪ {u,v}
  have hT : (T.card : ℝ) ≤ k+2 := by
    have hp : ({u,v} : Finset (Vertex A B W)).card ≤ 2 := by
      simpa using Finset.card_insert_le u ({v} : Finset (Vertex A B W))
    have hu := Finset.card_union_le F ({u,v} : Finset (Vertex A B W))
    have ht : T.card ≤ F.card+2 := by dsimp [T]; omega
    have htR : (T.card : ℝ) ≤ F.card+2 := by exact_mod_cast ht
    linarith
  have avoid {x : Vertex A B W} (hx : x ∉ T) : x ∉ F :=
    fun h => hx (Finset.mem_union_left _ h)
  have source {x : Vertex A B W} (hx : x ∉ T) : x ≠ u := by
    intro h
    subst x
    exact hx (by simp [T])
  have target {x : Vertex A B W} (hx : x ∉ T) : x ≠ v := by
    intro h
    subst x
    exact hx (by simp [T])
  have iA : Function.Injective (fun a : A => (Sum.inl a : Vertex A B W)) :=
    fun _ _ h => Sum.inl.inj h
  have iB : Function.Injective (fun b : B => (Sum.inr (.inl b) : Vertex A B W)) :=
    fun _ _ h => Sum.inl.inj (Sum.inr.inj h)
  have iW : Function.Injective (fun w : W => (Sum.inr (.inr w) : Vertex A B W)) :=
    fun _ _ h => Sum.inr.inj (Sum.inr.inj h)
  have pickAB (a : A) : ∃ b : B, G.ab a b ∧ (Sum.inr (.inl b) : Vertex A B W) ∉ T := by
    obtain ⟨b,hb,hbT⟩ := choose_from_large_set _ iB (G.neighborsB a) T k hT
      (by linarith [hG.degreeA a, hG.q_nonneg])
    exact ⟨b,by simpa [TripartiteGraph.neighborsB] using hb,hbT⟩
  have pickBA (b : B) : ∃ a : A, G.ab a b ∧ (Sum.inl a : Vertex A B W) ∉ T := by
    obtain ⟨a,ha,haT⟩ := choose_from_large_set _ iA (G.neighborsA b) T k hT
      (by linarith [hG.degreeB b, hG.q_nonneg])
    exact ⟨a,by simpa [TripartiteGraph.neighborsA] using ha,haT⟩
  have pickWA (w : W) : ∃ a : A, G.aw a w ∧ (Sum.inl a : Vertex A B W) ∉ T := by
    obtain ⟨a,ha,haT⟩ := choose_from_large_set _ iA (G.linkA w) T k hT
      (by linarith [hG.largeA, hG.missingWA w])
    exact ⟨a,by simpa [TripartiteGraph.linkA] using ha,haT⟩
  have pickBW (b : B) : ∃ w : W, G.bw b w ∧ (Sum.inr (.inr w) : Vertex A B W) ∉ T := by
    obtain ⟨w,hw,hwT⟩ := choose_from_large_set _ iW (G.neighborsWB b) T k hT
      (by linarith [hG.largeW, hG.missingB b, hG.q_nonneg])
    exact ⟨w,by simpa [TripartiteGraph.neighborsWB] using hw,hwT⟩
  have commonW (a : A) (b : B) :
      ∃ w : W, G.aw a w ∧ G.bw b w ∧ (Sum.inr (.inr w) : Vertex A B W) ∉ T := by
    obtain ⟨w,ha,hb,hwT⟩ := choose_from_two_almost_complete_sets _ iW
      (G.neighborsWA a) (G.neighborsWB b) T q k hT hG.largeW
      (hG.missingA a) (hG.missingB b)
    exact ⟨w,by simpa [TripartiteGraph.neighborsWA] using ha,
      by simpa [TripartiteGraph.neighborsWB] using hb,hwT⟩
  have commonB (a : A) (w : W) :
      ∃ b : B, G.ab a b ∧ G.bw b w ∧ (Sum.inr (.inl b) : Vertex A B W) ∉ T := by
    obtain ⟨b,ha,hw,hbT⟩ := choose_from_intersection _ iB
      (G.neighborsB a) (G.linkB w) T q k hT (hG.degreeA a) (hG.missingWB w)
    exact ⟨b,by simpa [TripartiteGraph.neighborsB] using ha,
      by simpa [TripartiteGraph.linkB] using hw,hbT⟩
  have commonA (b : B) (w : W) :
      ∃ a : A, G.ab a b ∧ G.aw a w ∧ (Sum.inl a : Vertex A B W) ∉ T := by
    obtain ⟨a,hb,hw,haT⟩ := choose_from_intersection _ iA
      (G.neighborsA b) (G.linkA w) T q k hT (hG.degreeB b) (hG.missingWA w)
    exact ⟨a,by simpa [TripartiteGraph.neighborsA] using hb,
      by simpa [TripartiteGraph.linkA] using hw,haT⟩
  rcases u with a | b | w <;> rcases v with a' | b' | w'
  · obtain ⟨b,hab,hbT⟩ := pickAB a
    obtain ⟨w,ha'w,hbw,hwT⟩ := commonW a' b
    exact routingPath_three (arcSet G) (.inl a) (.inr (.inl b)) (.inr (.inr w))
      (.inl a') F (by simp) (by simp) hne (by simp) (by simp) (by simp)
      (by simpa [arc] using hab) (by simpa [arc] using hbw)
      (by simpa [arc] using ha'w) (avoid hbT) (avoid hwT)
  · obtain ⟨b,hab,hbT⟩ := pickAB a
    obtain ⟨a',ha'b',haT⟩ := pickBA b'
    obtain ⟨w,ha'w,hbw,hwT⟩ := commonW a' b
    exact routingPath_four (arcSet G) (.inl a) (.inr (.inl b)) (.inr (.inr w))
      (.inl a') (.inr (.inl b')) F (by simp) (by simp) (source haT).symm hne
      (by simp) (by simp) (target hbT) (by simp) (by simp) (by simp)
      (by simpa [arc] using hab) (by simpa [arc] using hbw)
      (by simpa [arc] using ha'w) (by simpa [arc] using ha'b')
      (avoid hbT) (avoid hwT) (avoid haT)
  · obtain ⟨b,hab,hbw',hbT⟩ := commonB a w'
    exact routingPath_two (arcSet G) (.inl a) (.inr (.inl b)) (.inr (.inr w'))
      F (by simp) hne (by simp) (by simpa [arc] using hab)
      (by simpa [arc] using hbw') (avoid hbT)
  · obtain ⟨w,ha'w,hbw,hwT⟩ := commonW a' b
    exact routingPath_two (arcSet G) (.inr (.inl b)) (.inr (.inr w)) (.inl a')
      F (by simp) hne (by simp) (by simpa [arc] using hbw)
      (by simpa [arc] using ha'w) (avoid hwT)
  · obtain ⟨a,hab',haT⟩ := pickBA b'
    obtain ⟨w,haw,hbw,hwT⟩ := commonW a b
    exact routingPath_three (arcSet G) (.inr (.inl b)) (.inr (.inr w)) (.inl a)
      (.inr (.inl b')) F (by simp) (by simp) hne (by simp) (by simp) (by simp)
      (by simpa [arc] using hbw) (by simpa [arc] using haw)
      (by simpa [arc] using hab') (avoid hwT) (avoid haT)
  · obtain ⟨w,hbw,hwT⟩ := pickBW b
    obtain ⟨a,haw,haT⟩ := pickWA w
    obtain ⟨b',hab',hb'w',hbT⟩ := commonB a w'
    exact routingPath_four (arcSet G) (.inr (.inl b)) (.inr (.inr w)) (.inl a)
      (.inr (.inl b')) (.inr (.inr w')) F (by simp) (by simp) (source hbT).symm hne
      (by simp) (by simp) (target hwT) (by simp) (by simp) (by simp)
      (by simpa [arc] using hbw) (by simpa [arc] using haw)
      (by simpa [arc] using hab') (by simpa [arc] using hb'w')
      (avoid hwT) (avoid haT) (avoid hbT)
  · obtain ⟨a,haw,haT⟩ := pickWA w
    obtain ⟨b,hab,hbT⟩ := pickAB a
    obtain ⟨w',ha'w',hbw',hwT⟩ := commonW a' b
    exact routingPath_four (arcSet G) (.inr (.inr w)) (.inl a) (.inr (.inl b))
      (.inr (.inr w')) (.inl a') F (by simp) (by simp) (source hwT).symm hne
      (by simp) (by simp) (target haT) (by simp) (by simp) (by simp)
      (by simpa [arc] using haw) (by simpa [arc] using hab)
      (by simpa [arc] using hbw') (by simpa [arc] using ha'w')
      (avoid haT) (avoid hbT) (avoid hwT)
  · obtain ⟨a,hab',haw,haT⟩ := commonA b' w
    exact routingPath_two (arcSet G) (.inr (.inr w)) (.inl a) (.inr (.inl b'))
      F (by simp) hne (by simp) (by simpa [arc] using haw)
      (by simpa [arc] using hab') (avoid haT)
  · obtain ⟨a,haw,haT⟩ := pickWA w
    obtain ⟨b,hab,hbw',hbT⟩ := commonB a w'
    exact routingPath_three (arcSet G) (.inr (.inr w)) (.inl a) (.inr (.inl b))
      (.inr (.inr w')) F (by simp) (by simp) hne (by simp) (by simp) (by simp)
      (by simpa [arc] using haw) (by simpa [arc] using hab)
      (by simpa [arc] using hbw') (avoid haT) (avoid hbT)

end Overfull.Dense.BalanceRepair
