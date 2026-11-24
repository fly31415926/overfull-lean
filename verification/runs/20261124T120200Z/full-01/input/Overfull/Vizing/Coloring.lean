import Vizing.EdgeColoring
import Overfull.Vizing.Graph

/-!
A complete upstream coloring gives a proper coloring of the actual unordered
edges of a mathlib graph. This adapter does not postulate a coloring theorem.
-/

namespace Overfull.VizingAdapter

variable {n c : ℕ} {G : SimpleGraph (Fin n)}

def optionColor (C : _root_.EdgeColoring.EdgeColoring c (graph G)) :
    Sym2 (Fin n) → Option (Fin c) :=
  Sym2.lift ⟨fun u v => _root_.EdgeColoring.color C (u, v),
    _root_.EdgeColoring.color_symm C⟩

theorem optionColor_isSome (C : _root_.EdgeColoring.EdgeColoring c (graph G))
    (hcomplete : ∀ u v, G.Adj u v →
      (_root_.EdgeColoring.color C (u, v)).isSome)
    (e : G.edgeSet) : (optionColor C e.val).isSome := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v => exact hcomplete u v he

def toColoring (C : _root_.EdgeColoring.EdgeColoring c (graph G))
    (hcomplete : ∀ u v, G.Adj u v →
      (_root_.EdgeColoring.color C (u, v)).isSome) : EdgeColoring G c where
  color e := (optionColor C e.val).get (optionColor_isSome C hcomplete e)
  proper := by
    intro e f v hve hvf hcol
    obtain ⟨u, heu⟩ := Sym2.mem_iff_exists.mp hve
    obtain ⟨w, hfw⟩ := Sym2.mem_iff_exists.mp hvf
    have heSome := optionColor_isSome C hcomplete e
    have hfSome := optionColor_isSome C hcomplete f
    have hopt : optionColor C e.val = optionColor C f.val := by
      rw [← Option.some_get heSome, ← Option.some_get hfSome]
      exact congrArg some hcol
    have hsame : _root_.EdgeColoring.color C (v, u) =
        _root_.EdgeColoring.color C (v, w) := by
      simpa only [heu, hfw, optionColor, Sym2.lift_mk] using hopt
    have hSome : (_root_.EdgeColoring.color C (v, u)).isSome := by
      simpa only [heu, optionColor, Sym2.lift_mk] using heSome
    have huw := _root_.EdgeColoring.color_unique_of_isSome C v u w hSome hsame
    apply Subtype.ext
    rw [heu, hfw, huw]

def enlargeColors {k : ℕ} (C : EdgeColoring G c) (h : c ≤ k) : EdgeColoring G k where
  color e := Fin.castLE h (C.color e)
  proper := by
    intro e f v hve hvf hcol
    apply C.proper hve hvf
    exact Fin.ext (congrArg (fun i : Fin k => i.val) hcol)

end Overfull.VizingAdapter
