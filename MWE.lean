import Mathlib

example {V : Type} {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (hne : p.support.tail ≠ []) : p.support.tail.getLast hne = y := by
  sorry
