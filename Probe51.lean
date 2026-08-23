import Mathlib
example {A B : Type} (h : A = B) (b : A) (a : B) :
    (cast h b = a) ↔ (b = cast h.symm a) := by
  subst h
  simp
