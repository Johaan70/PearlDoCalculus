import Mathlib
example {α : Type} (l : List α) (z : α)
    (hmem : z ∈ l.tail.dropLast) : z ∈ l.dropLast := by
  exact List.Sublist.subset (by cases l with
    | nil => simp
    | cons hd tl =>
      simp only [List.tail_cons]
      cases tl with
      | nil => simp
      | cons h t =>
        simp only [List.dropLast]
        exact List.sublist_cons_self _ _) hmem
