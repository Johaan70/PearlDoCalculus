import PearlDoCalculus
open PearlDoCalculus DAG DAG.CausalModel Classical
example {V : Type} [DecidableEq V] [Fintype V] {α : V → Type} {G : DAG V}
    (M : CausalModel G α) (X Y Z : Finset V)
    (f : Assignment (α := α) (X ∪ Z) → ENNReal)
    (g : Assignment (α := α) (Y ∪ Z) → ENNReal)
    (hfactor : ∀ w : Assignment (α := α) (X ∪ Y ∪ Z),
      (M.marginal (X ∪ Y ∪ Z)) w =
        f (w.restrict (subset_union3_left_right X Y Z)) *
        g (w.restrict (subset_union3_mid_right X Y Z)))
    (w : Assignment (α := α) (X ∪ Y ∪ Z)) :
    (M.marginal (X ∪ Z)) (w.restrict (subset_union3_left_right X Y Z)) =
      f (w.restrict (subset_union3_left_right X Y Z)) *
      ∑' u : Assignment (α := α) (X ∪ Y ∪ Z),
        if w.restrict (subset_union3_left_right X Y Z) =
           u.restrict (subset_union3_left_right X Y Z)
        then g (u.restrict (subset_union3_mid_right X Y Z)) else 0 := by
  rw [← marginal_restrict M (subset_union3_left_right X Y Z), PMF.map_apply]
  rw [ENNReal.tsum_mul_left.symm]
  congr 1
  ext u
  by_cases hu : w.restrict (subset_union3_left_right X Y Z) =
      u.restrict (subset_union3_left_right X Y Z)
  · simp [hu, hfactor u]
  · simp [hu]
